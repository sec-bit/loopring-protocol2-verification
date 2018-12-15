Require Import
        List.

Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.

Require Import
        ERC20.

(** Tier definition *)
Definition TIER1 : uint := 3.
Definition TIER2 : uint := 2.
Definition TIER3 : uint := 1.
Definition TIER4 : uint := 0.

(** * Constants *)
Definition BURN_BASE_PERCENTAGE : uint := 100 * 10. (* 100% *)
(* Cost of upgrading the tier level of a token in a percentage of the total LRC supply *)
Definition TIER_UPGRADE_COST_PERCENTAGE : uint := 5. (* 0.5% *)
(* Burn rates *)
Definition BURN_MATCHING_TIER1 : uint := 5 * 10. (* 5% *)
Definition BURN_MATCHING_TIER2 : uint := 20 * 10. (* 20% *)
Definition BURN_MATCHING_TIER3 : uint := 40 * 10. (* 40% *)
Definition BURN_MATCHING_TIER4 : uint := 60 * 10. (* 60% *)
(* P2P *)
Definition BURN_P2P_TIER1 : uint := 5. (* 0.5% *)
Definition BURN_P2P_TIER2 : uint := 2 * 10. (* 2% *)
Definition BURN_P2P_TIER3 : uint := 3 * 10. (* 3% *)
Definition BURN_P2P_TIER4 : uint := 6 * 10. (* 6% *)

(* Defining 0x10000 in nat causes stack overflow... *)
Parameter x10000 : uint.

Parameter YEAR_TO_SECONDS : uint.

(** Here I assumed the BurnRateTable is constructed using correct LRC and WETH addresses *)
(* LRC address, WETH address *)
Parameter lrcAddress : address.
Parameter wethAddress : address.

(** * Auxiliary definitions *)

(** It seems the [BurnRateTableState] should be added to WorldState. *)
Definition get_state (wst : WorldState) : BurnRateTableState :=
  wst_burn_rate_table_state wst.

Definition set_state : WorldState -> BurnRateTableState -> WorldState :=
  wst_update_burn_rate_table.

Definition this : WorldState -> address := wst_burn_rate_table_addr.

(** * Method call specs *)

Section getTokenTier_SPEC.

  Variable (sender: address).
  Variable (token: address).

  (* function body:
     function getTokenTier(
        address token
        )
        public
        view
        returns (uint tier)
    {
        TokenData storage tokenData = tokens[token];
        // Fall back to lowest tier
        tier = (now > tokenData.validUntil) ? TIER_4 : tokenData.tier;
    }
   *)

  Definition getTIER (wst: WorldState) : uint :=
    let tokens := (burnratetable_tokens (get_state wst)) in
    let data := TokenDataMap.get tokens token in
    if Nat.ltb data.(validUntil) (block_timestamp (wst_block_state wst))
    then TIER4
    else data.(tier).

  Definition getTokenTier_require : WorldState -> Prop := fun _ => True.

  Inductive getTokenTier_trans : WorldState -> WorldState -> RetVal -> Prop :=
  | getTokenTierTrans: forall wst, getTokenTier_trans wst wst (RetUint (getTIER wst)).

  Inductive getTokenTier_events : WorldState -> list Event -> Prop :=
  | getTokenTierEvents: forall wst, getTokenTier_events wst nil.

  Definition getTokenTier_spec : FSpec :=
    mk_fspec getTokenTier_require getTokenTier_trans getTokenTier_events.

End getTokenTier_SPEC.


Section getBurnRate_SPEC.
  Variable (sender: address).
  Variable (token: address).

  (* function body:
     function getBurnRate(
        address token
        )
        external
        view
        returns (uint32 burnRate)
    {
        uint tier = getTokenTier(token);
        if (tier == TIER_1) {
            burnRate = uint32(BURN_P2P_TIER1) * 0x10000 + BURN_MATCHING_TIER1;
        } else if (tier == TIER_2) {
            burnRate = uint32(BURN_P2P_TIER2) * 0x10000 + BURN_MATCHING_TIER2;
        } else if (tier == TIER_3) {
            burnRate = uint32(BURN_P2P_TIER3) * 0x10000 + BURN_MATCHING_TIER3;
        } else {
            burnRate = uint32(BURN_P2P_TIER4) * 0x10000 + BURN_MATCHING_TIER4;
        }
    }
   *)
  Definition getRate (TIER: uint) : uint :=
    match TIER with
    (* TIER 4 *)
    | O => BURN_P2P_TIER4 * x10000 + BURN_MATCHING_TIER4
    (* TIER 3 *)
    | S O => BURN_P2P_TIER3 * x10000 + BURN_MATCHING_TIER3
    (* TIER 2 *)
    | S (S O) => BURN_P2P_TIER2 * x10000 + BURN_MATCHING_TIER2
    (* TIER 1 *)
    | S (S (S O)) => BURN_P2P_TIER1 * x10000 + BURN_MATCHING_TIER1
    (* other cases *)
    | _ => BURN_P2P_TIER4 * x10000 + BURN_MATCHING_TIER4
    end.

  Definition getBurnRate_require : WorldState -> Prop := fun _ => True.

  Inductive getBurnRate_trans : WorldState -> WorldState -> RetVal -> Prop :=
  | getBurnRateTrans: forall wst,
      getBurnRate_trans wst wst (RetUint (getRate (getTIER token wst))).

  Inductive getBurnRate_events : WorldState -> list Event -> Prop :=
  | getBurnRateEvents: forall wst, getBurnRate_events wst nil.

  Definition getBurnRate_spec : FSpec :=
    mk_fspec getBurnRate_require getBurnRate_trans getBurnRate_events.

End getBurnRate_SPEC.


Section upgradeTokenTier_SPEC.

  Variable (sender: address).
  Variable (token: address).
  (* function body
     function upgradeTokenTier(
        address token
        )
        external
        returns (bool)
    {
        require(token != 0x0, ZERO_ADDRESS);
        require(token != lrcAddress, BURN_RATE_FROZEN);
        require(token != wethAddress, BURN_RATE_FROZEN);

        uint currentTier = getTokenTier(token);

        // Can't upgrade to a higher level than tier 1
        require(currentTier != TIER_1, BURN_RATE_MINIMIZED);

        // Burn TIER_UPGRADE_COST_PERCENTAGE of total LRC supply
        BurnableERC20 LRC = BurnableERC20(lrcAddress);
        uint totalSupply = LRC.totalSupply();
        uint amount = totalSupply.mul(TIER_UPGRADE_COST_PERCENTAGE) / BURN_BASE_PERCENTAGE;
        bool success = LRC.burnFrom(msg.sender, amount);
        require(success, BURN_FAILURE);

        // Upgrade tier
        TokenData storage tokenData = tokens[token];
        tokenData.validUntil = now.add(2 * YEAR_TO_SECONDS);
        tokenData.tier = currentTier + 1;

        emit TokenTierUpgraded(token, tokenData.tier);

        return true;
    }
   *)


  Definition burnamount (totalSupply: uint) : uint :=
    Nat.div (totalSupply * TIER_UPGRADE_COST_PERCENTAGE) BURN_BASE_PERCENTAGE.

  Definition upgradetier (wst: WorldState) : WorldState * uint :=
    let tokens := burnratetable_tokens (get_state wst) in
    let data := TokenDataMap.get tokens token in
    let NOW := (block_timestamp (wst_block_state wst)) in
    let data' := mk_token_data (data.(tier) + 1) (NOW + 2 * YEAR_TO_SECONDS) in
    let tokens' := TokenDataMap.upd tokens token data' in
    (set_state wst (mk_burn_rate_table_state tokens'), data.(tier) + 1) .

  Definition upgradeTokenTier_require (wst: WorldState) : Prop :=
    exists totalSupply wst' evts,
      token <> 0
      /\ token <> lrcAddress
      /\ token <> wethAddress
      /\ getTIER token wst <> TIER1
      /\ ERC20s.model wst (msg_totalSupply sender lrcAddress)
                     wst (RetUint totalSupply) nil
      /\ ERC20s.model wst (msg_burnFrom (this wst) lrcAddress sender (burnamount totalSupply))
                     wst' (RetBool true) evts.

  Inductive upgradeTokenTier_trans (wst : WorldState) : WorldState -> RetVal -> Prop :=
  | upgradeTokenTier_TRANS: forall totalSupply wst' evts TIER wst'' ,
      ERC20s.model wst (msg_totalSupply sender lrcAddress)
                   wst (RetUint totalSupply) nil ->
      ERC20s.model wst (msg_burnFrom (this wst) lrcAddress sender (burnamount totalSupply))
                   wst' (RetBool true) evts ->
      upgradetier wst' = (wst'', TIER) ->
      upgradeTokenTier_trans wst wst'' (RetBool true).

  Inductive upgradeTokenTier_events (wst : WorldState) : list Event -> Prop :=
  | upgradeTokenTier_EVENTS: forall totalSupply wst' evts TIER wst'' ,
      ERC20s.model wst (msg_totalSupply sender lrcAddress)
                   wst (RetUint totalSupply) nil ->
      ERC20s.model wst (msg_burnFrom (this wst) lrcAddress sender (burnamount totalSupply))
                   wst' (RetBool true) evts ->
      upgradetier wst' = (wst'', TIER) ->
      upgradeTokenTier_events wst (evts ++ EvtTokenTierUpgraded token TIER :: nil).

  Definition upgradeTokenTier_spec : FSpec :=
    mk_fspec upgradeTokenTier_require upgradeTokenTier_trans upgradeTokenTier_events.

End upgradeTokenTier_SPEC.


Definition get_spec (msg: BurnRateTableMsg) : FSpec :=
  match msg with
  | msg_getBurnRate sender token => getBurnRate_spec token
  | msg_getTokenTier sender token => getTokenTier_spec token
  | msg_upgradeTokenTier sender token => upgradeTokenTier_spec sender token
  end.

Definition model
           (wst: WorldState)
           (msg: BurnRateTableMsg)
           (wst': WorldState)
           (retval: RetVal)
           (events: list Event)
  : Prop :=
  fspec_sat (get_spec msg) wst wst' retval events.