Require Import
        List.

Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.

(** * BurnRateTable messages *)

Inductive BurnRateTableMsg : Type :=
| msg_getBurnRate (sender: address) (token: address)
| msg_getTokenTier (sender: address) (token: address)
| msg_upgradeTokenTier (sender: address) (token: address)
(* [getRebateRate], 
   [lock], 
   [withdraw], 
   [getBalance], 
   [getWithdrawablebalance],  
   [getLockStartTime]
   are not implemented *).

(** * BurnRateTable state *)

(** Tier definition *)
Definition TIER1 : uint := 3.
Definition TIER2 : uint := 2.
Definition TIER3 : uint := 1.
Definition TIER4 : uint := 0.

(** Token data map *)
Record TokenData : Type :=
  mk_token_data {
      tier: uint;
      validUntil: uint;
    }.

Module TokenDataElem <: ElemType.
  Definition elt : Type := TokenData.
  Definition elt_zero : elt := mk_token_data 0 0.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof. decide equality; decide equality. Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
    unfold elt_eq; intros; congruence.
  Qed.

End TokenDataElem.

Module TokenDataMap := Mapping Address_as_DT TokenDataElem.

(** BurnRateTable state *)
Record BurnRateTableState : Type :=
  {
    burnratetable_tokens: TokenDataMap.t;
    (* balances not implemented *)
  }.

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

(** * Auxiliary definitions *)
(** What about events? should it be inserted in Events definition? *)
Parameter EvtTokenTierUpgraded : forall (addr: address) (tier: uint), Event.
(** It seems the [BurnRateTableState] should be added to WorldState. *)
Parameter get_state : WorldState -> BurnRateTableState.
Parameter set_state : WorldState -> BurnRateTableState -> WorldState.

(** * Method call specs *)
Parameter getBurnRate_spec : forall (sender: address) (token: address), FSpec.
Parameter getTokenTier_spec : forall (sender: address) (token: address), FSpec.
Parameter upgradeTokenTier_spec : forall (sender: address) (token: address), FSpec.

Definition get_spec (msg: BurnRateTableMsg) : FSpec :=
  match msg with
  | msg_getBurnRate sender token => getBurnRate_spec sender token
  | msg_getTokenTier sender token => getTokenTier_spec sender token
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