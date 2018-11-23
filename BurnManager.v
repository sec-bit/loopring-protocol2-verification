Require Import
        List.

Require Import
        ERC20
        Events
        LibModel
        Maps
        Messages
        States
        Types.

Require Import
        FeeHolder.


Module BurnManager.

  Section Burn.

    Definition burn_require (wst: WorldState) (token: address) : Prop :=
      burnMgr_lrcAddress (wst_burn_manager_state wst) = token.

    Definition burn_trans (wst: WorldState) (token: address)
               (wst': WorldState) (retval: RetVal) (events: list Event) : Prop :=
      forall balance sender wst1 events1 wst2 events2,
        balance = AA2V.get (feeholder_feeBalances (wst_feeholder_state wst))
                           (token, burnMgr_feeHolderAddress (wst_burn_manager_state wst)) /\
        sender = wst_burn_manager_addr wst /\
        FeeHolder.model wst (msg_withdrawBurned sender token balance)
                        wst1 (RetBool true) events1 /\
        ERC20s.model wst1 (msg_erc20_burn sender token balance)
                     wst2 (RetBool true) events2 /\
        wst' = wst2 /\
        retval = RetBool true /\
        events = events1 ++ events2.

    Definition burn_spec (sender token: address) :=
      {|
        fspec_require :=
          fun wst =>
            burn_require wst token;

        fspec_trans :=
          fun wst wst' retval =>
            forall wst'' retval'' events,
              burn_trans wst token wst'' retval'' events ->
              wst' = wst'' /\ retval = retval'';

        fspec_events :=
          fun wst events =>
            forall wst' retval events',
              burn_trans wst token wst' retval events' ->
              events = events';
      |}.

  End Burn.

  Definition get_spec (msg: BurnManagerMsg) : FSpec :=
    match msg with
    | msg_burn sender token => burn_spec sender token
    end.

  Definition model
             (wst: WorldState)
             (msg: BurnManagerMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End BurnManager.