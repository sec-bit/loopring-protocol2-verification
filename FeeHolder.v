Require Import
        List
        ZArith.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.
Require Import
        ERC20
        TradeDelegate.

Open Scope list_scope.


Module FeeHolder.

  Section Aux.

    Definition wst_before_transfer
               (wst: WorldState) (sender token: address) (value: uint)
    : WorldState :=
      let from := wst_feeholder_addr wst in
      let st := wst_feeholder_state wst in
      wst_update_feeholder
        wst
        {|
          feeholder_delegateAddress := feeholder_delegateAddress st;
          feeholder_feeBalances := AA2V_upd_dec (feeholder_feeBalances st)
                                                token from value;
        |}.

    Definition transfer_withdraw
               (wst: WorldState) (sender token: address) (value: uint)
      : WorldState -> list Event -> Prop :=
      fun wst' events =>
        forall retval,
          ERC20s.model wst
                       (msg_transfer (wst_feeholder_addr wst) token sender value)
                       wst' retval events.

    Definition is_authorized (wst: WorldState) (sender: address) : Prop :=
      exists wst' events retval,
        TradeDelegate.model wst
                            (msg_isAddressAuthorized (wst_feeholder_addr wst) sender)
                            wst' retval events /\
        retval = RetBool true.

  End Aux.

  Section WithdrawBurned.

    Definition withdrawBurned_spec
               (sender token: address) (value: uint) :=
      {|
        fspec_require :=
          fun wst =>
            is_authorized wst sender /\
            AA2V.get (feeholder_feeBalances (wst_feeholder_state wst))
                     (token, (wst_feeholder_addr wst)) >= value /\
            exists wst' events,
              transfer_withdraw (wst_before_transfer wst sender token value)
                                sender token value
                                wst' events
        ;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' events,
              transfer_withdraw (wst_before_transfer wst sender token value)
                                sender token value
                                wst'' events ->
              wst' = wst''
        ;

        fspec_events :=
          fun wst events =>
            forall wst' events',
              transfer_withdraw (wst_before_transfer wst sender token value)
                                sender token value
                                wst' events' ->
              events = events' ++ (EvtTokenWithdrawn (wst_feeholder_addr wst) token value :: nil)
        ;
      |}.

  End WithdrawBurned.

  Section WithdrawToken.

    Definition withdrawToken_spec (sender token: address) (value: uint) :=
      (* TODO: to be defined *)
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval => True;

        fspec_events :=
          fun wst events => True;
      |}.

  End WithdrawToken.

  Section BatchAddFeeBalances.

    Definition batchAddFeeBalances_spec
               (sender: address) (params: list FeeBalanceParam) :=
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval => True;

        fspec_events :=
          fun wst events => True;
      |}.

  End BatchAddFeeBalances.

  Definition get_spec (msg: FeeHolderMsg) : FSpec :=
    match msg with
    | msg_withdrawBurned sender token value =>
      withdrawBurned_spec sender token value

    | msg_withdrawToken sender token value =>
      withdrawToken_spec sender token value

    | msg_batchAddFeeBalances sender params =>
      batchAddFeeBalances_spec sender params
    end.

    Definition model
               (wst: WorldState)
               (msg: FeeHolderMsg)
               (wst': WorldState)
               (retval: RetVal)
               (events: list Event)
      : Prop :=
      fspec_sat (get_spec msg) wst wst' retval events.

End FeeHolder.
