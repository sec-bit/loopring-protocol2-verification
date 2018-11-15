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
               (wst: WorldState) (from sender token: address) (value: uint)
    : WorldState :=
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

    Definition withdraw_require
               (wst: WorldState) (from sender token: address) (value: uint) :=
      is_authorized wst sender /\
      AA2V.get (feeholder_feeBalances (wst_feeholder_state wst))
               (token, from) >= value /\
      exists wst' events,
        transfer_withdraw (wst_before_transfer wst from sender token value)
                          sender token value
                          wst' events.
    Definition withdraw_trans
               (wst wst': WorldState) (retval: RetVal) (from sender token: address) (value: uint) :=
      retval = RetNone /\
      forall wst'' events,
        transfer_withdraw (wst_before_transfer wst from sender token value)
                          sender token value
                          wst'' events ->
        wst' = wst''.

    Definition withdraw_events
               (wst: WorldState) (events: list Event) (from sender token: address) (value: uint) :=
      forall wst' events',
        transfer_withdraw (wst_before_transfer wst from sender token value)
                          sender token value
                          wst' events' ->
        events = events' ++ (EvtTokenWithdrawn from token value :: nil).

  End Aux.

  Section WithdrawBurned.

    (* withdraw(token, this, msg.sender, value); *)
    Definition withdrawBurned_spec
               (sender token: address) (value: uint) :=
      {|
        fspec_require :=
          fun wst =>
            withdraw_require wst (wst_feeholder_addr wst) sender token value
        ;

        fspec_trans :=
          fun wst wst' retval =>
            withdraw_trans wst wst' retval (wst_feeholder_addr wst) sender token value
        ;

        fspec_events :=
          fun wst events =>
            withdraw_events wst events (wst_feeholder_addr wst) sender token value
      |}.

  End WithdrawBurned.

  Section WithdrawToken.

    (* withdraw(token, msg.sender, msg.sender, value); *)
    Definition withdrawToken_spec (sender token: address) (value: uint) :=
      {|
        fspec_require :=
          fun wst =>
            withdraw_require wst sender sender token value
        ;

        fspec_trans :=
          fun wst wst' retval =>
            withdraw_trans wst wst' retval sender sender token value
        ;

        fspec_events :=
          fun wst events =>
            withdraw_events wst events sender sender token value
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
