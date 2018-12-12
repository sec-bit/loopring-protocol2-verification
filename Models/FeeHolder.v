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
               (wst: WorldState) (from to token: address) (value: uint)
    : WorldState :=
      let st := wst_feeholder_state wst in
      wst_update_feeholder
        wst
        {|
          feeholder_delegateAddress := feeholder_delegateAddress st;
          feeholder_feeBalances := AA2V_upd_dec (feeholder_feeBalances st)
                                                token from value;
        |}.

    Definition transfer_withdraw_succeed
               (wst: WorldState) (to token: address) (value: uint)
      : WorldState -> list Event -> Prop :=
      fun wst' events =>
        ERC20s.model wst
                     (msg_transfer (wst_feeholder_addr wst) token to value)
                     wst' (RetBool true) events.

    Definition is_authorized (wst: WorldState) (addr: address) : Prop :=
      exists wst' events,
        TradeDelegate.model wst
                            (msg_isAddressAuthorized (wst_feeholder_addr wst) addr)
                            wst' (RetBool true) events.

    Definition has_sufficient_feebalance
               (wst: WorldState) (from to token: address) (value: uint) :=
      AA2V.get (feeholder_feeBalances (wst_feeholder_state wst))
               (token, from) >= value.

    Definition withdraw_require_common
               (wst: WorldState) (from to token: address) (value: uint) :=
      has_sufficient_feebalance wst from to token value /\
      exists wst' events,
        transfer_withdraw_succeed (wst_before_transfer wst from to token value)
                                  to token value
                                  wst' events.

    Definition withdraw_trans
               (wst wst': WorldState)
               (retval: RetVal)
               (from to token: address)
               (value: uint) : Prop :=
      forall wst'' events',
        transfer_withdraw_succeed (wst_before_transfer wst from to token value)
                                  to token value wst'' events' ->
        wst' = wst'' /\ retval = RetBool true.

    Definition withdraw_events
               (wst: WorldState)
               (events: list Event)
               (from to token: address)
               (value: uint) : Prop :=
      forall wst'' events',
        transfer_withdraw_succeed (wst_before_transfer wst from to token value)
                                  to token value wst'' events' ->
        events = events' ++ (EvtTokenWithdrawn from token value :: nil).

  End Aux.

  Section WithdrawBurned.

    (* withdraw(token, this, msg.sender, value); *)
    Definition withdrawBurned_spec
               (sender token: address) (value: uint) :=
      {|
        fspec_require :=
          fun wst =>
            withdraw_require_common wst (wst_feeholder_addr wst) sender token value /\
            is_authorized wst sender
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
            withdraw_require_common wst sender sender token value
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

    Definition wst_add_fee
               (wst: WorldState) (token owner: address) (value: uint)
      : WorldState :=
      let st := wst_feeholder_state wst in
      wst_update_feeholder
        wst
        {|
          feeholder_delegateAddress := feeholder_delegateAddress st;
          feeholder_feeBalances := AA2V_upd_inc (feeholder_feeBalances st)
                                                token owner value;
        |}.

    Fixpoint add_fee
             (wst: WorldState) (params: list FeeBalanceParam)
    : WorldState :=
      match params with
      | nil => wst
      | param :: params' =>
        let wst' :=
            (wst_add_fee
               wst
               (feeblncs_token param)
               (feeblncs_owner param)
               (feeblncs_value param))
        in
        add_fee wst' params'
      end.

    Definition batchAddFeeBalances_spec
               (sender: address) (params: list FeeBalanceParam) :=
      {|
        fspec_require :=
          fun wst =>
            is_authorized wst sender;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            wst' = add_fee wst params;

        fspec_events :=
          fun wst events =>
            events = nil;
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
