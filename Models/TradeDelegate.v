Require Import
        List
        ZArith
        Bool.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.
Require Import
        ERC20.


Open Scope list_scope.


Module TradeDelegate.

  Section Aux.

    Definition is_authorized_address
               (st: TradeDelegateState) (addr: address) : Prop :=
      A2B.get (delegate_authorizedAddresses st) addr = true.

    Definition is_owner (st: TradeDelegateState) (addr: address) : Prop :=
      addr = delegate_owner st.

    Definition is_not_suspended (st: TradeDelegateState) : Prop :=
      delegate_suspended st = false.

    Definition authorized_and_nonsuspended
               (st: TradeDelegateState) (sender: address) : Prop :=
      is_authorized_address st sender /\ is_not_suspended st.

  End Aux.

  Section AuthorizeAddress.

    Definition authorizeAddress_spec (sender addr: address) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            is_owner st sender /\ addr <> 0 /\ ~ is_authorized_address st sender;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := A2B.upd (delegate_authorizedAddresses st) addr true;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled := delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = EvtAddressAuthorized addr :: nil;
      |}.

  End AuthorizeAddress.

  Section DeauthorizeAddress.

    Definition deauthorizeAddress_spec (sender addr: address) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            is_owner st sender /\ addr <> 0 /\ is_authorized_address st sender;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := A2B.upd (delegate_authorizedAddresses st) addr false;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled := delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = EvtAddressDeauthorized addr :: nil;
      |}.

  End DeauthorizeAddress.

  Section IsAddressAuthorized.

    Definition isAddressAuthorized_spec (sender addr: address) :=
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval =>
            wst' = wst /\
            let st := wst_trade_delegate_state wst in
            (is_authorized_address st addr -> retval = RetBool true) /\
            (~ is_authorized_address st addr -> retval = RetBool false);

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End IsAddressAuthorized.

  Section BatchTransfer.

    Inductive transfer_params
              (wst: WorldState) (sender: address) (params: list TransferParam)
    : WorldState -> list Event -> Prop :=
    | transfer_nil:
        params = nil ->
        transfer_params wst sender params wst nil

    | transfer_cons:
        forall param params' retval wst' events' wst'' events'',
          params = param :: params' ->
          ERC20s.model wst
                       (msg_transferFrom (wst_trade_delegate_addr wst)
                                         (transfer_token param)
                                         (transfer_from param)
                                         (transfer_to param)
                                         (transfer_amount param))
                       wst' retval events' ->
          transfer_params wst' sender params' wst'' events'' ->
          transfer_params wst sender params wst'' (events' ++ events'')
    .

    Definition batchTransfer_spec (sender: address) (params: list TransferParam) :=
      {|
        fspec_require :=
          fun wst =>
            authorized_and_nonsuspended (wst_trade_delegate_state wst) sender /\
            (exists wst' events, transfer_params wst sender params wst' events)
        ;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' events,
              transfer_params wst sender params wst'' events ->
              wst' = wst''
        ;

        fspec_events :=
          fun wst events =>
            forall wst' events',
              transfer_params wst sender params wst' events' ->
              events = events'
        ;
      |}.

  End BatchTransfer.

  Section BatchUpdateFilled.

    Fixpoint update_fills
             (st: TradeDelegateState) (params: list FilledParam)
    : TradeDelegateState :=
      match params with
      | nil => st
      | param :: params' =>
        let st' :=
            {|
              delegate_owner := delegate_owner st;
              delegate_suspended := delegate_suspended st;
              delegate_authorizedAddresses := delegate_authorizedAddresses st;
              delegate_filled := H2V.upd (delegate_filled st) (filled_order_hash param) (filled_amount param);
              delegate_cancelled := delegate_cancelled st;
              delegate_cutoffs := delegate_cutoffs st;
              delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
              delegate_cutoffsOwner := delegate_cutoffsOwner st;
              delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
            |} in
        update_fills st' params'
      end.

    Definition batchUpdateFilled_spec (sender: address) (params: list FilledParam) :=
      {|
        fspec_require :=
          fun wst =>
            authorized_and_nonsuspended (wst_trade_delegate_state wst) sender;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            wst' = wst_update_trade_delegate wst (update_fills (wst_trade_delegate_state wst) params);

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End BatchUpdateFilled.

  Section SetCancelled.

    Definition setCancelled_spec (sender broker: address) (orderHash: bytes32) :=
      {|
        fspec_require :=
          fun wst =>
            authorized_and_nonsuspended (wst_trade_delegate_state wst) sender;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled := AH2B.upd (delegate_cancelled st) (broker, orderHash) true;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End SetCancelled.

  Section SetCutOffs.

    Definition setCutoffs_spec (sender broker: address) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            authorized_and_nonsuspended st sender /\
            A2V.get (delegate_cutoffs st) (broker) < cutoff;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled := delegate_cancelled st;
                       delegate_cutoffs := A2V.upd (delegate_cutoffs st) (broker) cutoff;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End SetCutOffs.

  Section SetTradingPairCutOffs.

    Definition setTradingPairCutoffs_spec
               (sender broker: address) (tokenPair: bytes20) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            authorized_and_nonsuspended st sender /\
            AH2V.get (delegate_tradingPairCutoffs st) (broker, tokenPair) < cutoff;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled := delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := AH2V.upd (delegate_tradingPairCutoffs st) (broker, tokenPair) cutoff;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End SetTradingPairCutOffs.

  Section SetCutoffsOfOwner.

    Definition setCutoffsOfOwner_spec
               (sender broker owner: address) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            authorized_and_nonsuspended st sender /\
            AA2V.get (delegate_cutoffsOwner st) (broker, owner) < cutoff;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled := delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := AA2V.upd (delegate_cutoffsOwner st) (broker, owner) cutoff;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End SetCutoffsOfOwner.

  Section SetTradingPairCutoffsOfOwner.

    Definition setTradingPairCutoffsOfOwner_spec
               (sender broker owner: address) (tokenPair: bytes20) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            authorized_and_nonsuspended st sender /\
            AAH2V.get (delegate_tradingPairCutoffsOwner st) (broker, owner, tokenPair) < cutoff;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled := delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := AAH2V.upd (delegate_tradingPairCutoffsOwner st) (broker, owner, tokenPair) cutoff;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End SetTradingPairCutoffsOfOwner.

  Section BatchGetFilledAndCheckCancelled.

    Definition is_cancelled
               (st: TradeDelegateState) (param: OrderParam)
    : bool :=
      let broker := order_param_broker param in
      let owner := order_param_owner param in
      let trading_pair := order_param_tradingPair param in
      let hash := order_param_hash param in
      let valid_since := order_param_validSince param in
      AH2B.get (delegate_cancelled st) (broker, hash) ||
      Nat.leb valid_since
              (AH2V.get (delegate_tradingPairCutoffs st) (broker, trading_pair)) ||
      Nat.leb valid_since
              (A2V.get (delegate_cutoffs st) broker)  ||
      Nat.leb valid_since
              (AAH2V.get (delegate_tradingPairCutoffsOwner st) (broker, owner, trading_pair)) ||
      Nat.leb valid_since
              (AA2V.get (delegate_cutoffsOwner st) (broker, owner)).

    Fixpoint build_fills
             (st: TradeDelegateState) (params: list OrderParam)
      : list (option uint) :=
      match params with
      | nil => nil
      | param :: params' =>
        let fill := match is_cancelled st param with
                    | true => None
                    | _ => Some (H2V.get (delegate_filled st) (order_param_hash param))
                    end
        in fill :: build_fills st params'
      end.

    Definition batchGetFilledAndCheckCancelled_spec
               (sender: address) (params: list OrderParam) :=
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval =>
            wst' = wst /\
            retval = RetFills (build_fills (wst_trade_delegate_state wst) params);

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End BatchGetFilledAndCheckCancelled.

  Section Suspend.

    Definition suspend_spec (sender: address) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            is_owner st sender /\ is_not_suspended st;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := true;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled :=delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End Suspend.

  Section Resume.

    Definition resume_spec (sender: address) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            is_owner st sender /\ ~ is_not_suspended st;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := delegate_owner st;
                       delegate_suspended := false;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled :=delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End Resume.

  Section Kill.

    Definition kill_spec (sender: address) :=
      {|
        fspec_require :=
          fun wst =>
            let st := wst_trade_delegate_state wst in
            is_owner st sender /\ ~ is_not_suspended st;

        fspec_trans :=
          fun wst wst' retval =>
            let st := wst_trade_delegate_state wst in
            wst' = wst_update_trade_delegate
                     wst
                     {|
                       delegate_owner := 0;
                       delegate_suspended := delegate_suspended st;
                       delegate_authorizedAddresses := delegate_authorizedAddresses st;
                       delegate_filled := delegate_filled st;
                       delegate_cancelled :=delegate_cancelled st;
                       delegate_cutoffs := delegate_cutoffs st;
                       delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
                       delegate_cutoffsOwner := delegate_cutoffsOwner st;
                       delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
                     |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            let st := wst_trade_delegate_state wst in
            events = (EvtOwnershipTransferred (delegate_owner st) 0) :: nil;
      |}.

  End Kill.

  Definition get_spec (msg: TradeDelegateMsg) : FSpec :=
    match msg with
    | msg_authorizeAddress sender addr =>
      authorizeAddress_spec sender addr

    | msg_deauthorizeAddress sender addr =>
      deauthorizeAddress_spec sender addr

    | msg_isAddressAuthorized sender addr =>
      isAddressAuthorized_spec sender addr

    | msg_batchTransfer sender params =>
      batchTransfer_spec sender params

    | msg_batchUpdateFilled sender params =>
      batchUpdateFilled_spec sender params

    | msg_setCancelled sender broker orderHash =>
      setCancelled_spec sender broker orderHash

    | msg_setCutoffs sender broker cutoff =>
      setCutoffs_spec sender broker cutoff

    | msg_setTradingPairCutoffs sender broker tokenPair cutoff =>
      setTradingPairCutoffs_spec sender broker tokenPair cutoff

    | msg_setCutoffsOfOwner sender broker owner cutoff =>
      setCutoffsOfOwner_spec sender broker owner cutoff

    | msg_setTradingPairCutoffsOfOwner sender broker owner tokenPair cutoff =>
      setTradingPairCutoffsOfOwner_spec sender broker owner tokenPair cutoff

    | msg_batchGetFilledAndCheckCancelled sender params =>
      batchGetFilledAndCheckCancelled_spec sender params

    | msg_suspend sender =>
      suspend_spec sender

    | msg_resume sender =>
      resume_spec sender

    | msg_kill sender =>
      kill_spec sender
    end.

  Definition model
             (wst: WorldState)
             (msg: TradeDelegateMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End TradeDelegate.
