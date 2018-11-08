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
        ERC20.


Open Scope list_scope.


Section Aux.

  Definition is_authorized_address (st: TradeDelegateState) (addr: address) : bool :=
    match (in_dec (Nat.eq_dec) addr (delegate_authorizedAddresses st)) with
    | left _ => true
    | right _ => false
    end.

  Definition is_owner (st: TradeDelegateState) (addr: address) : bool :=
    Nat.eqb (delegate_owner st) addr.

  Definition is_suspended (st: TradeDelegateState) : bool :=
    delegate_suspended st.

  Definition authorized_and_nonsuspended
             (st: TradeDelegateState) (sender: address) : bool :=
    andb (is_authorized_address st sender) (negb (is_suspended st)).

End Aux.


Section Func_authorizeAddress.

  Definition authorizeAddress_sat_requirements
             (wst: WorldState) (sender addr: address) :=
    let st := wst_trade_delegate_state wst in
    andb (is_owner st sender)
         (andb (negb (Nat.eqb addr 0))
               (negb (is_authorized_address st addr))).

  Definition func_authorizeAddress
             (wst0 wst: WorldState) (sender addr: address)
    : (WorldState * RetVal * list Event) :=
    if authorizeAddress_sat_requirements wst sender addr then
      (
        let st := wst_trade_delegate_state wst in
        wst_update_trade_delegate
          wst
          {|
            delegate_owner := delegate_owner st;
            delegate_suspended := delegate_suspended st;
            delegate_authorizedAddresses := addr :: delegate_authorizedAddresses st;
            delegate_filled := delegate_filled st;
            delegate_cancelled := delegate_cancelled st;
            delegate_cutoffs := delegate_cutoffs st;
            delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
            delegate_cutoffsOwner := delegate_cutoffsOwner st;
            delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
          |},
        RetNone,
        EvtAddressAuthorized addr :: nil
      )
    else
      (wst0, RetNone, EvtRevert :: nil).

End Func_authorizeAddress.


Section Func_deauthorizeAddress.

  Definition func_deauthorizeAddress
             (wst0 wst: WorldState) (sender addr: address)
    : (WorldState * RetVal * list Event) :=
    (* TODO: to be defined *)
    (wst0, RetNone, nil).

End Func_deauthorizeAddress.


Section Func_isAddressAuthorized.

  Definition func_isAddressAuthorized
             (wst0 wst: WorldState) (sender addr: address)
  : (WorldState * RetVal * list Event):=
    (wst,
     RetBool (is_authorized_address (wst_trade_delegate_state wst) addr),
     nil
    ).

End Func_isAddressAuthorized.


Section Func_batchTransfer.

  Fixpoint func_batchTransfer
           (wst0 wst: WorldState) (sender: address) (params: list TransferParam)
    : (WorldState * RetVal * list Event) :=
    if authorized_and_nonsuspended (wst_trade_delegate_state wst) sender then
      match params with
      | nil => (wst, RetNone, nil)
      | param :: params' =>
        match ERC20_step wst0 wst
                         (msg_transferFrom (wst_trade_delegate_addr wst)
                                           (transfer_token param)
                                           (transfer_from param)
                                           (transfer_to param)
                                           (transfer_amount param))
        with
        | (wst', ret', evts') =>
          if has_revert_event evts' then
            (wst0, RetNone, EvtRevert :: nil)
          else
            match func_batchTransfer wst0 wst' sender params' with
            | (wst'', ret'', evts'') =>
              if has_revert_event evts'' then
                (wst0, RetNone, EvtRevert :: nil)
              else
                (wst'', ret'', evts' ++ evts'')
            end
        end
      end
    else
      (wst0, RetNone, EvtRevert :: nil).

End Func_batchTransfer.


Section Func_batchUpdateFilled.

  Definition func_batchUpdateFilled
             (wst0 wst: WorldState) (sender: address) (params: list FilledParam)
  : (WorldState * RetVal * list Event) :=
    (* TODO: to be defined *)
    (wst0, RetNone, nil).

End Func_batchUpdateFilled.


Section Func_setCancelled.

  Definition func_setCancelled
             (wst0 wst: WorldState) (sender broker: address) (orderHash: bytes32)
  : (WorldState * RetVal * list Event) :=
    if authorized_and_nonsuspended (wst_trade_delegate_state wst) sender then
      let st := wst_trade_delegate_state wst in
      (wst_update_trade_delegate
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
         |},
       RetNone,
       nil
      )
    else
      (wst0, RetNone, EvtRevert :: nil).

End Func_setCancelled.


Section Func_setCutoffs.

  Definition func_setCutoffs
             (wst0 wst: WorldState) (sender broker: address) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let st := wst_trade_delegate_state wst in
    if andb (authorized_and_nonsuspended (wst_trade_delegate_state wst) sender)
                (Nat.ltb (A2V.get (delegate_cutoffs st) (broker)) cutoff) then
       (wst_update_trade_delegate
       wst
       {|
         delegate_owner := delegate_owner st;
         delegate_suspended := delegate_suspended st;
         delegate_authorizedAddresses := delegate_authorizedAddresses st;
         delegate_filled := delegate_filled st;
         delegate_cancelled := delegate_cancelled st;
         delegate_cutoffs := A2V.upd (delegate_cutoffs st) (broker) cutoff; (*TODO check this line*)
         delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
         delegate_cutoffsOwner := delegate_cutoffsOwner st;
         delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
       |},
       RetNone,
       nil
       )
    else
       (wst0, RetNone, EvtRevert :: nil).

End Func_setCutoffs.


Section Func_setTradingPairCutoffs.

  Definition func_setTradingPairCutoffs
             (wst0 wst: WorldState) (sender broker: address) (tokenPair: bytes20) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let st := wst_trade_delegate_state wst in
    if andb (authorized_and_nonsuspended (wst_trade_delegate_state wst) sender)
           (Nat.ltb (AH2V.get (delegate_tradingPairCutoffs st) (broker, tokenPair)) cutoff) then
       (wst_update_trade_delegate
       wst
       {|
          delegate_owner := delegate_owner st;
          delegate_suspended := delegate_suspended st;
          delegate_authorizedAddresses := delegate_authorizedAddresses st;
          delegate_filled := delegate_filled st;
          delegate_cancelled := delegate_cancelled st;
          delegate_cutoffs := delegate_cutoffs st;
          delegate_tradingPairCutoffs := AH2V.upd (delegate_tradingPairCutoffs st) (broker, tokenPair) cutoff; (*TODO check this line*)
          delegate_cutoffsOwner := delegate_cutoffsOwner st;
          delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
       |},
       RetNone,
       nil
       )
    else
      (wst0, RetNone, EvtRevert :: nil).

End Func_setTradingPairCutoffs.


Section Func_setCutoffsOfOwner.

  Definition func_setCutoffsOfOwner
             (wst0 wst: WorldState) (sender broker owner: address) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let st := wst_trade_delegate_state wst in
    if andb (authorized_and_nonsuspended (wst_trade_delegate_state wst) sender)
            (Nat.ltb (AA2V.get (delegate_cutoffsOwner st) (broker, owner)) cutoff) then
        (wst_update_trade_delegate
            wst
            {|
             delegate_owner := delegate_owner st;
             delegate_suspended := delegate_suspended st;
             delegate_authorizedAddresses := delegate_authorizedAddresses st;
             delegate_filled := delegate_filled st;
             delegate_cancelled := delegate_cancelled st;
             delegate_cutoffs := delegate_cutoffs st;
             delegate_tradingPairCutoffs := delegate_tradingPairCutoffs st;
             delegate_cutoffsOwner := AA2V.upd (delegate_cutoffsOwner st) (broker, owner) cutoff; (*TODO check this line*)
             delegate_tradingPairCutoffsOwner := delegate_tradingPairCutoffsOwner st;
            |},
            RetNone,
            nil
        )
    else
      (wst0, RetNone, EvtRevert :: nil).

End Func_setCutoffsOfOwner.


Section Func_setTradingPairCutoffsOfOwner.

  Definition func_setTradingPairCutoffsOfOwner
             (wst0 wst: WorldState)
             (sender broker owner: address) (tokenPair: bytes20) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let st := wst_trade_delegate_state wst in
      if andb (authorized_and_nonsuspended (wst_trade_delegate_state wst) sender)
              (Nat.ltb (AAH2V.get (delegate_tradingPairCutoffsOwner st) (broker, owner, tokenPair)) cutoff) then
        (wst_update_trade_delegate
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
               delegate_tradingPairCutoffsOwner := AAH2V.upd (delegate_tradingPairCutoffsOwner st) (broker, owner, tokenPair) cutoff; (*TODO check this line*)
              |},
              RetNone,
              nil
          )
      else
        (wst0, RetNone, EvtRevert :: nil).

End Func_setTradingPairCutoffsOfOwner.


Section Func_batchGetFilledAndCheckCancelled.

  Definition is_not_cancelled
             (st: TradeDelegateState) (broker: address) (hash pair: bytes20)
  : bool :=
    (* TODO: to be defined *)
    false.

  Fixpoint build_fills
           (st: TradeDelegateState) (params: list OrderParam)
    : list (option uint) :=
    match params with
    | nil => nil
    | param :: params' =>
      let fill :=
          if is_not_cancelled
               st (order_param_broker param) (order_param_hash param) (order_param_tradingPair param)
          then
            Some (H2V.get (delegate_filled st) (order_param_hash param))
          else
            None
      in
      fill :: build_fills st params'
    end.

  Definition func_batchGetFilledAndCheckCancelled
             (wst0 wst: WorldState) (sender: address) (params: list OrderParam)
    : (WorldState * RetVal * list Event) :=
    (wst,
     RetFills (build_fills (wst_trade_delegate_state wst) params),
     nil
    ).

End Func_batchGetFilledAndCheckCancelled.


Section Func_suspend.

  Definition func_suspend
             (wst0 wst: WorldState) (sender: address)
  : (WorldState * RetVal * list Event) :=
    (* TODO: to be defined *)
    (wst0, RetNone, nil).

End Func_suspend.


Section Func_resume.

  Definition func_resume
             (wst0 wst: WorldState) (sender: address)
  : (WorldState * RetVal * list Event) :=
    (* TODO: to be defined *)
    (wst0, RetNone, nil).

End Func_resume.


Section Func_kill.

  Definition func_kill
             (wst0 wst: WorldState) (sender: address)
  : (WorldState * RetVal * list Event) :=
    (* TODO: to be defined *)
    (wst0, RetNone, nil).

End Func_kill.


Definition TradeDelegate_step
           (wst0 wst: WorldState) (msg: TradeDelegateMsg)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | msg_authorizeAddress sender addr =>
    func_authorizeAddress wst0 wst sender addr
  | msg_deauthorizeAddress sender addr =>
    func_deauthorizeAddress wst0 wst sender addr
  | msg_isAddressAuthorized sender addr =>
    func_isAddressAuthorized wst0 wst sender addr
  | msg_batchTransfer sender params =>
    func_batchTransfer wst0 wst sender params
  | msg_batchUpdateFilled sender params =>
    func_batchUpdateFilled wst0 wst sender params
  | msg_setCancelled sender broker orderHash =>
    func_setCancelled wst0 wst sender broker orderHash
  | msg_setCutoffs sender broker cutoff =>
    func_setCutoffs wst0 wst sender broker cutoff
  | msg_setTradingPairCutoffs sender broker tokenPair cutoff =>
    func_setTradingPairCutoffs wst0 wst sender broker tokenPair cutoff
  | msg_setCutoffsOfOwner sender broker owner cutoff =>
    func_setCutoffsOfOwner wst0 wst sender broker owner cutoff
  | msg_setTradingPairCutoffsOfOwner sender broker owner tokenPair cutoff =>
    func_setTradingPairCutoffsOfOwner wst0 wst sender broker owner tokenPair cutoff
  | msg_batchGetFilledAndCheckCancelled sender params =>
    func_batchGetFilledAndCheckCancelled wst0 wst sender params
  | msg_suspend sender =>
    func_suspend wst0 wst sender
  | msg_resume sender =>
    func_resume wst0 wst sender
  | msg_kill sender =>
    func_kill wst0 wst sender
  end.
