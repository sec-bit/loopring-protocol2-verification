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
    : (WorldState * Result) :=
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

        {|
          res_events := EvtAddressAuthorized addr :: nil;
          res_return := None;
        |}
      )
    else
      (wst0, make_revert_result).

End Func_authorizeAddress.


Section Func_deauthorizeAddress.

  Definition func_deauthorizeAddress
             (wst0 wst: WorldState) (sender addr: address)
    : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_deauthorizeAddress.


Section Func_isAddressAuthorized.

  Definition func_isAddressAuthorized
             (wst0 wst: WorldState) (sender addr: address) :=
    (wst,
     {|
       res_events := nil;
       res_return := Some (Return
                             (is_authorized_address
                                (wst_trade_delegate_state wst) addr));
     |}
    ).

End Func_isAddressAuthorized.


Section Func_batchTransfer.

  Fixpoint func_batchTransfer
           (wst0 wst: WorldState) (sender: address) (params: list TransferParam)
    : (WorldState * Result) :=
    if authorized_and_nonsuspended (wst_trade_delegate_state wst) sender then
      match params with
      | nil => (wst, {| res_events := nil; res_return := None |})
      | param :: params' =>
        match ERC20_step wst0 wst
                         (msg_transferFrom (wst_trade_delegate_addr wst)
                                           (transfer_token param)
                                           (transfer_from param)
                                           (transfer_to param)
                                           (transfer_amount param))
        with
        | (wst', res') =>
          if is_revert res' then
            (wst0, make_revert_result)
          else
            match func_batchTransfer wst0 wst' sender params' with
            | (wst'', res'') =>
              if is_revert res'' then
                (wst0, make_revert_result)
              else
                (wst'', concat_results res' res'')
            end
        end
      end
    else
      (wst0, make_revert_result).

End Func_batchTransfer.


Section Func_batchUpdateFilled.

  Definition func_batchUpdateFilled
             (wst0 wst: WorldState) (sender: address) (params: list FilledParam)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_batchUpdateFilled.


Section Func_setCancelled.

  Definition func_setCancelled
             (wst0 wst: WorldState) (sender broker: address) (orderHash: bytes32)
  : (WorldState * Result) :=
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
       make_empty_result
      )
    else
      (wst0, make_revert_result).

End Func_setCancelled.


Section Func_setCutoffs.

  Definition func_setCutoffs
             (wst0 wst: WorldState) (sender broker: address) (cutoff: uint)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_setCutoffs.


Section Func_setTradingPairCutoffs.

  Definition func_setTradingPairCutoffs
             (wst0 wst: WorldState) (sender broker: address) (cutoff: uint)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_setTradingPairCutoffs.


Section Func_setCutoffsOfOwner.

  Definition func_setCutoffsOfOwner
             (wst0 wst: WorldState) (sender broker owner: address) (cutoff: uint)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_setCutoffsOfOwner.


Section Func_setTradingPairCutoffsOfOwner.

  Definition func_setTradingPairCutoffsOfOwner
             (wst0 wst: WorldState)
             (sender broker owner: address) (tokenPair: bytes20) (cutoff: uint)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

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
               st (order_broker param) (order_hash param) (order_tradingPair param)
          then
            Some (H2V.get (delegate_filled st) (order_hash param))
          else
            None
      in
      fill :: build_fills st params'
    end.

  Definition func_batchGetFilledAndCheckCancelled
             (wst0 wst: WorldState) (sender: address) (params: list OrderParam)
    : (WorldState * Result) :=
    (wst,
     {|
       res_events := nil;
       res_return := Some (Return
                             (build_fills (wst_trade_delegate_state wst) params));
     |}
    ).

End Func_batchGetFilledAndCheckCancelled.


Section Func_suspend.

  Definition func_suspend
             (wst0 wst: WorldState) (sender: address)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_suspend.


Section Func_resume.

  Definition func_resume
             (wst0 wst: WorldState) (sender: address)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_resume.


Section Func_kill.

  Definition func_kill
             (wst0 wst: WorldState) (sender: address)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst0, make_empty_result).

End Func_kill.


Definition TradeDelegate_step
           (wst0 wst: WorldState) (msg: TradeDelegateMsg)
  : (WorldState * Result) :=
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
  | msg_setTradingPairCutoffs sender broker cutoff =>
    func_setTradingPairCutoffs wst0 wst sender broker cutoff
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
