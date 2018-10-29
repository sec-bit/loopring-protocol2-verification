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


Section Func_withdrawBurned.

  Definition withdrawBurned_requirements
             (wst: WorldState) (sender token from: address) (value: uint)
  : bool :=
    andb (is_authorized_address (wst_trade_delegate_state wst) sender)
         (Nat.leb value
                  (AA2V.get (feeholder_feeBalances (wst_feeholder_state wst))
                            (token, from))).

  Definition func_withdrawBurned
             (wst0 wst: WorldState) (sender token: address) (value: uint)
  : (WorldState * Result) :=
    if withdrawBurned_requirements
         wst sender token (wst_feeholder_addr wst) value then
      match ERC20_step
              wst0 wst (msg_transfer (wst_feeholder_addr wst) token sender value)
      with
      | (wst', res') =>
        if is_revert res' then
          (wst0, make_revert_result)
        else
          let from := (wst_feeholder_addr wst) in
          (let st := wst_feeholder_state wst in
           wst_update_feeholder
             wst
             {|
               feeholder_delegateAddress := feeholder_delegateAddress st;
               feeholder_feeBalances := AA2V_upd_dec (feeholder_feeBalances st)
                                                     token from value;
             |},
           {|
             res_events := EvtTokenWithdrawn from token value :: nil;
             res_return := None;
           |}
          )
      end
    else
      (wst0, make_revert_result).

End Func_withdrawBurned.


Section Func_withdrawToken.

  Definition func_withdrawToken
             (wst0 wst: WorldState) (sender token: address) (value: uint)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst, make_empty_result).

End Func_withdrawToken.


Section Func_batchAddFeeBalances.

  Definition func_batchAddFeeBalances
             (wst0 wst: WorldState) (sender: address) (params: list FeeBalanceParam)
  : (WorldState * Result) :=
    (* TODO: to be defined *)
    (wst, make_empty_result).

End Func_batchAddFeeBalances.


Definition FeeHolder_step
           (wst0 wst: WorldState) (msg: FeeHolderMsg)
  : (WorldState * Result) :=
  match msg with
  | msg_withdrawBurned sender token value =>
    func_withdrawBurned wst0 wst sender token value
  | msg_withdrawToken sender token value =>
    func_withdrawToken wst0 wst sender token value
  | msg_batchAddFeeBalances sender params =>
    func_batchAddFeeBalances wst0 wst sender params
  end.