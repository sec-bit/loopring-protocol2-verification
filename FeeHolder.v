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
  : (WorldState * RetVal * list Event) :=
    if withdrawBurned_requirements
         wst sender token (wst_feeholder_addr wst) value then
      match ERC20_step
              wst0 wst (msg_transfer (wst_feeholder_addr wst) token sender value)
      with
      | (wst', ret', evts') =>
        if has_revert_event evts' then
          (wst0, RetNone, EvtRevert :: nil)
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
           RetNone,
           EvtTokenWithdrawn from token value :: nil
          )
      end
    else
      (wst0, RetNone, EvtRevert :: nil).

End Func_withdrawBurned.


Section Func_withdrawToken.

  Definition func_withdrawToken
             (wst0 wst: WorldState) (sender token: address) (value: uint)
  : (WorldState * RetVal * list Event) :=
    (* TODO: to be defined *)
    (wst, RetNone, nil).

End Func_withdrawToken.


Section Func_batchAddFeeBalances.

  Definition func_batchAddFeeBalances
             (wst0 wst: WorldState) (sender: address) (params: list FeeBalanceParam)
  : (WorldState * RetVal * list Event) :=
    (* TODO: to be defined *)
    (wst, RetNone, nil).

End Func_batchAddFeeBalances.


Definition FeeHolder_step
           (wst0 wst: WorldState) (msg: FeeHolderMsg)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | msg_withdrawBurned sender token value =>
    func_withdrawBurned wst0 wst sender token value
  | msg_withdrawToken sender token value =>
    func_withdrawToken wst0 wst sender token value
  | msg_batchAddFeeBalances sender params =>
    func_batchAddFeeBalances wst0 wst sender params
  end.