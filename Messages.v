Require Import List.
Require Import Types.


Section RingSubmitter.

  Inductive RingSubmitterMsg : Type :=
  | msg_submitRings (sender: address) (orders: list Order) (rings: list Ring) (mining: Mining)
  .

End RingSubmitter.


Section RingCanceller.

  Inductive RingCancellerMsg : Type :=
  | msg_cancelOrders (sender: address) (order_hashes: list bytes32)
  | msg_cancelAllOrdersForTradingPair (sender token1 token2: address) (cutoff: uint)
  | msg_cancelAllOrders (sender: address) (cutoff: uint)
  | msg_cancelAllOrdersForTradingPairOfOwner (sender owner token1 token2: address) (cutoff: uint)
  | msg_cancelAllOrdersOfOwner (sender owner: address) (cutoff: uint)
  .

End RingCanceller.


Section TradeDelegate.

  Record TransferParam : Type :=
    mk_transfer_param {
        transfer_token: address;
        transfer_from: address;
        transfer_to: address;
        transfer_amount: uint;
      }.

  Record FilledParam : Type :=
    mk_fiiled_param {
        filled_order_hash: bytes20;
        filled_amount: uint;
      }.

  Record OrderParam : Type :=
    mk_order_param {
        order_param_broker: address;
        order_param_owner: address;
        order_param_hash: bytes20;
        order_param_validSince: uint;
        order_param_tradingPair: bytes20;
      }.

  Inductive TradeDelegateMsg : Type :=
  | msg_authorizeAddress (sender addr: address)
  | msg_deauthorizeAddress (sender addr: address)
  | msg_isAddressAuthorized (sender add: address)

  | msg_batchTransfer (sender: address) (params: list TransferParam)
  | msg_batchUpdateFilled (sender: address) (params: list FilledParam)

  | msg_setCancelled (sender broker: address) (orderHash: bytes32)
  | msg_setCutoffs (sender broker: address) (cutoff: uint)
  | msg_setTradingPairCutoffs (sender broker: address) (tokenPair: bytes20) (cutoff: uint)
  | msg_setCutoffsOfOwner (sender broker owner: address) (cutoff: uint)
  | msg_setTradingPairCutoffsOfOwner (sender broker owner: address) (tokenPair: bytes20) (cutoff: uint)
  | msg_batchGetFilledAndCheckCancelled (sender: address) (params: list OrderParam)

  | msg_suspend (sender: address)
  | msg_resume (sender: address)
  | msg_kill (sender: address)
  .

End TradeDelegate.


Section FeeHolder.

  Record FeeBalanceParam : Type :=
    mk_fee_balance_param {
        feeblncs_token: address;
        feeblncs_owner: address;
        feeblncs_value: uint;
      }.

  Inductive FeeHolderMsg : Type :=
  | msg_withdrawBurned (sender token: address) (value: uint)
  | msg_withdrawToken (sender token: address) (value: uint)
  | msg_batchAddFeeBalances (sender: address) (params: list FeeBalanceParam)
  .

End FeeHolder.


Section ERC20.

  Inductive ERC20Msg : Type :=
  | msg_totalSupply (sender token: address)
  | msg_balanceOf (sender token who: address)
  | msg_allowance (sender token owner spender: address)
  | msg_transfer (sender token to: address) (value: uint)
  | msg_transferFrom (sender token from to: address) (value: uint)
  | msg_approve (sender token spender: address) (value: uint)
  .

End ERC20.


Section BrokerRegistry.

  Inductive BrokerRegistryMsg : Type :=
  | msg_getBroker (sender owner broker: address)
  (* Due to the way we model BrokerRegistry::brokersMap, it's not
     feasible to model the semantics of getBrokers() *)
  (* | msg_getBrokers (sender owner: address) (s e: uint) *)
  | msg_registerBroker (sender broker interceptor: address)
  | msg_unregisterBroker (sender broker: address)
  | msg_unregisterAllBrokers (sender: address)
  .

End BrokerRegistry.


Section OrderRegistry.

  Inductive OrderRegistryMsg : Type :=
  | msg_isOrderHashRegistered (sender owner: address) (hash: bytes32)
  | msg_registerOrderHash (sender: address) (hash: bytes32)
  .

End OrderRegistry.


Inductive Message : Type :=
| MsgRingSubmitter (msg: RingSubmitterMsg)
| MsgRingCanceller (msg: RingCancellerMsg)
| MsgTradeDelegate (msg: TradeDelegateMsg)
| MsgFeeHolder (msg: FeeHolderMsg)
| MsgERC20 (msg: ERC20Msg)
| MsgBrokerRegistry (msg: BrokerRegistryMsg)
| MsgOrderRegistry (msg: OrderRegistryMsg)
(* TODO: add messages of other LPSC contracts *)
.