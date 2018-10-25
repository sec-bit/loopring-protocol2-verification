Require Import Nat List.
Require Import Types.

Inductive LPSCAction : Type :=
(* RingSubmitter *)
| LPSC_submitRings (sender: address) (orders: list Order) (rings: list Ring)

(* RingCanceller *)
| LPSC_cancelOrders (sender: address) (order_hashes: list bytes20)
| LPSC_cancelAllOrdersForTradingPair (sender: address) (token1 token2: address) (cutoff: nat)
| LPSC_cancelAllOrders (sender: address) (cutoff: nat)
| LPSC_cancelAllOrdersForTradingPairOfOwner (sender: address) (owner token1 token2: address) (cutoff: nat)
| LPSC_cancelAllOrdersOfOwner (sender: address) (owner: address) (cutoff: uint)

(* BurnManager, to be defined  *)
| LPSC_burn

(* BrokerRegistry, to be defined  *)
| LPSC_getBroker
| LPSC_getBrokers
| LPSC_registerBroker
| LPSC_unregisterBroker
| LPSC_unregisterAllBrokers

(* FeeHolder, to be defined  *)
| LPSC_batchAddFeeBalances
| LPSC_withdrawBurned
| LPSC_withdrawToken

(* OrderBook, to be defined  *)
| LPSC_submitOrder
| LPSC_getOrderData

(* OrderRegistry, to be defined  *)
| LPSC_isOrderHashRegistered
| LPSC_registerOrderHash

(* TradeDelegate *)
(* Do we need to model trade delegate here? *)
.

Inductive TokenAction: Type :=
(* to be defined *)
.

Inductive OrderOwnerAction: Type :=
(* to be defined *)
.

Inductive WalletAction: Type :=
(* to be defined *)
.

Inductive MinerAction: Type :=
(* to be defined *)
.

Inductive Action: Type :=
| Action_LPSC (a: LPSCAction)
| Action_Token (a: TokenAction)
| Action_OrderOwner (a: OrderOwnerAction)
| Action_Wallet (a: WalletAction)
| Action_Miner (a: MinerAction)
.
