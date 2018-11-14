Require Import
        List.
Require Import
        Types.

Set Implicit Arguments.
Unset Strict Implicit.


Inductive Event : Type :=
(* Not model `Errors` for simplification *)
| EvtRevert
(* TradeDelegate events*)
| EvtAddressAuthorized (addr: address)
| EvtAddressDeauthorized (addr: address)
(* FeeHolder events *)
| EvtTokenWithdrawn (owner token: address) (value: uint)
(* RingCanceller events *)
| EvtOrderCancelled (broker: address) (hashes: list bytes20)
| EvtAllOrdersCancelledForTradingPair (broker token1 token2: address) (cutoff: uint)
| EvtAllOrdersCancelled (broker: address) (cutoff: uint)
| EvtOrdersCancelledByBroker (broker owner: address) (hashes: list bytes20)
| EvtAllOrdersCancelledForTradingPairByBroker (broker owner token1 token2: address) (cutoff: uint)
| EvtAllOrdersCancelledByBroker (broker owner: address) (cutoff: uint)
(* BrokerRegistry events *)
| EvtBrokerRegistered (owner broker interceptor: address)
| EvtBrokerUnregistered (owner broker interceptor: address)
| EvtAllBrokersUnregistered (owner: address)
(* OrderRegistry events *)
| EvtOrderRegistered (owner: address) (hash: bytes32)
(* TODO Loopring protocol events *)
| EvtOwnershipTransferred (owner dest: address)
(* to be defined *)
.

Fixpoint has_revert_event (evts: list Event) : bool :=
  match evts with
  | nil => false
  | evt :: evts' =>
    match evt with
    | EvtRevert => true
    | _ => has_revert_event evts'
    end
  end.


Inductive RetVal : Type :=
| RetNone
| RetUint (val: uint)
| RetBool (val: bool)
| RetAddr (val: address)
| RetFills (val: list (option uint))
| RetGetBroker (registered: bool) (interceptor: address)
.
