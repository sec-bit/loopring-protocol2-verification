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
(* BurnRateTable events *)
| EvtTokenTierUpgraded (token: address) (TIER: uint)
| EvtOwnershipTransferred (owner dest: address)
(* OrderBook events *)
| EvtOrderSubmitted (owner: address) (hash: bytes32)
(* Pseudo events, used only in model and proving *)
| EvtRingSkipped (r: Ring)
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
| RetBytes32 (val: bytes32)
| RetOrder (order: Order)
| RetFills (val: list (option uint))
| RetBrokerInterceptor (interceptor: option address) (* None: not registered
                                                        Some _: registered *)
.
