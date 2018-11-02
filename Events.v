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
(* to be defined *)
.


Inductive RetVal : Type :=
| Return {T: Type} (val: T)
.


Record Result: Type :=
  mk_result {
      res_events: list Event; (* events issued in the execution *)
      res_return: option RetVal;   (* return value if any *)
    }.


Fixpoint has_revert_event (evts: list Event) : bool :=
  match evts with
  | nil => false
  | evt :: evts' =>
    match evt with
    | EvtRevert => true
    | _ => has_revert_event evts'
    end
  end.

Definition is_revert (res: Result) : bool :=
  match res with
  | mk_result evts _ => has_revert_event evts
  end.


Definition concat_results (res res': Result) : Result :=
  match res with
  | mk_result evts _ =>
    match res' with
    | mk_result evts' ret' => mk_result (evts ++ evts') ret'
    end
  end.

Definition make_revert_result : Result :=
  {|
    res_events := EvtRevert :: nil;
    res_return := None;
  |}.

Definition make_empty_result : Result :=
  {|
    res_events := nil;
    res_return := None;
  |}.
