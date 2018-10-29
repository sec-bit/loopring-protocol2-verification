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