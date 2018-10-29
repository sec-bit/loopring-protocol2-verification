Require Import
        List.
Require Import
        Types.

Set Implicit Arguments.
Unset Strict Implicit.


Inductive Event : Type :=
(* Abstract event that can represent any events other than following ones *)
| EvtAny {T: Type} (data: T)
(* Not model `Errors` for simplification *)
| EvtRevert
(* Pseudo event that models the return value *)
| EvtReturn {T: Type} (data: T)
(* TradeDelegate events*)
| EvtAddressAuthorized (addr: address)
| EvtAddressDeauthorized (addr: address)
(* to be defined *)
.

Fixpoint IsRevert (evts: list Event) : bool :=
  match evts with
  | nil => false
  | evt :: evts' =>
    match evt with
    | EvtRevert => true
    | _ => IsRevert evts'
    end
  end.