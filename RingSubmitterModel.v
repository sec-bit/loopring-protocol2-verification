Require Import Nat List.
Require Import Actions State Types.


(** Semantics of submitRings *)

Definition lpsc_submitRings
           (st: WorldState)
           (sender: address)
           (orders: list Order)
           (rings: list Ring) : WorldState * WorldEvents :=
  (* to be defined *)
  (st, nil).


Definition LPSC_actor (act: LPSCAction) (st: WorldState) : WorldState * WorldEvents :=
  match act with
  | LPSC_submitRings sender orders rings => lpsc_submitRings st sender orders rings
  (* to be defined *)
  | _ => (st, nil)
  end.
