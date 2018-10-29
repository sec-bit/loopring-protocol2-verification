Require Import
        Events
        Messages
        States
        Types.

Definition RingCanceller_step
           (wst0 wst: WorldState) (msg: RingCancellerMsg)
  : (WorldState * Result) :=
  (* TODO: to be defined *)
  (wst0, make_empty_result).