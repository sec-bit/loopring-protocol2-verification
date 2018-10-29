Require Import
        Events
        Messages
        States
        Types.

Definition RingCanceller_step
           (wst0 wst: WorldState) (msg: RingCancellerMsg)
  : (WorldState * list Event) :=
  (* TODO: to be defined *)
  (wst0, nil).