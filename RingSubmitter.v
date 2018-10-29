Require Import
        List.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.


Open Scope list_scope.


Definition func_submitRings
           (wst0 wst: WorldState)
           (sender: address)
           (orders: list Order) (rings: list Ring) (mining: Mining)
  : (WorldState * Result) :=
  (* to be defined *)
  (wst, make_empty_result).

Definition RingSubmitter_step
           (wst0 wst: WorldState) (msg: RingSubmitterMsg)
  : (WorldState * Result) :=
  match msg with
  | msg_submitRings sender orders rings mining =>
    func_submitRings wst0 wst sender orders rings mining
  end.
