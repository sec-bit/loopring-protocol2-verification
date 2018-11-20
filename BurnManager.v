Require Import
        List.

Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.


Inductive BurnManagerMsg : Type :=
| msg_burn (sender: address) (token: address).

Record BurnManagerState : Type :=
  {
    burnmanager_feeHolderAddress : address;
    burnmanager_lrcAddress : address;
  }.

(** The [BurnManagerState] should be added to [WorldState]. *)
Parameter get_state : forall (wst: WorldState), BurnManagerState.

Parameter set_state : forall (wst: WorldState) (new_bmst: BurnManagerState), WorldState.

Parameter burn_spec : forall (sender: address) (token: address), FSpec.

Definition get_spec (msg: BurnManagerMsg) : FSpec :=
  match msg with
  | msg_burn sender token => burn_spec sender token
  end.

Definition model
           (wst: WorldState)
           (msg: BurnManagerMsg)
           (wst': WorldState)
           (retval: RetVal)
           (events: list Event)
  : Prop :=
  fspec_sat (get_spec msg) wst wst' retval events.