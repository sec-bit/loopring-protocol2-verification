Require Import
        Events
        Messages
        States.

Record FSpec : Type :=
  mk_fspec {
      fspec_require: WorldState -> Prop;
      fspec_trans: WorldState -> WorldState -> RetVal -> Prop;
      fspec_events: WorldState -> list Event -> Prop;
    }.

Definition fspec_sat
           (fspec: FSpec) (wst wst': WorldState) (retval: RetVal) (events: list Event)
  : Prop :=
  fspec_require fspec wst /\
  fspec_trans fspec wst wst' retval /\
  fspec_events fspec wst events.