Require Import
        Events
        Messages
        States.

Record FSpec : Type :=
  mk_fspec {
      (* Requirements that must be satisfied by the pre-state in order
         to execute a message call successfully (i.e., not revert event
         occurs). *)
      fspec_require: WorldState (* pre-state *) ->
                     Prop;

      (* Relations between the pre-state and the post-state of a
         successful execution of a message call. *)
      fspec_trans: WorldState (* pre-state *) ->
                   WorldState (* post-state *) ->
                   RetVal -> Prop;

      (* Propositions that must be satisfied by the events generated
         from a successful execution of a message call. *)
      fspec_events: WorldState (* pre-state *) ->
                    list Event (* events *) ->
                    Prop;
    }.

Definition fspec_sat
           (fspec: FSpec) (wst wst': WorldState) (retval: RetVal) (events: list Event)
  : Prop :=
  fspec_require fspec wst /\
  fspec_trans fspec wst wst' retval /\
  fspec_events fspec wst events.