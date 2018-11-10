Require Import
        List.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.


Module OrderRegistry.

  Section Aux.

    Definition get_hashMap (wst: WorldState) : AH2B.t :=
      order_registry_hashMap ((wst_order_registry_state wst)).

  End Aux.

  Section IsOrderHashRegistered.

    Definition isOrderHashRegistered_spec
               (sender owner: address) (hash: bytes32) :=
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval =>
            wst' = wst /\
            retval = RetBool (AH2B.get (get_hashMap wst) (owner, hash));

        fspec_events :=
          fun wst events =>
            events = nil;
      |}.

  End IsOrderHashRegistered.

  Section RegisterOrderHash.

    Definition registerOrderHash_spec (sender: address) (hash: bytes32) :=
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            let hashMap := get_hashMap wst in
            let hashMap' := AH2B.upd hashMap (sender, hash) true in
            wst' = wst_update_order_registry wst {| order_registry_hashMap := hashMap' |};

        fspec_events :=
          fun wst events =>
            events = EvtOrderRegistered sender hash :: nil;
      |}.

  End RegisterOrderHash.

  Definition get_spec (msg: OrderRegistryMsg) : FSpec :=
    match msg with
    | msg_isOrderHashRegistered sender owner hash =>
      isOrderHashRegistered_spec sender owner hash

    | msg_registerOrderHash sender hash =>
      registerOrderHash_spec sender hash
    end.

  Definition model
             (wst: WorldState)
             (msg: OrderRegistryMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End OrderRegistry.
