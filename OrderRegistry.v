Require Import
        List.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.


Section Aux.

  Definition get_hashMap (wst: WorldState) : AH2B.t :=
    order_registry_hashMap ((wst_order_registry_state wst)).

End Aux.


Section Func_isOrderHashRegistered.

  Definition func_isOrderHashRegistered
             (wst0 wst: WorldState) (sender owner: address) (hash: bytes32)
  : WorldState * RetVal * list Event :=
    (wst,
     RetBool (AH2B.get (get_hashMap wst) (owner, hash)),
     nil
    ).

End Func_isOrderHashRegistered.


Section Func_registerOrderHash.

  Definition func_registerOrderHash
             (wst0 wst: WorldState) (sender: address) (hash: bytes32)
  : WorldState * RetVal * list Event :=
    let hashMap := get_hashMap wst in
    let hashMap' := AH2B.upd hashMap (sender, hash) true in
    (wst_update_order_registry wst {| order_registry_hashMap := hashMap' |},
     RetNone,
     EvtOrderRegistered sender hash :: nil
    ).

End Func_registerOrderHash.


Definition OrderRegistry_step
           (wst0 wst: WorldState) (msg: OrderRegistryMsg)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | msg_isOrderHashRegistered sender owner hash =>
    func_isOrderHashRegistered wst0 wst sender owner hash
  | msg_registerOrderHash sender hash =>
    func_registerOrderHash wst0 wst sender hash
  end.
