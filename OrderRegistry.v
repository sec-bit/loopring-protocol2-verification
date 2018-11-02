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
  : WorldState * Result :=
    (wst,
     {|
       res_events := nil;
       res_return := Some (Return (AH2B.get (get_hashMap wst) (owner, hash)));
     |}).

End Func_isOrderHashRegistered.


Section Func_registerOrderHash.

  Definition func_registerOrderHash
             (wst0 wst: WorldState) (sender: address) (hash: bytes32)
  : WorldState * Result :=
    let hashMap := get_hashMap wst in
    let hashMap' := AH2B.upd hashMap (sender, hash) true in
    (wst_update_order_registry wst {| order_registry_hashMap := hashMap' |},
     {|
       res_events := EvtOrderRegistered sender hash :: nil;
       res_return := None;
     |}).

End Func_registerOrderHash.


Definition OrderRegistry_step
           (wst0 wst: WorldState) (msg: OrderRegistryMsg)
  : (WorldState * Result) :=
  match msg with
  | msg_isOrderHashRegistered sender owner hash =>
    func_isOrderHashRegistered wst0 wst sender owner hash
  | msg_registerOrderHash sender hash =>
    func_registerOrderHash wst0 wst sender hash
  end.
