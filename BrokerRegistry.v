Require Import
        List
        Coq.FSets.FMapWeakList.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.


Section Aux.

  Definition get_brokersMap (wst: WorldState) : BrokersMap.t :=
    broker_registry_brokersMap (wst_broker_registry_state wst).

  Definition get_broker_info
             (m: BrokersMap.t) (owner broker: address)
    : option Broker :=
    match BrokersMap.find m owner with
    | None => None
    | Some brokers =>
      match Brokers.find brokers broker with
      | None => None
      | Some broker_info => Some broker_info
      end
    end.

  Definition upd_broker_info
             (m: BrokersMap.t) (owner broker: address) (broker_info: Broker)
    : BrokersMap.t :=
    BrokersMap.upd m
                   owner
                   (Brokers.upd (BrokersMap.get m owner)
                                broker
                                broker_info).

  Definition del_broker_info
             (m: BrokersMap.t) (owner broker: address)
    : BrokersMap.t :=
    BrokersMap.upd m
                   owner
                   (Brokers.del (BrokersMap.get m owner) broker).

End Aux.


Section Func_getBroker.

  Definition func_getBroker
             (wst0 wst: WorldState) (sender owner broker: address)
  : (WorldState * RetVal * list Event) :=
    let brokersMap := get_brokersMap wst in
    match get_broker_info brokersMap owner broker with
    | None => (wst, RetGetBroker false 0, nil)
    | Some broker_info => (wst,
                          RetGetBroker true (broker_interceptor broker_info),
                          nil)
    end.

End Func_getBroker.


Section Func_registerBroker.

  Definition func_registerBroker
             (wst0 wst: WorldState) (sender broker interceptor: address)
  : (WorldState * RetVal * list Event) :=
    match broker with
    | O => (wst0, RetNone, EvtRevert :: nil)
    | _ =>
      let brokersMap := get_brokersMap wst in
      match get_broker_info brokersMap sender broker with
      | Some _ => (wst0, RetNone, EvtRevert :: nil)
      | None =>
        let brokerInfo := {| broker_owner := sender;
                             broker_addr := broker;
                             broker_interceptor := interceptor;
                          |}
        in
        let brokersMap' := upd_broker_info brokersMap sender broker brokerInfo in
        (wst_update_broker_registry wst {| broker_registry_brokersMap := brokersMap' |},
         RetNone,
         EvtBrokerRegistered sender broker interceptor :: nil
        )
      end
    end.

End Func_registerBroker.


Section Func_unregisterBroker.

  Definition func_unregisterBroker
             (wst0 wst: WorldState) (sender broker: address)
  : WorldState * RetVal * list Event :=
    match broker with
    | O => (wst0, RetNone, EvtRevert :: nil)
    | _ =>
      let brokersMap := get_brokersMap wst in
      match get_broker_info brokersMap sender broker with
      | None => (wst0, RetNone, EvtRevert :: nil)
      | Some broker_info =>
        let brokersMap' := del_broker_info brokersMap sender broker in
        (wst_update_broker_registry wst {| broker_registry_brokersMap := brokersMap' |},
         RetNone,
         EvtBrokerUnregistered sender broker (broker_interceptor broker_info) :: nil
        )
      end
    end.

End Func_unregisterBroker.


Section Func_unregsterAllBrokers.

  Definition func_unregisterAllBrokers
             (wst0 wst: WorldState) (sender: address)
  : WorldState * RetVal * list Event :=
    let brokersMap := get_brokersMap wst in
    let brokersMap' := BrokersMap.del brokersMap sender in
    (wst_update_broker_registry wst {| broker_registry_brokersMap := brokersMap' |},
     RetNone,
     EvtAllBrokersUnregistered sender :: nil
    ).

End Func_unregsterAllBrokers.


Definition BrokerRegistry_step
           (wst0 wst: WorldState) (msg: BrokerRegistryMsg)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | msg_getBroker sender owner broker =>
    func_getBroker wst0 wst sender owner broker
  (* | msg_getBrokers sender owner s e => *)
  (*   func_getBrokers wst0 wst sender owner s e *)
  | msg_registerBroker sender broker interceptor =>
    func_registerBroker wst0 wst sender broker interceptor
  | msg_unregisterBroker sender broker =>
    func_unregisterBroker wst0 wst sender broker
  | msg_unregisterAllBrokers sender =>
    func_unregisterAllBrokers wst0 wst sender
  end.
