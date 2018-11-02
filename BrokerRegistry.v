Require Import
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
  : (WorldState * Result) :=
    let brokersMap := get_brokersMap wst in
    match get_broker_info brokersMap owner broker with
    | None => (wst,
              {| res_events := nil;
                 res_return := Some (Return (false, 0))|})
    | Some broker_info => (wst,
                          {| res_events := nil;
                             res_return := Some (Return (true, broker_interceptor broker_info)) |})
    end.

End Func_getBroker.


Section Func_registerBroker.

  Definition func_registerBroker
             (wst0 wst: WorldState) (sender broker interceptor: address)
  : (WorldState * Result) :=
    match broker with
    | O => (wst0, make_revert_result)
    | _ =>
      let brokersMap := get_brokersMap wst in
      match get_broker_info brokersMap sender broker with
      | Some _ => (wst0, make_revert_result)
      | None =>
        let brokerInfo := {| broker_owner := sender;
                             broker_addr := broker;
                             broker_interceptor := interceptor;
                          |}
        in
        let brokersMap' := upd_broker_info brokersMap sender broker brokerInfo in
        (wst_update_broker_registry wst {| broker_registry_brokersMap := brokersMap' |},
         {|
           res_events := EvtBrokerRegistered sender broker interceptor :: nil;
           res_return := None;
         |})
      end
    end.

End Func_registerBroker.


Section Func_unregisterBroker.

  Definition func_unregisterBroker
             (wst0 wst: WorldState) (sender broker: address)
  : WorldState * Result :=
    match broker with
    | O => (wst0, make_revert_result)
    | _ =>
      let brokersMap := get_brokersMap wst in
      match get_broker_info brokersMap sender broker with
      | None => (wst0, make_revert_result)
      | Some broker_info =>
        let brokersMap' := del_broker_info brokersMap sender broker in
        (wst_update_broker_registry wst {| broker_registry_brokersMap := brokersMap' |},
         {|
           res_events := EvtBrokerUnregistered sender broker (broker_interceptor broker_info) :: nil;
           res_return := None;
         |})
      end
    end.

End Func_unregisterBroker.


Section Func_unregsterAllBrokers.

  Definition func_unregisterAllBrokers
             (wst0 wst: WorldState) (sender: address)
  : WorldState * Result :=
    let brokersMap := get_brokersMap wst in
    let brokersMap' := BrokersMap.del brokersMap sender in
    (wst_update_broker_registry wst {| broker_registry_brokersMap := brokersMap' |},
     {|
       res_events := EvtAllBrokersUnregistered sender :: nil;
       res_return := None;
     |}).

End Func_unregsterAllBrokers.


Definition BrokerRegistry_step
           (wst0 wst: WorldState) (msg: BrokerRegistryMsg)
  : (WorldState * Result) :=
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
