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

Module BrokerRegistry.

  Section Aux.

    Definition get_brokersMap (wst: WorldState) : BrokersMap.t :=
      broker_registry_brokersMap (wst_broker_registry_state wst).

    Definition get_broker_info
               (m: BrokersMap.t) (owner broker: address)
      : option Broker :=
      match BrokersMap.map.find owner m with
      | None => None
      | Some brokers =>
        match Brokers.map.find broker brokers with
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

  Section GetBroker.

    Definition getBroker_spec (sender owner broker: address) :=
      {|
        fspec_require :=
          fun wst => True
        ;

        fspec_trans :=
          fun wst wst' retval =>
            wst' = wst /\
            retval = match get_broker_info (get_brokersMap wst) owner broker with
                     | None => RetBrokerInterceptor None
                     | Some broker_info => RetBrokerInterceptor (Some (broker_interceptor broker_info))
                     end
        ;

        fspec_events :=
          fun wst events => events = nil
        ;
      |}.

  End GetBroker.

  Section RegisterBroker.

    Definition registerBroker_spec (sender broker interceptor: address) :=
      {|
        fspec_require :=
          fun wst =>
            broker <> 0 /\
            get_broker_info (get_brokersMap wst) sender broker = None;

        fspec_trans :=
          fun wst wst' retval =>
            let brokerInfo := {| broker_owner := sender;
                                 broker_addr := broker;
                                 broker_interceptor := interceptor;
                              |} in
            let brokersMap' := upd_broker_info
                                 (get_brokersMap wst) sender broker brokerInfo in
            wst' = wst_update_broker_registry
                     wst {| broker_registry_brokersMap := brokersMap' |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = EvtBrokerRegistered sender broker interceptor :: nil;
      |}.

  End RegisterBroker.

  Section UnregisterBroker.

    Definition unregisterBroker_spec (sender broker: address) :=
      {|
        fspec_require :=
          fun wst =>
            broker <> 0 /\
            get_broker_info (get_brokersMap wst) sender broker <> None;

        fspec_trans :=
          fun wst wst' retval =>
            get_broker_info (get_brokersMap wst) sender broker <> None ->
            let brokersMap' := del_broker_info (get_brokersMap wst) sender broker in
            wst' = wst_update_broker_registry
                     wst
                     {| broker_registry_brokersMap := brokersMap' |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            forall broker_info,
              get_broker_info (get_brokersMap wst) sender broker = Some broker_info ->
              events = EvtBrokerUnregistered sender broker (broker_interceptor broker_info) :: nil;
      |}.

  End UnregisterBroker.

  Section UnregisterAllBrokers.

    Definition unregisterAllBrokers_spec (sender: address) :=
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval =>
            let brokersMap' := BrokersMap.del (get_brokersMap wst) sender in
            wst' = wst_update_broker_registry
                     wst {| broker_registry_brokersMap := brokersMap' |} /\
            retval = RetNone;

        fspec_events :=
          fun wst events =>
            events = EvtAllBrokersUnregistered sender :: nil;
      |}.

  End UnregisterAllBrokers.

  Definition get_spec
             (msg: BrokerRegistryMsg)
    : FSpec :=
    match msg with
    | msg_getBroker sender owner broker =>
      getBroker_spec sender owner broker

    | msg_registerBroker sender broker interceptor =>
      registerBroker_spec sender broker interceptor

    | msg_unregisterBroker sender broker =>
      unregisterBroker_spec sender broker

    | msg_unregisterAllBrokers sender =>
      unregisterAllBrokers_spec sender
    end.

  Definition model
             (wst: WorldState)
             (msg: BrokerRegistryMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End BrokerRegistry.
