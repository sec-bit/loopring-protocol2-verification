Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.


Parameter oracle_broker_intercetor_getAllowance_spec
  : address (* param: owner *) ->
    address (* param: broker *) ->
    address (* param: token *) ->
    FSpec.
Parameter oracle_broker_interceptor_onTokenSpent_spec
  : address (* param: owner *) ->
    address (* param: broker *) ->
    address (* param: token *) ->
    address (* param: amount *) ->
    FSpec.

Module BrokerInterceptor.

  Definition get_spec (msg: BrokerInterceptorMsg) : FSpec :=
    match msg with
    | msg_getAllowanceSafe sender interceptor owner broker token =>
      oracle_broker_intercetor_getAllowance_spec owner broker token

    | msg_onTokenSpentSafe sender interceptor owner broker token amount =>
      oracle_broker_interceptor_onTokenSpent_spec owner broker token amount
    end.

  Definition model
             (wst: WorldState)
             (msg: BrokerInterceptorMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End BrokerInterceptor.