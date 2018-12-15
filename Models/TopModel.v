Require Import
        List.

Require Import
        Events
        Messages
        States
        Types.
Require Import
        BrokerInterceptor
        BrokerRegistry
        BurnManager
        ERC20
        FeeHolder
        OrderBook
        OrderRegistry
        RingSubmitter
        RingCanceller
        TradeDelegate
        BurnRateTable.


Parameter wst_init: WorldState.

Definition lr_step
           (wst: WorldState) (msg: Message)
           (wst': WorldState) (retval: RetVal) (events: list Event) : Prop :=
  match msg with
  | MsgRingSubmitter msg' =>
    RingSubmitter.model wst msg' wst' retval events

  | MsgRingCanceller msg' =>
    RingCanceller.model wst msg' wst' retval events

  | MsgTradeDelegate msg' =>
    TradeDelegate.model wst msg' wst' retval events

  | MsgFeeHolder msg' =>
    FeeHolder.model wst msg' wst' retval events

  | MsgERC20 msg' =>
    ERC20s.model wst msg' wst' retval events

  | MsgBrokerRegistry msg' =>
    BrokerRegistry.model wst msg' wst' retval events

  | MsgOrderRegistry msg' =>
    OrderRegistry.model wst msg' wst' retval events

  | MsgBurnRateTable msg' =>
    BurnRateTable.model wst msg' wst' retval events

  | MsgBrokerInterceptor msg' =>
    BrokerInterceptor.model wst msg' wst' retval events

  | MsgBurnManager msg' =>
    BurnManager.model wst msg' wst' retval events

  | MsgOrderBook msg' =>
    OrderBook.model wst msg' wst' retval events
  end.

Inductive lr_steps (wst: WorldState) (msgs: list Message)
  : WorldState -> RetVal -> list Event -> Prop :=
| lr_steps_nil:
    msgs = nil ->
    lr_steps wst msgs wst RetNone nil

| lr_steps_cons:
    forall msg msgs' wst' retval' events' wst'' retval'' events'',
      msgs = msg :: msgs' ->
      lr_step wst msg wst' retval' events' ->
      lr_steps wst' msgs' wst'' retval'' events'' ->
      lr_steps wst msgs wst'' retval'' (events' ++ events'')
.

Definition lr_model
           (msgs: list Message)
           (wst': WorldState)
           (retval: RetVal)
           (events: list Event) : Prop :=
  lr_steps wst_init msgs wst' retval events.
