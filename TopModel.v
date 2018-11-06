Require Import
        List.

Require Import
        Events
        Messages
        States
        Types.
Require Import
        BrokerRegistry
        ERC20
        FeeHolder
        OrderRegistry
        RingSubmitter
        RingCanceller
        TradeDelegate.


(* TODO: to be defined *)
Parameter wst_init: WorldState.

Definition lr_step
           (wst0 wst: WorldState) (msg: Message)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | MsgRingSubmitter msg' =>
    RingSubmitter_step wst0 wst msg'
  | MsgRingCanceller msg' =>
    RingCanceller_step wst0 wst msg'
  | MsgTradeDelegate msg' =>
    TradeDelegate_step wst0 wst msg'
  | MsgFeeHolder msg' =>
    FeeHolder_step wst0 wst msg'
  | MsgERC20 msg' =>
    ERC20_step wst0 wst msg'
  | MsgBrokerRegistry msg' =>
    BrokerRegistry_step wst0 wst msg'
  | MsgOrderRegistry msg' =>
    OrderRegistry_step wst0 wst msg'
  end.

Fixpoint lr_steps (wst0 wst: WorldState) (msgs: list Message)
  : (WorldState * RetVal * list Event) :=
  match msgs with
  | nil => (wst, RetNone, nil)
  | msg :: msgs' =>
    match lr_step wst0 wst msg with
    | (wst', ret', evts') =>
      if has_revert_event evts' then
        (wst0, RetNone, EvtRevert :: nil)
      else
        match lr_steps wst0 wst' msgs' with
        | (wst'', ret'', evts'') =>
          if has_revert_event evts'' then
            (wst0, RetNone, EvtRevert :: nil)
          else
            (wst'', ret'', evts' ++ evts'')
        end
    end
  end.


Definition lr_model (msgs: list Message) : (WorldState * RetVal * list Event) :=
  lr_steps wst_init wst_init msgs.