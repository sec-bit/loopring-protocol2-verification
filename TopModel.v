Require Import
        List.

Require Import
        Events
        Messages
        States
        Types.
Require Import
        ERC20
        RingSubmitter
        RingCanceller
        TradeDelegate.


(* TODO: to be defined *)
Parameter wst_init: WorldState.

Definition lr_step
           (wst0 wst: WorldState) (msg: Message)
  : (WorldState * list Event) :=
  match msg with
  | MsgRingSubmitter msg' =>
    RingSubmitter_step wst0 wst msg'
  | MsgRingCanceller msg' =>
    RingCanceller_step wst0 wst msg'
  | MsgTradeDelegate msg' =>
    TradeDelegate_step wst0 wst msg'
  | MsgERC20 msg' =>
    ERC20_step wst0 wst msg'
  end.

Fixpoint lr_steps (wst0 wst: WorldState) (msgs: list Message)
  : (WorldState * list Event) :=
  match msgs with
  | nil => (wst, nil)
  | msg :: msgs' =>
    match lr_step wst0 wst msg with
    | (wst', evts') =>
      if IsRevert evts' then
        (wst0, EvtRevert :: nil)
      else
        match lr_steps wst0 wst' msgs' with
        | (wst'', evts'') =>
          if IsRevert evts'' then
            (wst0, EvtRevert :: nil)
          else
            (wst'', evts' ++ evts'')
        end
    end
  end.


Definition lr_model (msgs: list Message) : (WorldState * list Event) :=
  lr_steps wst_init wst_init msgs.