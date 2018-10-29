Require Import
        List.

Require Import
        Events
        Messages
        States
        Types.
Require Import
        ERC20
        FeeHolder
        RingSubmitter
        RingCanceller
        TradeDelegate.


(* TODO: to be defined *)
Parameter wst_init: WorldState.

Definition lr_step
           (wst0 wst: WorldState) (msg: Message)
  : (WorldState * Result) :=
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
  end.

Fixpoint lr_steps (wst0 wst: WorldState) (msgs: list Message)
  : (WorldState * Result) :=
  match msgs with
  | nil => (wst, make_empty_result)
  | msg :: msgs' =>
    match lr_step wst0 wst msg with
    | (wst', res') =>
      if is_revert res' then
        (wst0, make_revert_result)
      else
        match lr_steps wst0 wst' msgs' with
        | (wst'', res'') =>
          if is_revert res'' then
            (wst0, make_revert_result)
          else
            (wst'', concat_results res' res'')
        end
    end
  end.


Definition lr_model (msgs: list Message) : (WorldState * Result) :=
  lr_steps wst_init wst_init msgs.