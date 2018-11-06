Require Import
        List.
Require Import
        Events
        Messages
        States
        Types.
Require Import
        TradeDelegate.


Section Aux.

  Definition get_cutoff (bst: BlockState) (cutoff: uint) : uint :=
    match cutoff with
    | O => block_timestamp bst
    | _ => cutoff
    end.

End Aux.


Section Func_cancelOrders.

  Fixpoint func_cancelOrders
           (wst0 wst: WorldState) (sender: address) (hashes: list bytes20)
  : (WorldState * RetVal * list Event) :=
    match hashes with
    | nil => (wst0, RetNone, EvtRevert :: nil)
    | hash :: hashes' =>
      match TradeDelegate_step
              wst0 wst
              (msg_setCancelled (wst_ring_canceller_addr wst) sender hash) with
      | (wst', ret', evts') =>
        if has_revert_event evts' then
          (wst0, RetNone, EvtRevert :: nil)
        else
          match func_cancelOrders wst0 wst' sender hashes' with
          | (wst'', ret'', evts'') =>
            if has_revert_event evts'' then
              (wst0, RetNone, EvtRevert :: nil)
            else
              (wst'',
               ret'',
               evts' ++ evts'' ++ (EvtOrderCancelled sender hashes :: nil)
              )
          end
      end
    end.

End Func_cancelOrders.


Section Fun_cancelAllOrdersForTradingPair.

  Definition func_cancelAllOrdersForTradingPair
             (wst0 wst: WorldState) (sender: address) (token1 token2: address) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setTradingPairCutoffs (wst_ring_canceller_addr wst) sender (Nat.lxor token1 token2) t)
    with
    | (wst', ret', evts') =>
      if has_revert_event evts' then
        (wst0, RetNone, EvtRevert :: nil)
      else
        (wst',
         ret',
         evts' ++ (EvtAllOrdersCancelledForTradingPair sender token1 token2 t :: nil)
        )
    end.

End Fun_cancelAllOrdersForTradingPair.


Section Func_cancelAllOrders.

  Definition func_cancelAllOrders
             (wst0 wst: WorldState) (sender: address) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setCutoffs (wst_ring_canceller_addr wst) sender t)
    with
    | (wst', ret', evts') =>
      if has_revert_event evts' then
        (wst0, RetNone, EvtRevert :: nil)
      else
        (wst',
         ret',
         evts' ++ (EvtAllOrdersCancelled sender t :: nil)
        )
    end.

End Func_cancelAllOrders.


Section Func_cancelAllOrdersForTradingPairOfOwner.

  Definition func_cancelAllOrdersForTradingPairOfOwner
             (wst0 wst: WorldState) (sender: address) (owner token1 token2: address) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setTradingPairCutoffsOfOwner (wst_ring_canceller_addr wst)
                                              sender owner
                                              (Nat.lxor token1 token2) t)
    with
    | (wst', ret', evts') =>
      if has_revert_event evts' then
        (wst0, RetNone, EvtRevert :: nil)
      else
        (wst',
         ret',
         evts' ++ (EvtAllOrdersCancelledForTradingPairByBroker sender owner token1 token2 t :: nil)
        )
    end.

End Func_cancelAllOrdersForTradingPairOfOwner.


Section Func_cancelAllOrdersOfOwner.

  Definition func_cancelAllOrdersOfOwner
             (wst0 wst: WorldState) (sender: address) (owner: address) (cutoff: uint)
  : (WorldState * RetVal * list Event) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setCutoffsOfOwner (wst_ring_canceller_addr wst) sender owner t)
    with
    | (wst', ret', evts') =>
      if has_revert_event evts' then
        (wst0, RetNone, EvtRevert :: nil)
      else
        (wst',
         ret',
         evts' ++ (EvtAllOrdersCancelledByBroker sender owner t :: nil)
        )
    end.

End Func_cancelAllOrdersOfOwner.

Definition RingCanceller_step
           (wst0 wst: WorldState) (msg: RingCancellerMsg)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | msg_cancelOrders sender order_hashes =>
    func_cancelOrders wst0 wst sender order_hashes
  | msg_cancelAllOrdersForTradingPair sender token1 token2 cutoff =>
    func_cancelAllOrdersForTradingPair wst0 wst sender token1 token2 cutoff
  | msg_cancelAllOrders sender cutoff =>
    func_cancelAllOrders wst0 wst sender cutoff
  | msg_cancelAllOrdersForTradingPairOfOwner sender owner token1 token2 cutoff =>
    func_cancelAllOrdersForTradingPairOfOwner wst0 wst sender owner token1 token2 cutoff
  | msg_cancelAllOrdersOfOwner sender owner cutoff =>
    func_cancelAllOrdersOfOwner wst0 wst sender owner cutoff
  end.