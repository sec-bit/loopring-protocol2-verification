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
  : (WorldState * Result) :=
    match hashes with
    | nil => (wst0, make_revert_result)
    | hash :: hashes' =>
      match TradeDelegate_step
              wst0 wst
              (msg_setCancelled (wst_ring_canceller_addr wst) sender hash) with
      | (wst', res') =>
        if is_revert res' then
          (wst0, make_revert_result)
        else
          match func_cancelOrders wst0 wst' sender hashes' with
          | (wst'', res'') =>
            if is_revert res'' then
              (wst0, make_revert_result)
            else
              (wst'',
               {|
                 res_events := res_events res' ++ res_events res'' ++ (EvtOrderCancelled sender hashes :: nil);
                 res_return := res_return res'';
               |}
              )
          end
      end
    end.

End Func_cancelOrders.


Section Fun_cancelAllOrdersForTradingPair.

  Definition func_cancelAllOrdersForTradingPair
             (wst0 wst: WorldState) (sender: address) (token1 token2: address) (cutoff: uint)
  : (WorldState * Result) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setTradingPairCutoffs (wst_ring_canceller_addr wst) sender (Nat.lxor token1 token2) t)
    with
    | (wst', res') =>
      if is_revert res' then
        (wst0, make_revert_result)
      else
        (wst',
         {|
           res_events := res_events res' ++ (EvtAllOrdersCancelledForTradingPair sender token1 token2 t :: nil);
           res_return := res_return res';
         |})
    end.

End Fun_cancelAllOrdersForTradingPair.


Section Func_cancelAllOrders.

  Definition func_cancelAllOrders
             (wst0 wst: WorldState) (sender: address) (cutoff: uint)
  : (WorldState * Result) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setCutoffs (wst_ring_canceller_addr wst) sender t)
    with
    | (wst', res') =>
      if is_revert res' then
        (wst0, make_revert_result)
      else
        (wst',
         {|
           res_events := res_events res' ++ (EvtAllOrdersCancelled sender t :: nil);
           res_return := res_return res';
         |})
    end.

End Func_cancelAllOrders.


Section Func_cancelAllOrdersForTradingPairOfOwner.

  Definition func_cancelAllOrdersForTradingPairOfOwner
             (wst0 wst: WorldState) (sender: address) (owner token1 token2: address) (cutoff: uint)
  : (WorldState * Result) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setTradingPairCutoffsOfOwner (wst_ring_canceller_addr wst)
                                              sender owner
                                              (Nat.lxor token1 token2) t)
    with
    | (wst', res') =>
      if is_revert res' then
        (wst0, make_revert_result)
      else
        (wst',
         {|
           res_events := res_events res' ++ (EvtAllOrdersCancelledForTradingPairByBroker sender owner token1 token2 t :: nil);
           res_return := res_return res';
         |})
    end.

End Func_cancelAllOrdersForTradingPairOfOwner.


Section Func_cancelAllOrdersOfOwner.

  Definition func_cancelAllOrdersOfOwner
             (wst0 wst: WorldState) (sender: address) (owner: address) (cutoff: uint)
  : (WorldState * Result) :=
    let t := get_cutoff (wst_block_state wst) cutoff in
    match TradeDelegate_step
            wst0 wst
            (msg_setCutoffsOfOwner (wst_ring_canceller_addr wst) sender owner t)
    with
    | (wst', res') =>
      if is_revert res' then
        (wst0, make_revert_result)
      else
        (wst',
         {|
           res_events := res_events res' ++ (EvtAllOrdersCancelledByBroker sender owner t :: nil);
           res_return := res_return res';
         |})
    end.

End Func_cancelAllOrdersOfOwner.

Definition RingCanceller_step
           (wst0 wst: WorldState) (msg: RingCancellerMsg)
  : (WorldState * Result) :=
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