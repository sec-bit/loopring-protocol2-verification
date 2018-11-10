Require Import
        List.
Require Import
        Events
        LibModel
        Messages
        States
        Types.
Require Import
        TradeDelegate.

Module RingCanceller.

  Section Aux.

    Definition get_cutoff (bst: BlockState) (cutoff: uint) : uint :=
      match cutoff with
      | O => block_timestamp bst
      | _ => cutoff
      end.

  End Aux.

  Section CancelOrders.

    Inductive cancel_orders
              (wst: WorldState) (sender: address) (hashes: list bytes32)
    : WorldState -> list Event -> Prop :=
    | cancel_orders_nil:
        hashes = nil ->
        cancel_orders wst sender hashes wst nil

    | cancel_orders_cons:
        forall hash hashes' wst' events' retval wst'' events'',
          hashes = hash :: hashes' ->
          TradeDelegate.model wst
                              (msg_setCancelled (wst_ring_canceller_addr wst) sender hash)
                              wst' retval events' ->
          cancel_orders wst' sender hashes' wst'' events'' ->
          cancel_orders wst sender hashes wst'' (events' ++ events'')
    .

    Definition cancelOrders_spec
               (sender: address) (hashes: list bytes32) :=
      {|
        fspec_require :=
          fun wst =>
            hashes <> nil /\
            exists wst' events,
              cancel_orders wst sender hashes wst' events;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' events,
              cancel_orders wst sender hashes wst'' events ->
              wst' = wst'';

        fspec_events :=
          fun wst events =>
            forall wst' events',
              cancel_orders wst sender hashes wst' events' ->
              events = events' ++ (EvtOrderCancelled sender hashes :: nil);
      |}.

  End CancelOrders.

  Section CancelAllOrdersForTradingPair.

    Definition set_trading_pair_cutoffs
               (wst: WorldState) (sender token1 token2: address) (cutoff: uint)
    : WorldState -> list Event -> Prop :=
      fun wst' events' =>
        forall retval,
          TradeDelegate.model
            wst
            (msg_setTradingPairCutoffs (wst_ring_canceller_addr wst)
                                       sender (Nat.lxor token1 token2) cutoff)
            wst' retval events'.

    Definition cancelAllOrdersForTradingPair_spec
               (sender: address) (token1 token2: address) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            exists wst' events,
              set_trading_pair_cutoffs wst sender token1 token2
                                       (get_cutoff (wst_block_state wst) cutoff)
                                       wst' events;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' events,
              set_trading_pair_cutoffs wst sender token1 token2
                                       (get_cutoff (wst_block_state wst) cutoff)
                                       wst'' events ->
              wst' = wst'';

        fspec_events :=
          fun wst events =>
            let t := get_cutoff (wst_block_state wst) cutoff in
            forall wst' events',
              set_trading_pair_cutoffs wst sender token1 token2 t
                                       wst' events' ->
              events = events' ++ (EvtAllOrdersCancelledForTradingPair sender token1 token2 t :: nil);
      |}.

  End CancelAllOrdersForTradingPair.

  Section CancelAllOrders.

    Definition set_cutoffs (wst: WorldState) (sender: address) (cutoff: uint)
    : WorldState -> list Event -> Prop :=
      fun wst' events =>
        forall retval,
          TradeDelegate.model
            wst (msg_setCutoffs (wst_ring_canceller_addr wst) sender cutoff)
            wst' retval events.

    Definition cancelAllOrders_spec (sender: address) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            exists wst' events,
              set_cutoffs wst sender (get_cutoff (wst_block_state wst) cutoff)
                          wst' events;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' events,
              set_cutoffs wst sender (get_cutoff (wst_block_state wst) cutoff)
                          wst'' events ->
              wst' = wst'';

        fspec_events :=
          fun wst events =>
            let t := get_cutoff (wst_block_state wst) cutoff in
            forall wst' events',
              set_cutoffs wst sender t wst' events' ->
              events = events' ++ (EvtAllOrdersCancelled sender t :: nil);
      |}.

  End CancelAllOrders.

  Section CancelAllOrdersForTradingPairOfOwner.

    Definition set_trading_pair_cutoffs_of_owner
               (wst: WorldState) (sender owner token1 token2: address) (cutoff: uint)
    : WorldState -> list Event -> Prop :=
      fun wst' events =>
        forall retval,
          TradeDelegate.model
            wst
            (msg_setTradingPairCutoffsOfOwner (wst_ring_canceller_addr wst)
                                              sender owner
                                              (Nat.lxor token1 token2) cutoff)
            wst' retval events.

    Definition cancelAllOrdersForTradingPairOfOwner_spec
               (sender: address) (owner token1 token2: address) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            exists wst' events,
              set_trading_pair_cutoffs_of_owner wst sender owner token1 token2
                                                (get_cutoff (wst_block_state wst) cutoff)
                                                wst' events;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' events,
              set_trading_pair_cutoffs_of_owner wst sender owner token1 token2
                                                (get_cutoff (wst_block_state wst) cutoff)
                                                wst'' events ->
              wst' = wst'';

        fspec_events :=
          fun wst events =>
            let t := get_cutoff (wst_block_state wst) cutoff in
            forall wst' events',
              set_trading_pair_cutoffs_of_owner wst sender owner token1 token2
                                                t wst' events' ->
              events = events' ++ (EvtAllOrdersCancelledForTradingPairByBroker sender owner token1 token2 t :: nil);
      |}.

  End CancelAllOrdersForTradingPairOfOwner.

  Section CancelAllOrdersOfOwner.

    Definition set_cutoffs_of_owner
               (wst: WorldState) (sender owner: address) (cutoff: uint)
    : WorldState -> list Event -> Prop :=
      fun wst' events =>
        forall retval,
          TradeDelegate.model
            wst
            (msg_setCutoffsOfOwner (wst_ring_canceller_addr wst) sender owner cutoff)
            wst' retval events.

    Definition cancelAllOrdersOfOwner_spec (sender owner: address) (cutoff: uint) :=
      {|
        fspec_require :=
          fun wst =>
            exists wst' events,
              set_cutoffs_of_owner wst sender owner
                                   (get_cutoff (wst_block_state wst) cutoff)
                                   wst' events;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' events,
              set_cutoffs_of_owner wst sender owner
                                   (get_cutoff (wst_block_state wst) cutoff)
                                   wst'' events ->
              wst' = wst'';

        fspec_events :=
          fun wst events =>
            let t := get_cutoff (wst_block_state wst) cutoff in
            forall wst' events',
              set_cutoffs_of_owner wst sender owner t wst' events' ->
              events = events' ++ (EvtAllOrdersCancelledByBroker sender owner t :: nil);
      |}.

  End CancelAllOrdersOfOwner.

  Definition get_spec (msg: RingCancellerMsg) : FSpec :=
    match msg with
    | msg_cancelOrders sender order_hashes =>
      cancelOrders_spec sender order_hashes

    | msg_cancelAllOrdersForTradingPair sender token1 token2 cutoff =>
      cancelAllOrdersForTradingPair_spec sender token1 token2 cutoff

    | msg_cancelAllOrders sender cutoff =>
      cancelAllOrders_spec sender cutoff

    | msg_cancelAllOrdersForTradingPairOfOwner sender owner token1 token2 cutoff =>
      cancelAllOrdersForTradingPairOfOwner_spec sender owner token1 token2 cutoff

    | msg_cancelAllOrdersOfOwner sender owner cutoff =>
      cancelAllOrdersOfOwner_spec sender owner cutoff
    end.

  Definition model
             (wst: WorldState)
             (msg: RingCancellerMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End RingCanceller.