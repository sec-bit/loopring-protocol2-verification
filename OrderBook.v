Require Import
        List.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.

Module OrderBook.

  Section SubmitOrder.

    Definition submitOrder_spec (sender: address) (order: Order) : FSpec :=
      {|
        fspec_require :=
          fun wst =>
            (sender = order_owner order \/ sender = order_broker order) /\
            H2O.find (ob_orders (wst_order_book_state wst))
                     (get_order_hash order) = None
        ;

        fspec_trans :=
          fun wst wst' retval =>
            let hash := get_order_hash order in
            let orders := ob_orders (wst_order_book_state wst) in
            let orders' := H2O.upd orders hash order in
            wst' = wst_update_order_book wst {| ob_orders := orders' |} /\
            retval = RetBytes32 hash
        ;

        fspec_events :=
          fun wst events =>
            events = EvtOrderSubmitted sender (get_order_hash order) :: nil
        ;
      |}.

  End SubmitOrder.

  Section GetOrderData.

    Definition getOrderData_spec (sender: address) (hash: bytes32) : FSpec :=
      {|
        fspec_require :=
          fun wst => True;

        fspec_trans :=
          fun wst wst' retval =>
            wst' = wst /\
            retval = RetOrder (H2O.get (ob_orders (wst_order_book_state wst))
                                       hash);

        fspec_events :=
          fun wst events => events = nil;
      |}.

  End GetOrderData.

  Definition get_spec (msg: OrderBookMsg) : FSpec :=
    match msg with
    | msg_submitOrder sender order =>
      submitOrder_spec sender order

    | msg_getOrderData sender hash =>
      getOrderData_spec sender hash
    end.

  Definition model
             (wst: WorldState)
             (msg: OrderBookMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End OrderBook.