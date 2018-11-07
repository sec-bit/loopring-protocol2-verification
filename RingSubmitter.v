Require Import
        List.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.
Require Import
        BrokerRegistry
        OrderRegistry.

Open Scope list_scope.


Set Implicit Arguments.
Unset Strict Implicit.


Section DataTypes.

  (* Order in Loopring contract is composed of two parts. One is the
     static data from submitter, while the other is dynamically
     generated and used only in LPSC.

     `Order` in Coq defines the static part. `OrderRuntimeState`
     combines it and the dynamic parts together.
   *)
  Record OrderRuntimeState :=
    mk_order_runtime_state {
        ord_rt_order: Order;

        ord_rt_p2p: bool;
        ord_rt_hash: bytes32;
        ord_rt_brokerInterceptor: address;
        ord_rt_filledAmountS : uint;
        ord_rt_initialFilledAmountS: uint;
        ord_rt_valid: bool;
      }.

  (* Similarly for Mining. *)
  Record MiningRuntimeState :=
    mk_mining_runtime_state {
        mining_rt_static: Mining;
        mining_rt_hash: bytes32;
        mining_rt_interceptor: address;
      }.

  Record Participation :=
    mk_participation {
        part_order_idx: nat; (* index in another order list *)
        part_splitS: uint;
        part_feeAmount: uint;
        part_feeAmountS: uint;
        part_feeAmountB: uint;
        part_rebateFee: uint;
        part_rebateS: uint;
        part_rebateB: uint;
        part_fillAmountS: uint;
        part_fillAmountB: uint;
      }.

  Record RingRuntimeState :=
    mk_ring_runtime_state {
        ring_rt_static: Ring;
        ring_rt_participations: list Participation;
        ring_rt_hash: bytes32;
        ring_rt_valid: bool;
      }.

  (* `RingSubmitterState` models the state of RingSubmitter state
     observable from the outside of contract.

     `RingSubmitterRuntimeState` also models the state (e.g., memory)
     that is only visible within the contract in its execution.
   *)
  Record RingSubmitterRuntimeState :=
    mk_ring_submitter_runtime_state {
        submitter_rt_mining: MiningRuntimeState;
        submitter_rt_orders: list OrderRuntimeState;
        submitter_rt_rings: list RingRuntimeState;
        (* TODO: add necessary fields of Context *)
      }.

  Definition make_rt_order (order: Order): OrderRuntimeState :=
    {|
      ord_rt_order := order;
      ord_rt_p2p := false;
      ord_rt_hash := 0;
      ord_rt_brokerInterceptor := 0;
      ord_rt_filledAmountS := 0;
      ord_rt_initialFilledAmountS := 0;
      ord_rt_valid := true;
    |}.

  Fixpoint make_rt_orders (orders: list Order): list OrderRuntimeState :=
    match orders with
    | nil => nil
    | order :: orders => make_rt_order order :: make_rt_orders orders
    end.

  Definition make_rt_mining (mining: Mining): MiningRuntimeState :=
    {|
      mining_rt_static := mining;
      mining_rt_hash := 0;
      mining_rt_interceptor := 0;
    |}.

  Definition make_participation (ord_idx: nat): Participation :=
    {|
      part_order_idx := ord_idx;
      part_splitS := 0;
      part_feeAmount := 0;
      part_feeAmountS := 0;
      part_feeAmountB := 0;
      part_rebateFee := 0;
      part_rebateS := 0;
      part_rebateB := 0;
      part_fillAmountS := 0;
      part_fillAmountB := 0;
    |}.

  Fixpoint make_participations (nr_ords: nat): list Participation :=
    match nr_ords with
    | O => nil
    | S n => make_participation n :: make_participations n
    end.

  Definition make_rt_ring (ring: Ring): RingRuntimeState :=
    {|
      ring_rt_static := ring;
      ring_rt_participations := make_participations (length (ring_orders ring));
      ring_rt_hash := 0;
      ring_rt_valid := true;
    |}.

  Fixpoint make_rt_rings (rings: list Ring): list RingRuntimeState :=
    match rings with
    | nil => nil
    | ring :: rings => make_rt_ring ring :: make_rt_rings rings
    end.

  Definition make_rt_submitter_state
             (mining: Mining) (orders: list Order) (rings: list Ring)
    : RingSubmitterRuntimeState :=
    {|
      submitter_rt_mining := make_rt_mining mining;
      submitter_rt_orders := make_rt_orders orders;
      submitter_rt_rings := make_rt_rings rings;
    |}.

  Definition submitter_update_mining
             (rsst: RingSubmitterRuntimeState) (st: MiningRuntimeState)
    : RingSubmitterRuntimeState :=
    {|
      submitter_rt_mining := st;
      submitter_rt_orders := submitter_rt_orders rsst;
      submitter_rt_rings := submitter_rt_rings rsst;
    |}.

  Definition submitter_update_orders
             (rsst: RingSubmitterRuntimeState) (sts: list OrderRuntimeState)
    : RingSubmitterRuntimeState :=
    {|
      submitter_rt_mining := submitter_rt_mining rsst;
      submitter_rt_orders := sts;
      submitter_rt_rings := submitter_rt_rings rsst;
    |}.

  Definition submitter_update_rings
             (rsst: RingSubmitterRuntimeState) (sts: list RingRuntimeState)
    : RingSubmitterRuntimeState :=
    {|
      submitter_rt_mining := submitter_rt_mining rsst;
      submitter_rt_orders := submitter_rt_orders rsst;
      submitter_rt_rings := sts;
    |}.

  Definition upd_order_broker
             (ord: OrderRuntimeState) (broker: address)
    : OrderRuntimeState :=
    let order := ord_rt_order ord in
    {|
      ord_rt_order :=
        {|
          order_owner                 := order_owner                 order;
          order_tokenS                := order_tokenS                order;
          order_tokenB                := order_tokenB                order;
          order_amountS               := order_amountS               order;
          order_amountB               := order_amountB               order;
          order_validSince            := order_validSince            order;
          order_tokenSpendableS       := order_tokenSpendableS       order;
          order_tokenSpendableFee     := order_tokenSpendableFee     order;
          order_dualAuthAddr          := order_dualAuthAddr          order;
          order_broker                := broker;
          order_brokerSpendableS      := order_brokerSpendableS      order;
          order_brokerSpendableFee    := order_brokerSpendableFee    order;
          order_orderInterceptor      := order_orderInterceptor      order;
          order_wallet                := order_wallet                order;
          order_validUntil            := order_validUntil            order;
          order_sig                   := order_sig                   order;
          order_dualAuthSig           := order_dualAuthSig           order;
          order_allOrNone             := order_allOrNone             order;
          order_feeToken              := order_feeToken              order;
          order_feeAmount             := order_feeAmount             order;
          order_feePercentage         := order_feePercentage         order;
          order_waiveFeePercentage    := order_waiveFeePercentage    order;
          order_tokenSFeePercentage   := order_tokenSFeePercentage   order;
          order_tokenBFeePercentage   := order_tokenBFeePercentage   order;
          order_tokenRecipient        := order_tokenRecipient        order;
          order_walletSplitPercentage := order_walletSplitPercentage order;
        |};
      ord_rt_p2p                  := ord_rt_p2p ord;
      ord_rt_hash                 := ord_rt_hash ord;
      ord_rt_brokerInterceptor    := ord_rt_brokerInterceptor ord;
      ord_rt_filledAmountS        := ord_rt_filledAmountS ord;
      ord_rt_initialFilledAmountS := ord_rt_initialFilledAmountS ord;
      ord_rt_valid                := ord_rt_valid ord;
    |}.

  Definition upd_order_interceptor
             (ord: OrderRuntimeState) (interceptor: address)
    : OrderRuntimeState :=
    {|
      ord_rt_order                := ord_rt_order ord;
      ord_rt_p2p                  := ord_rt_p2p ord;
      ord_rt_hash                 := ord_rt_hash ord;
      ord_rt_brokerInterceptor    := interceptor;
      ord_rt_filledAmountS        := ord_rt_filledAmountS ord;
      ord_rt_initialFilledAmountS := ord_rt_initialFilledAmountS ord;
      ord_rt_valid                := ord_rt_valid ord;
    |}.

  Definition upd_order_valid
             (ord: OrderRuntimeState) (valid: bool)
    : OrderRuntimeState :=
    {|
      ord_rt_order                := ord_rt_order ord;
      ord_rt_p2p                  := ord_rt_p2p ord;
      ord_rt_hash                 := ord_rt_hash ord;
      ord_rt_brokerInterceptor    := ord_rt_brokerInterceptor ord;
      ord_rt_filledAmountS        := ord_rt_filledAmountS ord;
      ord_rt_initialFilledAmountS := ord_rt_initialFilledAmountS ord;
      ord_rt_valid                := valid;
    |}.

End DataTypes.


Section Func_submitRings.

  (* We only define an abstract hash function with several properties
     rather than a concrete keccak until a concrete one is really
     needed.
   *)
  Context `{order_hash: Order -> bytes32}.
  Definition get_order_hash_preimg (order: Order) :=
    (order_allOrNone order,
     order_tokenBFeePercentage order,
     order_tokenSFeePercentage order,
     order_feePercentage order,
     order_walletSplitPercentage order,
     order_feeToken order,
     order_tokenRecipient order,
     order_wallet order,
     order_orderInterceptor order,
     order_broker order,
     order_dualAuthAddr order,
     order_tokenB order,
     order_tokenS order,
     order_owner order,
     order_validUntil order,
     order_validSince order,
     order_feeAmount order,
     order_amountB order,
     order_amountS order).
  Context `{order_hash_dec: forall ord ord': Order,
               (get_order_hash_preimg ord = get_order_hash_preimg ord' -> order_hash ord = order_hash ord') /\
               (get_order_hash_preimg ord <> get_order_hash_preimg ord' -> order_hash ord <> order_hash ord')}.

  Section UpdateOrdersHash.

    Fixpoint __update_orders_hash
             (orders: list OrderRuntimeState)
    : list OrderRuntimeState :=
      match orders with
      | nil => nil
      | order :: orders' =>
        let order' := {|
              ord_rt_order := ord_rt_order order;
              ord_rt_p2p := ord_rt_p2p order;
              ord_rt_hash := order_hash (ord_rt_order order);
              ord_rt_brokerInterceptor := ord_rt_brokerInterceptor order;
              ord_rt_filledAmountS := ord_rt_filledAmountS order;
              ord_rt_initialFilledAmountS := ord_rt_initialFilledAmountS order;
              ord_rt_valid := ord_rt_valid order;
            |}
        in order' :: __update_orders_hash orders'
      end.

    Definition update_orders_hash
               (wst0 wst: WorldState) (st: RingSubmitterRuntimeState)
      : (WorldState * RingSubmitterRuntimeState * list Event) :=
      (wst,
       submitter_update_orders st (__update_orders_hash (submitter_rt_orders st)),
       nil).

  End UpdateOrdersHash.


  Section UpdateOrdersBrokernAndInterceptor.

    Definition call_get_broker
               (wst0 wst: WorldState) (order: OrderRuntimeState)
    : (WorldState * OrderRuntimeState * list Event) :=
      let static_order := ord_rt_order order in
      let owner := order_owner static_order in
      let broker := order_broker static_order in
      let valid := ord_rt_valid order in
      match BrokerRegistry_step
              wst0 wst (msg_getBroker (wst_ring_submitter_addr wst) owner broker)
      with
      | (wst', ret', evts') =>
        if has_revert_event evts' then
          (wst0, order, EvtRevert :: nil)
        else
          match ret' with
          | RetGetBroker registered interceptor =>
            let order' := upd_order_interceptor order interceptor in
            let order' := if andb registered valid then
                            upd_order_valid order' true
                          else
                            upd_order_valid order' false
            in (wst', order', evts')
          | _ => (wst0, order, EvtRevert :: nil)
          end
      end.

    Fixpoint __update_orders_broker_interceptor
             (wst0 wst: WorldState) (orders: list OrderRuntimeState)
    : (WorldState * list OrderRuntimeState * list Event) :=
      match orders with
      | nil => (wst, nil, nil)
      | order :: orders' =>
        let static_order := ord_rt_order order in
        match
          match order_broker static_order with
          | O => (wst,
                 upd_order_broker order (order_owner static_order),
                 nil)
          | _ => call_get_broker wst0 wst order
          end
        with
        | (wst', order', evts') =>
          if has_revert_event evts' then
            (wst0, nil, EvtRevert :: nil)
          else
            match  __update_orders_broker_interceptor wst0 wst' orders' with
            | (wst'', orders'', evts'') =>
              if has_revert_event evts'' then
                (wst0, nil, EvtRevert :: nil)
              else
                (wst'', order' :: orders'', evts' ++ evts'')
            end
        end
      end.

    Definition update_orders_broker_interceptor
               (wst0 wst: WorldState) (st: RingSubmitterRuntimeState)
      : (WorldState * RingSubmitterRuntimeState * list Event) :=
      match __update_orders_broker_interceptor wst0 wst (submitter_rt_orders st) with
      | (wst', orders', evts') =>
        if has_revert_event evts' then
          (wst0, st, EvtRevert :: nil)
        else
          (wst', submitter_update_orders st orders', evts')
      end.

  End UpdateOrdersBrokernAndInterceptor.

  Definition submitter_seq
             (f0 f1: WorldState -> WorldState -> RingSubmitterRuntimeState ->
                     WorldState * RingSubmitterRuntimeState * list Event) :=
    fun (wst0 wst: WorldState) (st: RingSubmitterRuntimeState) =>
      match f0 wst0 wst st with
      | (wst', st', evts') =>
        if has_revert_event evts' then
          (wst0, st, EvtRevert :: nil)
        else
          match f1 wst0 wst' st' with
          | (wst'', st'', evts'') =>
            if has_revert_event evts'' then
              (wst0, st, EvtRevert :: nil)
            else
              (wst'', st'', evts' ++ evts'')
          end
      end.

  Notation "f0 ';;' f1" := (submitter_seq f0 f1) (left associativity, at level 400).

  Definition func_submitRings
             (wst0 wst: WorldState)
             (sender: address)
             (orders: list Order) (rings: list Ring) (mining: Mining)
    : (WorldState * RetVal * list Event) :=
    let st := make_rt_submitter_state mining orders rings in
    match (update_orders_hash ;; update_orders_broker_interceptor) wst0 wst st with
    | (wst', st', evts') =>
      if has_revert_event evts' then
        (wst0, RetNone, EvtRevert :: nil)
      else
        (wst', RetNone, evts')
    end.

End Func_submitRings.


Parameter order_hash: Order -> bytes32.
Parameter order_hash_dec: forall ord ord': Order,
    (get_order_hash_preimg ord = get_order_hash_preimg ord' -> order_hash ord = order_hash ord') /\
    (get_order_hash_preimg ord <> get_order_hash_preimg ord' -> order_hash ord <> order_hash ord').

Definition RingSubmitter_step
           (wst0 wst: WorldState) (msg: RingSubmitterMsg)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | msg_submitRings sender orders rings mining =>
    func_submitRings (order_hash := order_hash) wst0 wst sender orders rings mining
  end.
