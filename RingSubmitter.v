Require Import
        List
        ZArith.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.
Require Import
        BrokerRegistry
        OrderRegistry
        TradeDelegate.

Open Scope list_scope.
Open Scope bool_scope.


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

  Fixpoint make_participations (ord_indices: list nat): list Participation :=
    match ord_indices with
    | nil => nil
    | idx :: indices' => make_participation idx :: make_participations indices'
    end.

  Definition make_rt_ring (ring: Ring): RingRuntimeState :=
    {|
      ring_rt_static := ring;
      ring_rt_participations := make_participations (ring_orders ring);
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
          order_version               := order_version               order;
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

  Definition upd_order_init_filled
             (ord: OrderRuntimeState) (amount: uint)
    : OrderRuntimeState :=
    {|
      ord_rt_order                := ord_rt_order ord;
      ord_rt_p2p                  := ord_rt_p2p ord;
      ord_rt_hash                 := ord_rt_hash ord;
      ord_rt_brokerInterceptor    := ord_rt_brokerInterceptor ord;
      ord_rt_filledAmountS        := ord_rt_filledAmountS ord;
      ord_rt_initialFilledAmountS := amount;
      ord_rt_valid                := ord_rt_valid ord;
    |}.

  Definition upd_order_filled
             (ord: OrderRuntimeState) (amount: uint)
    : OrderRuntimeState :=
    {|
      ord_rt_order                := ord_rt_order ord;
      ord_rt_p2p                  := ord_rt_p2p ord;
      ord_rt_hash                 := ord_rt_hash ord;
      ord_rt_brokerInterceptor    := ord_rt_brokerInterceptor ord;
      ord_rt_filledAmountS        := amount;
      ord_rt_initialFilledAmountS := ord_rt_initialFilledAmountS ord;
      ord_rt_valid                := ord_rt_valid ord;
    |}.

  Definition clear_order_broker_spendables
             (ord: OrderRuntimeState)
    : OrderRuntimeState :=
    let order := ord_rt_order ord in
    {|
      ord_rt_order :=
        {|
          order_version               := order_version               order;
          order_owner                 := order_owner                 order;
          order_tokenS                := order_tokenS                order;
          order_tokenB                := order_tokenB                order;
          order_amountS               := order_amountS               order;
          order_amountB               := order_amountB               order;
          order_validSince            := order_validSince            order;
          order_tokenSpendableS       := order_tokenSpendableS       order;
          order_tokenSpendableFee     := order_tokenSpendableFee     order;
          order_dualAuthAddr          := order_dualAuthAddr          order;
          order_broker                := order_broker                order;
          order_brokerSpendableS      := mk_spendable false 0 0;
          order_brokerSpendableFee    := mk_spendable false 0 0;
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

  Definition upd_ring_hash
             (r: RingRuntimeState) (hash: bytes32)
    : RingRuntimeState :=
    {|
      ring_rt_static         := ring_rt_static r;
      ring_rt_participations := ring_rt_participations r;
      ring_rt_hash           := hash;
      ring_rt_valid          := ring_rt_valid r;
    |}.

  Definition upd_ring_valid
             (r: RingRuntimeState) (valid: bool)
    : RingRuntimeState :=
    {|
      ring_rt_static         := ring_rt_static r;
      ring_rt_participations := ring_rt_participations r;
      ring_rt_hash           := ring_rt_hash r;
      ring_rt_valid          := valid;
    |}.

  Definition upd_mining_hash
             (m: MiningRuntimeState) (hash: bytes32)
    : MiningRuntimeState :=
    {|
      mining_rt_static      := mining_rt_static m;
      mining_rt_hash        := hash;
      mining_rt_interceptor := mining_rt_interceptor m;
    |}.

  Definition upd_mining_interceptor
             (m: MiningRuntimeState) (interceptor: address)
    : MiningRuntimeState :=
    {|
      mining_rt_static      := mining_rt_static m;
      mining_rt_hash        := mining_rt_hash m;
      mining_rt_interceptor := interceptor;
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


  Section GetFilledAndCancelled.

    Fixpoint build_order_params
             (orders: list OrderRuntimeState) : list OrderParam :=
      match orders with
      | nil => nil
      | order :: orders' =>
        let static_order := ord_rt_order order in
        let param :=
            {|
              order_param_broker := order_broker static_order;
              order_param_owner  := order_owner static_order;
              order_param_hash   := ord_rt_hash order;
              order_param_validSince := order_validSince static_order;
              order_param_tradingPair := Nat.lxor (order_tokenS static_order) (order_tokenB static_order);
            |}
        in param :: build_order_params orders'
      end.

    Definition update_order_filled
               (order: OrderRuntimeState) (filled: option uint)
      : OrderRuntimeState :=
      match filled with
      | None => upd_order_valid order false
      | Some amount => upd_order_filled (upd_order_init_filled order amount)
                                       amount
      end.

    Fixpoint update_orders_filled
             (orders: list OrderRuntimeState) (fills: list (option uint))
      : list OrderRuntimeState :=
      match orders with
      | nil => nil
      | order :: orders' =>
        match fills with
        | nil => nil
        | filled :: fills' =>
          update_order_filled order filled :: update_orders_filled orders' fills'
        end
      end.

    Definition get_filled_and_check_cancelled
               (wst0 wst: WorldState) (st: RingSubmitterRuntimeState)
      : (WorldState * RingSubmitterRuntimeState * list Event) :=
      let params := build_order_params (submitter_rt_orders st) in
      match TradeDelegate_step
              wst0 wst (msg_batchGetFilledAndCheckCancelled (wst_ring_submitter_addr wst) params)
      with
      | (wst', ret', evts') =>
        if has_revert_event evts' then
          (wst0, st, EvtRevert :: nil)
        else
          match ret' with
          | RetFills fills =>
            let orders := submitter_rt_orders st in
            if Nat.eqb (length fills) (length orders) then
              (wst',
               submitter_update_orders st (update_orders_filled orders fills),
               evts')
            else
              (wst0, st, EvtRevert :: nil)
          | _ => (wst0, st, EvtRevert :: nil)
          end
      end.

  End GetFilledAndCancelled.


  Section UpdateBrokerSpendables.

    Fixpoint __update_orders_spendables
             (orders: list OrderRuntimeState)
    : list OrderRuntimeState :=
      match orders with
      | nil => nil
      | order :: orders' =>
        (* ??? *)
        clear_order_broker_spendables order :: __update_orders_spendables orders'
      end.

    Definition update_broker_spendables
               (wst0 wst: WorldState) (st: RingSubmitterRuntimeState)
    : (WorldState * RingSubmitterRuntimeState * list Event) :=
      (wst,
       submitter_update_orders st (__update_orders_spendables (submitter_rt_orders st)),
       nil).

  End UpdateBrokerSpendables.


  Section CheckOrders.

    Definition is_order_valid (order: OrderRuntimeState) (now: uint) : bool :=
      let static_order := ord_rt_order order in
      (ord_rt_valid order) &&
      (Nat.eqb (order_version static_order) 0) &&
      (negb (Nat.eqb (order_owner static_order) 0)) &&
      (negb (Nat.eqb (order_tokenS static_order) 0)) &&
      (negb (Nat.eqb (order_tokenB static_order) 0)) &&
      (negb (Nat.eqb (order_amountS static_order) 0)) &&
      (negb (Nat.eqb (order_feeToken static_order) 0)) &&
      (Nat.ltb (order_feePercentage static_order) FEE_PERCENTAGE_BASE_N) &&
      (Nat.ltb (order_tokenSFeePercentage static_order) FEE_PERCENTAGE_BASE_N) &&
      (Nat.ltb (order_tokenBFeePercentage static_order) FEE_PERCENTAGE_BASE_N) &&
      (Nat.leb (order_walletSplitPercentage static_order) 100) &&
      (Nat.leb (order_validSince static_order) now) &&
      (Nat.eqb (order_validUntil static_order) 0 ||
       Nat.ltb now (order_validUntil static_order)) &&
      (Z.leb (order_waiveFeePercentage static_order) FEE_PERCENTAGE_BASE_Z) &&
      (Z.leb (- FEE_PERCENTAGE_BASE_Z) (order_waiveFeePercentage static_order)) &&
      (Nat.eqb (order_dualAuthAddr static_order) 0 ||
       Nat.ltb 0 (length (order_dualAuthSig static_order)))
      (* TODO: model signature check *)
    .

    Fixpoint __check_orders
             (orders: list OrderRuntimeState) (now: uint)
      : list OrderRuntimeState :=
      match orders with
      | nil => nil
      | order :: orders' =>
        upd_order_valid order (is_order_valid order now) :: __check_orders orders' now
      end.

    Definition check_orders
               (wst0 wst: WorldState) (st: RingSubmitterRuntimeState)
    : (WorldState * RingSubmitterRuntimeState * list Event) :=
      let orders' := __check_orders (submitter_rt_orders st)
                                    (block_timestamp (wst_block_state wst)) in
      (wst, submitter_update_orders st orders', nil).

  End CheckOrders.


  (* Again, we use an abstract function to model the calculation of ring hash. *)
  Context `{ring_hash: RingRuntimeState -> list OrderRuntimeState -> bytes32}.

  Fixpoint __get_ring_hash_preimg
           (ps: list Participation) (orders: list OrderRuntimeState)
    : list (option (bytes32 * int16)):=
    match ps with
    | nil => nil
    | p :: ps' =>
      let ord_idx := part_order_idx p in
      let preimg := match nth_error orders ord_idx with
                    | None => None
                    | Some order => Some (ord_rt_hash order,
                                         order_waiveFeePercentage (ord_rt_order order))
                    end
      in preimg :: __get_ring_hash_preimg ps' orders
    end.

  Definition get_ring_hash_preimg
             (st: RingRuntimeState) (orders: list OrderRuntimeState)
    : list (option (bytes32 * int16)):=
    __get_ring_hash_preimg (ring_rt_participations st) orders.

  Context `{ring_hash_dec: forall (r r': RingRuntimeState) (orders: list OrderRuntimeState),
              (get_ring_hash_preimg r orders = get_ring_hash_preimg r' orders ->
               ring_hash r orders = ring_hash r' orders) /\
              (get_ring_hash_preimg r orders <> get_ring_hash_preimg r' orders ->
               ring_hash r orders <> ring_hash r' orders)}.

  Section UpdateRingsHash.

    Fixpoint __update_rings_hash
             (rings: list RingRuntimeState) (orders: list OrderRuntimeState)
    : list RingRuntimeState :=
      match rings with
      | nil => nil
      | r :: rings' =>
        upd_ring_hash r (ring_hash r orders) :: __update_rings_hash rings' orders
      end.

    Definition update_rings_hash
               (wst0 wst: WorldState) (st: RingSubmitterRuntimeState)
      : WorldState * RingSubmitterRuntimeState * (list Event) :=
      (wst,
       submitter_update_rings
         st (__update_rings_hash (submitter_rt_rings st) (submitter_rt_orders st)),
       nil).

  End UpdateRingsHash.


  Context `{mining_hash: Mining -> list RingRuntimeState -> bytes32}.

  Fixpoint xor_rings_hash (rings: list RingRuntimeState) : bytes32 :=
    match rings with
    | nil => 0
    | r :: rings' => Nat.lxor (ring_rt_hash r) (xor_rings_hash rings')
    end.

  Definition get_mining_hash_preimg
             (mining: Mining) (rings: list RingRuntimeState) :=
    (mining_miner mining, mining_feeRecipient mining, xor_rings_hash (rings)).

  Context `{mining_hash_dec: forall (m m': Mining) (rings: list RingRuntimeState),
               (get_mining_hash_preimg m rings = get_mining_hash_preimg m' rings ->
                mining_hash m rings = mining_hash m' rings) /\
               (get_mining_hash_preimg m rings <> get_mining_hash_preimg m' rings ->
                mining_hash m rings <> mining_hash m' rings)}.


  Section UpdateMiningHash.

    Definition update_mining_hash
               (wst0 wst: WorldState) (st: RingSubmitterRuntimeState)
    : WorldState * RingSubmitterRuntimeState * list Event :=
      let mining := submitter_rt_mining st in
      let rings := submitter_rt_rings st in
      (wst,
       submitter_update_mining
         st (upd_mining_hash mining (mining_hash (mining_rt_static mining) rings)),
       nil).

  End UpdateMiningHash.


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
    match (update_orders_hash ;;
           update_orders_broker_interceptor ;;
           get_filled_and_check_cancelled ;;
           update_broker_spendables ;;
           check_orders ;;
           update_rings_hash ;;
           update_mining_hash) wst0 wst st
    with
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
Parameter ring_hash: RingRuntimeState -> list OrderRuntimeState -> bytes32.
Parameter ring_hash_dec: forall (r r': RingRuntimeState) (orders: list OrderRuntimeState),
    (get_ring_hash_preimg r orders = get_ring_hash_preimg r' orders ->
     ring_hash r orders = ring_hash r' orders) /\
    (get_ring_hash_preimg r orders <> get_ring_hash_preimg r' orders ->
     ring_hash r orders <> ring_hash r' orders).
Parameter mining_hash: Mining -> list RingRuntimeState -> bytes32.
Parameter mining_hash_dec: forall (m m': Mining) (rings: list RingRuntimeState),
    (get_mining_hash_preimg m rings = get_mining_hash_preimg m' rings ->
     mining_hash m rings = mining_hash m' rings) /\
    (get_mining_hash_preimg m rings <> get_mining_hash_preimg m' rings ->
     mining_hash m rings <> mining_hash m' rings).

Definition RingSubmitter_step
           (wst0 wst: WorldState) (msg: RingSubmitterMsg)
  : (WorldState * RetVal * list Event) :=
  match msg with
  | msg_submitRings sender orders rings mining =>
    func_submitRings (order_hash := order_hash)
                     (ring_hash := ring_hash)
                     (mining_hash := mining_hash)
                     wst0 wst sender orders rings mining
  end.
