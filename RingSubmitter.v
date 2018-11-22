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
        BrokerInterceptor
        BrokerRegistry
        ERC20
        OrderRegistry
        TradeDelegate.


Open Scope bool_scope.


Section Aux.

  Fixpoint last_error {A: Type} (l: list A) : option A :=
    match l with
    | nil => None
    | a :: nil => Some a
    | a :: (_ :: _) as l' => last_error l'
    end.

  Definition alt_nth {A: Type} (l: list A) (n: nat) (a: A)
    : option (list A) :=
    match nth_error l n with
    | None => None
    | _ => Some (firstn n l ++ a :: tl (skipn n l))
    end.

End Aux.

Module SpendableElem <: ElemType.
  Definition elt := Spendable.
  Definition elt_zero := mk_spendable false O O.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof. decide equality; decide equality. Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
    unfold elt_eq; auto.
  Qed.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
    unfold elt_eq; intros; congruence.
  Qed.

End SpendableElem.

(* broker -> owner -> token -> spendable *)
Module BrokerSpendableMap := Mapping AAA_as_DT SpendableElem.
(* owner -> token -> spendable *)
Module TokenSpendableMap := Mapping AA_as_DT SpendableElem.

Module RingSubmitter.

  Section RunTimeState.

    (* Order in Loopring contract is composed of two parts. One is the *)
    (*      static data from submitter, while the other is dynamically *)
    (*      generated and used only in LPSC. *)

    (*      `Order` in Coq defines the static part. `OrderRuntimeState` *)
    (*      combines it and the dynamic parts together. *)
    (*    *)
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

    (* `RingSubmitterState` models the state of RingSubmitter state *)
    (*      observable from the outside of contract. *)

    (*      `RingSubmitterRuntimeState` also models the state (e.g., memory) *)
    (*      that is only visible within the contract in its execution. *)
    (*    *)
    Record RingSubmitterRuntimeState :=
      mk_ring_submitter_runtime_state {
          submitter_rt_mining: MiningRuntimeState;
          submitter_rt_orders: list OrderRuntimeState;
          submitter_rt_rings: list RingRuntimeState;
          submitter_rt_token_spendables: TokenSpendableMap.t;
          submitter_rt_broker_spendables: BrokerSpendableMap.t;
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
        submitter_rt_token_spendables := TokenSpendableMap.empty;
        submitter_rt_broker_spendables := BrokerSpendableMap.empty;
      |}.

    Definition submitter_update_mining
               (rsst: RingSubmitterRuntimeState) (st: MiningRuntimeState)
      : RingSubmitterRuntimeState :=
      {|
        submitter_rt_mining := st;
        submitter_rt_orders := submitter_rt_orders rsst;
        submitter_rt_rings := submitter_rt_rings rsst;
        submitter_rt_token_spendables := submitter_rt_token_spendables rsst;
        submitter_rt_broker_spendables := submitter_rt_broker_spendables rsst;
      |}.

    Definition submitter_update_orders
               (rsst: RingSubmitterRuntimeState) (sts: list OrderRuntimeState)
      : RingSubmitterRuntimeState :=
      {|
        submitter_rt_mining := submitter_rt_mining rsst;
        submitter_rt_orders := sts;
        submitter_rt_rings := submitter_rt_rings rsst;
        submitter_rt_token_spendables := submitter_rt_token_spendables rsst;
        submitter_rt_broker_spendables := submitter_rt_broker_spendables rsst;
      |}.

    Definition submitter_update_rings
               (rsst: RingSubmitterRuntimeState) (sts: list RingRuntimeState)
      : RingSubmitterRuntimeState :=
      {|
        submitter_rt_mining := submitter_rt_mining rsst;
        submitter_rt_orders := submitter_rt_orders rsst;
        submitter_rt_rings := sts;
        submitter_rt_token_spendables := submitter_rt_token_spendables rsst;
        submitter_rt_broker_spendables := submitter_rt_broker_spendables rsst;
      |}.

    Definition submitter_update_token_spendables
               (rsst: RingSubmitterRuntimeState) (spendables: TokenSpendableMap.t)
      : RingSubmitterRuntimeState :=
      {|
        submitter_rt_mining := submitter_rt_mining rsst;
        submitter_rt_orders := submitter_rt_orders rsst;
        submitter_rt_rings := submitter_rt_rings rsst;
        submitter_rt_token_spendables := spendables;
        submitter_rt_broker_spendables := submitter_rt_broker_spendables rsst;
      |}.

    Definition submitter_update_token_spendable
               (rsst: RingSubmitterRuntimeState)
               (ord: OrderRuntimeState) (token: address)
               (spendable: Spendable)
      : RingSubmitterRuntimeState :=
      let order := ord_rt_order ord in
      let spendables := submitter_rt_token_spendables rsst in
      let spendables' :=
          TokenSpendableMap.upd spendables (order_owner order, token) spendable in
      submitter_update_token_spendables rsst spendables'.

    Definition submitter_update_broker_spendables
               (rsst: RingSubmitterRuntimeState) (spendables: BrokerSpendableMap.t)
      : RingSubmitterRuntimeState :=
      {|
        submitter_rt_mining := submitter_rt_mining rsst;
        submitter_rt_orders := submitter_rt_orders rsst;
        submitter_rt_rings := submitter_rt_rings rsst;
        submitter_rt_token_spendables := submitter_rt_token_spendables rsst;
        submitter_rt_broker_spendables := spendables;
      |}.

    Definition submitter_update_broker_spendable
               (rsst: RingSubmitterRuntimeState)
               (ord: OrderRuntimeState) (token: address)
               (spendable: Spendable)
      : RingSubmitterRuntimeState :=
      let order := ord_rt_order ord in
      let spendables := submitter_rt_broker_spendables rsst in
      let spendables' :=
          BrokerSpendableMap.upd spendables
                                 (order_broker order, order_owner order, token)
                                 spendable in
      submitter_update_broker_spendables rsst spendables'.

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

    Definition upd_order_p2p
               (ord: OrderRuntimeState) (p2p: bool)
      : OrderRuntimeState :=
      {|
        ord_rt_order                := ord_rt_order ord;
        ord_rt_p2p                  := p2p;
        ord_rt_hash                 := ord_rt_hash ord;
        ord_rt_brokerInterceptor    := ord_rt_brokerInterceptor ord;
        ord_rt_filledAmountS        := ord_rt_filledAmountS ord;
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

    Definition upd_ring_participations
               (r: RingRuntimeState) (ps: list Participation)
      : RingRuntimeState :=
      {|
        ring_rt_static         := ring_rt_static r;
        ring_rt_participations := ps;
        ring_rt_hash           := ring_rt_hash r;
        ring_rt_valid          := ring_rt_valid r;
      |}.

    Definition inc_ring_minerFeesToOrdersPercentage
               (r: RingRuntimeState) (amount: uint)
      : RingRuntimeState :=
      {|
        ring_rt_static         := ring_add_minerFeesToOrdersPercentage (ring_rt_static r) amount;
        ring_rt_participations := ring_rt_participations r;
        ring_rt_hash           := ring_rt_hash r;
        ring_rt_valid          := ring_rt_valid r;
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

    Definition upd_mining_miner
               (m: MiningRuntimeState) (miner: address)
      : MiningRuntimeState :=
      let mining := mining_rt_static m in
      {|
        mining_rt_static      :=
          {|
            mining_feeRecipient := mining_feeRecipient mining;
            mining_miner        := miner;
            mining_sig          := mining_sig mining;
          |};
        mining_rt_hash        := mining_rt_hash m;
        mining_rt_interceptor := mining_rt_interceptor m;
      |}.

    Definition upd_part_fillAmounts
               (p: Participation) (amountS amountB: uint)
      : Participation :=
      {|
        part_order_idx   := part_order_idx   p;
        part_splitS      := part_splitS      p;
        part_feeAmount   := part_feeAmount   p;
        part_feeAmountS  := part_feeAmountS  p;
        part_feeAmountB  := part_feeAmountB  p;
        part_rebateFee   := part_rebateFee   p;
        part_rebateS     := part_rebateS     p;
        part_rebateB     := part_rebateB     p;
        part_fillAmountS := amountS;
        part_fillAmountB := amountB;
      |}.

    Definition upd_part_fillAmountS
               (p: Participation) (amountS: uint)
      : Participation :=
      {|
        part_order_idx   := part_order_idx   p;
        part_splitS      := part_splitS      p;
        part_feeAmount   := part_feeAmount   p;
        part_feeAmountS  := part_feeAmountS  p;
        part_feeAmountB  := part_feeAmountB  p;
        part_rebateFee   := part_rebateFee   p;
        part_rebateS     := part_rebateS     p;
        part_rebateB     := part_rebateB     p;
        part_fillAmountS := amountS;
        part_fillAmountB := part_fillAmountB p;
      |}.

    Definition upd_part_splitS
               (p: Participation) (amount: uint)
      : Participation :=
      {|
        part_order_idx   := part_order_idx   p;
        part_splitS      := amount;
        part_feeAmount   := part_feeAmount   p;
        part_feeAmountS  := part_feeAmountS  p;
        part_feeAmountB  := part_feeAmountB  p;
        part_rebateFee   := part_rebateFee   p;
        part_rebateS     := part_rebateS     p;
        part_rebateB     := part_rebateB     p;
        part_fillAmountS := part_fillAmountS p;
        part_fillAmountB := part_fillAmountB p;
      |}.

    Definition upd_part_feeAmounts
               (p: Participation) (amount amountS amountB: uint)
      : Participation :=
      {|
        part_order_idx   := part_order_idx   p;
        part_splitS      := part_splitS      p;
        part_feeAmount   := amount;
        part_feeAmountS  := amountS;
        part_feeAmountB  := amountB;
        part_rebateFee   := part_rebateFee   p;
        part_rebateS     := part_rebateS     p;
        part_rebateB     := part_rebateB     p;
        part_fillAmountS := part_fillAmountS p;
        part_fillAmountB := part_fillAmountB p;
      |}.

    Definition upd_part_rebates
               (p: Participation) (amount amountS amountB: uint)
      : Participation :=
      {|
        part_order_idx   := part_order_idx   p;
        part_splitS      := part_splitS      p;
        part_feeAmount   := part_feeAmount   p;
        part_feeAmountS  := part_feeAmountS  p;
        part_feeAmountB  := part_feeAmountB  p;
        part_rebateFee   := amount;
        part_rebateS     := amountS;
        part_rebateB     := amountB;
        part_fillAmountS := part_fillAmountS p;
        part_fillAmountB := part_fillAmountB p;
      |}.

  End RunTimeState.

  Section GetSpendable.

    Section StGetSpendable.

      (** Get broker spendable from spendable map *)
      Definition __st_get_broker_spendable
                 (st: RingSubmitterRuntimeState)
                 (ord: OrderRuntimeState)
                 (token: address) :=
        let order := ord_rt_order ord in
        let broker := order_broker order in
        let owner := order_owner order in
        BrokerSpendableMap.get (submitter_rt_broker_spendables st)
                               (broker, owner, token).

      (** Get broker spendableS from spendable map *)
      Definition _st_get_brokerSpendableS
                 (st: RingSubmitterRuntimeState) (ord: OrderRuntimeState) :=
        __st_get_broker_spendable st ord (order_tokenS (ord_rt_order ord)).

      (** Get broker spendableFee from spendable map *)
      Definition _st_get_brokerSpendableFee
                 (st: RingSubmitterRuntimeState) (ord: OrderRuntimeState) :=
        __st_get_broker_spendable st ord (order_feeToken (ord_rt_order ord)).

      (** Get token spendable from spendable map *)
      Definition __st_get_token_spendable
                 (st: RingSubmitterRuntimeState)
                 (ord: OrderRuntimeState)
                 (token: address) :=
        let order := ord_rt_order ord in
        let owner := order_owner order in
        TokenSpendableMap.get (submitter_rt_token_spendables st) (owner, token).

      (** Get token spendableS from spendable map *)
      Definition _st_get_tokenSpendableS
                 (st: RingSubmitterRuntimeState) (ord: OrderRuntimeState) :=
        __st_get_token_spendable st ord (order_tokenS (ord_rt_order ord)).

      (** Get token spendableFee from spendable map *)
      Definition _st_get_tokenSpendableFee
                 (st: RingSubmitterRuntimeState) (ord: OrderRuntimeState) :=
        __st_get_token_spendable st ord (order_feeToken (ord_rt_order ord)).

    End StGetSpendable.

    Section ERC20GetTokenSpendable.

      Definition __erc20_get_allowance_success
                 (wst: WorldState) (owner token: address)
                 (wst': WorldState) (allowance: uint) (events: list Event) : Prop :=
        ERC20s.model wst
                     (msg_allowance (wst_ring_submitter_addr wst)
                                    token
                                    owner
                                    (wst_trade_delegate_addr wst))
                     wst' (RetUint allowance) events.

      Definition __erc20_get_balance_success
                 (wst: WorldState) (owner token: address)
                 (wst': WorldState) (balance: uint) (events: list Event) : Prop :=
        ERC20s.model wst
                     (msg_balanceOf (wst_ring_submitter_addr wst) token owner)
                     wst' (RetUint balance) events.

      Inductive _erc20_get_token_spendable
                (wst: WorldState) (owner token: address)
        : WorldState -> uint -> list Event -> Prop :=
      | ERC20GetSpendable_zero:
          forall wst' events,
            __erc20_get_allowance_success wst owner token wst' 0 events ->
            _erc20_get_token_spendable wst owner token wst' 0 events

      | ERC20GetSpendable_nonzero_1:
          forall wst' allowance events' wst'' balance events'',
            __erc20_get_allowance_success wst owner token wst' allowance events' ->
            allowance <> 0 ->
            __erc20_get_balance_success wst' owner token wst'' balance events'' ->
            balance < allowance ->
            _erc20_get_token_spendable wst owner token wst'' balance (events' ++ events'')

      | ERC20GetSpendable_nonzero_2:
          forall wst' allowance events' wst'' balance events'',
            __erc20_get_allowance_success wst owner token wst' allowance events' ->
            allowance <> 0 ->
            __erc20_get_balance_success wst' owner token wst'' balance events'' ->
            balance >= allowance ->
            _erc20_get_token_spendable wst owner token wst'' allowance (events' ++ events'')
      .

      Definition __erc20_get_token_spendable
                 (wst: WorldState)
                 (ord: OrderRuntimeState)
                 (token: address)
                 (wst': WorldState)
                 (spendable: Spendable)
                 (events: list Event) : Prop :=
        forall wst'' amount events'',
          _erc20_get_token_spendable
            wst (order_owner (ord_rt_order ord)) token wst'' amount events'' ->
          wst' = wst'' /\
          events = events'' /\
          spendable = mk_spendable true amount 0.

      Definition _erc20_get_tokenSpendableS
                 (wst: WorldState)
                 (ord: OrderRuntimeState)
                 (wst': WorldState)
                 (spendable: Spendable)
                 (events: list Event) : Prop :=
        __erc20_get_token_spendable
          wst ord (order_tokenS (ord_rt_order ord)) wst' spendable events.

      Definition _erc20_get_tokenSpendableFee
                 (wst: WorldState)
                 (ord: OrderRuntimeState)
                 (wst': WorldState)
                 (spendable: Spendable)
                 (events: list Event) : Prop :=
        __erc20_get_token_spendable
          wst ord (order_feeToken (ord_rt_order ord)) wst' spendable events.

    End ERC20GetTokenSpendable.

    Section ProxyGetBrokerSpendable.

      Definition __proxy_get_allowance_success
                 (wst: WorldState) (broker owner token interceptor: address)
                 (wst': WorldState) (allowance: uint) (events: list Event) : Prop :=
        BrokerInterceptor.model wst
                                (msg_getAllowanceSafe (wst_ring_submitter_addr wst)
                                                      interceptor owner broker token)
                                wst' (RetUint allowance) events.

      Definition __proxy_get_broker_spendable
                 (wst: WorldState)
                 (ord: OrderRuntimeState)
                 (token: address)
                 (wst': WorldState)
                 (spendable: Spendable)
                 (events: list Event) : Prop :=
        forall order wst'' allowance events'',
          order = ord_rt_order ord ->
          __proxy_get_allowance_success
            wst
            (order_broker order) (order_owner order) token (ord_rt_brokerInterceptor ord)
            wst'' allowance events'' ->
          wst' = wst'' /\
          events = events'' /\
          spendable = mk_spendable true allowance 0.

      Definition _proxy_get_brokerSpendableS
                 (wst: WorldState)
                 (ord: OrderRuntimeState)
                 (wst': WorldState)
                 (spendable: Spendable)
                 (events: list Event) : Prop :=
        __proxy_get_broker_spendable
          wst ord (order_tokenS (ord_rt_order ord)) wst' spendable events.

      Definition _proxy_get_brokerSpendableFee
                 (wst: WorldState)
                 (ord: OrderRuntimeState)
                 (wst': WorldState)
                 (spendable: Spendable)
                 (events: list Event) : Prop :=
        __proxy_get_broker_spendable
          wst ord (order_feeToken (ord_rt_order ord)) wst' spendable events.

    End ProxyGetBrokerSpendable.

    Inductive _get_token_spendable
              (wst: WorldState)
              (st: RingSubmitterRuntimeState)
              (ord: OrderRuntimeState)
              (token: address)
      : WorldState -> RingSubmitterRuntimeState -> Spendable -> list Event -> Prop :=
    | GetTokenSpenable_noninited:
        forall wst' spendable events,
          spendable_initialized (__st_get_token_spendable st ord token) = false ->
          __erc20_get_token_spendable wst ord token wst' spendable events ->
          _get_token_spendable
            wst st ord token wst'
            (submitter_update_token_spendable st ord token spendable)
            spendable events

    | GetTokenSpenable_inited:
        forall spendable,
          spendable = __st_get_token_spendable st ord token ->
          spendable_initialized spendable = true ->
          _get_token_spendable wst st ord token wst st spendable nil
    .

    Inductive _get_broker_spendable
              (wst: WorldState)
              (st: RingSubmitterRuntimeState)
              (ord: OrderRuntimeState)
              (token: address)
      : WorldState -> RingSubmitterRuntimeState -> Spendable -> list Event -> Prop :=
    | GetBrokerSpenable_noninited:
        forall wst' spendable events,
          spendable_initialized (__st_get_broker_spendable st ord token) = false ->
          __proxy_get_broker_spendable wst ord token wst' spendable events ->
          _get_broker_spendable
            wst st ord token wst'
            (submitter_update_broker_spendable st ord token spendable)
            spendable events

    | GetBrokerSpenable_inited:
        forall spendable,
          spendable = __st_get_broker_spendable st ord token ->
          spendable_initialized spendable = true ->
          _get_broker_spendable wst st ord token wst st spendable nil
    .

    Definition get_tokenSpendableS
               (wst: WorldState) (st: RingSubmitterRuntimeState)
               (ord: OrderRuntimeState)
               (wst': WorldState) (st': RingSubmitterRuntimeState)
               (spendable: Spendable) (events: list Event) : Prop :=
      _get_token_spendable
        wst st ord (order_tokenS (ord_rt_order ord)) wst' st' spendable events.

    Definition get_tokenSpendableFee
               (wst: WorldState) (st: RingSubmitterRuntimeState)
               (ord: OrderRuntimeState)
               (wst': WorldState) (st': RingSubmitterRuntimeState)
               (spendable: Spendable) (events: list Event) : Prop :=
      _get_token_spendable
        wst st ord (order_feeToken (ord_rt_order ord)) wst' st' spendable events.

    Definition get_brokerSpendableS
               (wst: WorldState) (st: RingSubmitterRuntimeState)
               (ord: OrderRuntimeState)
               (wst': WorldState) (st': RingSubmitterRuntimeState)
               (spendable: Spendable) (events: list Event) : Prop :=
      _get_broker_spendable
        wst st ord (order_tokenS (ord_rt_order ord)) wst' st' spendable events.

    Definition get_brokerSpendableFee
               (wst: WorldState) (st: RingSubmitterRuntimeState)
               (ord: OrderRuntimeState)
               (wst': WorldState) (st': RingSubmitterRuntimeState)
               (spendable: Spendable) (events: list Event) : Prop :=
      _get_broker_spendable
        wst st ord (order_feeToken (ord_rt_order ord)) wst' st' spendable events.

  End GetSpendable.

  Section SetSpendable.

    Definition _token_spendable_reserved_inc
               (spendables: TokenSpendableMap.t)
               (ord: OrderRuntimeState)
               (token: address)
               (amount: uint)
    : TokenSpendableMap.t :=
      let owner := order_owner (ord_rt_order ord) in
      let spendable := TokenSpendableMap.get spendables (owner, token) in
      let spendable' := {| spendable_initialized := spendable_initialized spendable;
                           spendable_amount      := spendable_amount spendable;
                           spendable_reserved    := spendable_reserved spendable + amount;
                        |} in
      TokenSpendableMap.upd spendables (owner, token) spendable'.

    Definition _broker_spendable_reserved_inc
               (spendables: BrokerSpendableMap.t)
               (ord: OrderRuntimeState)
               (token: address)
               (amount: uint)
      : BrokerSpendableMap.t :=
      let order := ord_rt_order ord in
      let broker := order_broker order in
      let owner := order_owner order in
      let spendable := BrokerSpendableMap.get spendables (broker, owner, token) in
      let spendable' := {| spendable_initialized := spendable_initialized spendable;
                           spendable_amount      := spendable_amount spendable;
                           spendable_reserved    := spendable_reserved spendable + amount;
                        |} in
      BrokerSpendableMap.upd spendables (broker, owner, token) spendable'.

    Definition token_spendableS_reserved_inc
               (spendables: TokenSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : TokenSpendableMap.t :=
      _token_spendable_reserved_inc spendables ord (order_tokenS (ord_rt_order ord)) amount.

    Definition token_spendableFee_reserved_inc
               (spendables: TokenSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : TokenSpendableMap.t :=
      _token_spendable_reserved_inc spendables ord (order_feeToken (ord_rt_order ord)) amount.

    Definition broker_spendableS_reserved_inc
               (spendables: BrokerSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : BrokerSpendableMap.t :=
      _broker_spendable_reserved_inc spendables ord (order_tokenS (ord_rt_order ord)) amount.

    Definition broker_spendableFee_reserved_inc
               (spendables: BrokerSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : BrokerSpendableMap.t :=
      _broker_spendable_reserved_inc spendables ord (order_feeToken (ord_rt_order ord)) amount.

    Definition _clear_token_spendables_reserved
               (spendables: TokenSpendableMap.t)
               (ord: OrderRuntimeState)
      : TokenSpendableMap.t :=
      let order := ord_rt_order ord in
      let owner := order_owner order in
      let tokenS := order_tokenS order in
      let spendableS := TokenSpendableMap.get spendables (owner, tokenS) in
      let spendableS' := {| spendable_initialized := spendable_initialized spendableS;
                            spendable_amount      := spendable_amount spendableS;
                            spendable_reserved    := 0;
                         |} in
      let feeToken := order_feeToken order in
      let feeSpendable := TokenSpendableMap.get spendables (owner, feeToken) in
      let feeSpendable' := {| spendable_initialized := spendable_initialized feeSpendable;
                              spendable_amount      := spendable_amount feeSpendable;
                              spendable_reserved    := 0;
                           |} in
      TokenSpendableMap.upd
        (TokenSpendableMap.upd spendables (owner, tokenS) spendableS')
        (owner, feeToken) feeSpendable'.

    Definition _clear_broker_spendables_reserved
               (spendables: BrokerSpendableMap.t)
               (ord: OrderRuntimeState)
      : BrokerSpendableMap.t :=
      let order := ord_rt_order ord in
      let broker := order_broker order in
      let owner := order_owner order in
      let tokenS := order_tokenS order in
      let spendableS := BrokerSpendableMap.get spendables (broker, owner, tokenS) in
      let spendableS' := {| spendable_initialized := spendable_initialized spendableS;
                            spendable_amount      := spendable_amount spendableS;
                            spendable_reserved    := 0;
                         |} in
      let feeToken := order_feeToken order in
      let feeSpendable := BrokerSpendableMap.get spendables (broker, owner, feeToken) in
      let feeSpendable' := {| spendable_initialized := spendable_initialized feeSpendable;
                              spendable_amount      := spendable_amount feeSpendable;
                              spendable_reserved    := 0;
                           |} in
      BrokerSpendableMap.upd
        (BrokerSpendableMap.upd spendables (broker, owner, tokenS) spendableS')
        (broker, owner, feeToken) feeSpendable'.

    Definition clear_order_spendables_reserved
               (st: RingSubmitterRuntimeState) (ord: OrderRuntimeState)
      : RingSubmitterRuntimeState :=
      let token_spendables := submitter_rt_token_spendables st in
      let token_spendables' := _clear_token_spendables_reserved token_spendables ord in
      let broker_spendables := submitter_rt_broker_spendables st in
      let broker_spendables' :=
          match ord_rt_brokerInterceptor ord with
          | O => broker_spendables
          | _ => _clear_broker_spendables_reserved broker_spendables ord
          end
      in
      submitter_update_token_spendables
        (submitter_update_broker_spendables st broker_spendables')
        token_spendables'.

    Definition _token_spendable_amount_dec
               (spendables: TokenSpendableMap.t)
               (ord: OrderRuntimeState)
               (token: address)
               (amount: uint)
      : TokenSpendableMap.t :=
      let owner := order_owner (ord_rt_order ord) in
      let spendable := TokenSpendableMap.get spendables (owner, token) in
      let spendable' := {| spendable_initialized := spendable_initialized spendable;
                           spendable_amount      := spendable_amount spendable - amount;
                           spendable_reserved    := spendable_reserved spendable;
                        |} in
      TokenSpendableMap.upd spendables (owner, token) spendable'.

    Definition _broker_spendable_amount_dec
               (spendables: BrokerSpendableMap.t)
               (ord: OrderRuntimeState)
               (token: address)
               (amount: uint)
      : BrokerSpendableMap.t :=
      let order := ord_rt_order ord in
      let broker := order_broker order in
      let owner := order_owner order in
      let spendable := BrokerSpendableMap.get spendables (broker, owner, token) in
      let spendable' := {| spendable_initialized := spendable_initialized spendable;
                           spendable_amount      := spendable_amount spendable - amount;
                           spendable_reserved    := spendable_reserved spendable;
                        |} in
      BrokerSpendableMap.upd spendables (broker, owner, token) spendable'.

    Definition token_spendableS_amount_dec
               (spendables: TokenSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : TokenSpendableMap.t :=
      _token_spendable_amount_dec spendables ord (order_tokenS (ord_rt_order ord)) amount.

    Definition token_spendableFee_amount_dec
               (spendables: TokenSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : TokenSpendableMap.t :=
      _token_spendable_amount_dec spendables ord (order_feeToken (ord_rt_order ord)) amount.

    Definition broker_spendableS_amount_dec
               (spendables: BrokerSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : BrokerSpendableMap.t :=
      _broker_spendable_amount_dec spendables ord (order_tokenS (ord_rt_order ord)) amount.

    Definition broker_spendableFee_amount_dec
               (spendables: BrokerSpendableMap.t)
               (ord: OrderRuntimeState)
               (amount: uint)
      : BrokerSpendableMap.t :=
      _broker_spendable_amount_dec spendables ord (order_feeToken (ord_rt_order ord)) amount.

  End SetSpendable.

  Parameters get_order_hash: Order -> bytes32.
  Parameters get_ring_hash: Ring -> list OrderRuntimeState -> bytes32.
  Parameter get_mining_hash: Mining -> list RingRuntimeState -> bytes32.

  Section HashAxioms.

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

    Axiom order_hash_dec:
      forall (ord ord': Order),
        let preimg := get_order_hash_preimg ord in
        let preimg' := get_order_hash_preimg ord' in
        (preimg = preimg' -> get_order_hash ord = get_order_hash ord') /\
        (preimg <> preimg' -> get_order_hash ord <> get_order_hash ord').

    Fixpoint __get_ring_hash_preimg
             (indices: list nat) (orders: list OrderRuntimeState)
      : list (option (bytes32 * int16)):=
      match indices with
      | nil => nil
      | idx :: indices' =>
        let preimg := match nth_error orders idx with
                      | None => None
                      | Some order => Some (ord_rt_hash order,
                                           order_waiveFeePercentage (ord_rt_order order))
                      end
        in preimg :: __get_ring_hash_preimg indices' orders
      end.

    Definition get_ring_hash_preimg
               (r: Ring) (orders: list OrderRuntimeState) :=
      __get_ring_hash_preimg (ring_orders r) orders.

    Axiom ring_hash_dec:
      forall (r r': Ring) (orders orders': list OrderRuntimeState),
        let preimg := get_ring_hash_preimg r orders in
        let preimg' := get_ring_hash_preimg r' orders' in
        (preimg = preimg' -> get_ring_hash r orders = get_ring_hash r' orders') /\
        (preimg <> preimg' -> get_ring_hash r orders <> get_ring_hash r' orders').

    Fixpoint rings_hashes (rings: list RingRuntimeState) : list bytes32 :=
      match rings with
      | nil => nil
      | r :: rings' => ring_rt_hash r :: rings_hashes rings'
      end.

    Definition get_mining_hash_preimg
               (mining: Mining) (rings: list RingRuntimeState) :=
      (mining_miner mining, mining_feeRecipient mining, rings_hashes rings).

    Axiom mining_hash_dec:
      forall (m m': Mining) (rings rings': list RingRuntimeState),
        let preimg := get_mining_hash_preimg m rings in
        let preimg' := get_mining_hash_preimg m' rings' in
        (preimg = preimg' -> get_mining_hash m rings = get_mining_hash m' rings') /\
        (preimg <> preimg' -> get_mining_hash m rings <> get_mining_hash m' rings').

  End HashAxioms.

  Section SubSpec.

    Record SubSpec :=
      mk_sub_spec {
          subspec_require: WorldState -> RingSubmitterRuntimeState -> Prop;
          subspec_trans: WorldState -> RingSubmitterRuntimeState ->
                         WorldState -> RingSubmitterRuntimeState ->
                         Prop;
          subspec_events: WorldState -> RingSubmitterRuntimeState ->
                          list Event -> Prop;
        }.

  End SubSpec.

  Section SubmitRings.

    Section UpdateOrdersHashes.

      Fixpoint update_orders_hashes
               (orders: list OrderRuntimeState)
      : list OrderRuntimeState :=
        match orders with
        | nil => nil
        | order :: orders' =>
          let order' := {|
                ord_rt_order := ord_rt_order order;
                ord_rt_p2p := ord_rt_p2p order;
                ord_rt_hash := get_order_hash (ord_rt_order order);
                ord_rt_brokerInterceptor := ord_rt_brokerInterceptor order;
                ord_rt_filledAmountS := ord_rt_filledAmountS order;
                ord_rt_initialFilledAmountS := ord_rt_initialFilledAmountS order;
                ord_rt_valid := ord_rt_valid order;
              |}
          in order' :: update_orders_hashes orders'
        end.

      Definition update_orders_hashes_subspec
                 (sender: address)
                 (orders: list Order)
                 (rings: list Ring)
                 (mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\
              st' = submitter_update_orders
                      st (update_orders_hashes (submitter_rt_orders st));

          subspec_events :=
            fun wst st events => events = nil;
        |}.

    End UpdateOrdersHashes.

    Section UpdateOrdersBrokersAndIntercetors.

      Definition get_broker_success
                 (wst: WorldState) (ord: OrderRuntimeState)
                 (wst': WorldState) (retval: option address) (events: list Event)
      : Prop :=
        let order := ord_rt_order ord in
        BrokerRegistry.model
          wst
          (msg_getBroker (wst_ring_submitter_addr wst)
                         (order_owner order) (order_broker order))
          wst' (RetBrokerInterceptor retval) events.

      Inductive update_order_broker_interceptor
                (wst: WorldState) (ord: OrderRuntimeState)
        : WorldState -> OrderRuntimeState -> list Event -> Prop :=
      | UpdateBrokerInterceptor_P2P:
          let order := ord_rt_order ord in
          order_broker order = O ->
          update_order_broker_interceptor
            wst ord wst (upd_order_broker ord (order_owner order)) nil

      | UpdateBrokerInterceptor_NonP2P_registered:
          forall wst' interceptor events,
            get_broker_success wst ord wst' (Some interceptor) events ->
            update_order_broker_interceptor wst ord wst' ord events

      | UpdateBrokerInterceptor_NonP2P_unregistered:
          forall wst' events,
            get_broker_success wst ord wst' None events ->
            update_order_broker_interceptor
              wst ord wst' (upd_order_valid ord false) events
      .

      Inductive update_orders_broker_interceptor (wst: WorldState)
        : list OrderRuntimeState ->
          WorldState -> list OrderRuntimeState -> list Event -> Prop :=
      | UpdateOrdersBrokerInterceptor_nil:
          update_orders_broker_interceptor wst nil wst nil nil

      | UpdateOrdersBrokerInterceptor_cons:
          forall order orders wst' order' events wst'' orders' events',
            update_order_broker_interceptor wst order wst' order' events ->
            update_orders_broker_interceptor wst' orders wst'' orders' events' ->
            update_orders_broker_interceptor
              wst (order :: orders) wst'' (order' :: orders') (events ++ events')
      .

      Definition update_orders_brokers_and_interceptors
                 (sender: address)
                 (orders: list Order)
                 (rings: list Ring)
                 (mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              forall wst'' orders' events,
                update_orders_broker_interceptor
                  wst (submitter_rt_orders st) wst'' orders' events ->
                wst' = wst'' /\
                st' = submitter_update_orders st orders'
          ;

          subspec_events :=
            fun wst st events =>
              forall wst' orders' events',
                update_orders_broker_interceptor
                  wst (submitter_rt_orders st) wst' orders' events' ->
                events = events'
          ;
        |}.

    End UpdateOrdersBrokersAndIntercetors.

    Section GetFilledAndCheckCancelled.

      Fixpoint make_order_params
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
          in param :: make_order_params orders'
        end.

      Definition batchGetFilledAndCheckCancelled_success
                 (wst: WorldState) (st: RingSubmitterRuntimeState)
                 (fills: list (option uint))
                 (wst': WorldState) (events: list Event) : Prop :=
        TradeDelegate.model
          wst
          (msg_batchGetFilledAndCheckCancelled
             (wst_ring_submitter_addr wst)
             (make_order_params (submitter_rt_orders st)))
          wst' (RetFills fills) events.

      Inductive update_order_filled_and_valid (order: OrderRuntimeState)
        : option uint -> OrderRuntimeState -> Prop :=
      | UpdateOrderFilledAndValid_noncancelled:
          forall amount,
            update_order_filled_and_valid
              order (Some amount)
              (upd_order_filled (upd_order_init_filled order amount) amount)

      | UpdateOrderFilledAndValid_cancelled:
          update_order_filled_and_valid order None (upd_order_valid order false)
      .

      Inductive update_orders_filled_and_valid
        : list OrderRuntimeState (* orders in pre-state *) ->
          list (option uint)     (* argument fills *) ->
          list OrderRuntimeState (* orders in post-state *) ->
          Prop :=
      | UpdateOrdersFilledAndValid_nil:
          update_orders_filled_and_valid nil nil nil

      | UpdateOrdersFilledAndValid_cons:
          forall order orders fill fills order' orders',
            update_order_filled_and_valid order fill order' ->
            update_orders_filled_and_valid orders fills orders' ->
            update_orders_filled_and_valid
              (order :: orders) (fill :: fills) (order' :: orders')
      .

      Definition get_filled_and_check_cancelled_subspec
                 (sender: address)
                 (orders: list Order)
                 (rings: list Ring)
                 (mining: Mining) :=
        {|
          subspec_require :=
            fun wst st =>
              forall fills wst' events,
                batchGetFilledAndCheckCancelled_success wst st fills wst' events ->
                length fills = length (submitter_rt_orders st)
          ;

          subspec_trans :=
            fun wst st wst' st' =>
              forall fills wst'' events,
                batchGetFilledAndCheckCancelled_success wst st fills wst'' events ->
                wst' = wst'' /\
                forall orders',
                  update_orders_filled_and_valid (submitter_rt_orders st) fills orders' ->
                  st' = submitter_update_orders st orders'
          ;

          subspec_events :=
            fun wst st events =>
              forall fills wst' events',
                batchGetFilledAndCheckCancelled_success wst st fills wst' events' ->
                events = events'
          ;
        |}.

    End GetFilledAndCheckCancelled.

    Section CheckOrders.

      Definition is_order_valid (ord: OrderRuntimeState) (now: uint) : bool :=
        let order := ord_rt_order ord in
        (* if order.filledAmountS == 0 then ... *)
        (implb (Nat.eqb (ord_rt_filledAmountS ord) O)
               ((Nat.eqb (order_version order) 0) &&
               (negb (Nat.eqb (order_owner order) 0)) &&
               (negb (Nat.eqb (order_tokenS order) 0)) &&
               (negb (Nat.eqb (order_tokenB order) 0)) &&
               (negb (Nat.eqb (order_amountS order) 0)) &&
               (negb (Nat.eqb (order_feeToken order) 0)) &&
               (Nat.ltb (order_feePercentage order) FEE_PERCENTAGE_BASE_N) &&
               (Nat.ltb (order_tokenSFeePercentage order) FEE_PERCENTAGE_BASE_N) &&
               (Nat.ltb (order_tokenBFeePercentage order) FEE_PERCENTAGE_BASE_N) &&
               (Nat.leb (order_walletSplitPercentage order) 100) &&
               (Nat.leb (order_validSince order) now)
               (* TODO: model signature check *))) &&
        (* common check *)
        (Nat.eqb (order_validUntil order) 0 || Nat.ltb now (order_validUntil order)) &&
        (Z.leb (order_waiveFeePercentage order) FEE_PERCENTAGE_BASE_Z) &&
        (Z.leb (- FEE_PERCENTAGE_BASE_Z) (order_waiveFeePercentage order)) &&
        (Nat.eqb (order_dualAuthAddr order) 0 || Nat.ltb 0 (length (order_dualAuthSig order))) &&
        (ord_rt_valid ord).

      Fixpoint update_orders_valid (orders: list OrderRuntimeState) (now: uint)
        : list OrderRuntimeState :=
        match orders with
        | nil => nil
        | order :: orders' =>
          upd_order_valid order (is_order_valid order now) :: update_orders_valid orders' now
        end.

      Definition is_order_p2p (ord: OrderRuntimeState) : bool :=
        let order := ord_rt_order ord in
        (Nat.ltb 0 (order_tokenSFeePercentage order)) ||
        (Nat.ltb 0 (order_tokenBFeePercentage order)).

      Fixpoint update_orders_p2p (orders: list OrderRuntimeState)
        : list OrderRuntimeState :=
        match orders with
        | nil => nil
        | order :: orders' =>
          upd_order_p2p order (is_order_p2p order) :: update_orders_p2p orders'
        end.

      Definition check_orders_subspec
                 (sender: address)
                 (orders: list Order)
                 (rings: list Ring)
                 (mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\
              let orders' := update_orders_valid
                               (submitter_rt_orders st)
                               (block_timestamp (wst_block_state wst)) in
              let orders' := update_orders_p2p orders' in
              st' = submitter_update_orders st orders';

          subspec_events :=
            fun wst st events =>
              events = nil;
        |}.

    End CheckOrders.

    Section UpdateRingsHashes.

      Fixpoint update_rings_hash
               (rings: list RingRuntimeState) (orders: list OrderRuntimeState)
      : list RingRuntimeState :=
        match rings with
        | nil => nil
        | r :: rings' =>
          upd_ring_hash r (get_ring_hash (ring_rt_static r) orders) ::
          update_rings_hash rings' orders
        end.

      Definition update_rings_hash_subspec
                 (sender: address)
                 (orders: list Order)
                 (rings: list Ring)
                 (mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\
              st' = submitter_update_rings
                      st
                      (update_rings_hash
                         (submitter_rt_rings st) (submitter_rt_orders st));

          subspec_events :=
            fun wst st events => events = nil;
        |}.

    End UpdateRingsHashes.

    Section UpdateMiningHash.

      Definition update_mining_hash
                 (mining: MiningRuntimeState) (rings: list RingRuntimeState)
      : MiningRuntimeState :=
        upd_mining_hash mining (get_mining_hash (mining_rt_static mining) rings).

      Definition update_mining_hash_subspec
                 (sender: address)
                 (orders: list Order)
                 (rings: list Ring)
                 (mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\
              st' = submitter_update_mining
                      st
                      (update_mining_hash
                         (submitter_rt_mining st) (submitter_rt_rings st));

          subspec_events :=
            fun wst st events => events = nil;
        |}.

    End UpdateMiningHash.

    Section UpdateMinerAndInterceptor.

    Definition update_miner_interceptor (st: RingSubmitterRuntimeState) :=
      let mining := submitter_rt_mining st in
      let static_mining := mining_rt_static mining in
      match mining_miner static_mining with
      | O => submitter_update_mining
              st (upd_mining_miner mining (mining_feeRecipient static_mining))
      | _ => st
      end.

      Definition update_miner_interceptor_subspec
                 (sender: address)
                 (_orders: list Order)
                 (_rings: list Ring)
                 (_mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\
              st' = update_miner_interceptor st;

          subspec_events :=
            fun wst st events => events = nil;
        |}.

    End UpdateMinerAndInterceptor.

    Parameter verify_signature: address -> bytes32 -> bytes -> bool.

    Section CheckMinerSignature.

      Inductive miner_signature_valid
                (mining: MiningRuntimeState) (sender: address) : Prop :=
      | MinerSigValid_nosig:
          mining_sig (mining_rt_static mining) = nil ->
          mining_miner (mining_rt_static mining) = sender ->
          miner_signature_valid mining sender

      | MinerSigValid_sig:
          let sig := mining_sig (mining_rt_static mining) in
          sig <> nil ->
          verify_signature (mining_miner (mining_rt_static mining))
                           (mining_rt_hash mining)
                           sig = true ->
          miner_signature_valid mining sender
      .

      Definition check_miner_signature_subspec
                 (sender: address)
                 (_orders: list Order)
                 (_rings: list Ring)
                 (_mining: Mining) :=
        {|
          subspec_require :=
            fun wst st =>
              miner_signature_valid (submitter_rt_mining st) sender;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\ st' = st;

          subspec_events :=
            fun wst st events => events = nil;
        |}.

    End CheckMinerSignature.

    Section CheckOrdersDualSig.

      Inductive check_orders_dual_sig (mining_hash: bytes32)
      : list OrderRuntimeState -> list OrderRuntimeState -> Prop :=
      | CheckOrdersDualSig_nil:
          check_orders_dual_sig mining_hash nil nil

      | CheckOrdersDualSig_cons_valid:
          forall ord orders orders',
            let order := ord_rt_order ord in
            verify_signature (order_dualAuthAddr order)
                             mining_hash
                             (order_dualAuthSig order) = true ->
            check_orders_dual_sig mining_hash orders orders' ->
            check_orders_dual_sig mining_hash (ord :: orders) (ord :: orders')

      | CheckOrdersDualSig_cons_invalid:
          forall ord orders orders',
            let order := ord_rt_order ord in
            verify_signature (order_dualAuthAddr order)
                             mining_hash
                             (order_dualAuthSig order) = false ->
            check_orders_dual_sig mining_hash orders orders' ->
            check_orders_dual_sig
              mining_hash
              (ord :: orders)
              (upd_order_valid ord false :: orders')
      .

      Definition check_orders_dual_sig_subspec
                 (sender: address)
                 (_orders: list Order)
                 (_rings: list Ring)
                 (_mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\
              forall orders',
                check_orders_dual_sig (mining_rt_hash (submitter_rt_mining st))
                                      (submitter_rt_orders st)
                                      orders' ->
                st' = submitter_update_orders st orders';

          subspec_events :=
            fun wst st events => events = nil;
        |}.

    End CheckOrdersDualSig.

    Section CalculateFillsAndFees.

      Definition ring_orders_valid
                 (r: RingRuntimeState) (orders: list OrderRuntimeState) : Prop :=
        ring_rt_valid r = true /\
        let ps := ring_rt_participations r in
        1 < length ps <= 8 /\
        forall p,
          In p ps ->
          let ord_idx := part_order_idx p in
          forall order,
            nth_error orders ord_idx = Some order ->
            ord_rt_valid order = true.

      Definition ring_has_subrings
                 (r: RingRuntimeState) (orders: list OrderRuntimeState) : Prop :=
        exists p p',
          p <> p' /\
          In p (ring_rt_participations r) /\
          In p' (ring_rt_participations r) /\
          forall ord ord',
            nth_error orders (part_order_idx p) = Some ord ->
            nth_error orders (part_order_idx p') = Some ord' ->
            order_tokenS (ord_rt_order ord) = order_tokenS (ord_rt_order ord').

      Parameter ring_init_orders_max_fill_amounts:
        WorldState (* pre world state *) ->
        RingSubmitterRuntimeState (* pre ring submitter state *) ->
        RingRuntimeState (* ring *) ->
        list RingRuntimeState (* rings on the left *) ->
        list RingRuntimeState (* rings on the right *) ->
        WorldState (* post world state *) ->
        RingSubmitterRuntimeState (* post ring submitter state *) ->
        RingRuntimeState (* post ring state *) ->
        list Event ->
        Prop.

      (** Adjust fill amounts of `p` according to fillAmountS of `pp`.
          If `p` is adjust, return an option value of the adjusted `p`.
          Otherwise, return None.
       *)
      Definition adjust_order_fill_amounts_rev
                 (pp p: Participation) (orders: list OrderRuntimeState)
        : option Participation :=
        match (nth_error orders (part_order_idx pp),
               nth_error orders (part_order_idx p)) with
        | (None, _) => None (* impossible case *)
        | (_, None) => None (* impossible case *)
        | (Some pp_ord, Some p_ord) =>
          let pp_tokenSFeePercentage :=
              order_tokenSFeePercentage (ord_rt_order pp_ord) in
          let pp_available_fillAmountS :=
              part_fillAmountS pp * (1 - pp_tokenSFeePercentage/ FEE_PERCENTAGE_BASE_N) in
          if Nat.ltb pp_available_fillAmountS (part_fillAmountB p) then
            let p_order := ord_rt_order p_ord in
            Some (upd_part_fillAmounts
                    p
                    (pp_available_fillAmountS * order_amountS p_order / order_amountB p_order)
                    pp_available_fillAmountS)
          else
            None
        end.

      (* rem_ps starts from the second order of the order ring. *)
      Fixpoint _adjust_orders_fill_amounts_rev_round_1
               (head prev: Participation)
               (readj_ps adj_ps rem_ps: list Participation)
               (orders: list OrderRuntimeState)
        : list Participation * list Participation :=
        match rem_ps with
        | nil =>
          (** have iterated over all orders, adjust the head order accordingly *)
          match adjust_order_fill_amounts_rev prev head orders with
          | None => match readj_ps with
                   | nil => (readj_ps, head :: adj_ps)
                   | _   => (head :: readj_ps, adj_ps)
                   end
          | Some head' => (head :: readj_ps ++ adj_ps, nil)
          end

        | p :: rem_ps' =>
          (** on the half way of iterating the order ring *)
          match adjust_order_fill_amounts_rev prev p orders with
          | None    => _adjust_orders_fill_amounts_rev_round_1
                        head p readj_ps (adj_ps ++ p :: nil) rem_ps' orders
          | Some p' => _adjust_orders_fill_amounts_rev_round_1
                        head p' (readj_ps ++ adj_ps ++ p' :: nil) nil rem_ps' orders
          end
        end.

      (** Adjust the fill amounts of an order ring.

          In the process of adjustment, the order ring is separated
          into three segments:
          1. Adjusted and re-adjustment is required ()
          2. Adjusted and re-adjustment is not required
          3. Have not adjusted yet.

          Return a pair of
          - a list of orders that need to be re-adjusted
          - a list of remaining orders that have been adjusted and do
            not need re-adjustment.
       *)
      Definition adjust_orders_fill_amounts_rev_round_1
                 (ps: list Participation) (orders: list OrderRuntimeState)
        : list Participation * list Participation :=
        match ps with
        | nil => (nil, nil) (* invalid case: empty order ring *)
        | p :: ps' =>
          match ps' with
          | nil => (nil, nil) (* invalid case: single-element order ring *)
          | _ => _adjust_orders_fill_amounts_rev_round_1 p p nil nil ps' orders
          end
        end.

      Fixpoint _adjust_orders_fill_amounts_rev_round_2
               (head prev: Participation)
               (adj_ps pending_ps rem_ps: list Participation)
               (orders: list OrderRuntimeState)
        : list Participation :=
        match pending_ps with
        | nil =>
          (** have iterated over all orders in pending_ps *)
          match rem_ps with
          | nil =>
            (** pending_ps covers the entire order ring *)
            let head' := match adjust_order_fill_amounts_rev prev head orders with
                         | None        => head
                         | Some head'' => head''
                         end
            in head' :: adj_ps ++ rem_ps
          | _ =>
            (** pending_ps covers only the beginning portion of order ring *)
            head :: adj_ps ++ rem_ps
          end

        | p :: pending_ps' =>
          (** on the half way of iterating the pending_ps *)
          let p' := match adjust_order_fill_amounts_rev prev p orders with
                    | None     => p
                    | Some p'' => p''
                    end
          in _adjust_orders_fill_amounts_rev_round_2
               head p' (adj_ps ++ p' :: nil) pending_ps' rem_ps orders
        end.

      Definition adjust_orders_fill_amounts_rev_round_2
                 (readj_ps adj_ps: list Participation)
                 (orders: list OrderRuntimeState)
        : list Participation :=
        match readj_ps with
        | nil => adj_ps
        | p :: readj_ps' =>
          match readj_ps' with
          | nil => nil (* invalid case *)
          | _   => _adjust_orders_fill_amounts_rev_round_2 p p nil readj_ps' adj_ps orders
          end
        end.

      Definition adjust_orders_fill_amounts
                 (ps: list Participation)
                 (orders: list OrderRuntimeState)
        : list Participation :=
        match adjust_orders_fill_amounts_rev_round_1 (rev ps) orders with
        | (readj_ps, adj_ps) =>
          rev (adjust_orders_fill_amounts_rev_round_2 readj_ps adj_ps orders)
        end.

      Fixpoint _reserve_orders_fillAmountS
               (ps: list Participation)
               (orders: list OrderRuntimeState)
               (token_spendables: TokenSpendableMap.t)
               (broker_spendables: BrokerSpendableMap.t)
        : option (TokenSpendableMap.t * BrokerSpendableMap.t) :=
        match ps with
        | nil => Some (token_spendables, broker_spendables)
        | p :: ps' =>
          match nth_error orders (part_order_idx p) with
          | None => None (* invalid case *)
          | Some ord =>
            let reserved := part_fillAmountS p in
            let token_spendables' :=
                token_spendableS_reserved_inc token_spendables ord reserved in
            let broker_spendables' :=
                match ord_rt_brokerInterceptor ord with
                | O => broker_spendables
                | _ => broker_spendableS_reserved_inc broker_spendables ord reserved
                end
            in _reserve_orders_fillAmountS ps' orders token_spendables' broker_spendables'
          end
        end.

      Definition reserve_orders_fillAmounts
                 (st: RingSubmitterRuntimeState) (r: RingRuntimeState)
        : RingSubmitterRuntimeState :=
        match _reserve_orders_fillAmountS (ring_rt_participations r)
                                          (submitter_rt_orders st)
                                          (submitter_rt_token_spendables st)
                                          (submitter_rt_broker_spendables st)
        with
        | None => st
        | Some (token_spendables', broker_spendables') =>
          submitter_update_broker_spendables
            (submitter_update_token_spendables st token_spendables')
            broker_spendables'
        end.

      Definition fee_paid_in_tokenB
                 (p: Participation) (orders: list OrderRuntimeState) : bool :=
        match nth_error orders (part_order_idx p) with
        | None => false (* invalid case *)
        | Some ord =>
          let order := ord_rt_order ord in
          Nat.leb (order_feeAmount order * part_fillAmountS p / order_amountS order)
                  (part_fillAmountB p) &&
          Nat.eqb (order_feeToken order)
                  (order_tokenB order) &&
          Nat.eqb (order_owner order)
                  (order_tokenRecipient order)
        end.

      Parameter order_get_spendableFee: RingSubmitterRuntimeState -> OrderRuntimeState -> uint.

      Definition insufficient_spendable
                 (st: RingSubmitterRuntimeState)
                 (p: Participation)
                 (ord: OrderRuntimeState)
        : bool :=
        let order := ord_rt_order ord in
        Nat.ltb (order_get_spendableFee st ord)
                (order_feeAmount order * part_fillAmountS p / order_amountS order).

      Definition reserve_order_fee
                 (st: RingSubmitterRuntimeState)
                 (ord: OrderRuntimeState)
                 (amount: uint)
        : RingSubmitterRuntimeState :=
        let order := ord_rt_order ord in
        let broker := order_broker order in
        let owner := order_owner order in
        let token := order_feeToken order in
        let token_spendables := submitter_rt_token_spendables st in
        let token_spendables' := token_spendableFee_reserved_inc token_spendables ord amount in
        let broker_spendables := submitter_rt_broker_spendables st in
        let broker_spendables' :=
            match ord_rt_brokerInterceptor ord with
            | O => broker_spendables
            | _ => broker_spendableFee_reserved_inc broker_spendables ord amount
            end
        in submitter_update_broker_spendables
             (submitter_update_token_spendables st token_spendables')
             broker_spendables'
      .

      (** Update feeAmount, feeAmountS, feeAmountB and splitS of `p`
          according to fillAmountB of `pp`. *)
      Definition calculate_fees
                 (st: RingSubmitterRuntimeState)
                 (pp p: Participation)
        : option (RingSubmitterRuntimeState * Participation) :=
        let orders := submitter_rt_orders st in
        match nth_error orders (part_order_idx p) with
        | None => None (* invalid case *)
        | Some ord =>
          let order := ord_rt_order ord in
          let p_fillAmountS := part_fillAmountS p in
          let p_fillAmountB := part_fillAmountB p in
          let pp_fillAmountB := part_fillAmountB pp in
          match ord_rt_p2p ord with
          | true =>
            (** P2P *)
            let p_feeAmountS := p_fillAmountS * order_tokenSFeePercentage order / FEE_PERCENTAGE_BASE_N in
            let p_feeAmountB := p_fillAmountB * order_tokenBFeePercentage order / FEE_PERCENTAGE_BASE_N in
            if Nat.ltb (p_fillAmountS - p_feeAmountS) pp_fillAmountB then
              (** p does not have sufficient token to sell *)
              None
            else
              (** otherwise ... *)
              let p_splitS := p_fillAmountS - p_feeAmountS - pp_fillAmountB in
              Some (st,
                    upd_part_fillAmountS
                      (upd_part_splitS
                         (upd_part_feeAmounts p 0 p_feeAmountS p_feeAmountB)
                         p_splitS)
                      (pp_fillAmountB + p_feeAmountS))

          | false =>
            (** non-P2P *)
            if fee_paid_in_tokenB p orders then
              (** feeToken is tokenB ... *)
              if Nat.ltb p_fillAmountS pp_fillAmountB then
                (** p does not have sufficient token to sell *)
                None
              else
                (** otherwise ... *)
                let p_feeAmountB := order_feeAmount order * p_fillAmountS / (order_amountS order) in
                let p_splitS := p_fillAmountS - pp_fillAmountB in
                Some (st,
                      upd_part_splitS
                        (upd_part_feeAmounts p 0 0 p_feeAmountB)
                        p_splitS)
            else
              (** otherwise ... *)
              if insufficient_spendable st p ord then
                (** p does not sufficient feeToken *)
                if Nat.ltb p_fillAmountS pp_fillAmountB then
                  (** p dose not have sufficient token to sell *)
                  None
                else
                  (** p can pay fee by tokenB *)
                  let p_feeAmountB := p_fillAmountB * order_feePercentage order / FEE_PERCENTAGE_BASE_N in
                  let p_splitS := p_fillAmountS - pp_fillAmountB in
                  Some (st,
                        upd_part_fillAmountS
                          (upd_part_splitS
                             (upd_part_feeAmounts p 0 0 p_feeAmountB)
                             p_splitS)
                          pp_fillAmountB)
              else
                (** p has sufficient feeToken *)
                if Nat.ltb p_fillAmountS p_fillAmountB then
                  (** p does not have sufficient token to sell *)
                  None
                else
                  (** otherwise ... *)
                  let p_feeAmount := p_fillAmountB * order_feePercentage order / FEE_PERCENTAGE_BASE_N in
                  let p_splitS := p_fillAmountS - pp_fillAmountB in
                  Some (reserve_order_fee st ord p_feeAmount,
                        upd_part_fillAmountS
                          (upd_part_splitS
                             (upd_part_feeAmounts p p_feeAmount 0 0)
                             p_splitS)
                          pp_fillAmountB)
          end
        end.

      Definition get_pp (pps ps: list Participation) : option Participation :=
        match ps with
        | nil => None (* invalid case *)
        | p :: ps' =>
          match pps with
          | nil => last_error ps
          | _ => last_error pps
          end
        end.

      Fixpoint _calc_orders_fees_and_waive
               (st: RingSubmitterRuntimeState)
               (r: RingRuntimeState) (lrings rrings: list RingRuntimeState)
               (pps ps: list Participation)
        : option (RingSubmitterRuntimeState * RingRuntimeState) :=
        match ps with
        | nil => Some (st, r)
        | p :: ps' =>
          match get_pp pps ps with
          | None => None (* invalid case *)
          | Some pp =>
            match calculate_fees st pp p with
            | None =>
              (** `p` cannot pay fees *)
              let r' := upd_ring_valid r false in
              Some (submitter_update_rings st (lrings ++ r' :: rrings), r')
            | Some (st', p') =>
              (** `p` can pay fees *)
              let orders := submitter_rt_orders st' in
              match nth_error orders (part_order_idx p') with
              | None => None (* invalid case *)
              | Some ord =>
                let waive := match order_waiveFeePercentage (ord_rt_order ord) with
                             | Z.neg p => Z.abs_nat (Z.pos p)
                             | _ => 0
                             end
                in
                let pps' := pps ++ p' :: nil in
                let r' := inc_ring_minerFeesToOrdersPercentage
                            (upd_ring_participations r (pps' ++ ps')) waive in
                let st'' := submitter_update_rings st' (lrings ++ r' :: rrings) in
                _calc_orders_fees_and_waive st'' r' lrings rrings pps' ps'
              end
            end
          end
        end.

      Fixpoint calc_orders_fees_and_waive
               (st: RingSubmitterRuntimeState)
               (r: RingRuntimeState) (lrings rrings: list RingRuntimeState)
        : option (RingSubmitterRuntimeState * RingRuntimeState) :=
        match _calc_orders_fees_and_waive st r lrings rrings nil (ring_rt_participations r) with
        | None => None
        | Some (st', r') =>
          if Nat.ltb FEE_PERCENTAGE_BASE_N
                     (ring_minerFeesToOrdersPercentage (ring_rt_static r')) then
            let r'' := upd_ring_valid r' false in
            Some (submitter_update_rings st' (lrings ++ r'' :: rrings), r'')
          else
            Some (st', r')
        end.

      Fixpoint clear_orders_reservations
               (st: RingSubmitterRuntimeState) (ps: list Participation)
        : option RingSubmitterRuntimeState :=
        match ps with
        | nil => Some st
        | p :: ps' =>
          match nth_error (submitter_rt_orders st) (part_order_idx p) with
          | None => None (* invalid case *)
          | Some ord => clear_orders_reservations (clear_order_spendables_reserved st ord) ps'
          end
        end.

      Definition calculate_fill_amount_and_fee
                 (wst: WorldState)
                 (st: RingSubmitterRuntimeState)
                 (r: RingRuntimeState)
                 (lrings rrings: list RingRuntimeState)
                 (wst': WorldState)
                 (st': RingSubmitterRuntimeState)
                 (r': RingRuntimeState)
                 (events: list Event) : Prop :=
        forall wst1 st1 r1 events1
          wst2 st2 r2 events2
          wst3 st3 r3 events3
          wst4 st4 r4 events4
          wst5 st5 r5 events5,
          (* init *)
          ring_init_orders_max_fill_amounts wst st r lrings rrings wst1 st1 r1 events1 ->
          (* adjust fill amounts *)
          r2 = upd_ring_participations
                   r1
                   (adjust_orders_fill_amounts (ring_rt_participations r1)
                                               (submitter_rt_orders st1)) ->
          st2 = submitter_update_rings st1 (lrings ++ r2 :: rrings) ->
          wst2 = wst1 ->
          events2 = nil ->
          (* reserve fill amountS *)
          st3 = reserve_orders_fillAmounts st2 r2 ->
          r3 = r2 ->
          wst3 = wst2 ->
          events3 = nil ->
          (* calc fees and waive *)
          calc_orders_fees_and_waive st3 r3 lrings rrings = Some (st4, r4) ->
          wst4 = wst3 ->
          events4 = nil ->
          (* clear reservations *)
          clear_orders_reservations st4 (ring_rt_participations r4) = Some st5 ->
          r5 = r4 ->
          wst5 = wst4 ->
          events5 = nil ->
          (* final *)
          wst' = wst5 /\ st' = st5 /\ r' = r5 /\ events = events1 ++ events2 ++ events3 ++ events4 ++ events5.

      Definition adjust_order_state
                 (p: Participation)
                 (ord: OrderRuntimeState)
                 (token_spendables: TokenSpendableMap.t)
                 (broker_spendables: BrokerSpendableMap.t)
        : OrderRuntimeState * TokenSpendableMap.t * BrokerSpendableMap.t :=
        let filled_amount := part_fillAmountS p + part_splitS p in
        let fee_amount := part_feeAmount p in
        let ord' := upd_order_filled ord filled_amount in
        let token_spendables' :=
            token_spendableFee_amount_dec
              (token_spendableS_amount_dec token_spendables ord filled_amount)
              ord fee_amount in
        let broker_spendables' :=
            match ord_rt_brokerInterceptor ord with
            | O => broker_spendables
            | _ =>
              broker_spendableFee_amount_dec
                (broker_spendableS_amount_dec broker_spendables ord filled_amount)
                ord fee_amount
            end
        in (ord', token_spendables, broker_spendables).

      Fixpoint _adjust_orders_state
               (ps: list Participation)
               (orders: list OrderRuntimeState)
               (token_spendables: TokenSpendableMap.t)
               (broker_spendables: BrokerSpendableMap.t)
        : option (list OrderRuntimeState * TokenSpendableMap.t * BrokerSpendableMap.t) :=
        match ps with
        | nil => Some (orders, token_spendables, broker_spendables)
        | p :: ps' =>
          let ord_idx := part_order_idx p in
          match nth_error orders ord_idx with
          | None => None (* invalid case *)
          | Some ord =>
            match adjust_order_state p ord token_spendables broker_spendables with
            | (ord', token_spendables', broker_spendables') =>
              match alt_nth orders ord_idx ord' with
              | None => None (* invalid case *)
              | Some orders' => _adjust_orders_state
                                 ps' orders' token_spendables' broker_spendables'
              end
            end
          end
        end.

      Definition adjust_orders_state
                 (st: RingSubmitterRuntimeState) (r: RingRuntimeState)
        : option RingSubmitterRuntimeState :=
        match _adjust_orders_state
                (ring_rt_participations r)
                (submitter_rt_orders st)
                (submitter_rt_token_spendables st)
                (submitter_rt_broker_spendables st) with
        | None => None (* invalid case *)
        | Some (orders', token_spendables', broker_spendables') =>
          Some (submitter_update_broker_spendables
                  (submitter_update_token_spendables
                     (submitter_update_orders st orders')
                     token_spendables')
                  broker_spendables')
        end.

      Inductive _rings_check_and_calc_fills_fees
                (wst: WorldState)
                (st: RingSubmitterRuntimeState)
        : list RingRuntimeState (* rings that have been checked and updated *) ->
          list RingRuntimeState (* rings that have not been checked and updated *) ->
          WorldState (* post world state *) ->
          RingSubmitterRuntimeState (* post ring submitter state *) ->
          list Event ->
          Prop :=
      | RingsCheckAndCalcFillsFees_nil:
          _rings_check_and_calc_fills_fees wst st (submitter_rt_rings st) nil wst st nil

      | RingsCheckAndCalcFillsFees_valid_cons:
          forall lrings r rrings wst' st' r' events st'' wst''' st''' events',
            submitter_rt_rings st = lrings ++ r :: rrings ->
            ring_orders_valid r (submitter_rt_orders st) ->
            ~ ring_has_subrings r (submitter_rt_orders st) ->
            calculate_fill_amount_and_fee wst st r lrings rrings wst' st' r' events ->
            adjust_orders_state st' r' = Some st'' ->
            _rings_check_and_calc_fills_fees wst' st'' (lrings ++ r' :: nil) rrings wst''' st''' events' ->
            _rings_check_and_calc_fills_fees wst st lrings (r :: rrings) wst''' st''' (events ++ events')

      | RingsCheckAndCalcFillsFees_invalid_cons:
          forall lrings r rrings r' wst'' st'' events,
            submitter_rt_rings st = lrings ++ r :: rrings ->
            (~ ring_orders_valid r (submitter_rt_orders st) \/ ring_has_subrings r (submitter_rt_orders st)) ->
            r' = upd_ring_valid r false ->
            _rings_check_and_calc_fills_fees
              wst (submitter_update_rings st (lrings ++ r' :: rrings))
              (lrings ++ r' :: nil) rrings wst'' st'' events ->
            _rings_check_and_calc_fills_fees wst st lrings (r :: rrings) wst'' st'' events
      .

      Definition calc_fills_and_fees_subspec
                 (sender: address)
                 (_orders: list Order)
                 (_rings: list Ring)
                 (_mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              forall wst'' st'' events,
                _rings_check_and_calc_fills_fees
                  wst st nil (submitter_rt_rings st) wst'' st'' events ->
                wst' = wst'' /\ st' = st''
          ;

          subspec_events :=
            fun wst st events =>
              forall wst'' st'' events',
                _rings_check_and_calc_fills_fees
                  wst st nil (submitter_rt_rings st) wst'' st'' events ->
                events = events'
          ;
        |}.

    End CalculateFillsAndFees.

    Section ValidateAllOrNone.

      Fixpoint validate_AllOrNone (orders: list OrderRuntimeState)
      : list OrderRuntimeState :=
        match orders with
        | nil => nil
        | ord :: orders' =>
          let order := ord_rt_order ord in
          let ord' := match order_allOrNone order with
                      | true => if Nat.eqb (ord_rt_filledAmountS ord)
                                          (order_amountS (ord_rt_order ord)) then
                                 ord
                               else
                                 upd_order_valid ord false
                      | false => ord
                      end
          in ord' :: validate_AllOrNone orders'
        end.

      Definition validate_AllOrNone_subspec
                 (sender: address)
                 (_orders: list Order)
                 (_rings: list Ring)
                 (_mining: Mining) :=
        {|
          subspec_require :=
            fun wst st => True;

          subspec_trans :=
            fun wst st wst' st' =>
              wst' = wst /\
              st' = submitter_update_orders
                      st (validate_AllOrNone (submitter_rt_orders st));

          subspec_events :=
            fun wst st events => events = nil;
        |}.

    End ValidateAllOrNone.

    Definition SubmitRingsSubSpec :=
      address -> list Order -> list Ring -> Mining -> SubSpec.

    Definition submit_rings_subspec_seq (_spec _spec': SubmitRingsSubSpec) : SubmitRingsSubSpec :=
      fun sender orders rings mining =>
        let spec := _spec sender orders rings mining in
        let spec' := _spec' sender orders rings mining in
        {|
          subspec_require :=
            fun wst st =>
              subspec_require spec wst st /\
              forall wst' st',
                subspec_trans spec wst st wst' st' ->
                subspec_require spec' wst' st';

          subspec_trans :=
            fun wst st wst' st' =>
              forall wst'' st'',
                subspec_trans spec wst st wst'' st'' /\
                subspec_trans spec' wst'' st'' wst' st';

          subspec_events :=
            fun wst st events =>
              forall wst' st' events' events'',
                subspec_trans spec wst st wst' st' ->
                subspec_events spec wst st events' ->
                subspec_events spec' wst' st' events'' ->
                events = events' ++ events'';
        |}.
    Notation "s ;; s'" := (submit_rings_subspec_seq s s') (left associativity, at level 400).

    Definition submit_rings_subspec_to_fspec
               (subspec: SubmitRingsSubSpec)
               (sender: address) (orders: list Order) (rings: list Ring) (mining: Mining)
      : FSpec :=
      let spec := subspec sender orders rings mining in
      let st := make_rt_submitter_state mining orders rings in
      {|
        fspec_require :=
          fun wst => subspec_require spec wst st;

        fspec_trans :=
          fun wst wst' retval =>
            retval = RetNone /\
            forall wst'' st'',
              subspec_trans spec wst st wst'' st'' ->
              wst' = wst'';

        fspec_events :=
          fun wst events =>
              subspec_events spec wst st events;
      |}.

    Definition submitRings_spec
               (sender: address)
               (orders: list Order) (rings: list Ring) (mining: Mining) :=
      submit_rings_subspec_to_fspec
        (
           update_orders_hashes_subspec ;;
           update_orders_brokers_and_interceptors ;;
           get_filled_and_check_cancelled_subspec ;;
           check_orders_subspec ;;
           update_rings_hash_subspec ;;
           update_mining_hash_subspec ;;
           update_miner_interceptor_subspec ;;
           check_miner_signature_subspec ;;
           check_orders_dual_sig_subspec ;;
           calc_fills_and_fees_subspec ;;
           validate_AllOrNone_subspec
        )
        sender orders rings mining.

  End SubmitRings.

  Definition get_spec (msg: RingSubmitterMsg) : FSpec :=
    match msg with
    | msg_submitRings sender orders rings mining =>
      submitRings_spec sender orders rings mining
    end.

  Definition model
             (wst: WorldState)
             (msg: RingSubmitterMsg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec msg) wst wst' retval events.

End RingSubmitter.
