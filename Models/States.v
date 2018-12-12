Require Import
        List
        ZArith.
Require Import
        Maps
        Types.

Require Logic.ProofIrrelevance.

(** State of ERC20 token contract *)
Record ERC20State : Type :=
  mk_erc20_state {
      erc20_balances: A2V.t;
      erc20_allowed: AA2V.t;
    }.

Module ERC20StateElem <: ElemType.
  Definition elt : Type := ERC20State.
  Definition elt_zero :=
    {| erc20_balances := A2V.empty; erc20_allowed := AA2V.empty |}.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma aa2v_slist_eq_dec (elt: Type) (elt_dec: forall x y: elt, {x = y} + {x <> y}) :
    forall sl1 sl2 : AA2V.map.slist elt, {sl1 = sl2} + {sl1 <> sl2}.
  Proof.
    destruct sl1 as [l1 nodup1], sl2 as [l2 nodup2].
    assert (forall x y : nat * nat * elt, {x = y} + {x <> y}) as H_dec'.
    { repeat decide equality. }
    destruct (list_eq_dec H_dec' l1 l2).
    left. subst. f_equal. apply ProofIrrelevance.proof_irrelevance.
    right. intro. apply n. inversion H; auto.
  Qed.

  Lemma a2v_slist_eq_dec (elt: Type) (elt_dec: forall x y: elt, {x = y} + {x <> y}) :
    forall sl1 sl2 : A2V.map.slist elt, {sl1 = sl2} + {sl1 <> sl2}.
  Proof.
    destruct sl1 as [l1 nodup1], sl2 as [l2 nodup2].
    assert (forall x y : nat * elt, {x = y} + {x <> y}) as H_dec'.
    { repeat decide equality. }
    destruct (list_eq_dec H_dec' l1 l2).
    left. subst. f_equal. apply ProofIrrelevance.proof_irrelevance.
    right. intro. apply n. inversion H; auto.
  Qed.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
    decide equality.
    eapply aa2v_slist_eq_dec. decide equality.
    eapply a2v_slist_eq_dec. decide equality.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    constructor.
  Qed.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
    inversion 1. constructor.
  Qed.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
    inversion 1; inversion 1; constructor.
  Qed.
End ERC20StateElem.

Module ERC20StateMap := Mapping (Address_as_DT) ERC20StateElem.


(** State of RingSubmitter contract *)
Record RingSubmitterState : Type :=
  mk_ring_submitter_state {
      submitter_lrcTokenAddress: address;
      submitter_wethTokenAddress: address;
      submitter_delegateAddress: address;
      submitter_orderBrokerRegistryAddress: address;
      submitter_orderRegistryAddress: address;
      submitter_feeHolderAddress: address;
      submitter_orderBookAddress: address;
      submitter_burnRateTableAddress: address;
      submitter_ringIndex: uint64;
    }.


(** State of RingCanceller contract *)
Record RingCancellerState : Type :=
  mk_ring_canceller_state {
      canceller_delegateAddress: address;
    }.


(** State of TradeDelegate contract *)
Record TradeDelegateState : Type :=
  mk_trade_delegate_state {
      delegate_owner: address;
      delegate_suspended: bool;
      delegate_authorizedAddresses: A2B.t;
      delegate_filled: H2V.t;
      delegate_cancelled: AH2B.t;
      delegate_cutoffs: A2V.t;
      delegate_tradingPairCutoffs: AH2V.t;
      delegate_cutoffsOwner: AA2V.t;
      delegate_tradingPairCutoffsOwner: AAH2V.t;
    }.


(** State of FeeHolder contract *)
Record FeeHolderState : Type :=
  mk_fee_holder_state {
      feeholder_delegateAddress: address;
      feeholder_feeBalances: AA2V.t;
    }.


(** State of BrokerRegistry *)
Record Broker : Type :=
  mk_broker {
      broker_owner: address;
      broker_addr: address;
      broker_interceptor: address;
    }.

Module BrokerElem <: ElemType.
  Definition elt := Broker.
  Definition elt_zero : elt :=
    {| broker_owner := 0; broker_addr := 0; broker_interceptor := 0 |}.
  Definition elt_eq := fun b b': elt => b = b'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
    decide equality; decide equality.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    constructor.
  Qed.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
    inversion 1; constructor.
  Qed.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
    inversion 1; inversion 1; constructor.
  Qed.
End BrokerElem.

Module Brokers := Mapping Address_as_DT BrokerElem.

Module BrokersElem <: ElemType.
  Definition elt := Brokers.t.
  Definition elt_zero := Brokers.empty.
  Definition elt_eq := fun m m': elt => Brokers.map.Equal m m'.

  Lemma slist_eq_dec (elt: Type) (elt_dec: forall x y: elt, {x = y} + {x <> y}) :
    forall sl1 sl2 : Brokers.map.slist elt, {sl1 = sl2} + {sl1 <> sl2}.
  Proof.
    destruct sl1 as [l1 nodup1], sl2 as [l2 nodup2].
    assert (forall x y : nat * elt, {x = y} + {x <> y}) as H_dec'.
    { repeat decide equality. }
    destruct (list_eq_dec H_dec' l1 l2).
    left. subst. f_equal. apply ProofIrrelevance.proof_irrelevance.
    right. intro. apply n. inversion H; auto.
  Qed.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
    apply slist_eq_dec. auto using BrokerElem.elt_eq_dec.
  Qed.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
    constructor.
  Qed.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
    intros x y H k. rewrite H; auto.
  Qed.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
    intros x y H1 z H2 k. rewrite H1, H2. auto.
  Qed.
End BrokersElem.

Module BrokersMap := Mapping Address_as_DT BrokersElem.

Record BrokerRegistryState : Type :=
  mk_broker_registry_state {
      (* We model BrokerRegistry::brokersMap approximatively by a map
        address -> address -> Broker *)
      broker_registry_brokersMap : BrokersMap.t;
    }.


(** * BurnRateTable state *)
(** Token data map *)
Record TokenData : Type :=
  mk_token_data {
      tier: uint;
      validUntil: uint;
    }.

Module TokenDataElem <: ElemType.
  Definition elt : Type := TokenData.
  Definition elt_zero : elt := mk_token_data 0 0.
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

End TokenDataElem.

Module TokenDataMap := Mapping Address_as_DT TokenDataElem.

(** BurnRateTable state *)
Record BurnRateTableState : Type :=
  mk_burn_rate_table_state {
    burnratetable_tokens: TokenDataMap.t;
    (* balances not implemented *)
    }.


(** State of order registry *)
Record OrderRegistryState : Type :=
  mk_order_registry_state {
      order_registry_hashMap: AH2B.t;
    }.


(** State of the block *)
Record BlockState : Type :=
  mk_block_state {
      block_timestamp: uint;
    }.


(** State of burn manager *)
Record BurnManagerState : Type :=
  {
    burnMgr_feeHolderAddress : address;
    burnMgr_lrcAddress : address;
  }.


(** State of order book *)
Module OrderElem <: ElemType.

  Definition elt: Type := Order.
  Definition elt_zero: elt :=
    {|
      order_version               := 0;
      order_owner                 := 0;
      order_tokenS                := 0;
      order_tokenB                := 0;
      order_amountS               := 0;
      order_amountB               := 0;
      order_validSince            := 0;
      order_tokenSpendableS       := mk_spendable false 0 0;
      order_tokenSpendableFee     := mk_spendable false 0 0;
      order_dualAuthAddr          := 0;
      order_broker                := 0;
      order_brokerSpendableS      := mk_spendable false 0 0;
      order_brokerSpendableFee    := mk_spendable false 0 0;
      order_orderInterceptor      := 0;
      order_wallet                := 0;
      order_validUntil            := 0;
      order_sig                   := nil;
      order_dualAuthSig           := nil;
      order_allOrNone             := false;
      order_feeToken              := 0;
      order_feeAmount             := 0;
      order_feePercentage         := 0;
      order_waiveFeePercentage    := 0%Z;
      order_tokenSFeePercentage   := 0;
      order_tokenBFeePercentage   := 0;
      order_tokenRecipient        := 0;
      order_walletSplitPercentage := 0;
    |}.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof. repeat decide equality. Qed.

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

End OrderElem.

Module H2O := Mapping (Hash_as_DT) OrderElem.

Record OrderBookState : Type :=
  {
    (* model both orderSubmitted and orders by a single map *)
    ob_orders         : H2O.t;
  }.


(** World state modeling all parties of Loopring protocol *)
Record WorldState : Type :=
  mk_world_state {
      (* ERC20 token contracts called from LPSC *)
      wst_erc20s: ERC20StateMap.t;

      (* LPSC ring submitter contract *)
      wst_ring_submitter_state: RingSubmitterState;
      wst_ring_submitter_addr: address;
      (* LPSC ring canceller contract *)
      wst_ring_canceller_state: RingCancellerState;
      wst_ring_canceller_addr: address;
      (* LPSC trade delegate contract *)
      wst_trade_delegate_state: TradeDelegateState;
      wst_trade_delegate_addr: address;
      (* LPSC fee holder contract *)
      wst_feeholder_state: FeeHolderState;
      wst_feeholder_addr: address;
      (* LPSC broker registry contract *)
      wst_broker_registry_state: BrokerRegistryState;
      wst_broker_registry_addr: address;
      (* LPSC order registry contract *)
      wst_order_registry_state: OrderRegistryState;
      wst_order_registry_addr: address;
      (* LPSC burn rate table contract *)
      wst_burn_rate_table_state: BurnRateTableState;
      wst_burn_rate_table_addr: address;
      (* LPSC burn manager contract *)
      wst_burn_manager_state: BurnManagerState;
      wst_burn_manager_addr: address;
      (* LPSC order book contract *)
      wst_order_book_state: OrderBookState;
      wst_order_book_addr: address;

      (* state of the current block *)
      wst_block_state: BlockState;

      (* TODO: add states of other LPSC contracts and ... *)
    }.

Definition wst_update_trade_delegate
           (wst: WorldState) (st: TradeDelegateState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := st;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.

Definition wst_update_feeholder
           (wst: WorldState) (st: FeeHolderState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := st;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.


Definition wst_update_erc20s
           (wst: WorldState) (st: ERC20StateMap.t)
  : WorldState :=
  {|
    wst_erc20s := st;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.

Definition wst_update_broker_registry
           (wst: WorldState) (st: BrokerRegistryState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := st;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.

Definition wst_update_order_registry
           (wst: WorldState) (st: OrderRegistryState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := st;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.

Definition wst_update_ring_submitter
           (wst: WorldState) (st: RingSubmitterState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := st;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.

Definition wst_update_burn_rate_table
           (wst: WorldState) (st: BurnRateTableState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := st;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.

Definition wst_update_burn_manager
           (wst: WorldState) (st: BurnManagerState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := st;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := wst_order_book_state wst;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.

Definition wst_update_order_book
           (wst: WorldState) (st: OrderBookState)
  : WorldState :=
  {|
    wst_erc20s := wst_erc20s wst;
    wst_ring_submitter_state := wst_ring_submitter_state wst;
    wst_ring_submitter_addr := wst_ring_submitter_addr wst;
    wst_ring_canceller_state := wst_ring_canceller_state wst;
    wst_ring_canceller_addr := wst_ring_canceller_addr wst;
    wst_trade_delegate_state := wst_trade_delegate_state wst;
    wst_trade_delegate_addr := wst_trade_delegate_addr wst;
    wst_feeholder_state := wst_feeholder_state wst;
    wst_feeholder_addr := wst_feeholder_addr wst;
    wst_broker_registry_state := wst_broker_registry_state wst;
    wst_broker_registry_addr := wst_broker_registry_addr wst;
    wst_order_registry_state := wst_order_registry_state wst;
    wst_order_registry_addr := wst_order_registry_addr wst;
    wst_burn_rate_table_state := wst_burn_rate_table_state wst;
    wst_burn_rate_table_addr := wst_burn_rate_table_addr wst;
    wst_burn_manager_state := wst_burn_manager_state wst;
    wst_burn_manager_addr := wst_burn_manager_addr wst;
    wst_order_book_state := st;
    wst_order_book_addr := wst_order_book_addr wst;
    wst_block_state := wst_block_state wst;
  |}.
