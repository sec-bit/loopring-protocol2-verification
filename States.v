Require Import
        List.
Require Import
        Maps
        Types.

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

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
  Admitted.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
  Admitted.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
  Admitted.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
  Admitted.
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
  Admitted.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
  Admitted.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
  Admitted.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
  Admitted.
End BrokerElem.

Module Brokers := Mapping Address_as_DT BrokerElem.

Module BrokersElem <: ElemType.
  Definition elt := Brokers.t.
  Definition elt_zero := Brokers.empty.
  Definition elt_eq := fun m m': elt => Brokers.map.Equal m m'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
  Admitted.

  Lemma elt_eq_refl:
    forall x, elt_eq x x.
  Proof.
  Admitted.

  Lemma elt_eq_symm:
    forall x y, elt_eq x y -> elt_eq y x.
  Proof.
  Admitted.

  Lemma elt_eq_trans:
    forall x y, elt_eq x y -> forall z, elt_eq y z -> elt_eq x z.
  Proof.
  Admitted.
End BrokersElem.

Module BrokersMap := Mapping Address_as_DT BrokersElem.

Record BrokerRegistryState : Type :=
  mk_broker_registry_state {
      (* We model BrokerRegistry::brokersMap approximatively by a map
        address -> address -> Broker *)
      broker_registry_brokersMap : BrokersMap.t;
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
    wst_block_state := wst_block_state wst;
  |}.