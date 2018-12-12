Require Import
        Nat ZArith.

(** Basic types used in the model *)

Definition address : Type := nat.
Definition uint : Type := nat.
Definition uint16 : Type := nat.
Definition uint64 : Type := nat.
Definition uint256 : Type := nat.
Definition int16 : Type := Z.
Definition byte : Type := nat.
Definition bytes20 : Type := nat.
Definition bytes32 : Type := nat.
Definition bytes : Type := list byte.
Definition value : Type := nat.


(** Model integer overflow/underflow *)
Parameter MAX_UINT256 : uint256.

Definition plus_with_overflow (lhs: value) (rhs: value) :=
  if (Nat.ltb (MAX_UINT256 - rhs) lhs)
  then (if (Nat.eqb rhs 0)
        then lhs
         else (lhs + rhs - MAX_UINT256 - 1))
  else (lhs + rhs).

Definition minus_with_underflow (lhs: value) (rhs: value) :=
  if (Nat.ltb lhs rhs) then (lhs + MAX_UINT256 + 1 - rhs) else (lhs - rhs).

Lemma plus_safe_lt : forall (x: value) (y: value),
    x <= MAX_UINT256 - y -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  rewrite Nat.ltb_antisym.
  rewrite (proj2 (Nat.leb_le _ _) H).
  reflexivity.
Qed.

Lemma plus_safe_lhs0 : forall (x: value) (y: value),
    x = 0 -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  subst.
  reflexivity.
Qed.

Lemma plus_safe_rhs0 : forall (x: value) (y: value),
    y = 0 -> plus_with_overflow x y = x + y.
Proof.
  intros.
  unfold plus_with_overflow.
  subst. simpl.
  rewrite Nat.add_0_r.
  destruct (MAX_UINT256 - 0 <? x); reflexivity.
Qed.

Lemma minus_safe : forall (x: value) (y: value),
    x >= y -> minus_with_underflow x y = x - y.
Proof.
  intros.
  unfold minus_with_underflow.
  rewrite Nat.ltb_antisym.
  rewrite (proj2 (Nat.leb_le _ _) H).
  reflexivity.
Qed.

Lemma minus_plus_safe: forall (x y : value),
    x <= MAX_UINT256 -> x >= y -> plus_with_overflow (minus_with_underflow x y) y = x.
Proof.
  intros x y Hhi Hlo.
  rewrite (minus_safe _ _ Hlo).
  assert (y <= x). auto with arith.
  assert (x - y <= MAX_UINT256 - y). omega.
  rewrite (plus_safe_lt _ _ H0).
  omega.
Qed.


(** Key pair *)

Parameter Key: Type. (* to be defined *)

Record KeyPair : Type :=
  mk_key_pair {
      pubkey: Key;
      privKey: Key;
    }.


(** Mining Parameters *)
Record Mining: Type :=
  mk_mining {
      mining_feeRecipient: address;
      mining_miner: address;
      mining_sig: bytes;
      (* computed fields are not modeled here *)
    }.


(** Spendable *)
Record Spendable : Type :=
  mk_spendable {
      spendable_initialized: bool;
      spendable_amount: uint;
      spendable_reserved: uint;
    }.


(** Order *)
(* only model non-computed fields *)
Record Order : Type :=
  mk_order {
      order_version               : uint;
      order_owner                 : address;
      order_tokenS                : address;
      order_tokenB                : address;
      order_amountS               : uint;
      order_amountB               : uint;
      order_validSince            : uint;
      order_tokenSpendableS       : Spendable;
      order_tokenSpendableFee     : Spendable;
      (** optional fields *)
      order_dualAuthAddr          : address;
      order_broker                : address; (* mutated in updateBrokerAndInterceptor() *)
      order_brokerSpendableS      : Spendable;  (* cleared by updateBrokerSpendables() *)
      order_brokerSpendableFee    : Spendable;  (* cleared by updateBrokerSpendables() *)
      order_orderInterceptor      : address; (* mutated in updateBrokerAndinterceptor() *)
      order_wallet                : address;
      order_validUntil            : uint;
      order_sig                   : bytes;
      order_dualAuthSig           : bytes;
      order_allOrNone             : bool;
      order_feeToken              : address;
      order_feeAmount             : uint;
      order_feePercentage         : uint16;    (** Post-trading *)
      order_waiveFeePercentage    : int16;
      order_tokenSFeePercentage   : uint16;    (** Pre-trading *)
      order_tokenBFeePercentage   : uint16;    (** Post-trading *)
      order_tokenRecipient        : address;
      order_walletSplitPercentage : uint16;
    }.

Parameters get_order_hash: Order -> bytes32.

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

(** Ring *)
Record Ring : Type :=
  mk_ring {
      (* order positions in another order list *)
      ring_orders: list nat;
      ring_minerFeesToOrdersPercentage: uint;
    }.

Definition ring_add_minerFeesToOrdersPercentage (r: Ring) (amount: uint) : Ring :=
  {|
    ring_orders := ring_orders r;
    ring_minerFeesToOrdersPercentage := ring_minerFeesToOrdersPercentage r + amount;
  |}.

Notation FEE_PERCENTAGE_BASE_N := (1000%nat).
Notation FEE_PERCENTAGE_BASE_Z := (1000%Z).