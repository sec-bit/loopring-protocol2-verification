Require Import
        Nat ZArith.

(** Basic types used in the model *)

Definition address : Type := nat.
Definition uint : Type := nat.
Definition uint16 : Type := nat.
Definition uint64 : Type := nat.
Definition uint256 : Type := nat.
Definition int16 : Type := nat.
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
      initialized: bool;
      amount: uint;
      reserved: uint;
    }.


(** Order *)
(* only model non-computed fields *)
Record Order : Type :=
  mk_order {
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
      order_broker                : address;
      order_brokerSpendableS      : Spendable;
      order_brokerSpendableFee    : Spendable;
      order_orderInterceptor      : address;
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


(** Ring *)
Record Ring : Type :=
  mk_ring {
      (* order positions in another order list *)
      ring_orders: list nat;
      ring_minerFeesToOrdersPercentage: uint;
    }.
