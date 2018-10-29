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
      owner                 : address;
      tokenS                : address;
      tokenB                : address;
      amountS               : uint;
      amountB               : uint;
      validSince            : uint;
      tokenSpendableS       : Spendable;
      tokenSpendableFee     : Spendable;
      (** optional fields *)
      dualAuthAddr          : address;
      broker                : address;
      brokerSpendableS      : Spendable;
      brokerSpendableFee    : Spendable;
      orderInterceptor      : address;
      wallet                : address;
      validUntil            : uint;
      sig                   : bytes;
      dualAuthSig           : bytes;
      allOrNone             : bool;
      feeToken              : address;
      feeAmount             : uint;
      feePercentage         : uint16;    (** Post-trading *)
      waiveFeePercentage    : int16;
      tokenSFeePercentage   : uint16;    (** Pre-trading *)
      tokenBFeePercentage   : uint16;    (** Post-trading *)
      tokenRecipient        : address;
      walletSplitPercentage : uint16;
    }.


(** Ring *)
Record Ring : Type :=
  mk_ring {
      (* order positions in another order list *)
      orders: list nat;
    }.
