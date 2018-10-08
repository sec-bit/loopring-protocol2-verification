(** *********************************** *)
(**                                     *)
(**    Loopring Smart Contract Model    *)
(**                                     *)
(**            Version 0.01             *)
(**                                     *)
(** *********************************** *)

Require Import
        List
        QArith.

Open Scope Q_scope.

Set Implicit Arguments.

Class LTS : Type :=
  {
    state : Type;
    label : Type;
    initState : state;
    transition : state -> label -> state -> Prop;
  }.

(** * States *)
(** *)
Parameter LPSCState : Type.
Parameter initLPSCState : LPSCState.



(** Basic data types *)
Parameter address : Type.
Parameter uint : Type.
Parameter uint16 : Type.
Parameter uint64 : Type.
Parameter int16 : Type.
Parameter byte : Type.
Parameter bytes32 : Type.
Definition bytes : Type := list byte.

(** * Inputs *)
Module Contxt.
  Record t : Type :=
    {
      lrcTokenAddress       : address;
      (** These fields are set on contract construction *)
      (*
      delegate              : ITradeDelegate;
      orderBrokerRegistry   : IBrokerRegistry;
      orderRegistry         : IOrderRegistry;
      feeHolder             : IFeeHolder;
      orderBook             : IOrderBook;
      burnRateTable         : IBurnRateTable;
       *)
      (** highest bit serves as a lock to prevent reentrence *)
      (** TODO: lower bits not known *)
      ringIndex             : uint64;
      feePercentageBase     : uint;
      (** tokenBurnRates is computed from orders/rings *)
      tokenBurnRates        : list bytes32;
      feeData               : uint;
      feePtr                : uint;
      transferData          : uint;
      transferPtr           : uint;
    }.
  
End Contxt.


(** Mining ? *)
Module Mining.
  Record t : Type :=
    {
      feeRecipient          : address;
      (** optional fields *)
      miner                 : address;
      sig                   : bytes;
      (** computed fields *)
      hash                  : bytes32;
      interceptor           : address;
    }.
End Mining.

(** Orders *)
Module Spendable.
  Record t : Type :=
    {
      initialized : bool;
      amount : uint;
      reserved : uint;
    }.
End Spendable.

Module Order.
  Record t : Type := 
    {
      owner                 : address;
      tokenS                : address;
      tokenB                : address;
      amountS               : uint;
      amountB               : uint;
      validSince            : uint;
      tokenSpendableS       : Spendable.t;
      tokenSpendableFee     : Spendable.t;
      (** optional fields *)
      dualAuthAddr          : address;
      broker                : address;
      brokerSpendableS      : Spendable.t;
      brokerSpendableFee    : Spendable.t;
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
      (** computed fields *)
      (** TODO: are the computed fields computable from fields above? *)
      (** No, some of the computations rely on LPSC state *)
      (*
      P2P                   : bool;
      hash                  : bytes32;
      brokerInterceptor     : address;
      filledAmountS         : uint;
      valid                 : bool;
       *)
    }.

  
  Section OrderProperties.
    
    Variable s : LPSCState.
    
    Parameter P2P : t -> bool.
    Parameter hash : t -> bytes32.
    Parameter brokerInterceptor : t -> address.
    Parameter filledAmountS : t -> uint.
    Parameter valid : t -> bool.
    
  End OrderProperties.
  
End Order.

(** Rings *)
Parameter Ring : Type.

Parameter Inputs : Type.

(** * Effects/Events *)
(** Check validity *)
(** Emit Ring mined / Ring invalid *)
(** Fee transfer *)
(** Token transfer *)
Parameter Event : Type.


(** * Transition *)
(** Two transition representations:
    - [LPSCTransition]: relational definition, suitable for reasoning;
    - [LPSCTransitionFunc]: defined as Coq function, runnable.

    Let's implement LPSCTransitionFunc first.
 *)

Inductive LPSCTransition : LPSCState -> Inputs * Event -> LPSCState -> Prop :=
| SubmitRing : forall s i e s',
    (** Blablabla... *)
    LPSCTransition s (i, e) s'
.

Parameter LPSCTransitionFunc:  forall (s: LPSCState) (i: Inputs), Event * LPSCState.


(** * Whole model *)
Instance LPSC : LTS :=
  {
    state := LPSCState;
    label := Inputs * Event;
    initState := initLPSCState;
    transition := LPSCTransition;
  }.
