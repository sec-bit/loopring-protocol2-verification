From mathcomp.ssreflect Require Import ssrnat ssrbool div.
Require Import List.

Record Order : Type :=
  mk_order {
      amountS : nat;
      amountB : nat;
      fillS : nat;
      fillB : nat;
    }.

Definition Ring : Type := list Order.

(** 
    Loopring order ring structure :

    | S0 |  / | S1 |  / ...  / | SN |
    | B0 | /  | B1 | /  ... /  | BN |

    In this file we organize ring as 
    Order_{N-1} :: Order_{N-2} :: ... :: Order_0 :: nil

 *)

Definition upd_order (order: Order) (fillS' fillB': nat) :=
  mk_order (amountS order) (amountB order) fillS' fillB'.

Definition shrink_S (B': nat) (order: Order) : nat := (B' * amountS order) %/ amountB order.
  
Definition shrink_order (prev cur: Order) : Order :=
  if fillS prev < fillB cur
  then upd_order cur (shrink_S (fillS prev) cur) (fillS prev)
  else cur.

(** shrink Order_{k-1} according to Order_{k},
    k in {1, ..., N-1} *)

Fixpoint shrink_ring_aux (prev: Order) (orderring: Ring) : Ring :=
  match orderring with
  | nil => nil
  | cur :: orderring' =>
    let cur' :=  shrink_order prev cur in
    cur' :: shrink_ring_aux cur' orderring'
  end.

Definition shrink_ring (orderring: Ring) : option Ring :=
  match orderring with
  | nil 
  | _ :: nil => None
  | lastorder :: orderring =>
    Some (lastorder :: shrink_ring_aux lastorder orderring)
  end.

Definition check_last_can_fill (orderring: Ring) : bool :=
  match orderring with
  | nil 
  | _ :: nil => false
  | lastorder :: orderring =>
    let order0' := last orderring lastorder in
    fillS order0' >= fillB lastorder
  end.

Definition calc_fill_amount (orderring: Ring) : option Ring :=
  (** The first pass *)
  match shrink_ring orderring with
  | None
  | Some nil
  | Some (_ :: nil) => None
  | Some (lastorder :: orderring') =>
    if check_last_can_fill (lastorder :: orderring')
    then Some (lastorder :: orderring')
    else
      let order0' := last orderring' lastorder in
      let lastorder' := shrink_order order0' lastorder in
      shrink_ring (lastorder' :: orderring')
  end.

(** * Correctness *)
Section Correctness.

  (** Pre-conditions *)
  
  Definition PreConditionFill : Ring -> Prop :=
    Forall (fun order => fillS order = amountS order /\ fillB order = amountB order).

  Definition PreConditionGamma (orderring : Ring) : Prop :=
    fold_left
      (fun product order => product * amountS order %/ amountB order)
      orderring 1 >= 1.

  Definition PreConditionLength (orderring : Ring ) : Prop :=
    length orderring >= 2.

  (** Post-conditions *)
  
  Definition AlmostCanFill (orderring : Ring) : Prop :=
    forall n orderprev ordercur,
      nth_error orderring n = Some orderprev ->
      nth_error orderring n.+1 = Some ordercur ->
      fillS orderprev >= fillB ordercur.

  Definition CanFill (orderring : Ring) : Prop :=
    AlmostCanFill orderring
    /\ check_last_can_fill orderring = true.

  Definition WinWin : Ring -> Prop :=
    Forall (fun order => fillS order * amountB order >= amountS order * fillB order
                      /\ fillS order <= amountS order).

  Definition RateUnchanged : Ring -> Ring -> Prop :=
    Forall2 (fun order order' => amountS order = amountS order' /\ amountB order = amountB order').

  Definition Correct (orderring orderring': Ring) :=
    RateUnchanged orderring orderring' 
    /\ CanFill orderring'
    /\ WinWin orderring'.
  
  (** Soundness *)
  Theorem soundness:
    forall orderring orderring',
      PreConditionFill orderring ->
      PreConditionLength orderring ->
      PreConditionGamma orderring ->
      calc_fill_amount orderring = Some orderring' ->
      check_last_can_fill orderring' = true ->
      Correct orderring orderring'.
  Proof.
  Admitted.

  (** Completeness *)
  Theorem completeness:
    forall orderring,
      PreConditionFill orderring ->
      PreConditionLength orderring ->
      PreConditionGamma orderring ->
      exists orderring',
        calc_fill_amount orderring = Some orderring'
        /\ check_last_can_fill orderring' = true.
  Proof.
  Admitted.

End Correctness.
      
      
  