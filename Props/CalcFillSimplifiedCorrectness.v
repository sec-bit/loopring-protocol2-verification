From mathcomp.ssreflect Require Import ssrnat ssrbool div.
Require Import List Omega.

Ltac inv H :=
  inversion H; clear H; subst; simpl in *.

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

  Definition OrderWinWin : Order -> Prop :=
    (fun order => fillS order * amountB order <= amountS order * fillB order
               /\ fillS order <= amountS order
               /\ fillB order <= amountB order).
  
  Definition WinWin : Ring -> Prop :=
    Forall OrderWinWin.

  Definition OrderRateUnchanged : Order -> Order -> Prop :=
    (fun order order' => amountS order = amountS order' /\ amountB order = amountB order').
  
  Definition RateUnchanged : Ring -> Ring -> Prop :=
    Forall2 OrderRateUnchanged.

  Definition Correct (orderring orderring': Ring) :=
    RateUnchanged orderring orderring' 
    /\ CanFill orderring'
    /\ WinWin orderring'.

  (** Lemmas *)
  
  (** ** Rate unchanged *)
  Lemma rate_unchanged_after_shrinking_order:
    forall order prev,
      OrderRateUnchanged order (shrink_order prev order).
  Proof. 
    unfold shrink_order, upd_order, OrderRateUnchanged; intros.
    destruct leq; auto.
  Qed.
  
  Lemma rate_unchanged_after_shrinking_ring_aux:
    forall ring1 prev ring2,
      shrink_ring_aux prev ring1 = ring2 ->
      RateUnchanged ring1 ring2.
  Proof.
    induction ring1; simpl; intros.
    destruct ring2; [constructor|discriminate].
    destruct ring2. discriminate.
    inv H. constructor. apply rate_unchanged_after_shrinking_order.
    eapply IHring1; eauto.
  Qed.

  Lemma rate_unchanged_after_shrinking_ring:
    forall ring1 ring2,
      shrink_ring ring1 = Some ring2 ->
      RateUnchanged ring1 ring2.
  Proof.
    intros ring1 ring2 Hshrink.
    destruct ring1. simpl in *. discriminate.
    destruct ring1. simpl in *. discriminate.
    inv Hshrink. constructor. unfold OrderRateUnchanged; auto.
    eapply rate_unchanged_after_shrinking_ring_aux.
    simpl. eauto.
  Qed.

  Lemma OrderRateUnchanged_trans:
    forall o1 o2 o3,
      OrderRateUnchanged o1 o2 ->
      OrderRateUnchanged o2 o3 ->
      OrderRateUnchanged o1 o3.
  Proof. unfold OrderRateUnchanged. intuition; congruence. Qed.
  
  Lemma RateUnchanged_trans:
    forall ring1 ring2 ring3,
      RateUnchanged ring1 ring2 ->
      RateUnchanged ring2 ring3 ->
      RateUnchanged ring1 ring3.
  Proof.
    induction ring1; intros.
    inv H. inv H0. constructor.
    inv H. inv H0. constructor.
    eapply OrderRateUnchanged_trans; eauto.
    eapply IHring1; eauto.
  Qed.

  Lemma RateUnchanged_refl:
    forall orderring,
      RateUnchanged orderring orderring.
  Proof.
    induction orderring; constructor; 
      unfold OrderRateUnchanged; auto.
  Qed.
  
  Lemma rate_unchanged_after_calc_fill_amount:
    forall ring1 ring2,
      calc_fill_amount ring1 = Some ring2 ->
      RateUnchanged ring1 ring2.
  Proof.
    unfold calc_fill_amount. intros.
    destruct (shrink_ring ring1) eqn:Hpass1;[|discriminate].
    apply rate_unchanged_after_shrinking_ring in Hpass1.
    destruct r; [discriminate|].
    destruct r; [discriminate|].
    destruct (check_last_can_fill _) eqn:Hchecklast.
    inv H; auto. 
    eapply RateUnchanged_trans. eauto.
    eapply RateUnchanged_trans.
    econstructor. eapply rate_unchanged_after_shrinking_order.
    eapply RateUnchanged_refl. 
    eapply rate_unchanged_after_shrinking_ring. eauto.
  Qed.
  
  (** * WinWin *)

  Lemma PreConditionFill_WinWin:
    forall r, PreConditionFill r -> WinWin r.
  Proof.
    induction r; constructor.
    inv H. unfold OrderWinWin. inv H2. rewrite H, H0. auto.
    inv H. apply IHr. auto.
  Qed.
  
  Lemma order_winwin_stable_wrt_shrink:
    forall prev cur, OrderWinWin cur -> OrderWinWin (shrink_order prev cur).
  Proof.
    intros. unfold shrink_order.
    destruct (fillS prev < fillB cur) eqn:Hlt; auto.
    inv H; split; simpl; unfold shrink_S.
    
    rewrite (mulnC (fillS prev) (amountS cur)).
    apply leq_trunc_div.

    inv H1. split.
    eapply leq_trans.
    eapply leq_div2r.
    eapply leq_mul. instantiate (1:= fillB cur). auto.
    instantiate (1:= amountS cur). auto. clear H0 Hlt H.
    rewrite mulnC. eapply leq_trans. eapply leq_div2r.
    instantiate (1:= amountS cur * amountB cur). eapply leq_mul; auto.
    destruct (amountB cur). auto. 
    rewrite mulnK; auto.

    eapply leq_trans. instantiate (1:= fillB cur). auto. auto.
  Qed.

  Lemma winwin_stable_wrt_shrink_aux:
    forall prev ring1 ring2,
      shrink_ring_aux prev ring1 = ring2 ->
      WinWin ring1 ->
      WinWin ring2.
  Proof.
    intros prev ring1. revert prev. induction ring1; intros.
    inv H. constructor.
    inv H. inv H0. constructor.
    apply order_winwin_stable_wrt_shrink. auto.
    eapply IHring1; eauto. 
  Qed.

  Lemma winwin_stable_wrt_shrink:
    forall ring1 ring2,
      shrink_ring ring1 = Some ring2 ->
      WinWin ring1 ->
      WinWin ring2.
  Proof.
    unfold shrink_ring.
    destruct ring1. discriminate.
    destruct ring1. discriminate.
    intros. inv H. inv H0. constructor. auto.
    eapply winwin_stable_wrt_shrink_aux.
    instantiate (1:= o0 :: ring1). simpl. eauto. eauto.
  Qed.

  Lemma winwin_stable_wrt_calc_fill_amount:
    forall ring1 ring2,
      calc_fill_amount ring1 = Some ring2 ->
      WinWin ring1 ->
      WinWin ring2.
  Proof.
    destruct ring1. discriminate.
    destruct ring1. discriminate.
    unfold calc_fill_amount.
    destruct (shrink_ring (o :: o0 :: ring1)) eqn:Hshrink1; [|discriminate].
    destruct r. discriminate.
    destruct r. discriminate.
    intros ring2 Hshrink2 Hwinwin.
    eapply winwin_stable_wrt_shrink in Hshrink1; auto. 
    destruct (check_last_can_fill (o1 :: o2 :: r)) eqn:Hcheck. inv Hshrink2. auto.
    eapply winwin_stable_wrt_shrink in Hshrink2; auto.
    inv Hshrink1.
    constructor; auto. apply order_winwin_stable_wrt_shrink. auto. 
  Qed.
  
  (** * Almostcanfill *)

  Lemma almost_can_fill_after_shrinking_order:
    forall prev cur,
      fillB (shrink_order prev cur) <= fillS prev.
  Proof.
    intros. unfold shrink_order.
    destruct (fillS prev < fillB cur) eqn: Hlt.
    simpl. auto.
    revert Hlt. generalize (fillS prev) (fillB cur). clear. intros m n H.
    destruct (@ltP m n). discriminate. apply not_lt in n0.
    destruct (@leP n m); auto.
  Qed.
  
  Lemma almost_can_fill_after_shrinking_aux:
    forall ring1 prev ring2,
      shrink_ring_aux prev ring1 = ring2 ->
      AlmostCanFill (prev :: ring2).
  Proof.
    induction ring1.
    intros. inv H. intros N op oc. destruct N; discriminate.
    intros. simpl in H. inv H.
    specialize (IHring1 (shrink_order prev a)
                        (shrink_ring_aux (shrink_order prev a) ring1) eq_refl).
    intros N op oc Hop Hoc.
    destruct N. simpl in *. inv Hop; inv Hoc.
    apply almost_can_fill_after_shrinking_order.
    simpl in Hop, Hoc.
    eapply IHring1; eauto. 
  Qed.
  
  Lemma almost_can_fill_after_shrinking:
    forall ring1 ring2,
      shrink_ring ring1 = Some ring2 ->
      AlmostCanFill ring2.
  Proof.
    destruct ring1. simpl. discriminate.
    destruct ring1. simpl. discriminate.
    simpl. intros. inv H.
    intros N op oc. destruct N; simpl.
    intros. inv H; inv H0. apply almost_can_fill_after_shrinking_order.
    intros. eapply almost_can_fill_after_shrinking_aux; eauto.
  Qed.

  Lemma almost_can_fill_after_calc_fill_amount:
    forall ring1 ring2,
      calc_fill_amount ring1 = Some ring2 ->
      AlmostCanFill ring2.
  Proof.
    unfold calc_fill_amount. intros ring1 ring2.
    destruct (shrink_ring ring1) eqn:Hshrink1; [|discriminate].
    destruct r. discriminate.
    destruct r. discriminate.
    destruct (check_last_can_fill _) eqn:Hcheck. intro H; inv H.
    eapply almost_can_fill_after_shrinking. eauto.
    intro. eapply almost_can_fill_after_shrinking. eauto.
  Qed.

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
    intros.
    split. apply rate_unchanged_after_calc_fill_amount. auto.
    split. split; auto. eapply almost_can_fill_after_calc_fill_amount; eauto.
    eapply winwin_stable_wrt_calc_fill_amount; eauto.
    apply PreConditionFill_WinWin. auto.
  Qed.


  
  (** Completeness *)
  
  Lemma PreConditionLength_calc_fill_Some:
    forall orderring,
      PreConditionLength orderring ->
      exists orderring',
        calc_fill_amount orderring = Some orderring'.
  Proof.
    intros.
    destruct orderring. inv H.
    destruct orderring. inv H.
    unfold calc_fill_amount. simpl.
    match goal with
    | |- context[if ?b then _ else _] =>
      destruct b; eauto
    end.
  Qed.
    
  Lemma completeness':
    forall orderring orderring',
      WinWin orderring ->
      PreConditionGamma orderring ->
      calc_fill_amount orderring = Some orderring' ->
      check_last_can_fill orderring' = true.
  Proof.
    
  Admitted.

  Theorem completeness:
    forall orderring,
      PreConditionFill orderring ->
      PreConditionLength orderring ->
      PreConditionGamma orderring ->
      exists orderring',
        calc_fill_amount orderring = Some orderring'
        /\ check_last_can_fill orderring' = true.
  Proof.
    intros. apply PreConditionLength_calc_fill_Some in H0.
    destruct H0 as [orderring' Hcalc].
    eexists. split. eauto.
    eapply completeness'; eauto.
    apply PreConditionFill_WinWin; auto.
  Qed.

End Correctness.
      
      
  