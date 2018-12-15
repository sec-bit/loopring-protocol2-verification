From mathcomp.ssreflect Require Import ssrnat ssrbool div.
Require Import List Omega.

Require PArith.

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
Require Import QArith.

Section Correctness.

  (** Pre-conditions *)
  
  Definition PreConditionFill : Ring -> Prop :=
    Forall (fun order => fillS order = amountS order /\ fillB order = amountB order).

  Definition mult_gamma (product: Q) (order: Order) : Q :=
    product * inject_Z (Z.of_nat (amountS order)) / inject_Z (Z.of_nat (amountB order)).

  Definition mult_gamma_nat (product: nat) (order: Order) : nat :=
    (product * (amountS order) %/ (amountB order))%nat.
  
  Definition fillB_mult_gamma (fillB: nat) (r: Ring) : nat :=
    fold_left mult_gamma_nat r fillB.

  Definition PreConditionGamma (r : Ring) : Prop := 
    forall  o r1,
      shrink_ring r = Some (o :: r1) ->
      let last' := shrink_order (last r1 o ) o in
      (fillB last' <= fillB_mult_gamma (fillB last') r)%nat.

  Lemma pre_condition_gamma_implies:
    forall r,
      PreConditionGamma r ->
      forall  o o0 r1,
        shrink_ring r = Some (o :: o0 :: r1) ->
        let last' := shrink_order (last (o0 :: r1) o ) o in
        (fillB last' <=
         fillB_mult_gamma (fillB last') r)%nat.
  Proof. auto. Qed.


  Definition PreConditionLength (orderring : Ring ) : Prop :=
    (length orderring >= 2)%nat.

  (** Post-conditions *)
  
  Definition AlmostCanFill (orderring : Ring) : Prop :=
    forall n orderprev ordercur,
      nth_error orderring n = Some orderprev ->
      nth_error orderring n.+1 = Some ordercur ->
      (fillS orderprev >= fillB ordercur)%nat.

  Definition CanFill (orderring : Ring) : Prop :=
    AlmostCanFill orderring
    /\ check_last_can_fill orderring = true.

  Definition OrderWinWin : Order -> Prop :=
    (fun order => fillS order * amountB order <= amountS order * fillB order
               /\ fillS order <= amountS order
               /\ fillB order <= amountB order)%nat.
  
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
    destruct (fillS prev < fillB cur)%nat eqn:Hlt; auto.
    inv H; split; simpl; unfold shrink_S.
    
    rewrite (mulnC (fillS prev) (amountS cur)).
    apply leq_trunc_div.

    inv H1. split.
    eapply leq_trans.
    eapply leq_div2r.
    eapply leq_mul. instantiate (1:= fillB cur). auto.
    instantiate (1:= amountS cur). auto. clear H0 Hlt H.
    rewrite mulnC. eapply leq_trans. eapply leq_div2r.
    instantiate (1:= (amountS cur * amountB cur)%nat). eapply leq_mul; auto.
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
      (fillB (shrink_order prev cur) <= fillS prev)%nat.
  Proof.
    intros. unfold shrink_order.
    destruct (fillS prev < fillB cur)%nat eqn: Hlt.
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
    
  (** post condition of shrink pass 2 *)
  Lemma fillB_mult_gamma_shrink_canc:
    forall r n r',
      shrink_ring r = Some r' ->
      fillB_mult_gamma n r' = fillB_mult_gamma n r.
  Proof.
    intros. apply rate_unchanged_after_shrinking_ring in H.
    revert n. induction H. auto.
    simpl. intro n. rewrite IHForall2. inv H.
    unfold mult_gamma_nat. rewrite H1, H2. auto.
  Qed.
  
  Lemma fillB_mult_gamma_shrink_order_canc:
    forall r o n o',
      fillB_mult_gamma n (shrink_order o' o :: r) = fillB_mult_gamma n (o :: r).
  Proof.
    intros. unfold shrink_order. destruct (fillS o' < fillB o)%nat; simpl; auto.
  Qed.

  Lemma mult_gamma_nat_shrink_order_canc:
    forall o o' amount, 
      mult_gamma_nat amount (shrink_order o' o) =
      mult_gamma_nat amount o.
  Proof.
    unfold mult_gamma_nat, shrink_order. intros.
    destruct (fillS o' < fillB o)%nat; auto.
  Qed.
  
  Lemma almost_can_fill_tail:
    forall olast r,
      AlmostCanFill (olast :: r) ->
      AlmostCanFill r.
  Proof.
    intros. intros N prev cur Hprev Hcur.
    specialize (H N.+1). simpl in H, Hcur. rewrite Hprev, Hcur in H.
    eapply H; eauto.
  Qed.
  
  Lemma lt_ge_False:
    forall a b,
      (a <= b)%nat ->
      (b < a = true)%nat ->
      False.
  Proof.
    intros. destruct (@leP a b); destruct (@leP (S b) a); try discriminate.
    omega.
  Qed.
  
  Lemma lt_false_le:
    forall a b,
      (b < a)%nat = false ->
      (a <= b)%nat.
  Proof.
    intros. destruct (@leP a b); destruct (@leP (S b) a); try discriminate; auto.
    omega.
  Qed.

  Lemma almost_can_fill_tail':
    forall olast a r,
      AlmostCanFill (a :: r) ->
      (fillB a <= fillS olast)%nat ->
      AlmostCanFill (olast :: a :: r).
  Proof.
    intros. intro N. destruct N; simpl; [|apply H]. intros.
    inv H1; inv H2. auto.
  Qed.

  Lemma check_pass_shrink_order_unchanged:
    forall a b,
      (fillB a <= fillS b)%nat ->
      shrink_order b a = a.
  Proof.
    unfold shrink_order. intros.
    destruct (fillS b < fillB a)%nat eqn:?; auto.
    exfalso. eapply lt_ge_False; eauto.
  Qed.
  
  Lemma almost_can_fill_shrinking_unchanged:
    forall r olast r',
      AlmostCanFill (olast :: r) ->
      shrink_ring (olast :: r) = Some r' ->
      r' = olast :: r.
  Proof.
    induction r; intros. discriminate.
    simpl in H0. inv H0. destruct r.
    clear IHr. simpl. unfold shrink_order.
    destruct (fillS olast < fillB a)%nat eqn:Hlt; auto.
    exfalso. specialize (H 0%nat). simpl in H. specialize (H _ _ eq_refl eq_refl). 
    eapply lt_ge_False; eauto.
    assert (shrink_order olast a = a).
    { specialize (H 0%nat _ _ eq_refl eq_refl).
      apply check_pass_shrink_order_unchanged; auto. }
    rewrite H0.
    apply almost_can_fill_tail in H. eapply IHr in H; eauto.
    rewrite H. auto.
  Qed.

  Lemma shrink_ring_post_condition:
    forall olast r r' anyorder,
      AlmostCanFill r ->
      shrink_ring (olast :: r) = Some (olast :: r') ->
      (* case 1: check passed in the middle of the second pass *)
      (last r' anyorder = last r anyorder)
      \/
      (* case 2: check failed till the end of the second pass *)
      fillS (last r' anyorder) =
      fillB_mult_gamma (fillS olast) r'.
  Proof.
    intros olast r.
    revert olast. induction r.
    discriminate.
    intros olast r' anyorder Hfill Hshrink.
    assert (AlmostCanFill r) by (eapply almost_can_fill_tail; eauto).
    simpl in Hshrink.
    destruct r as [|b r].
    (* ring of 2 *)
    clear IHr. inv Hshrink. clear H Hfill.
    rewrite mult_gamma_nat_shrink_order_canc.
    unfold shrink_order. destruct (fillS olast < fillB a)%nat; auto.
    (* ring of more .. *)
    destruct (fillS olast < fillB a)%nat eqn:Hfail.
    (* check failed at the beginning of the pass *)
    specialize (IHr (shrink_order olast a)
                    (shrink_ring_aux (shrink_order olast a) (b :: r))
                    anyorder H eq_refl).
    clear H. destruct IHr;[left|right].
    (* check passed in the middle of the pass *)
    inv Hshrink. auto.
    (* check failed till the end of the pass *)
    inv Hshrink. rewrite H. clear H.
    repeat rewrite mult_gamma_nat_shrink_order_canc.
    clear Hfill. generalize (shrink_ring_aux (shrink_order (shrink_order olast a) b) r).
    clear r anyorder. intro r.
    unfold shrink_order. rewrite Hfail. clear Hfail. simpl.
    unfold fillB_mult_gamma. f_equal.
    (* check passed at the beginning of the pass *)
    left. rename Hfail into Hpass.
    apply lt_false_le in Hpass. apply check_pass_shrink_order_unchanged in Hpass.
    rewrite Hpass in *.
    assert (shrink_ring (a :: b :: r) = Some r').
    { inv Hshrink. auto. }
    apply almost_can_fill_shrinking_unchanged in H0; auto. subst r'. auto.
  Qed.

  Lemma mult_gamma_eq_wrt_shrink_order:
    forall a o o',
      mult_gamma a o = mult_gamma a (shrink_order o' o).
  Proof.
    unfold shrink_order, mult_gamma. intros.
    destruct (fillS o' < fillB o)%nat; auto.
  Qed.
  
  Lemma completeness':
    forall orderring orderring',
      WinWin orderring ->
      PreConditionGamma orderring ->
      calc_fill_amount orderring = Some orderring' ->
      check_last_can_fill orderring' = true.
  Proof.
    unfold calc_fill_amount. intros r r' Hwinwin Hgamma.
    destruct (shrink_ring r) as [r1|] eqn:Hshrink1; [|discriminate].
    pose proof (almost_can_fill_after_shrinking _ _ Hshrink1) as Hcanfill1.
    pose proof (winwin_stable_wrt_shrink _ _ Hshrink1 Hwinwin) as Hwinwin1.
    (* pose proof (PreConditionGamma_stable_wrt_shrink _ _ Hshrink1 Hgamma) as Hgamma1. *)
    clear Hwinwin.
    destruct r1; [discriminate|].
    destruct r1; [discriminate|].
    destruct (check_last_can_fill (o :: o0 :: r1)) eqn:Hcheck1.
    intro A. inv A. auto.
    intros.
    destruct r'. inv H.
    pose proof H as Hshrink2.
    assert (o1 = shrink_order (last (o0 :: r1) o) o).
    { inv H. auto. }
    subst o1.
    eapply shrink_ring_post_condition in H; try eauto using almost_can_fill_tail.
    destruct H.
    (* case 1: check passed *)
    unfold check_last_can_fill. destruct r'. discriminate.
    rewrite H. clear.
    unfold shrink_order at 1. destruct (fillS (last (o0 :: r1) o) < fillB o)%nat eqn:Hlt.
    simpl. clear Hlt.
    match goal with
    | |- context[shrink_order ?x ?y] => generalize (shrink_order x y)
    end.
    revert o o0. induction r1; intros. apply leqnn. simpl. apply IHr1.
    assert (forall o', last (o0 :: r1) o = last (o0 :: r1) o').
    { clear. revert o0 o. induction r1; auto. intros. simpl in *. apply IHr1. }
    rewrite <- H. apply lt_false_le. auto.
    (* case 2: check failed till the end *)
    eapply pre_condition_gamma_implies in Hgamma; [|exact Hshrink1].
    unfold check_last_can_fill.
    destruct r'. discriminate.
    rewrite H.
    assert (fillB_mult_gamma (fillS (shrink_order (last (o0 :: r1) o) o)) (o1 :: r') =
            fillB_mult_gamma (fillB (shrink_order (last (o0 :: r1) o) o))
                             ((shrink_order (last (o0 :: r1) o ) o :: o1 :: r'))).
    { unfold shrink_order. unfold check_last_can_fill in Hcheck1.
      destruct (fillS (last (o0 :: r1) o) < fillB o)%nat eqn:Hlt. auto.
      exfalso. revert Hcheck1 Hlt. clear.
      generalize (fillB o) (fillS (last (o0 :: r1) o)). clear. intros m n A B.
      destruct (@leP m n); try discriminate.
      destruct (@leP (S n) m); try discriminate.
      omega.
    }
    rewrite H0.
    erewrite fillB_mult_gamma_shrink_canc; [|exact Hshrink2].
    rewrite fillB_mult_gamma_shrink_order_canc.
    erewrite fillB_mult_gamma_shrink_canc; [|exact Hshrink1].
    auto.
  Qed.

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
      
      
  