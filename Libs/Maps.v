Require Import
        Nat
        List
        ZArith
        Coq.FSets.FMapWeakList
        Coq.Structures.DecidableType
        Coq.Structures.DecidableTypeEx.
Require Import
        Types.

Set Implicit Arguments.
Unset Strict Implicit.


(** Abstract Mapping Element Type *)
Module Type ElemType.
  Parameter Inline elt: Type.
  Parameter Inline elt_zero: elt.
  Parameter Inline elt_eq: elt -> elt -> Prop.

  Axiom elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.

  Axiom elt_eq_refl:
    forall x: elt, elt_eq x x.

  Axiom elt_eq_symm:
    forall (x y: elt), elt_eq x y -> elt_eq y x.

  Axiom elt_eq_trans:
    forall (x y: elt), elt_eq x y -> forall (z: elt), elt_eq y z -> elt_eq x z.
End ElemType.


(** Abstract Mapping Type *)
Module Mapping (K: DecidableType) (Elt: ElemType).
  Module Import map := FMapWeakList.Make(K).
  Module Import et := Elt.

  Notation t := (map.t elt).
  Notation empty := (map.empty elt).

  Definition get (m: t) (k: K.t) : elt :=
    match find k m with
    | Some v => v
    | None => elt_zero
    end.

  Definition upd (m: t) (k: K.t) (v: elt) : t := add k v m.

  Definition del (m: t) (k: K.t) : t := remove k m.

  Definition equal (m m': t) := forall k, get m k = get m' k.

  Section Aux.
    Lemma kv_eq_dec:
      forall (e e': K.t * elt), { Raw.PX.eqke e e' } + { ~ Raw.PX.eqke e e' }.
    Proof.
      intros [k v] [k' v'].
      destruct (K.eq_dec k k'); destruct (elt_eq_dec v v');
        unfold Raw.PX.eqke;
        simpl; tauto.
    Qed.

    Lemma not_eq_sym:
      forall (k k': K.t), ~ K.eq k k' -> ~ K.eq k' k.
    Proof.
      intros k k' Hneq Heq.
      apply Hneq.
      apply K.eq_sym; auto.
    Qed.

    Lemma find_add_eq:
      forall (m: t) (k k': K.t) (v: elt),
        K.eq k' k -> find k (add k' v m) = Some v.
    Proof.
      intros.
      apply find_1; apply add_1; auto.
    Qed.

    Lemma find_add_neq:
      forall (m: t) (k k': K.t) (v: elt),
        ~ K.eq k' k -> find k' (add k v m) = find k' m.
    Proof.
      intros.
      case_eq (find k' m).

      - intros e Hfind.
        apply find_2 in Hfind.
        apply find_1.
        apply add_2; auto.

      - unfold find, Raw.find.
        destruct m. simpl.
        generalize this0 NoDup0 k k' v H; clear this0 NoDup0 k k' v H.
        induction this0.

        + intros. simpl.
          destruct (K.eq_dec k' k); auto.
          apply H in e; inversion e.

        + intros. simpl.
          destruct a.
          destruct (K.eq_dec k t).

          * {
              destruct (K.eq_dec k' k).
              - apply H in e1; inversion e1.
              - destruct (K.eq_dec k' t); auto.
                apply K.eq_sym in e0.
                apply (K.eq_trans e1) in e0.
                apply n in e0; inversion e0.
            }

          * {
              destruct (K.eq_dec k' t); auto.
              inversion NoDup0; auto.
            }
    Qed.

    Lemma not_in_neq:
      forall k v k' v' m,
        ~ InA (Raw.PX.eqk (elt := elt)) (k, v) ((k', v') :: m) ->
        ~ K.eq k k'.
    Proof.
      intros k v k' v' m Hnotin Heq.
      apply Hnotin.
      constructor; auto.
    Qed.

    Lemma not_in_neq':
      forall k k' v' m nodup,
        ~ In (elt:=elt) k {| this := (k', v') :: m; NoDup := nodup |} ->
        ~ K.eq k k'.
    Proof.
      unfold In, Raw.PX.In, Raw.PX.MapsTo.
      intros k k' v' m nodup Hnotin Heq.
      apply Hnotin.
      exists v'.
      constructor 1; auto.
    Qed.

    Lemma not_InA_not_InA_tl:
      forall A (eqA: A -> A -> Prop) e e' m,
        ~ InA eqA e' (e :: m) ->
        ~ InA eqA e' m.
    Proof.
      intros k v k' v' m Hnot_in Hin.
      apply Hnot_in.
      constructor 2; auto.
    Qed.

    Lemma not_In_not_In_tl:
      forall k a m nodup nodup',
        ~ In (elt:=elt) k {| this := a :: m; NoDup := nodup |} ->
        ~ In (elt:=elt) k {| this := m; NoDup := nodup' |}.
    Proof.
      unfold In, Raw.PX.In, Raw.PX.MapsTo.
      intros k a m nodup nodup' Hnotin Hin.
      apply Hnotin.
      destruct Hin.
      exists x.
      constructor 2; auto.
    Qed.

    Lemma find_hd_eq:
      forall m k v nodup,
        find (elt:=elt) k {| this := (k, v) :: m; NoDup := nodup |} = Some v.
    Proof.
      unfold find. simpl; intros.
      destruct (K.eq_dec k k); auto.
      destruct n; auto.
    Qed.

    Lemma find_hd_neq_none:
      forall k v m
             (Hm: NoDupA (Raw.PX.eqk (elt := elt)) ((k, v) :: m))
             dup,
        find (elt := elt) k {| this := m; NoDup := dup |} = None.
    Proof.
      intros k v m Hm Hm'.

      inversion Hm. subst.
      unfold find.
      unfold Raw.find.
      simpl.
      induction m.

      - reflexivity.

      - destruct a.
        generalize (not_in_neq H1); intros Hneq.
        destruct (K.eq_dec k t).

        + apply Hneq in e0; inversion e0.

        + generalize (not_InA_not_InA_tl H1); intros Hnotin.

          assert (Hlst: (k, v) :: (t, e) :: m = ((k, v) :: nil) ++ (t, e) :: m).
          { reflexivity. }
          rewrite Hlst in Hm.
          apply SetoidList.NoDupA_split in Hm; simpl in Hm.

          inversion_clear Hm'.

          apply IHm; auto.
    Qed.

    Lemma find_hd_neq_tl:
      forall k k' v m
             (Hm: NoDupA (Raw.PX.eqk (elt:=elt)) ((k, v) :: m))
             dup,
        ~ K.eq k' k ->
        find (elt:=elt) k' {| this := (k, v) :: m; NoDup := Hm |} =
        find (elt:=elt) k' {| this := m; NoDup := dup |}.
    Proof.
      intros k k' v m Hm Hm' Hneq.

      unfold find.
      unfold Raw.find.
      simpl.
      destruct (K.eq_dec k' k).
      - apply Hneq in e; inversion e.
      - reflexivity.
    Qed.

    Lemma find_get:
      forall m k v,
        find k m = Some v ->
        get m k = v.
    Proof.
      intros m k v Hfind.
      unfold get.
      rewrite Hfind.
      auto.
    Qed.

    Lemma not_find_get:
      forall m k,
        find k m = None ->
        get m k = elt_zero.
    Proof.
      intros m k Hfind.
      unfold get.
      rewrite Hfind.
      auto.
    Qed.

    Lemma filter_true_eq:
      forall (T: Type) (l: list T), l = filter (fun _ => true) l.
    Proof.
      induction l; auto.
      simpl. rewrite <- IHl. reflexivity.
    Qed.
    Arguments filter_true_eq [T].

    Lemma find_eq:
      forall (k k': K.t) (m: t),
        K.eq k k' ->
        find k m = find k' m.
    Proof.
      intros k k' m Hkeq.
      destruct m as [this nodup].
      unfold find; simpl.
      rewrite (Raw.find_eq nodup Hkeq).
      reflexivity.
    Qed.

    Lemma in_find:
      forall m k v nodup,
        InA (Raw.PX.eqke (elt:=elt)) (k, v) m ->
        find k {| this := m; NoDup := nodup |} = Some v.
    Proof.
      induction m; simpl; auto.

      - intros k v nodup Hin.
        inversion Hin.

      - intros k v nodup Hin.
        destruct a as [k' v'].
        unfold find; simpl.
        destruct (K.eq_dec k k').
        + apply InA_cons in Hin; simpl in Hin.
          destruct Hin.
          * destruct H; simpl in *; congruence.
          * inversion nodup; subst.
            apply Raw.PX.InA_eqke_eqk in H.
            assert (Hkeq: Raw.PX.eqk (k, v) (k', v')).
            {
              unfold Raw.PX.eqk; simpl; auto.
            }
            apply (Raw.PX.InA_eqk Hkeq) in H.
            congruence.
        + unfold find in IHm; simpl in IHm.
          inversion nodup; subst.
          apply IHm; auto.
          apply InA_cons in Hin.
          destruct Hin; auto.
          unfold Raw.PX.eqke in H; simpl in H.
          destruct H as [Hkeq _].
          congruence.
    Qed.

    Lemma not_in_not_find:
      forall k v m nodup,
        ~ InA (Raw.PX.eqk (elt:=elt)) (k, v) m ->
        find k {| this := m; NoDup := nodup |} = None.
    Proof.
      induction m; simpl; auto.

      intros nodup Hnotin.
      inversion nodup; subst.
      destruct a.
      generalize (not_InA_not_InA_tl Hnotin); intros Hnotin'.
      generalize (IHm H2 Hnotin'); intros Hfind.
      generalize (not_in_neq Hnotin); intros Hneq.
      rewrite (find_hd_neq_tl nodup H2 Hneq).
      auto.
    Qed.

    Lemma not_in_not_find':
      forall (m: t) k,
        ~ In k m -> find k m = None.
    Proof.
      destruct m.
      induction this0; auto.

      intros k Hnotin.
      inversion NoDup0; subst.
      generalize (not_In_not_In_tl (nodup' := H2) Hnotin); intros Hnotin'.
      generalize (IHthis0 H2 k Hnotin'); intros Hfind.
      destruct a.
      generalize (not_in_neq' Hnotin); intros Hneq.
      rewrite (find_hd_neq_tl NoDup0 H2 Hneq).
      auto.
    Qed.
  End Aux.

  Section Rewrite.
    Lemma emp_zero:
      forall k, get empty k = elt_zero.
    Proof.
      auto.
    Qed.

    Lemma get_eq:
      forall m k k0, K.eq k k0 -> get m k = get m k0.
    Proof.
      intros.
      unfold get, find.
      rewrite (Raw.find_eq m.(NoDup) H).
      auto.
    Qed.

    Lemma get_hd_eq:
      forall m k k' v nodup,
        K.eq k' k ->
        get {| this := (k, v) :: m; NoDup := nodup |} k' = v.
    Proof.
      intros m k k' v nodup Heq.
      unfold get. unfold find. unfold Raw.find. simpl.
      destruct (K.eq_dec k' k); auto.
      apply n in Heq. inversion Heq.
    Qed.

    Lemma get_hd_eq':
      forall m k v nodup,
        get {| this := (k, v) :: m; NoDup := nodup |} k = v.
    Proof.
      intros.
      apply get_hd_eq.
      apply K.eq_refl.
    Qed.

    Lemma get_hd_neq:
      forall m k k' v nodup nodup',
        ~ K.eq k' k ->
        get {| this := (k, v) :: m; NoDup := nodup |} k' =
        get {| this := m; NoDup := nodup' |} k'.
    Proof.
      intros m k k' v nodup nodup' Hneq.
      unfold get. unfold find. unfold Raw.find. simpl.
      destruct (K.eq_dec k' k); auto.
      apply Hneq in e; inversion e.
    Qed.

    Lemma get_upd_eq:
      forall (m: t) (k k': K.t) (v: elt), K.eq k' k -> get (upd m k v) k' = v.
    Proof.
      intros m k k' v Hneq.
      unfold get, upd; rewrite find_add_eq; auto.
    Qed.

    Lemma get_upd_eq':
      forall (m: t) (k: K.t) (v: elt), get (upd m k v) k = v.
    Proof.
      intros. exact (get_upd_eq m v (K.eq_refl k)).
    Qed.

    Lemma get_upd_neq:
      forall (m: t) (k k': K.t) (v: elt), ~ K.eq k' k -> get (upd m k v) k' = get m k'.
    Proof.
      intros m k k' v Hneq.
      unfold upd, get.
      rewrite (find_add_neq m v Hneq).
      auto.
    Qed.

  End Rewrite.

  Section Equality.
    Lemma eq_equal:
      forall (m m': t),
        m = m' -> equal m m'.
    Proof.
      intros.
      subst.
      unfold equal.
      reflexivity.
    Qed.

    Lemma neq_not_equal:
      forall (m m': t), ~ equal m m' -> m <> m'.
    Proof.
      unfold equal.
      intros m m' Hneq Heq.
      apply Hneq.
      rewrite Heq.
      reflexivity.
    Qed.

    Lemma equal_refl:
      forall (m: t), equal m m.
    Proof.
      intros; apply eq_equal; auto.
    Qed.

    Lemma equal_sym:
      forall (m m': t), equal m m' -> equal m' m.
    Proof.
      unfold equal; auto.
    Qed.

    Lemma equal_trans:
      forall m m' m'', equal m m' -> equal m' m'' -> equal m m''.
    Proof.
      unfold equal; intros.
      generalize (H k); clear H; intros H; rewrite H.
      generalize (H0 k); clear H0; intros H0; rewrite H0.
      reflexivity.
    Qed.

    Lemma get_equal:
      forall m m' k k',
        equal m m' ->
        K.eq k k' ->
        get m k = get m' k'.
    Proof.
      intros m m' k k' Hmeq Hkeq.
      apply (get_eq m) in Hkeq.
      rewrite Hkeq.
      auto.
    Qed.

    Lemma upd_equal:
      forall m m' k v, equal m m' -> equal (upd m k v) (upd m' k v).
    Proof.
      unfold equal.
      intros m m' k v Heq k'.
      destruct (K.eq_dec k' k).
      - repeat rewrite get_upd_eq; auto.
      - repeat rewrite get_upd_neq; auto.
    Qed.

    Lemma upd_upd_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        K.eq k k' ->
        equal (upd (upd m k v) k' v')
              (upd m' k' v').
    Proof.
      unfold equal.
      intros m m' k k' v v' Hmeq Hkeq k0.

      case (K.eq_dec k0 k').
      - (* k = k0 *)
        intros Heq0.
        repeat rewrite (get_upd_eq _ _ Heq0).
        reflexivity.

      - (* k <> k0 *)
        intros Hneq0.
        assert (~ K.eq k0 k).
        { intros Heq0. apply Hneq0. eapply K.eq_trans; eauto. }
        repeat rewrite (get_upd_neq _ _ Hneq0).
        rewrite (get_upd_neq _ _ H).
        auto.
    Qed.

    Lemma upd_get_equal:
      forall (m m': t) (k k': K.t),
        equal m m' ->
        K.eq k k' ->
        equal m (upd m' k (get m' k')).
    Proof.
      unfold equal.
      intros m m' k k' Hmeq Hkeq k0.

      case (K.eq_dec k k0).
      - (* k0 = k *)
        intros Heq0.
        rewrite (get_upd_eq m' (get m' k')); auto.
        apply K.eq_sym in Hkeq.
        apply (K.eq_trans Hkeq) in Heq0.
        rewrite (Hmeq k0).
        apply get_eq; auto.

      - (* k0 <> k *)
        intros Hneq.
        rewrite get_upd_neq; auto.
    Qed.

    Lemma upd_upd_swap_equal:
      forall (m m': t) (k k': K.t) (v v': elt),
        equal m m' ->
        ~ K.eq k k' ->
        equal (upd (upd m k v) k' v')
              (upd (upd m' k' v') k v).
    Proof.
      unfold equal.
      intros m m' k k' v v' Hmeq Hneq k0.
      apply not_eq_sym in Hneq.

      case (K.eq_dec k0 k); case (K.eq_dec k0 k').
      - (* k = k' = k0 *)
        intros Heq Heq'.
        apply K.eq_sym in Heq.
        apply (K.eq_trans Heq) in Heq'.
        apply Hneq in Heq'; inversion Heq'.

      - (* k = k0 /\ k' <> k0 *)
        intros Hneq0' Heq0.
        repeat (try rewrite (get_upd_eq _ _ Heq0);
                try rewrite (get_upd_neq _ _ Hneq0');
                auto).

      - (* k <> k0 /\ k' = k0 *)
        intros Heq0 Hneq0'.
        repeat (try rewrite (get_upd_eq _ _ Heq0);
                try rewrite (get_upd_neq _ _ Hneq0');
                auto).

      - (* k <> k0 /\ k' <> k0 *)
        intros Hneq0' Hneq0''.
        repeat (try rewrite (get_upd_neq _ _ Hneq0');
                try rewrite (get_upd_neq _ _ Hneq0'');
                auto).
    Qed.
  End Equality.

  Hint Resolve
       (* Aux *)
       not_eq_sym
       find_add_eq find_add_neq
       not_in_neq not_in_neq' not_InA_not_InA_tl not_In_not_In_tl
       find_hd_eq find_hd_neq_none find_hd_neq_tl
       find_get not_find_get
       filter_true_eq
       not_in_not_find not_in_not_find'
       (* Rewrite *)
       emp_zero
       get_eq
       get_hd_eq get_hd_eq' get_hd_neq
       get_upd_eq get_upd_eq'
       get_upd_neq
       (* Equality *)
       eq_equal neq_not_equal
       equal_refl equal_sym equal_trans
       get_equal upd_equal
       upd_upd_equal upd_get_equal
       upd_upd_swap_equal
  .

  Hint Rewrite
       emp_zero
       get_hd_eq' get_upd_eq'
    : mapping_rewrite.

  Ltac msimpl :=
    match goal with
    (* emp_zero *)
    | [ |- context [ get empty ?k ]
      ] =>
      rewrite (emp_zero k);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_hd_eq *)
    | [ H: K.eq ?k' ?k
        |- context [ get {| this := (?k, ?v) :: ?m; NoDup := ?nodup |} ?k' ]
      ] =>
      rewrite (get_hd_eq nodup H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: K.eq ?k ?k'
        |- context [ get {| this := (?k, ?v) :: ?m; NoDup := ?nodup |} ?k' ]
      ] =>
      rewrite (get_hd_eq nodup (K.eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ |- context [ get {| this := (?k, ?v) :: ?m; NoDup := ?nodup |} ?k ]
      ] =>
      rewrite (get_hd_eq' nodup);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_eq *)
    | [ H: K.eq ?k' ?k
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_eq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: K.eq ?k ?k'
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_eq m v (K.eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_eq' *)
    | [ |- context [ get (upd ?m ?k ?v) ?k ]
      ] =>
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    (* get_upd_neq *)
    | [ H: ~ K.eq ?k' ?k
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_neq m v H);
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | [ H: ~ K.eq ?k ?k'
        |- context [ get (upd ?m ?k ?v) ?k' ]
      ] =>
      rewrite (get_upd_neq m v (not_eq_sym H));
      autorewrite with mapping_rewrite;
      auto;
      msimpl

    | _ => idtac
    end.

  Ltac msimpl_in H :=
    let T := type of H in
    generalize H; clear H; msimpl; intros H.

End Mapping.


(** Decidable Types *)
Module Address_as_DT <: UsualDecidableType := Nat_as_DT.
Module AA_as_DT := DecidableTypeEx.PairDecidableType (Address_as_DT) (Address_as_DT).
Module Hash_as_DT <: UsualDecidableType := Nat_as_DT.
Module AH_as_DT := DecidableTypeEx.PairDecidableType (Address_as_DT) (Hash_as_DT).
Module AAH_as_DT := DecidableTypeEx.PairDecidableType (AA_as_DT) (Hash_as_DT).
Module AAA_as_DT := DecidableTypeEx.PairDecidableType (AA_as_DT) (Address_as_DT).


(** Concrete Element Types *)
Module ValElem <: ElemType.
  Definition elt : Type := value.
  Definition elt_zero := 0.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
    exact Nat.eq_dec.
  Qed.

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
End ValElem.

Module BoolElem <: ElemType.
  Definition elt : Type := bool.
  Definition elt_zero := false.
  Definition elt_eq := fun (x x': elt) => x = x'.

  Lemma elt_eq_dec:
    forall (x y: elt), { x = y } + { ~ x = y }.
  Proof.
    exact Bool.bool_dec.
  Qed.

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
End BoolElem.


(** Concrete Mapping Types *)
(* Address -> Nat *)
Module A2V := Mapping Address_as_DT ValElem.
(* Address -> Bool *)
Module A2B := Mapping Address_as_DT BoolElem.
(* (Address, Address) -> Nat *)
Module AA2V := Mapping AA_as_DT ValElem.
(* Hash -> Nat *)
Module H2V := Mapping Hash_as_DT ValElem.
(* Hash -> Bool *)
Module H2B := Mapping Hash_as_DT BoolElem.
(* address -> Hash -> bool *)
Module AH2B := Mapping AH_as_DT BoolElem.
(* address -> Hash -> Nat *)
Module AH2V := Mapping AH_as_DT ValElem.
(* address -> address -> Hash -> Nat *)
Module AAH2V := Mapping AAH_as_DT ValElem.


(** Shortcuts for map updates  *)
Definition AA2V_upd_inc (m: AA2V.t) (a0 a1: address) (v: value) : AA2V.t :=
  AA2V.upd m (a0, a1) (plus_with_overflow (AA2V.get m (a0, a1)) v).

Definition AA2V_upd_dec (m: AA2V.t) (a0 a1: address) (v: value) : AA2V.t :=
  AA2V.upd m (a0, a1) (minus_with_underflow (AA2V.get m (a0, a1)) v).
