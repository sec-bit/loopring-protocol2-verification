Require Import
        List
        ZArith.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.
Require Import
        RingSubmitter.
Require Import
        TopModel.


Section NoSubRings.

  Definition has_subrings
             (rings: list RingSubmitter.RingRuntimeState)
             (orders: list RingSubmitter.OrderRuntimeState) : Prop :=
    forall r rs,
      rings = r :: rs /\ RingSubmitter.ring_has_subrings r orders.

  Theorem no_sub_rings:
    forall sender r orders mining st wst wst' retval events,
      st = RingSubmitter.make_rt_submitter_state mining orders (r :: nil) ->
      has_subrings (RingSubmitter.submitter_rt_rings st)
                   (RingSubmitter.submitter_rt_orders st) ->
      lr_step wst
              (MsgRingSubmitter (msg_submitRings sender orders (r :: nil) mining))
              wst' retval events ->
      In (EvtRingSkipped r) events.
  Proof.
    intros until events.
    intros Hst Hsubring Hstep.

    simpl in Hstep.
    unfold RingSubmitter.model in Hstep.
    destruct Hstep as [_ [st' Hstep]].
    specialize (Hstep sender orders (r :: nil) mining).
    destruct Hstep as [_ Hstep].

    assert (Hsubrings0:
              RingSubmitter.nth_ring_has_subrings (RingSubmitter.make_rt_ring r :: nil)
                                                  (RingSubmitter.make_rt_orders orders) 0).
    {
      rewrite Hst in Hsubring; simpl in Hsubring.
      specialize (Hsubring (RingSubmitter.make_rt_ring r) nil).
      destruct Hsubring as [_ Hsubring].

      unfold RingSubmitter.nth_ring_has_subrings; simpl.
      intros r0 Hnth0; inversion Hnth0; subst.

      trivial.
    }

    inversion Hstep; clear Hstep; subst.
    assert (Hsubrings1: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'0)
                          (RingSubmitter.submitter_rt_orders st'0)
                          0).
    {
      inversion H6; clear H6; subst.
      clear H0 H9; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring1:
              exists r1,
                nth_error (RingSubmitter.submitter_rt_rings st'0) 0 = Some r1 /\
                RingSubmitter.ring_rt_static r1 = r).
    {
      inversion H6; clear H6; subst.
      clear H0 H9; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve _] _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _];
        simpl in Hrings_preserve.
      specialize (Hrings_preserve (RingSubmitter.make_rt_ring r));
        simpl in Hrings_preserve.
      intuition.
      destruct H as [r' [Hr' [Hring' _]]].
      exists r'. split; auto.
    }

    inversion H7; clear H7; subst.
    assert (Hsubrings2: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'1)
                          (RingSubmitter.submitter_rt_orders st'1)
                          0).
    {
      inversion H8; clear H8; subst.
      clear H0 H10; simpl in H1.
      destruct H1 as [Hst_preserve _].
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring2:
              exists r2,
                nth_error (RingSubmitter.submitter_rt_rings st'1) 0 = Some r2 /\
                RingSubmitter.ring_rt_static r2 = r).
    {
      inversion H8; clear H8; subst.
      clear H0 H10; simpl in H1.
      destruct H1 as [Hst_preserve _].
      destruct Hst_preserve as [Hrings_preserve _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring1 as [r1 [Hnth1 Hring1]].
      specialize (Hrings_preserve r1 Hnth1).
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H9; clear H9; subst.
    assert (Hsubrings3: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'2)
                          (RingSubmitter.submitter_rt_orders st'2)
                          0).
    {
      inversion H7; clear H7; subst.
      clear H0 H11; simpl in H1.
      destruct H1 as [Hst_preserve _].
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring3:
              exists r3,
                nth_error (RingSubmitter.submitter_rt_rings st'2) 0 = Some r3 /\
                RingSubmitter.ring_rt_static r3 = r).
    {
      inversion H7; clear H7; subst.
      clear H0 H11; simpl in H1.
      destruct H1 as [Hst_preserve _].
      destruct Hst_preserve as [Hrings_preserve _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring2 as [r2 [Hnth2 Hring2]].
      specialize (Hrings_preserve r2 Hnth2).
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H10; clear H10; subst.
    assert (Hsubrings4: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'3)
                          (RingSubmitter.submitter_rt_orders st'3)
                          0).
    {
      inversion H9; clear H9; subst.
      clear H0 H11; simpl in H1.
      destruct H1 as [_ [Hst_preserve _]].
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring4:
              exists r4,
                nth_error (RingSubmitter.submitter_rt_rings st'3) 0 = Some r4 /\
                RingSubmitter.ring_rt_static r4 = r).
    {
      inversion H9; clear H9; subst.
      clear H0 H11; simpl in H1.
      destruct H1 as [_ [Hst_preserve _]].
      destruct Hst_preserve as [Hrings_preserve _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring3 as [r3 [Hnth3 Hring3]].
      specialize (Hrings_preserve r3 Hnth3).
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H11; clear H11; subst.
    assert (Hsubrings5: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'4)
                          (RingSubmitter.submitter_rt_orders st'4)
                          0).
    {
      inversion H10; clear H10; subst.
      clear H0 H13; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring5:
              exists r5,
                nth_error (RingSubmitter.submitter_rt_rings st'4) 0 = Some r5 /\
                RingSubmitter.ring_rt_static r5 = r).
    {
      inversion H10; clear H10; subst.
      clear H0 H13; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring4 as [r4 [Hnth4 Hring4]].
      specialize (Hrings_preserve r4 Hnth4).
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H12; clear H12; subst.
    assert (Hsubrings6: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'5)
                          (RingSubmitter.submitter_rt_orders st'5)
                          0).
    {
      inversion H11; clear H11; subst.
      clear H0 H14; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring6:
              exists r6,
                nth_error (RingSubmitter.submitter_rt_rings st'5) 0 = Some r6 /\
                RingSubmitter.ring_rt_static r6 = r).
    {
      inversion H11; clear H11; subst.
      clear H0 H14; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring5 as [r5 [Hnth5 Hring5]].
      specialize (Hrings_preserve r5 Hnth5).
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H13; clear H13; subst.
    assert (Hsubrings7: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'6)
                          (RingSubmitter.submitter_rt_orders st'6)
                          0).
    {
      inversion H12; clear H12; subst.
      clear H0 H15; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring7:
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'6) 0 = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H12; clear H12; subst.
      clear H0 H15; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring6 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H14; clear H14; subst.
    assert (Hsubrings8: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'7)
                          (RingSubmitter.submitter_rt_orders st'7)
                          0).
    {
      inversion H13; clear H13; subst.
      clear H0 H16; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring8:
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'7) 0 = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H13; clear H13; subst.
      clear H0 H16; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring7 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H15; clear H15; subst.
    assert (Hsubrings9: RingSubmitter.nth_ring_has_subrings
                          (RingSubmitter.submitter_rt_rings st'8)
                          (RingSubmitter.submitter_rt_orders st'8)
                          0).
    {
      inversion H14; clear H14; subst.
      clear H0 H17; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring9:
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'8) 0 = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H14; clear H14; subst.
      clear H0 H17; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring8 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H16; clear H16; subst.
    assert (Hsubrings10: RingSubmitter.nth_ring_has_subrings
                           (RingSubmitter.submitter_rt_rings st'9)
                           (RingSubmitter.submitter_rt_orders st'9)
                           0).
    {
      inversion H15; clear H15; subst.
      clear H0 H18; simpl in H1.
      destruct H1 as [Hst_preserve _].
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring10:
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'9) 0 = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H15; clear H15; subst.
      clear H0 H18; simpl in H1.
      destruct H1 as [Hst_preserve _].
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring9 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H17; clear H17; subst.
    assert (Hsubrings11: RingSubmitter.nth_ring_has_subrings
                           (RingSubmitter.submitter_rt_rings st'10)
                           (RingSubmitter.submitter_rt_orders st'10)
                           0).
    {
      inversion H16; clear H16; subst.
      clear H0 H19; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].
      unfold RingSubmitter.subrings_preserve in Hsubrings_preserve;
        simpl in Hsubrings_preserve.
      apply Hsubrings_preserve; auto.
    }
    assert (Hring11:
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'10) 0 = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H16; clear H16; subst.
      clear H0 H19; simpl in H1.
      destruct H1 as [_ [_ Hst_preserve]].
      destruct Hst_preserve as [[Hrings_preserve [Hsubrings_preserve _]] _].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring10 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

      exists r'. split; congruence.
    }

    inversion H18; clear H18; subst.
    clear H0 H1; simpl in H19.
    destruct H19 as [Hring_skipped _].

    destruct Hring11 as [r' [Hnth11 Hring11]].
    specialize (Hring_skipped 0 r' Hsubrings11 Hnth11).
    rewrite Hring11 in Hring_skipped.

    repeat (apply in_or_app; right); auto.
  Qed.

End NoSubRings.

Section NoCancelledOrders.

  Definition has_cancelled_order
             (wst: WorldState)
             (rings: list Ring)
             (orders: list Order)
             (n m: nat) : Prop :=
    RingSubmitter.nth_ring_mth_order_cancelled
      wst (RingSubmitter.make_rt_rings rings) (RingSubmitter.make_rt_orders orders)
      n m.

  Lemma make_rt_rings_impl:
    forall n rings r,
      nth_error rings n = Some r ->
      nth_error (RingSubmitter.make_rt_rings rings) n = Some (RingSubmitter.make_rt_ring r).
  Proof.
    induction n; induction rings; try (simpl in *; congruence).
    simpl. eapply IHn; eauto.
  Qed.

  Theorem no_cancelled_orders_dealt:
    forall sender rings orders mining n m r st wst wst' retval events,
      st = RingSubmitter.make_rt_submitter_state mining orders rings ->
      has_cancelled_order wst rings orders n m ->
      nth_error rings n = Some r ->
      lr_step wst
              (MsgRingSubmitter (msg_submitRings sender orders rings mining))
              wst' retval events ->
      In (EvtRingSkipped r) events.
  Proof.
    intros until events.
    intros Hst Hcancelled Hnth Hstep.

    simpl in Hstep.
    unfold RingSubmitter.model in Hstep.
    destruct Hstep as [_ [st' Hstep]].
    specialize (Hstep sender orders rings mining).
    destruct Hstep as [_ Hstep].

    assert (Hpre:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst
                (RingSubmitter.submitter_rt_rings st)
                (RingSubmitter.submitter_rt_orders st) n m /\
              nth_error (RingSubmitter.submitter_rt_rings st) n =
              Some (RingSubmitter.make_rt_ring r)).
    {
      rewrite Hst; simpl.
      split; auto.
      eapply make_rt_rings_impl; eauto.
    }

    inversion Hstep; clear Hstep; subst.
    assert (Hinv0:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'0
                (RingSubmitter.submitter_rt_rings st'0)
                (RingSubmitter.submitter_rt_orders st'0) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'0) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H6; subst; clear H6.
      clear H0 H9; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve Hwst_preserve]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].
        destruct Hpre as [Hcancelled_pre Hring_pre].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve (RingSubmitter.make_rt_ring r) Hring_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; auto.
    }

    inversion H7; subst; clear H7.
    assert (Hinv1:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'1
                (RingSubmitter.submitter_rt_rings st'1)
                (RingSubmitter.submitter_rt_orders st'1) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'1) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H8; subst; clear H8.
      clear H0 H10; simpl in H1.
      destruct H1 as [Hst_preserve [Hwst_preserve _]].
      destruct Hinv0 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H9; subst; clear H9.
    assert (Hinv2:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'2
                (RingSubmitter.submitter_rt_rings st'2)
                (RingSubmitter.submitter_rt_orders st'2) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'2) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H7; subst; clear H7.
      clear H0 H11; simpl in H1.
      destruct H1 as [Hst_preserve [Hwst_preserve _]].
      destruct Hinv1 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H10; subst; clear H10.
    assert (Hinv3:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'3
                (RingSubmitter.submitter_rt_rings st'3)
                (RingSubmitter.submitter_rt_orders st'3) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'3) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H9; subst; clear H9.
      clear H0 H12; simpl in H1.
      destruct H1 as [_ [Hst_preserve [Hwst_preserve _]]].
      destruct Hinv2 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H11; subst; clear H11.
    assert (Hinv4:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'4
                (RingSubmitter.submitter_rt_rings st'4)
                (RingSubmitter.submitter_rt_orders st'4) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'4) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H10; subst; clear H10.
      clear H0 H13; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve Hwst_preserve]]].
      destruct Hinv3 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H12; subst; clear H12.
    assert (Hinv5:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'5
                (RingSubmitter.submitter_rt_rings st'5)
                (RingSubmitter.submitter_rt_orders st'5) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'5) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H11; subst; clear H11.
      clear H0 H14; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve Hwst_preserve]]].
      destruct Hinv4 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H13; subst; clear H13.
    assert (Hinv6:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'6
                (RingSubmitter.submitter_rt_rings st'6)
                (RingSubmitter.submitter_rt_orders st'6) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'6) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H12; subst; clear H12.
      clear H0 H15; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve Hwst_preserve]]].
      destruct Hinv5 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H14; subst; clear H14.
    assert (Hinv7:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'7
                (RingSubmitter.submitter_rt_rings st'7)
                (RingSubmitter.submitter_rt_orders st'7) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'7) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H13; subst; clear H13.
      clear H0 H16; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve Hwst_preserve]]].
      destruct Hinv6 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H15; subst; clear H15.
    assert (Hinv8:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'8
                (RingSubmitter.submitter_rt_rings st'8)
                (RingSubmitter.submitter_rt_orders st'8) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'8) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H14; subst; clear H14.
      clear H0 H17; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve Hwst_preserve]]].
      destruct Hinv7 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H16; subst; clear H16.
    assert (Hinv9:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'9
                (RingSubmitter.submitter_rt_rings st'9)
                (RingSubmitter.submitter_rt_orders st'9) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'9) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H15; subst; clear H15.
      clear H0 H18; simpl in H1.
      destruct H1 as [Hst_preserve [Hwst_preserve _]].
      destruct Hinv8 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H17; subst; clear H17.
    assert (Hinv10:
              RingSubmitter.nth_ring_mth_order_cancelled
                wst'10
                (RingSubmitter.submitter_rt_rings st'10)
                (RingSubmitter.submitter_rt_orders st'10) n m /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'10) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H16; subst; clear H16.
      clear H0 H19; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve Hwst_preserve]]].
      destruct Hinv9 as [Hcancelled_pre [r_pre [Hnth_pre Hring_pre]]].

      split.
      - apply Hwst_preserve; auto.
      - destruct Hst_preserve as [Hrings_preserve _].

        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r_pre Hnth_pre).
        destruct Hrings_preserve as [r' [Hnth' [Hring' _]]].

        exists r'. split; congruence.
    }

    inversion H18; subst; clear H18.
    clear H0; simpl in H1, H19.
    destruct H19 as [_ [Hevents' _]].

    destruct Hinv10 as [Hcancelled' [r' [Hnth' Hring']]].
    specialize (Hevents' n m r' Hcancelled' Hnth').
    rewrite Hring' in Hevents'.

    repeat (apply in_or_app; right); auto.
  Qed.

End NoCancelledOrders.

Section NoTokenMismatchOrders.

  Definition prev_order_idx (r: Ring) (n: nat) : option nat :=
    let indices := ring_orders r in
    match nth_error indices n with
    | None => None
    | Some _ => match n with
               | O => nth_error indices (length indices - 1)
               | S n' => nth_error indices n'
               end
    end.

  Definition prev_order (r: Ring) (orders: list Order) (n: nat) :
    option Order :=
    match prev_order_idx r n with
    | None => None
    | Some idx => nth_error orders idx
    end.

  Definition has_token_mismatch_orders (r: Ring) (orders: list Order) : Prop :=
    exists idx order p_order,
      nth_error orders idx = Some order /\
      prev_order r orders idx = Some p_order /\
      order_tokenS order <> order_tokenB p_order.

  Lemma nth_order_ord:
    forall n orders order,
      nth_error orders n = Some order ->
      nth_error (RingSubmitter.make_rt_orders orders) n =
      Some (RingSubmitter.make_rt_order order).
  Proof.
    induction n; induction orders; simpl;
      try (intros; congruence).
    intros; eapply IHn; eauto.
  Qed.

  Lemma nth_order_participation_index:
    forall n orders idx p,
      nth_error orders n = Some idx ->
      nth_error (RingSubmitter.make_participations orders) n = Some p ->
      RingSubmitter.part_order_idx p = idx.
  Proof.
    induction n; induction orders; simpl; try (intros; congruence).

    - intros idx p Hidx Hp.
      inversion Hidx; subst; clear Hidx.
      inversion Hp; subst; clear Hp.
      simpl; auto.

    - intros; eapply IHn; eauto.
  Qed.

  Lemma nth_order_participation_index_some:
    forall n orders idx,
      nth_error orders n = Some idx ->
      nth_error (RingSubmitter.make_participations orders) n <> None.
  Proof.
    induction n; induction orders; simpl; try (intros; congruence).
    eapply IHn; eauto.
  Qed.

  Lemma nth_order_participation:
    forall n r idx p,
      nth_error (ring_orders r) n = Some idx ->
      nth_error (RingSubmitter.ring_rt_participations (RingSubmitter.make_rt_ring r)) n = Some p ->
      RingSubmitter.part_order_idx p = idx.
  Proof.
    simpl.
    intros; eapply nth_order_participation_index; eauto.
  Qed.

  Lemma nth_order_participation_some:
    forall n r idx,
      nth_error (ring_orders r) n = Some idx ->
      nth_error (RingSubmitter.ring_rt_participations (RingSubmitter.make_rt_ring r)) n <> None.
  Proof.
    simpl. intros; eapply nth_order_participation_index_some; eauto.
  Qed.

  Lemma make_participations_length_eq:
    forall orders,
      length orders = length (RingSubmitter.make_participations orders).
  Proof.
    induction orders; simpl; congruence.
  Qed.

  Lemma prev_order_idx_ps:
    forall r n idx p,
      prev_order_idx r n = Some idx ->
      RingSubmitter.prev_ps (RingSubmitter.make_rt_ring r) n = Some p ->
      RingSubmitter.part_order_idx p = idx.
  Proof.
    intros until p; intros Horder Hp.

    unfold prev_order_idx in Horder.
    destruct (nth_error (ring_orders r) n); try congruence.
    unfold RingSubmitter.prev_ps in Hp.
    destruct (nth_error
                (RingSubmitter.ring_rt_participations (RingSubmitter.make_rt_ring r))
                n);
      try congruence.

    simpl in *.
    rewrite <- (make_participations_length_eq (ring_orders r)) in *.
    destruct n; eapply nth_order_participation; eauto.
  Qed.

  Lemma prev_order_idx_ps_some:
    forall r n idx,
      prev_order_idx r n = Some idx ->
      RingSubmitter.prev_ps (RingSubmitter.make_rt_ring r) n <> None.
  Proof.
    intros until idx; intros Horder.

    unfold prev_order_idx in Horder.
    case_eq (nth_error (ring_orders r) n).

    - intros idx' Hidx'.
      specialize (nth_order_participation_some _ _ _ Hidx');
        intros Hsome.
      unfold RingSubmitter.prev_ps.
      case_eq (nth_error (RingSubmitter.ring_rt_participations (RingSubmitter.make_rt_ring r)) n);
        try (intros; congruence).
      intros p' Hp'. simpl in *.
      rewrite Hidx' in Horder.
      destruct n.
      + rewrite <- (make_participations_length_eq (ring_orders r)) in *.
        eapply nth_order_participation_some; eauto.
      + eapply nth_order_participation_some; eauto.

    - intros Hnone.
      rewrite Hnone in Horder; congruence.
  Qed.

  Lemma prev_order_ord:
    forall r orders n order,
      prev_order r orders n = Some order ->
      RingSubmitter.prev_ord (RingSubmitter.make_rt_ring r)
               (RingSubmitter.make_rt_orders orders) n =
      Some (RingSubmitter.make_rt_order order).
  Proof.
    intros until order; intros Horder.

    unfold prev_order in Horder.
    unfold RingSubmitter.prev_ord.

    case_eq (prev_order_idx r n).

    - intros idx Hidx.
      rewrite Hidx in Horder.
      case_eq (RingSubmitter.prev_ps (RingSubmitter.make_rt_ring r) n).
      + intros p Hp.
        specialize (prev_order_idx_ps _ _ _ _ Hidx Hp);
          intros Hp_idx.
        rewrite Hp_idx.
        apply nth_order_ord; auto.
      + specialize (prev_order_idx_ps_some _ _ _ Hidx).
        intros; congruence.

    - intros Hnone; rewrite Hnone in Horder; congruence.
  Qed.

  Lemma make_rt_ring_preserve_token_mismatch:
    forall r orders,
      has_token_mismatch_orders r orders ->
      RingSubmitter.has_token_mismatch_ords
        (RingSubmitter.make_rt_ring r) (RingSubmitter.make_rt_orders orders).
  Proof.
    intros r orders Hpreserve.
    destruct Hpreserve as [idx [order [p_order [Horder [Hporder Htokens]]]]].
    exists idx, (RingSubmitter.make_rt_order order), (RingSubmitter.make_rt_order p_order).

    repeat split.

    - eapply nth_order_ord; eauto.
    - apply prev_order_ord; auto.
    - simpl; auto.
  Qed.

  Lemma prev_ps_preserve:
    forall r r',
      RingSubmitter.participations_preserve r r' ->
      forall idx p,
        RingSubmitter.prev_ps r idx = Some p ->
        exists p',
          RingSubmitter.prev_ps r' idx = Some p' /\
          RingSubmitter.part_order_idx p = RingSubmitter.part_order_idx p'.
  Proof.
    intros r r' Hpreserve idx p Hp.
    destruct Hpreserve as [Hlength Hpreserve].

    unfold RingSubmitter.prev_ps in Hp.
    case_eq (nth_error (RingSubmitter.ring_rt_participations r) idx).

    - intros p0 Hp0.
      rewrite Hp0 in Hp.

      unfold RingSubmitter.prev_ps.
      generalize (Hpreserve idx p0 Hp0); intros Hp0'.
      destruct Hp0' as [p0' [Hp0' Hp0'_idx]].
      rewrite Hp0'.

      destruct idx.
      + specialize (Hpreserve _ p Hp).
        destruct Hpreserve as [p' [Hp' Hp'_idx]].
        exists p'.
        rewrite <- Hlength.
        split; auto.

      + specialize (Hpreserve _ p Hp).
        destruct Hpreserve as [p' [Hp' Hp'_idx]].
        exists p'.
        split; auto.

    - intros Hidx; rewrite Hidx in Hp.
      inversion Hp.
  Qed.

  Lemma token_mismatch_preserve:
    forall st st' n,
      RingSubmitter.rings_preserve st st' ->
      RingSubmitter.orders_preserve st st' ->
      RingSubmitter.nth_ring_has_token_mismatch_orders st n ->
      RingSubmitter.nth_ring_has_token_mismatch_orders st' n.
  Proof.
    intros until n; intros Hrings Horders Hmismatch.

    destruct Hmismatch as [r [Hring Hmismatch]].

    specialize (Hrings n).
    destruct Hrings as [Hrings _].
    specialize (Hrings r Hring).
    destruct Hrings as [r' [Hring' [Hr' Hps]]].

    exists r'; split; auto.

    destruct Hmismatch as [idx [ord [p_ord [Hord [Hp_ord Htokens]]]]].
    exists idx.

    generalize (Horders idx); intros Horders1.
    destruct Horders1 as [Horders1 _].
    generalize (Horders1 ord Hord); clear Horders1.
    intros Hord'. destruct Hord' as [ord' [Hord' [Hord'_tokenS Hord'_tokenB]]].
    exists ord'.

    unfold RingSubmitter.prev_ord in *.
    case_eq (RingSubmitter.prev_ps r idx).

    - intros p Hp.
      rewrite Hp in Hp_ord.
      generalize (Horders (RingSubmitter.part_order_idx p)); intros Horders1.
      destruct Horders1 as [Horders1 _].
      generalize (Horders1 p_ord Hp_ord); clear Horders1.
      intros Hp_ord'. destruct Hp_ord' as [p_ord' [Hp_ord' [Hp_ord'_tokenS Hp_ord'_tokenB]]].

      exists p_ord'. split; auto.
      split; try congruence.

      specialize (prev_ps_preserve _ _ Hps _ _ Hp).
      intros Hps'.
      destruct Hps' as [p' [Hpps' Hp'_idx]].
      rewrite Hpps'.
      congruence.

    - intros Hp; rewrite Hp in Hp_ord; congruence.
  Qed.

  Theorem no_token_mismatch_orders:
    forall sender rings orders mining n r st wst wst' retval events,
      st = RingSubmitter.make_rt_submitter_state mining orders rings ->
      nth_error rings n = Some r ->
      has_token_mismatch_orders r orders ->
      lr_step wst
              (MsgRingSubmitter (msg_submitRings sender orders rings mining))
              wst' retval events ->
      In (EvtRingSkipped r) events.
  Proof.
    intros until events; intros Hst Hnth Hmismatch Hstep.

    simpl in Hstep.
    unfold RingSubmitter.model in Hstep.
    destruct Hstep as [_ [st' Hstep]].
    specialize (Hstep sender orders rings mining).
    destruct Hstep as [_ Hstep].

    assert (Hpre:
              RingSubmitter.nth_ring_has_token_mismatch_orders st n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      split.
      - subst st.
        generalize (make_rt_ring_preserve_token_mismatch _ _ Hmismatch);
          intros Hmismatch0.
        eexists; split; eauto.
        apply make_rt_rings_impl; auto.
      - exists (RingSubmitter.make_rt_ring r).
        split; auto.
        subst st; simpl.
        apply make_rt_rings_impl; auto.
    }

    inversion Hstep; subst; clear Hstep.
    assert (Hinv0:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'0 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'0) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H6; subst; clear H6.
      clear H0 H9; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve _]]].

      destruct Hpre as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H7; subst; clear H7.
    assert (Hinv1:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'1 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'1) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H8; subst; clear H8.
      clear H0 H10; simpl in H1.
      destruct H1 as [Hst_preserve _].

      destruct Hinv0 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H9; subst; clear H9.
    assert (Hinv2:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'2 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'2) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H7; subst; clear H7.
      clear H0 H11; simpl in H1.
      destruct H1 as [Hst_preserve _].

      destruct Hinv1 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H10; subst; clear H10.
    assert (Hinv3:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'3 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'3) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H9; subst; clear H9.
      clear H0 H12; simpl in H1.
      destruct H1 as [_ [Hst_preserve _]].

      destruct Hinv2 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H11; subst; clear H11.
    assert (Hinv4:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'4 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'4) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H10; subst; clear H10.
      clear H0 H13; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve _]]].

      destruct Hinv3 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H12; subst; clear H12.
    assert (Hinv5:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'5 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'5) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H11; subst; clear H11.
      clear H0 H14; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve _]]].

      destruct Hinv4 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H13; subst; clear H13.
    assert (Hinv6:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'6 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'6) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H12; subst; clear H12.
      clear H0 H15; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve _]]].

      destruct Hinv5 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H14; subst; clear H14.
    assert (Hinv7:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'7 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'7) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H13; subst; clear H13.
      clear H0 H16; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve _]]].

      destruct Hinv6 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H15; subst; clear H15.
    assert (Hinv8:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'8 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'8) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H14; subst; clear H14.
      clear H0 H17; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve _]]].

      destruct Hinv7 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H16; subst; clear H16.
    assert (Hinv9:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'9 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'9) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H15; subst; clear H15.
      clear H0 H18; simpl in H1.
      destruct H1 as [Hst_preserve _].

      destruct Hinv8 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    inversion H17; subst; clear H17.
    assert (Hinv10:
              RingSubmitter.nth_ring_has_token_mismatch_orders st'10 n /\
              exists r',
                nth_error (RingSubmitter.submitter_rt_rings st'10) n = Some r' /\
                RingSubmitter.ring_rt_static r' = r).
    {
      inversion H16; subst; clear H16.
      clear H0 H19; simpl in H1.
      destruct H1 as [_ [_ [Hst_preserve _]]].

      destruct Hinv9 as [Hmismatch0 Hr0].
      destruct Hst_preserve as [Hrings_preserve [_ Horders_preserve]].

      split.
      - eapply token_mismatch_preserve; eauto.
      - destruct Hr0 as [r0 [Hnth0 Hr0]].
        specialize (Hrings_preserve n).
        destruct Hrings_preserve as [Hrings_preserve _].
        specialize (Hrings_preserve r0 Hnth0).
        destruct Hrings_preserve as [r' [Hnth' [Hr' _]]].
        exists r'; split; congruence.
    }

    destruct Hinv10 as [Hmismatch' [r' [Hnth' Hr']]].
    inversion H18; subst; clear H18.
    simpl in H19.
    destruct H19 as [_ [_ [Hevents _]]].
    specialize (Hevents _ _ Hmismatch' Hnth').
    repeat (apply in_or_app; right); auto.
  Qed.

End NoTokenMismatchOrders.