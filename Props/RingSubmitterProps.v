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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
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
      destruct Hst_preserve as [Hrings_preserve _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _];
        simpl in Hrings_preserve.
      specialize (Hrings_preserve (RingSubmitter.make_rt_ring r));
        simpl in Hrings_preserve.
      apply Hrings_preserve; trivial.
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
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
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
      destruct Hst_preserve as [Hrings_preserve _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring4 as [r4 [Hnth4 Hring4]].
      specialize (Hrings_preserve r4 Hnth4).
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
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
      destruct Hst_preserve as [Hrings_preserve _].
      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring5 as [r5 [Hnth5 Hring5]].
      specialize (Hrings_preserve r5 Hnth5).
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring6 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring7 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring8 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].
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
      destruct Hst_preserve as [Hrings_preserve Hsubrings_preserve].

      specialize (Hrings_preserve 0).
      destruct Hrings_preserve as [Hrings_preserve _].

      destruct Hring10 as [r'' [Hnth'' Hring'']].
      specialize (Hrings_preserve r'' Hnth'').
      destruct Hrings_preserve as [r' [Hnth' Hring']].

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
