Require Import
        List
        Nat
        Omega
        ZArith.
Require Import
        Events
        LibModel
        Maps
        Messages
        States
        Types.
Require Import
        RingCanceller
        TradeDelegate.
Require Import
        TopModel.


Set Implicit Arguments.
Unset Strict Implicit.


Section CancellOrdersNoSideEffect.

  Definition is_order_cancelled
             (st: TradeDelegateState) (broker: address) (hash: bytes32) : Prop :=
    AH2B.get (delegate_cancelled st) (broker, hash) = true.

  Lemma setCancel_preserve:
    forall wst sender broker hash wst' retval events,
      TradeDelegate.model wst
                          (msg_setCancelled sender broker hash)
                          wst' retval events ->
      forall broker' hash',
        is_order_cancelled (wst_trade_delegate_state wst) broker' hash' ->
        is_order_cancelled (wst_trade_delegate_state wst') broker' hash'.
  Proof.
    intros until events; intros Hcall broker' hash' Hcancelled.
    destruct Hcall as [_ [Htrans _]]; simpl in Htrans.
    destruct Htrans as [Hwst _].

    unfold is_order_cancelled in *.
    rewrite Hwst; unfold wst_update_trade_delegate; simpl.

    destruct (Nat.eq_dec broker' broker);
      destruct (Nat.eq_dec hash' hash);
      subst;
      solve [ AH2B.msimpl |
              rewrite <- Hcancelled at 2;
              apply AH2B.get_upd_neq;
              simpl; intros H; destruct H as [H0 H1]; congruence ].
  Qed.

  Lemma cancel_orders_preserve:
    forall hashes sender wst wst' events,
      RingCanceller.cancel_orders wst sender hashes wst' events ->
      forall hash,
        is_order_cancelled (wst_trade_delegate_state wst) sender hash ->
        is_order_cancelled (wst_trade_delegate_state wst') sender hash.
  Proof.
    induction hashes.

    - intros until events; intros Hs.
      inversion Hs; subst; clear Hs; congruence.

    - intros until events. intros Hs hash Hcancelled.
      inversion Hs; subst; clear Hs; try congruence.
      generalize (setCancel_preserve H0 Hcancelled);
        intros Hcancelled'.
      inversion H; subst; clear H.
      eapply IHhashes; eauto.
  Qed.

  Theorem cancelOrders_no_side_effect:
    forall sender hashes wst wst' retval events,
      lr_step wst
              (MsgRingCanceller (msg_cancelOrders sender hashes))
              wst' retval events ->
      forall hash',
        is_order_cancelled (wst_trade_delegate_state wst) sender hash' ->
        is_order_cancelled (wst_trade_delegate_state wst') sender hash'.
  Proof.
    intros until events; intros Hstep.
    intros hash' Hcancelled.

    destruct Hstep as [Hreq [Htrans _]];
      simpl in Hreq, Htrans.
    destruct Hreq as [Hhashes [wst'' [events'' Hcancel_orders]]].
    destruct Htrans as [_ Htrans].
    specialize (Htrans wst'' events'' Hcancel_orders);
      subst.

    eapply cancel_orders_preserve; eauto.
  Qed.

End CancellOrdersNoSideEffect.


Section CancelAllOrdersForTradingPairNoSideEffect.

  Definition is_order_cancelled_wst_trading_pair
             (wst: WorldState) (order: Order) : Prop :=
    order_validSince order <
    AH2V.get (delegate_tradingPairCutoffs (wst_trade_delegate_state wst))
             (order_broker order, lxor (order_tokenS order) (order_tokenB order)).

  Theorem cancelAllOrdersForTradingPair_no_side_effect:
    forall sender token1 token2 cutoff wst wst' retval events,
      lr_step wst
              (MsgRingCanceller (msg_cancelAllOrdersForTradingPair sender token1 token2 cutoff))
              wst' retval events ->
      forall order,
        is_order_cancelled_wst_trading_pair wst order ->
        is_order_cancelled_wst_trading_pair wst' order.
  Proof.
    intros until events; intros Hstep order Hcancelled.
    destruct Hstep as [Hreq [Htrans _]];
      simpl in Hreq, Htrans.

    destruct Hreq as [wst'' [events' Hcall]].
    generalize (Hcall RetNone); intros Hdelegate.
    destruct Hdelegate as [Hdelegate_req [Hdelegate_trans _]];
      simpl in Hdelegate_req, Hdelegate_trans.
    destruct Hdelegate_req as [_ Hlt].
    destruct Hdelegate_trans as [Hwst'' _].

    destruct Htrans as [_ Htrans].
    specialize (Htrans wst'' events' Hcall); clear Hcall.
    subst wst''; subst wst'.

    unfold is_order_cancelled_wst_trading_pair in *; simpl.

    destruct (Nat.eq_dec sender (order_broker order));
      destruct (Nat.eq_dec (lxor (order_tokenS order) (order_tokenB order))
                           (lxor token1 token2));
      subst;
      solve [ rewrite e0 in *;
              rewrite AH2V.get_upd_eq; simpl; auto;
              eapply lt_trans; eauto |
              rewrite AH2V.get_upd_neq; simpl; auto;
              intros H; destruct H as [Hsender Hpair]; congruence ].
  Qed.

End CancelAllOrdersForTradingPairNoSideEffect.


Section CancelAllOrdersNoSideEffect.

  Definition is_order_cancelled_wst_broker
             (wst: WorldState) (order: Order) : Prop :=
    order_validSince order <
    A2V.get (delegate_cutoffs (wst_trade_delegate_state wst)) (order_broker order).

  Theorem cancelAllOrders_no_side_effect:
    forall sender cutoff wst wst' retval events,
      lr_step wst
              (MsgRingCanceller (msg_cancelAllOrders sender cutoff))
              wst' retval events ->
      forall order,
        is_order_cancelled_wst_broker wst order ->
        is_order_cancelled_wst_broker wst' order.
  Proof.
    intros until events; intros Hstep order Hcancelled.
    destruct Hstep as [Hreq [Htrans _]];
      simpl in Hreq, Htrans.

    destruct Hreq as [wst'' [events' Hcall]].
    generalize (Hcall RetNone); intros Hdelegate.
    destruct Hdelegate as [Hdelegate_req [Hdelegate_trans _]];
      simpl in Hdelegate_req, Hdelegate_trans.
    destruct Hdelegate_req as [_ Hlt].
    destruct Hdelegate_trans as [Hwst'' _].

    destruct Htrans as [_ Htrans].
    specialize (Htrans wst'' events' Hcall); clear Hcall.
    subst wst''; subst wst'.

    unfold is_order_cancelled_wst_broker in *; simpl.

    destruct (Nat.eq_dec sender (order_broker order));
      subst; A2V.msimpl; solve [ omega | auto ].
  Qed.

End CancelAllOrdersNoSideEffect.


Section CancelAllOrdersOfOwnerNoSideEffect.

  Definition is_order_cancelled_wst_broker_owner
             (wst: WorldState) (order: Order) : Prop :=
    order_validSince order <
    AA2V.get (delegate_cutoffsOwner (wst_trade_delegate_state wst))
             (order_broker order, order_owner order).

  Theorem cancelAllOrdersOfOwner_no_side_effect:
    forall sender owner cutoff wst wst' retval events,
      lr_step wst
              (MsgRingCanceller (msg_cancelAllOrdersOfOwner sender owner cutoff))
              wst' retval events ->
      forall order,
        is_order_cancelled_wst_broker_owner wst order ->
        is_order_cancelled_wst_broker_owner wst' order.
  Proof.
    intros until events; intros Hstep order Hcancelled.
    destruct Hstep as [Hreq [Htrans _]];
      simpl in Hreq, Htrans.

    destruct Hreq as [wst'' [events' Hcall]].
    generalize (Hcall RetNone); intros Hdelegate.
    destruct Hdelegate as [Hdelegate_req [Hdelegate_trans _]];
      simpl in Hdelegate_req, Hdelegate_trans.
    destruct Hdelegate_req as [_ Hlt].
    destruct Hdelegate_trans as [Hwst'' _].

    destruct Htrans as [_ Htrans].
    specialize (Htrans wst'' events' Hcall); clear Hcall.
    subst wst''; subst wst'.

    unfold is_order_cancelled_wst_broker_owner in *; simpl.

    destruct (Nat.eq_dec sender (order_broker order));
      destruct (Nat.eq_dec owner (order_owner order));
      subst;
      solve [ AA2V.msimpl; omega |
              rewrite AA2V.get_upd_neq; simpl;
              [ auto |
                intros H; destruct H as [Hbroker Howner]; congruence ] ].
  Qed.

End CancelAllOrdersOfOwnerNoSideEffect.


Section CancelAllOrdersForTradingPairOfOwnerNoSideEffect.

  Definition is_order_cancelled_wst_trading_pair_owner
             (wst: WorldState) (order: Order) : Prop :=
    order_validSince order <
    AAH2V.get (delegate_tradingPairCutoffsOwner (wst_trade_delegate_state wst))
              (order_broker order,
               order_owner order,
               lxor (order_tokenS order) (order_tokenB order)).

  Theorem cancelAllOrdersForTradingPairOfOwner_no_side_effect:
    forall sender owner token1 token2 cutoff wst wst' retval events,
      lr_step wst
              (MsgRingCanceller (msg_cancelAllOrdersForTradingPairOfOwner
                                   sender owner token1 token2 cutoff))
              wst' retval events ->
      forall order,
        is_order_cancelled_wst_trading_pair_owner wst order ->
        is_order_cancelled_wst_trading_pair_owner wst' order.
  Proof.
    intros until events; intros Hstep order Hcancelled.
    destruct Hstep as [Hreq [Htrans _]];
      simpl in Hreq, Htrans.

    destruct Hreq as [wst'' [events' Hcall]].
    generalize (Hcall RetNone); intros Hdelegate.
    destruct Hdelegate as [Hdelegate_req [Hdelegate_trans _]];
      simpl in Hdelegate_req, Hdelegate_trans.
    destruct Hdelegate_req as [_ Hlt].
    destruct Hdelegate_trans as [Hwst'' _].

    destruct Htrans as [_ Htrans].
    specialize (Htrans wst'' events' Hcall); clear Hcall.
    subst wst''; subst wst'.

    unfold is_order_cancelled_wst_trading_pair_owner in *; simpl.

    destruct (Nat.eq_dec sender (order_broker order));
      destruct (Nat.eq_dec owner (order_owner order));
      destruct (Nat.eq_dec (lxor (order_tokenS order) (order_tokenB order))
                           (lxor token1 token2));
      subst;
      solve [ rewrite e1 in *;
              rewrite AAH2V.get_upd_eq; simpl; auto;
              eapply lt_trans; eauto |
              rewrite AAH2V.get_upd_neq; simpl; auto;
              intros H; destruct H as [[Hsender Howner] Hpair]; congruence ].
  Qed.

End CancelAllOrdersForTradingPairOfOwnerNoSideEffect.