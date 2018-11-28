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
