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
        ERC20
        FeeHolder
        TradeDelegate.
Require Import
        TopModel.


Section WithdrawBurnedReqAuth.

  Theorem withdrawBurn_req_auth:
    forall sender wst,
      ~ FeeHolder.is_authorized wst sender ->
      forall token amount,
        ~ (exists wst' retval events,
              lr_step wst (MsgFeeHolder (msg_withdrawBurned sender token amount))
                      wst' retval events).
  Proof.
    intros sender wst Hnot_auth token amount Hstep.

    destruct Hstep as [ wst' [retval [events Hstep]]].
    destruct Hstep as [Hreq _]; simpl in Hreq.
    destruct Hreq as [_ Hauth].
    congruence.
  Qed.

End WithdrawBurnedReqAuth.


Section WithdrawTokenReqNoAuth.

  Theorem withdrawToken_req_noauth:
    forall sender wst,
      ~ FeeHolder.is_authorized wst sender ->
      forall token amount wst' retval events,
        lr_step wst (MsgFeeHolder (msg_withdrawToken sender token amount))
                wst' retval events ->
        In (EvtTokenWithdrawn sender token amount) events.
  Proof.
    intros sender wst Hsender_noauth.
    intros until events; intros Hstep.

    destruct Hstep as [Hreq [_ Hevents]];
      simpl in Hreq, Hevents.
    destruct Hreq as [Hamount [wst'' [events' Htransfer]]].

    specialize (Hevents wst'' events' Htransfer).
    rewrite Hevents.

    apply in_or_app; right.
    constructor; auto.
  Qed.

End WithdrawTokenReqNoAuth.