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

  Theorem withdrawToken_noauth:
    forall sender token amount wst wst' retval events,
      lr_step wst (MsgFeeHolder (msg_withdrawToken sender token amount))
              wst' retval events ->
      retval = RetBool true /\
      In (EvtTokenWithdrawn sender token amount) events.
  Proof.
    intros until events; intros Hstep.

    destruct Hstep as [Hreq [Htrans Hevents]];
      simpl in Hreq, Htrans, Hevents.
    destruct Hreq as [Hamount Htransfer].
    destruct Htransfer as [wst'' [events' Htransfer]].

    split.
    - specialize (Htrans wst'' events' Htransfer).
      destruct Htrans as [Hwst' Hretval].
      auto.
    - specialize (Hevents wst'' events' Htransfer).
      rewrite Hevents.
      apply in_or_app; right.
      constructor; auto.
  Qed.

End WithdrawTokenReqNoAuth.