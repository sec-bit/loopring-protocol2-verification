Require Import
        List.

Require Import
        Events
        Messages
        States
        Types.

Require Import
        FeeHolder
        TopModel.

Ltac inv H := inversion H; subst; simpl in *; clear H.


(** * Axioms about msg sender *)
Axiom RingSubmitter_msg_sender_not_zero:
  forall msg sender orders rings mining,
    msg = msg_submitRings sender orders rings mining ->
    sender <> 0.

Definition RingCancellerMsg_sender (msg: RingCancellerMsg) : address :=
  match msg with
  | msg_cancelOrders sender _ => sender
  | msg_cancelAllOrdersForTradingPair sender _ _ _  => sender
  | msg_cancelAllOrders sender _ => sender
  | msg_cancelAllOrdersForTradingPairOfOwner sender _ _ _ _ => sender
  | msg_cancelAllOrdersOfOwner sender _ _ => sender
  end.

Axiom RingCanceller_msg_sender_not_zero:
  forall msg sender,
    RingCancellerMsg_sender msg = sender ->
    sender <> 0.

Definition TradeDelegateMsg_sender (msg: TradeDelegateMsg) : address :=
  match msg with
  | msg_authorizeAddress sender _
  | msg_deauthorizeAddress sender _
  | msg_isAddressAuthorized sender _
  | msg_batchTransfer sender _
  | msg_batchUpdateFilled sender _
  | msg_setCancelled sender _ _
  | msg_setCutoffs sender _ _
  | msg_setTradingPairCutoffs sender _ _ _
  | msg_setCutoffsOfOwner sender _ _ _
  | msg_setTradingPairCutoffsOfOwner sender _ _ _ _
  | msg_batchGetFilledAndCheckCancelled sender _
  | msg_suspend sender
  | msg_resume sender
  | msg_kill sender
    => sender
  end.

Axiom TradeDelegateMsg_sender_not_zero:
  forall msg sender,
    TradeDelegateMsg_sender msg = sender ->
    sender <> 0.

Inductive MsgTypeTradeDelegate : Type :=
| TransactionMsg
| ControlMsg
| View.

Definition TradeDelegateMsgType (msg: TradeDelegateMsg) : MsgTypeTradeDelegate :=
  match msg with
  | msg_authorizeAddress sender _
  | msg_deauthorizeAddress sender _
  | msg_suspend sender
  | msg_resume sender
  | msg_kill sender
    => ControlMsg

  | msg_batchTransfer sender _
  | msg_batchUpdateFilled sender _
  | msg_setCancelled sender _ _
  | msg_setCutoffs sender _ _
  | msg_setTradingPairCutoffs sender _ _ _
  | msg_setCutoffsOfOwner sender _ _ _
  | msg_setTradingPairCutoffsOfOwner sender _ _ _ _
    =>TransactionMsg

  | msg_isAddressAuthorized sender _
  | msg_batchGetFilledAndCheckCancelled sender _
    => View
  end.

(** message corresponds to transactions,
    notably RingSubmitter/RingCanceller messages *)
Definition transaction_msg (msg: Message) : Prop :=
  match msg with
  | MsgRingSubmitter _
  | MsgRingCanceller _
    => True
  | MsgTradeDelegate msg'
    => TradeDelegateMsgType msg' = TransactionMsg
  | _
    => False
  end.

(** event corresponds to transactions *)
Definition transaction_event (evt: Event) : Prop :=
  match evt with
  | EvtAddressAuthorized _
  | EvtAddressDeauthorized _
  | EvtOrderCancelled _ _
  | EvtAllOrdersCancelledForTradingPair _ _ _ _
  | EvtAllOrdersCancelled _ _
  | EvtOrdersCancelledByBroker _ _ _
  | EvtAllOrdersCancelledForTradingPairByBroker _ _ _ _ _
  | EvtAllOrdersCancelledByBroker _ _ _
  | EvtOwnershipTransferred _ _
    => True
  | _
    => False
  end.

(** * ERC20 Axioms *)
Axiom ERC20s_do_not_modify_TradeDelegate_state:
  forall wst msg wst' retval events,
    ERC20.ERC20s.model wst msg wst' retval events ->
    wst_trade_delegate_state wst' = wst_trade_delegate_state wst.

(** * BrokerInterceptor Axioms *)
Axiom broker_interceptor_does_not_change_trade_delegate_state:
  forall wst msg wst' retval events,
    lr_step wst (MsgBrokerInterceptor msg) wst' retval events ->
    wst_trade_delegate_state wst' = wst_trade_delegate_state wst.

(** * RingSubmitter Axioms *)
Axiom RingSubmitter_no_further_msg_once_suspended:
  forall wst msg wst' retval events,
    delegate_suspended (wst_trade_delegate_state wst) = true ->
    ~ RingSubmitter.RingSubmitter.model wst msg wst' retval events.

Axiom RingSubmitter_does_not_change_trade_delegate_owner:
  forall wst msg wst' retval events,
    lr_step wst (MsgRingSubmitter msg) wst' retval events ->
    delegate_owner (wst_trade_delegate_state wst') = delegate_owner (wst_trade_delegate_state wst).

(** * Lemmas *)
Lemma lr_steps_partition:
  forall wst msgs msg msgs' events wst' retval,
    lr_steps wst (msgs ++ msg :: msgs') wst' retval events ->
    exists wst0 wst1 retval0 retval1 events0 events1 events',
      lr_steps wst msgs wst0 retval0 events0
      /\ lr_step wst0 msg wst1 retval1 events1
      /\ lr_steps wst1 msgs' wst' retval events'
      /\ events0 ++ events1 ++ events' = events.
Proof.
  intros. remember (msgs ++ msg :: msgs') as msgs0.
  revert msgs msg msgs' Heqmsgs0. induction H.
  intros. subst; destruct msgs0; inv Heqmsgs0.
  subst. intros.
  destruct msgs; simpl in *.

  inv Heqmsgs0. do 7 eexists.
  split. econstructor; auto.
  split. eauto.
  split. eauto. eauto.

  inv Heqmsgs0. edestruct IHlr_steps. eauto.
  destruct H as (wst1 & retval0 & retval1 & events0 & events1 & events'''
                 & Hsteps0 & Hstep & Hsteps' & Hevents).
  do 7 eexists.
  split. eapply lr_steps_cons; eauto.
  split. eauto.
  split. eauto. rewrite <- Hevents, app_assoc_reverse.  auto.
Qed.

Lemma TradeDelegate_view_msg_state_unchanged:
  forall wst msg wst' retval events,
    TradeDelegate.TradeDelegate.model wst msg wst' retval events ->
    TradeDelegateMsgType msg = View ->
    wst' = wst.
Proof.
  intros wst msg wst' retval events Hstep HmsgType.
  destruct msg eqn:Hmsg; try discriminate;
    destruct Hstep as [_ [Htrans _]].
  inv Htrans; auto.
  inv Htrans; auto.
Qed.





(** * No further LPSC transactions once TradeDelegate is suspended *)

Definition MsgSuspend (sender: address) : Message :=
  MsgTradeDelegate (msg_suspend sender).

Definition MsgResume (sender: address) : Message :=
  MsgTradeDelegate (msg_resume sender).

Lemma suspend_world_state:
  forall wst wst' retval owner events,
    lr_step wst (MsgSuspend owner) wst' retval events ->
    delegate_suspended (wst_trade_delegate_state wst') = true.
Proof.
  intros wst wst' retval owner events [_ [[Htrans _] _]].
  simpl in *. rewrite Htrans. auto.
Qed.

Lemma TradeDelegate_no_further_transaction_msg_once_suspended:
  forall wst msg wst' retval events,
    delegate_suspended (wst_trade_delegate_state wst) = true ->
    TradeDelegate.TradeDelegate.model wst msg wst' retval events ->
    TradeDelegateMsgType msg <> TransactionMsg.
Proof.
  intros. destruct H0 as [Hrequire _].
  destruct msg eqn:Hmsg; simpl in *; intuition;
    repeat match goal with
           | H: TradeDelegate.TradeDelegate.authorized_and_nonsuspended _ _ |- _ =>
             destruct H
           | H: TradeDelegate.TradeDelegate.is_not_suspended _ |- _ =>
             unfold TradeDelegate.TradeDelegate.is_not_suspended in H
           end;
    try congruence.
Qed.

Lemma RingCanceller_no_further_msg_once_suspended:
  forall wst msg wst' retval events,
    delegate_suspended (wst_trade_delegate_state wst) = true ->
    ~ RingCanceller.RingCanceller.model wst msg wst' retval events.
Proof.
  intros. intro. destruct H0 as [Hrequire _].
  destruct msg eqn:Hmsg; simpl in *.

  intuition destruct H1 as (? & ? & ?). inv H1; auto.
  eapply TradeDelegate_no_further_transaction_msg_once_suspended.
  eauto. eauto. simpl. auto.

  destruct Hrequire as (? & ? & ?).
  eapply TradeDelegate_no_further_transaction_msg_once_suspended.
  eauto. eauto. simpl. auto.

  destruct Hrequire as (? & ? & ?).
  eapply TradeDelegate_no_further_transaction_msg_once_suspended.
  eauto. eauto. simpl. auto.

  destruct Hrequire as (? & ? & ?).
  eapply TradeDelegate_no_further_transaction_msg_once_suspended.
  eauto. eauto. simpl. auto.

  destruct Hrequire as (? & ? & ?).
  eapply TradeDelegate_no_further_transaction_msg_once_suspended.
  eauto. eauto. simpl. auto.

  Unshelve. all: exact RetNone.
Qed.

Local Hint Resolve
      TradeDelegate_no_further_transaction_msg_once_suspended
      RingCanceller_no_further_msg_once_suspended
      RingSubmitter_no_further_msg_once_suspended.

Lemma FeeHolder_does_not_modify_trade_delegate_state:
  forall wst msg wst' retval events,
    lr_step wst (MsgFeeHolder msg) wst' retval events ->
    wst_trade_delegate_state wst' = wst_trade_delegate_state wst.
Proof.
  intros wst msg wst' retval events Hstep.
  destruct msg eqn:Hmsg; destruct Hstep as [Hrequire [Htrans _]];
    simpl in *.

  {
    destruct Hrequire as [[Hvalue Htransfer] Hauth].
    destruct Htransfer as [wst'' [events' Hcall]].

    specialize (Htrans wst'' events' Hcall).
    destruct Htrans as [Hwst' Hretval].
    subst wst'; subst retval.

    unfold FeeHolder.transfer_withdraw_succeed in Hcall.
    apply ERC20s_do_not_modify_TradeDelegate_state in Hcall.
    rewrite Hcall; simpl; auto.
  }

  {
    destruct Hrequire as [Hvalue Htransfer].
    destruct Htransfer as [wst'' [events' Hcall]].

    specialize (Htrans wst'' events' Hcall).
    destruct Htrans as [Hwst' Hretval].
    subst wst'; subst retval.

    unfold FeeHolder.transfer_withdraw_succeed in Hcall.
    apply ERC20s_do_not_modify_TradeDelegate_state in Hcall.
    rewrite Hcall; simpl; auto.
  }

  {
    destruct Hrequire as [wst0 [events0 Hcall0]].

    destruct Htrans as [Hretval Hwst'].
    subst retval; subst wst'.

    eapply TradeDelegate_view_msg_state_unchanged in Hcall0; eauto.
    subst. clear. revert wst. induction params; auto.
    intro. simpl.
    rewrite (IHparams (FeeHolder.FeeHolder.wst_add_fee
                         wst (feeblncs_token a)
                         (feeblncs_owner a)
                         (feeblncs_value a))).
    simpl; auto.
  }
Qed.

Lemma always_suspended_if_not_resumed:
  forall wst msg wst' retval events,
    delegate_suspended (wst_trade_delegate_state wst) = true ->
    lr_step wst msg wst' retval events ->
    (forall sender, msg <> MsgResume sender) ->
    delegate_suspended (wst_trade_delegate_state wst') = true.
Proof.
  intros. destruct msg.
  exfalso; eapply RingSubmitter_no_further_msg_once_suspended; eauto.
  exfalso; eapply RingCanceller_no_further_msg_once_suspended; eauto.
  { pose proof H as Hsuspend.
    eapply TradeDelegate_no_further_transaction_msg_once_suspended in H; eauto.
    destruct msg; simpl in *; try contradiction.
    destruct H0 as [_ [[Htrans _] _]]. subst. simpl; auto.
    destruct H0 as [_ [[Htrans _] _]]. subst. simpl; auto.
    destruct H0 as [_ [[Htrans _] _]]. subst. simpl; auto.
    destruct H0 as [_ [[Htrans _] _]]. subst. simpl; auto.
    destruct H0 as [Hrequire _]. exfalso. inv Hrequire. congruence.
    exfalso; eapply H1; unfold MsgResume; eauto.
    destruct H0 as [_ [[Htrans _] _]]. subst. simpl; auto. }
  erewrite FeeHolder_does_not_modify_trade_delegate_state; eauto.
  erewrite ERC20s_do_not_modify_TradeDelegate_state; eauto.
  { (* BrokerRegistry *)
    destruct H0 as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
  { (* OrderRegistry *)
    destruct H0 as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
  { (* BurnRateTable *)
    destruct H0 as [Hrequire [Htrans _]].
    destruct msg; inv Htrans; simpl in *; intuition; subst; intuition.
    unfold BurnRateTable.upgradetier in H3. simpl in H3. inv H3.
    erewrite ERC20s_do_not_modify_TradeDelegate_state; eauto. }
  { (* BrokerInterceptor *)
    erewrite broker_interceptor_does_not_change_trade_delegate_state; eauto.
  }
  { (* BurnManager *)
    destruct H0 as [Hrequire [Htrans _]].
    destruct msg; simpl in *. clear H1. destruct Htrans as (events' & A & B & C & D & E).
    simpl in E. intuition. subst.
    erewrite ERC20s_do_not_modify_TradeDelegate_state; try eexact H2.
    erewrite FeeHolder_does_not_modify_trade_delegate_state; eauto. }
  { (* OrderBook *)
    destruct H0 as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
Qed.

Theorem no_further_LPSC_transaction_once_suspended:
  forall msgs owner msgs' events wst' retval,
    lr_model (msgs ++ MsgSuspend owner :: msgs') wst' retval events ->
    (forall sender', ~ In (MsgResume sender') msgs') ->
    (forall msg, In msg msgs' -> ~ transaction_msg msg).
Proof.
  intros msgs owner msgs' events wst' retval Hsteps.
  apply lr_steps_partition in Hsteps.
  destruct Hsteps as (wst0 & wst1 & retval0 & retval1 & events0 & events1 & events'
                      & Hpre & Hsuspend & Hsteps & Hevents).
  clear events0 retval0 events0 Hpre Hevents.
  apply suspend_world_state in Hsuspend.
  revert Hsuspend Hsteps. clear. intro Hsuspended.
  induction 1; subst.
  intros. inv H0.
  intros. inv H1.
  { revert H0 Hsuspended H; clear; intros. intro.
    destruct msg0; simpl in *; try contradiction.
    (* RingSubmitter *)
    eapply RingSubmitter_no_further_msg_once_suspended; eauto.
    (* RingCanceller *)
    eapply RingCanceller_no_further_msg_once_suspended; eauto.
    (* TradeDelegate *)
    eapply TradeDelegate_no_further_transaction_msg_once_suspended; eauto.
  }
  { apply IHHsteps in H2; auto.
    eapply always_suspended_if_not_resumed; eauto.
    intros. intro. eapply H; eauto.
    intros. intro. eapply H; eauto.
  }
Qed.

(** * No futher LPSC transactions once TradeDelegate is killed *)

Definition EvtKill (owner: address) : Event :=
  EvtOwnershipTransferred owner 0.

Definition MsgKill (owner: address) : Message :=
  MsgTradeDelegate (msg_kill owner).

Lemma kill_world_state:
  forall wst wst' retval owner events,
    lr_step wst (MsgKill owner) wst' retval events ->
    delegate_owner (wst_trade_delegate_state wst') = 0
    /\ delegate_suspended (wst_trade_delegate_state wst') = true.
Proof.
  intros wst wst' retval owner events [Hrequire [[Htrans _] _]].
  simpl in *. rewrite Htrans. simpl. split; auto. clear Htrans.
  destruct Hrequire.
  unfold TradeDelegate.TradeDelegate.is_not_suspended in H0.
  destruct (delegate_suspended _); try discriminate; auto.
Qed.

Lemma TradeDelegate_no_further_control_msg_once_killed:
  forall wst msg wst' retval events,
    delegate_owner (wst_trade_delegate_state wst) = 0 ->
    TradeDelegate.TradeDelegate.model wst msg wst' retval events ->
    TradeDelegateMsgType msg <> ControlMsg.
Proof.
  intros wst msg wst' retval events Hkilled Hstep.
  destruct Hstep as [Hrequire _].
  destruct msg eqn:Hmsg; simpl in *; intuition;
    try discriminate;
    unfold TradeDelegate.TradeDelegate.is_owner in *;
    try rewrite Hkilled in *;
    try (eapply (TradeDelegateMsg_sender_not_zero msg sender);
         subst; try assumption; auto; fail).
Qed.

Local Hint Resolve
      TradeDelegate_no_further_control_msg_once_killed.

Lemma kill_inv:
  forall wst msg wst' retval events,
    delegate_owner (wst_trade_delegate_state wst) = 0 ->
    delegate_suspended (wst_trade_delegate_state wst) = true ->
    lr_step wst msg wst' retval events ->
    delegate_owner (wst_trade_delegate_state wst') = 0
    /\ delegate_suspended (wst_trade_delegate_state wst') = true.
Proof.
  intros wst msg wst' retval events Hkilled Hsuspended Hstep.
  destruct msg; simpl in *; try (contradict Hstep; eauto; fail).
  destruct (TradeDelegateMsgType msg) eqn:HmsgType;
    try (contradict HmsgType; eauto; fail).
  eapply TradeDelegate_view_msg_state_unchanged in HmsgType; eauto. subst; auto.
  { (* FeeHolder *)
    erewrite FeeHolder_does_not_modify_trade_delegate_state; eauto.
  }
  { (* ERC20 *)
    erewrite ERC20s_do_not_modify_TradeDelegate_state; eauto.
  }
  { (* BrokerRegistry *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
  { (* OrderRegistry *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
  { (* BurnRateTable *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; inv Htrans; simpl in *; subst; try (intuition; fail).
    inv H1. erewrite ERC20s_do_not_modify_TradeDelegate_state; eauto. }
  { (* BrokerInterceptor *)
    erewrite broker_interceptor_does_not_change_trade_delegate_state; eauto.
  }
  { (* BurnManager *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *. destruct Htrans as (events' & A & B & C & D & E).
    simpl in E. destruct E. destruct H0. destruct H1 as (F & G & I). subst.
    erewrite ERC20s_do_not_modify_TradeDelegate_state; try eexact H0.
    erewrite FeeHolder_does_not_modify_trade_delegate_state; eauto. }
  { (* OrderBook *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
Qed.

Theorem no_further_LPSC_transaction_once_killed:
  forall msgs owner msgs' events wst' retval,
    lr_model (msgs ++ MsgKill owner :: msgs') wst' retval events ->
    (forall msg, In msg msgs' -> ~ transaction_msg msg).
Proof.
  intros msgs owner msgs' events wst' retval Hsteps.
  apply lr_steps_partition in Hsteps.
  destruct Hsteps as (wst0 & wst1 & retval0 & retval1 & events0 & events1 & events'
                      & Hpre & Hkill & Hsteps & Hevents).
  clear events0 retval0 events0 Hpre Hevents.
  apply kill_world_state in Hkill.
  revert Hkill Hsteps. clear. intros [Hkilled Hsuspended].
  induction 1; subst.

  intros. inv H.
  intros. inv H.
  revert H0 Hkilled Hsuspended; clear; intros. intro.
  destruct msg0; simpl in *; try contradiction.
  (* RingSubmitter *)
  { eapply RingSubmitter_no_further_msg_once_suspended; eauto. }
  (* RingCanceller *)
  { eapply RingCanceller_no_further_msg_once_suspended; eauto. }
  (* TradeDelegate *)
  { eapply TradeDelegate_no_further_transaction_msg_once_suspended; eauto. }

  eapply kill_inv in H0; eauto. eapply IHHsteps; intuition.
Qed.

(** * LPSC cannot be resumed once killed *)
Theorem LPSC_cannot_be_resumed_once_killed:
  forall msgs owner msgs' events wst' retval,
    lr_model (msgs ++ MsgKill owner :: msgs') wst' retval events ->
    (forall msg sender, In msg msgs' -> msg <> MsgResume sender).
Proof.
  intros msgs owner msgs' events wst' retval Hsteps.
  apply lr_steps_partition in Hsteps.
  destruct Hsteps as (wst0 & wst1 & retval0 & retval1 & events0 & events1 & events'
                      & Hpre & Hkill & Hsteps & Hevents).
  clear events0 retval0 events0 Hpre Hevents.
  apply kill_world_state in Hkill.
  revert Hkill Hsteps. clear. intros [Hkilled Hsuspended].
  induction 1; subst.

  intros. inv H.
  intros. inv H.
  { destruct msg0; simpl in *; try (intro; discriminate; fail).
    eapply TradeDelegate_no_further_control_msg_once_killed in H0; eauto.
    intro. inv H. contradiction. }
  { eapply kill_inv in H0; eauto.
    eapply IHHsteps; intuition. }
Qed.


(** * Only owner (of TradeDelegate) is able to suspend/resume/kill LPSC *)
Lemma TradeDelegate_ControlMsg_sender_is_owner:
  forall wst msg wst' retval events,
    TradeDelegate.TradeDelegate.model wst msg wst' retval events ->
    TradeDelegateMsgType msg = ControlMsg ->
    TradeDelegateMsg_sender msg = (delegate_owner (wst_trade_delegate_state wst)).
Proof.
  intros wst msg wst' retval events Hstep HmsgType.
  destruct msg; inv HmsgType; symmetry;
    destruct Hstep as [Hrequire _];
    inv Hrequire; auto.
Qed.

Lemma TradeDelegate_owner_not_changed_if_not_killed:
  forall wst msg wst' retval events,
    TradeDelegate.TradeDelegate.model wst msg wst' retval events ->
    (forall sender, msg <> msg_kill sender) ->
    (delegate_owner (wst_trade_delegate_state wst'))
    = (delegate_owner (wst_trade_delegate_state wst)).
Proof.
  intros wst msg wst' retval events Hstep Hnotkill.
  destruct msg eqn:Hmsg; destruct Hstep as [Hrequire [Htrans _]];
    simpl in *; try (intuition; subst; auto; fail).
  { intuition. subst.
    destruct H0 as (wst'' & events' & Htrans).
    erewrite H2; try exact Htrans.
    revert Htrans. clear. revert wst events'.
    induction params; simpl; intros.
    inv Htrans; auto.
    inv H. inv Htrans. inv H. inv H.
    erewrite IHparams; try eexact H1.
    erewrite ERC20s_do_not_modify_TradeDelegate_state; eauto. }
  { intuition. rewrite H0. simpl.
    clear. generalize (wst_trade_delegate_state wst). clear.
    induction params; auto.
    intros. simpl. rewrite IHparams. auto. }
  exfalso. eapply Hnotkill. eauto.
Qed.

Lemma owner_not_changed_if_not_killed:
  forall wst msg wst' retval events,
    lr_step wst msg wst' retval events ->
    (forall sender, msg <> MsgKill sender) ->
    (delegate_owner (wst_trade_delegate_state wst'))
    = (delegate_owner (wst_trade_delegate_state wst)).
Proof.
  intros wst msg wst' retval events Hstep Hnotkill.
  destruct msg.
  { (* RingSubmitter *)
    clear Hnotkill.
    eapply RingSubmitter_does_not_change_trade_delegate_owner; eauto.
  }
  { (* RingCanceller *)
    clear Hnotkill.
    destruct msg eqn:Hmsg; destruct Hstep as [Hrequire [Htrans _]];
      simpl in *; intuition; subst.
    { destruct H0 as (wst'' & events' & Hstep).
      erewrite H2; try exact Hstep. clear H2.
      revert H wst events' Hstep. clear. intro H. induction order_hashes.
      intros. contradiction.
      intros. clear H. destruct order_hashes.
      inv Hstep. inv H. inv H. inv H1; inv H.
      erewrite TradeDelegate_owner_not_changed_if_not_killed; eauto.
      intros. intro. discriminate.
      inv Hstep; inv H.
      erewrite IHorder_hashes; try eassumption.
      erewrite TradeDelegate_owner_not_changed_if_not_killed; eauto.
      intros. intro. discriminate.
      intros. discriminate. }
    { destruct Hrequire as (wst'' & events' & Hstep).
      erewrite H0; try exact Hstep. clear H0.
      unfold RingCanceller.RingCanceller.set_trading_pair_cutoffs in Hstep.
      specialize (Hstep RetNone).
      erewrite TradeDelegate_owner_not_changed_if_not_killed; eauto.
      intros. intro. discriminate. }
    { destruct Hrequire as (wst'' & events' & Hstep).
      erewrite H0; try exact Hstep. clear H0.
      unfold RingCanceller.RingCanceller.set_trading_pair_cutoffs in Hstep.
      specialize (Hstep RetNone).
      erewrite TradeDelegate_owner_not_changed_if_not_killed; eauto.
      intros. intro. discriminate. }
    { destruct Hrequire as (wst'' & events' & Hstep).
      erewrite H0; try exact Hstep. clear H0.
      unfold RingCanceller.RingCanceller.set_trading_pair_cutoffs in Hstep.
      specialize (Hstep RetNone).
      erewrite TradeDelegate_owner_not_changed_if_not_killed; eauto.
      intros. intro. discriminate. }
    { destruct Hrequire as (wst'' & events' & Hstep).
      erewrite H0; try exact Hstep. clear H0.
      unfold RingCanceller.RingCanceller.set_trading_pair_cutoffs in Hstep.
      specialize (Hstep RetNone).
      erewrite TradeDelegate_owner_not_changed_if_not_killed; eauto.
      intros. intro. discriminate. }
  }
  { eapply TradeDelegate_owner_not_changed_if_not_killed; eauto.
    intros. intro. eapply Hnotkill. rewrite H. unfold MsgKill. eauto. }
  { erewrite FeeHolder_does_not_modify_trade_delegate_state; eauto. }
  { erewrite ERC20s_do_not_modify_TradeDelegate_state; eauto. }
  { destruct msg; destruct Hstep as [Hrequire [Htrans _]];
      simpl in *; intuition; subst; auto. }
  { destruct msg; destruct Hstep as [Hrequire [Htrans _]];
      simpl in *; intuition; subst; auto. }
  { destruct msg; destruct Hstep as [Hrequire [Htrans _]];
      inv Htrans; simpl in *; intuition; subst; auto.
    inv H1.
    erewrite ERC20s_do_not_modify_TradeDelegate_state; eauto. }
  { (* BrokerInterceptor *)
    erewrite broker_interceptor_does_not_change_trade_delegate_state; eauto. }
  { (* BurnManager *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *. destruct Htrans as (events' & A & B & C & D & E).
    simpl in E. destruct E. destruct H0. destruct H1 as (F & G & I). subst.
    erewrite ERC20s_do_not_modify_TradeDelegate_state; try eexact H0.
    erewrite FeeHolder_does_not_modify_trade_delegate_state; eauto. }
  { (* OrderBook *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
Qed.

Theorem only_owner_is_able_to_control_LPSC:
  forall msgs wst' retval events,
    (** For any execution trace [msgs] *)
    lr_model msgs wst' retval events ->
    (** If LPSC is not killed during execution *)
    (forall sender, ~ In (MsgKill sender) msgs) ->
    (** Then any succeeded control message call is performed by the initial owner *)
    (forall msg,
        In (MsgTradeDelegate msg) msgs ->
        TradeDelegateMsgType msg = ControlMsg ->
        TradeDelegateMsg_sender msg = delegate_owner (wst_trade_delegate_state wst_init)).
Proof.
  unfold lr_model. generalize wst_init.
  induction 1; intros; subst.
  inv H1.
  inv H3.
  eapply TradeDelegate_ControlMsg_sender_is_owner; eauto.
  eapply IHlr_steps in H4. rewrite H4.
  eapply owner_not_changed_if_not_killed.
  eauto. intros. intro. eapply H2. left. eauto.
  intros. intro. eapply H2. right. eauto.
  auto.
Qed.

(** * Only authorized users are able to fill/cancel orders *)
Theorem only_authorized_contracts_are_able_to_fill_or_cancel_orders:
  forall wst msg wst' retval events,
    lr_step wst (MsgTradeDelegate msg) wst' retval events ->
    TradeDelegateMsgType msg = TransactionMsg ->
    TradeDelegate.TradeDelegate.is_authorized_address
      (wst_trade_delegate_state wst) (TradeDelegateMsg_sender msg).
Proof.
  intros wst msg wst' retval events Hstep HmsgType.
  destruct msg eqn:Hmsg; destruct Hstep as [Hrequire _];
    subst; simpl in *; intuition; try discriminate.
  destruct H. auto.
  destruct Hrequire. auto.
  destruct Hrequire. auto.
  destruct H. auto.
  destruct H. auto.
  destruct H. auto.
  destruct H. auto.
Qed.
