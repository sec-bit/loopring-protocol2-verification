Require Import
        List.

Require Import
        Events
        Messages
        States
        Types.

Require Import
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

Lemma RingSubmitter_no_further_msg_once_suspended:
  forall wst msg wst' retval events,
    delegate_suspended (wst_trade_delegate_state wst) = true ->
    ~ RingSubmitter.RingSubmitter.model wst msg wst' retval events.
Proof.
Admitted.
  
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
  admit.
  admit.
  admit.
  admit.
  admit.
Admitted.
    
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
    admit.
  }
  { (* ERC20 *)
    admit.
  }
  { (* BrokerRegistry *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
  { (* OrderRegistry *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; simpl in *; intuition; subst; intuition. }
  { (* BurnRateTable *)
    destruct Hstep as [Hrequire [Htrans _]].
    destruct msg; inv Htrans; simpl in *; intuition; subst; intuition.
    admit. admit.
  }
Admitted.

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
    simpl in *; intuition; subst; auto.
  (* ERC20 prop... *)
  admit.
  simpl. clear. destruct wst. simpl. revert wst_trade_delegate_state. clear.
  induction params; auto.
  simpl. intros. erewrite IHparams. simpl. auto.
  exfalso. eauto.
Admitted.
  
Lemma owner_not_changed_if_not_killed:
  forall wst msg wst' retval events,
    lr_step wst msg wst' retval events ->
    (forall sender, msg <> MsgKill sender) ->
    (delegate_owner (wst_trade_delegate_state wst'))
    = (delegate_owner (wst_trade_delegate_state wst)).
Proof.
  intros wst msg wst' retval events Hstep Hnotkill.
  destruct msg.
  { admit. }
  { admit. }
  eapply TradeDelegate_owner_not_changed_if_not_killed; eauto.
  intros. intro. eapply Hnotkill. rewrite H. unfold MsgKill. eauto.
  { admit. }
  { admit. }
  { destruct msg; destruct Hstep as [Hrequire [Htrans _]];
      simpl in *; intuition; subst; auto. }
  { destruct msg; destruct Hstep as [Hrequire [Htrans _]];
      simpl in *; intuition; subst; auto. }
  { destruct msg; destruct Hstep as [Hrequire [Htrans _]];
      inv Htrans; simpl in *; intuition; subst; auto.
    admit.
  }
  { admit. }
Admitted.

Theorem only_owner_is_able_to_control_LPSC:
  forall msgs wst' retval events,
    (** For any execution trace msgs *)
    lr_model msgs wst' retval events ->
    (** If LPSC is not killed during execution *)
    (forall sender, ~ In (MsgKill sender) msgs) ->
    (** Then any succeeded control msg call is performed by the initial owner *)
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
