Require Import
        List.

Require Import
        Events
        Messages
        States
        Types.

Require Import
        BurnManager
        FeeHolder
        TradeDelegate
        ERC20
        TopModel.

Require Import
        FeeHolderProps.

Ltac inv H := inversion H; subst; clear H.

Definition BurnManagerMsg_sender (msg: BurnManagerMsg) : address :=
  match msg with
  | msg_burn sender token => sender
  end.

Definition get_erc20_state (wst: WorldState) (token: address) : ERC20State :=
  ERC20StateMap.get (wst_erc20s wst) token.

Definition get_erc20_balance (wst: WorldState) (token: address) (owner: address) : value :=
  let erc20_state := (ERC20StateMap.get (wst_erc20s wst) token) in
  Maps.A2V.get (erc20_balances erc20_state) owner.

Definition get_erc20_allowance (wst: WorldState) (token: address) (owner: address) (to: address) : value :=
  let erc20_state := (ERC20StateMap.get (wst_erc20s wst) token) in
  Maps.AA2V.get (erc20_allowed erc20_state) (owner, to).

Axiom ERC20_burn_balance_decrease:
  forall wst sender token value wst' events,
    ERC20s.model wst (msg_erc20_burn sender token value) wst' (RetBool true) events ->
    (forall token', token' <> token -> get_erc20_state wst' token' = get_erc20_state wst token')
    /\
    (forall user, user <> sender ->
             get_erc20_balance wst' token user = get_erc20_balance wst token user)
    /\
    (get_erc20_balance wst' token sender = get_erc20_balance wst token sender - value)
    /\
    (forall user to, get_erc20_allowance wst' token user to = get_erc20_allowance wst token user to).

Axiom ERC20_transfer_balance_transfer:
  forall wst sender token to value wst' events,
    sender <> to ->
    ERC20s.model wst (msg_transfer sender token to value) wst' (RetBool true) events ->
    (forall token', token' <> token -> get_erc20_state wst' token' = get_erc20_state wst token')
    /\
    (forall from to, get_erc20_allowance wst' token from to = get_erc20_allowance wst token from to)
    /\
    (forall user,
        user <> sender ->
        user <> to ->
        get_erc20_balance wst' token user = get_erc20_balance wst token user)
    /\
    get_erc20_balance wst' token to =
    get_erc20_balance wst token to + value
    /\
    get_erc20_balance wst' token sender =
    get_erc20_balance wst token sender - value.

Axiom burn_manager_addr_neq_feeholder_addr:
  forall wst, wst_feeholder_addr wst <> wst_burn_manager_addr wst.

Lemma FeeHolder_wst_before_transfer_do_not_modify_erc20_states:
  forall wst sender token amount,
    wst_erc20s (FeeHolder.wst_before_transfer wst (wst_feeholder_addr wst) sender token amount) =
    wst_erc20s wst.
Proof. auto. Qed.

Lemma FeeHolder_withdrawBurned_transfer_to_burn_manager:
  forall wst token amount wst' ret events,
    FeeHolder.model wst (msg_withdrawBurned (wst_burn_manager_addr wst) token amount) wst' ret events ->
    (forall token', token' <> token -> get_erc20_state wst' token' = get_erc20_state wst token')
    /\
    (forall from to, get_erc20_allowance wst' token from to = get_erc20_allowance wst token from to)
    /\
    (forall user,
        user <> wst_feeholder_addr wst ->
        user <> wst_burn_manager_addr wst ->
        get_erc20_balance wst' token user = get_erc20_balance wst token user)
    /\
    get_erc20_balance wst' token (wst_burn_manager_addr wst) =
    get_erc20_balance wst token (wst_burn_manager_addr wst) + amount
    /\
    get_erc20_balance wst' token (wst_feeholder_addr wst) =
    get_erc20_balance wst token (wst_feeholder_addr wst) - amount.
Proof.
  intros. destruct H as [Hrequire [Htrans _]]. simpl in Htrans.
  unfold FeeHolder.withdraw_trans in Htrans.
  destruct Hrequire as [Hrequire _].
  destruct Hrequire as [_ (wst'' & events' & Hrequire)].
  specialize (Htrans _ _ Hrequire). destruct Htrans; subst wst'' ret. clear events.
  unfold get_erc20_balance, get_erc20_allowance, get_erc20_state.
  erewrite <- (FeeHolder_wst_before_transfer_do_not_modify_erc20_states wst (wst_burn_manager_addr wst) token amount).
  eapply ERC20_transfer_balance_transfer.
  eapply burn_manager_addr_neq_feeholder_addr.
  unfold FeeHolder.transfer_withdraw_succeed in Hrequire.
  simpl in Hrequire. eauto.
Qed.

Require Import PeanoNat.

Section BurnManagerCanOnlyDecreaseTokenBalanceOfFeeHolder.

  Theorem BurnManager_decrease_balance_of_fee_holder:
    forall wst sender token wst' retval events,
      lr_step wst (MsgBurnManager (msg_burn sender token)) wst' retval events ->
      (forall token',
          token' <> token -> get_erc20_state wst' token' = get_erc20_state wst token')
      /\
      (forall user, user <> wst_feeholder_addr wst ->
               get_erc20_balance wst' token user = get_erc20_balance wst token user)
      /\
      (get_erc20_balance wst' token (wst_feeholder_addr wst) <= get_erc20_balance wst token (wst_feeholder_addr wst))
      /\
      (forall user to, get_erc20_allowance wst' token user to = get_erc20_allowance wst token user to).
  Proof.
    intros. destruct H as [Hrequire [Htrans _]]. 
    simpl in Htrans. destruct Htrans as [events' Htrans].
    destruct Htrans as (wst1 & events1 & wst2 & events2 & HFeeHoldertrans & HERC20trans &
                        A & B & C).
    subst.
    unfold get_erc20_balance, get_erc20_allowance, get_erc20_state.
    eapply FeeHolder_withdrawBurned_transfer_to_burn_manager in HFeeHoldertrans.
    eapply ERC20_burn_balance_decrease in HERC20trans.
    unfold get_erc20_balance, get_erc20_allowance, get_erc20_state in *.
    split.
    { intros. intuition. rewrite H2; auto. }
    split.
    { intros. intuition. destruct (Nat.eq_dec user (wst_burn_manager_addr wst)).
      subst. rewrite H5. rewrite H6. apply Nat.add_sub.
      rewrite H1; auto. }
    split.
    { intuition. 
      destruct (Nat.eq_dec (wst_burn_manager_addr wst) (wst_feeholder_addr wst)).
      exfalso. eapply burn_manager_addr_neq_feeholder_addr; eauto.
      rewrite H0; eauto.
      rewrite H8. apply Nat.le_sub_l. }
    { intros. intuition.
      rewrite H7; auto. }
  Qed.

End BurnManagerCanOnlyDecreaseTokenBalanceOfFeeHolder.
      
    

          
    

  

