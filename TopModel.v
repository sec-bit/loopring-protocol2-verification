Require Import Nat List.
Require Import Actions State Types.
Require Import RingSubmitterModel.

(* to be defined *)
Parameter Token_actor: TokenAction -> WorldState -> (WorldState * WorldEvents).
Parameter OrderOwner_actor: OrderOwnerAction -> WorldState -> (WorldState * WorldEvents).
Parameter Wallet_actor: WalletAction -> WorldState -> (WorldState * WorldEvents).
Parameter Miner_actor: MinerAction -> WorldState -> (WorldState * WorldEvents).

Definition lr_world_step (act: Action) (st: WorldState) : (WorldState * WorldEvents) :=
  match act with
  | Action_LPSC a => LPSC_actor a st
  | Action_Token a => Token_actor a st
  | Action_OrderOwner a => OrderOwner_actor a st
  | Action_Wallet a => Wallet_actor a st
  | Action_Miner a => Miner_actor a st
  end.

Fixpoint lr_world_steps (acts: list Action) (st: WorldState) : (WorldState * WorldEvents) :=
  match acts with
  | nil => (st, nil)
  | a :: acts' => match lr_world_step a st with
                 | (st', evts') => match lr_world_steps acts' st' with
                                  | (st'', evts'') => (st'', evts' ++ evts'')
                                  end
                 end
  end.

(* to be defined *)
Parameter InitGlobalState: WorldState.

(* Top-level model of loopring protocol *)
Definition lr_model :=
  fun acts: list Action => lr_world_steps acts InitGlobalState.