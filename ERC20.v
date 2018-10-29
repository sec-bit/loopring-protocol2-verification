Require Import
        Events
        LibModel
        Messages
        States
        Types.


(* Assume ERC20 contracts only change their own states. *)
Parameter oracle_totalSupply:
  ERC20StateMap.t -> address -> address -> ERC20StateMap.t * Result.
Parameter oracle_balanceOf:
  ERC20StateMap.t -> address -> address -> address -> ERC20StateMap.t * Result.
Parameter oracle_allowance:
  ERC20StateMap.t -> address -> address -> address -> address -> ERC20StateMap.t * Result.
Parameter oracle_transfer:
  ERC20StateMap.t -> address -> address -> address -> uint -> ERC20StateMap.t * Result.
Parameter oracle_transferFrom:
  ERC20StateMap.t -> address -> address -> address -> address -> uint -> ERC20StateMap.t * Result.
Parameter oracle_approve:
  ERC20StateMap.t -> address -> address -> address -> uint -> ERC20StateMap.t * Result.

Definition func_totalSupply
           (wst0 wst: WorldState) (sender token: address) :=
  match oracle_totalSupply (wst_erc20s wst) sender token with
  | (st', res') => ((wst_update_erc20s wst st'), res')
  end.

Definition func_balanceOf
           (wst0 wst: WorldState) (sender token who: address) :=
  match oracle_balanceOf (wst_erc20s wst) sender token who with
  | (st', res') => ((wst_update_erc20s wst st'), res')
  end.

Definition func_allowance
           (wst0 wst: WorldState) (sender token owner spender: address) :=
  match oracle_allowance (wst_erc20s wst) sender token owner spender with
  | (st', res') => ((wst_update_erc20s wst st'), res')
  end.

Definition func_transfer
           (wst0 wst: WorldState) (sender token to: address) (value: uint) :=
  match oracle_transfer (wst_erc20s wst) sender token to value with
  | (st', res') => ((wst_update_erc20s wst st'), res')
  end.

Definition func_transferFrom
           (wst0 wst: WorldState) (sender token from to: address) (value: uint) :=
  match oracle_transferFrom (wst_erc20s wst) sender token from to value with
  | (st', res') => ((wst_update_erc20s wst st'), res')
  end.

Definition func_approve
           (wst0 wst: WorldState) (sender token spender: address) (value: uint) :=
  match oracle_approve (wst_erc20s wst) sender token spender value with
  | (st', res') => ((wst_update_erc20s wst st'), res')
  end.

Definition ERC20_step
           (wst0 wst: WorldState) (msg: ERC20Msg)
  : (WorldState * Result) :=
  match msg with
  | msg_totalSupply sender token =>
    func_totalSupply wst0 wst sender token
  | msg_balanceOf sender token who =>
    func_balanceOf wst0 wst sender token who
  | msg_allowance sender token owner spender =>
    func_allowance wst0 wst sender token owner spender
  | msg_transfer sender token to value =>
    func_transfer wst0 wst sender token to value
  | msg_transferFrom sender token from to value =>
    func_transferFrom wst0 wst sender token from to value
  | msg_approve sender token spender value =>
    func_approve wst0 wst sender token spender value
  end.
