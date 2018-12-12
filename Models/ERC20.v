Require Import
        Events
        LibModel
        Messages
        States
        Types.


Parameter oracle_erc20_totalSupply_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address *) ->
    address (* msg.sender *) ->
    FSpec.
Parameter oracle_erc20_balanceOf_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address *) ->
    address (* msg.sender *) ->
    address (* param: account *) ->
    FSpec.
Parameter oracle_erc20_allowance_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address *) ->
    address (* msg.sender *) ->
    address (* param: from *) ->
    address (* param: to *) ->
    FSpec.
Parameter oracle_erc20_transfer_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address *) ->
    address (* msg.sender *) ->
    address (* param: to *) ->
    uint    (* param: amount *) ->
    FSpec.
Parameter oracle_erc20_transferFrom_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address *) ->
    address (* msg.sender *) ->
    address (* param: from *) ->
    address (* param: to *) ->
    uint    (* param: amount *) ->
    FSpec.
Parameter oracle_erc20_approve_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address *) ->
    address (* msg.sender *) ->
    address (* param: account *) ->
    uint    (* param: amount *) ->
    FSpec.

Parameter oracle_erc20_burnFrom_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address*) ->
    address (* msg.sender *) ->
    address (* param: from *) ->
    uint (* param: amount *) ->
    FSpec.

Parameter oracle_erc20_burn_spec
  : ERC20StateMap.t (* all ERC20 states *) ->
    address (* ERC20 address*) ->
    address (* msg.sender *) ->
    uint (* param: amount *) ->
    FSpec.

Module ERC20s.

  Definition get_spec (erc20s: ERC20StateMap.t) (msg: ERC20Msg): FSpec :=
    match msg with
    | msg_totalSupply sender token =>
      oracle_erc20_totalSupply_spec erc20s token sender

    | msg_balanceOf sender token account =>
      oracle_erc20_balanceOf_spec erc20s token sender account

    | msg_allowance sender token from to =>
      oracle_erc20_allowance_spec erc20s token sender from to

    | msg_transfer sender token to amount =>
      oracle_erc20_transfer_spec erc20s token sender to amount

    | msg_transferFrom sender token from to amount =>
      oracle_erc20_transferFrom_spec erc20s token sender from to amount

    | msg_approve sender token account amount =>
      oracle_erc20_approve_spec erc20s token sender account amount

    | msg_burnFrom sender token from amount =>
      oracle_erc20_burnFrom_spec erc20s token sender from amount

    | msg_erc20_burn sender token amount =>
      oracle_erc20_burn_spec erc20s token sender amount
    end.

  Definition model
             (wst: WorldState)
             (msg: ERC20Msg)
             (wst': WorldState)
             (retval: RetVal)
             (events: list Event)
    : Prop :=
    fspec_sat (get_spec (wst_erc20s wst) msg) wst wst' retval events.

End ERC20s.
