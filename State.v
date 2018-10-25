Require Import
        Mapping Types.

Set Implicit Arguments.


(** Sub-state of broker registry *)
Record Broker : Type :=
  mk_broker {
      broker_owner: address;
      broker_addr: address;
      broker_inteceptor: address;
    }.

Record BrokerRegistry : Type :=
  mk_broker_registry {
      (* order owner address -> Broker *)
      registered_brokers: @tmap address Broker;
    }.


(** Sub-state of order registry *)
Record OrderRegistry : Type :=
  mk_order_registry {
      (* order owner address -> order hash -> is registered? *)
      registered_orders: @tmap (prod address bytes20) bool;
    }.


(** Sub-state of burn rate table *)
Record TokenData : Type :=
  mk_token_data {
      token_tier: nat;
      token_valid_until: nat;
    }.

Record BurnRateTable : Type :=
  mk_burn_rate_table {
      (* token address -> TokenData *)
      burn_rates: @tmap address TokenData
    }.

Definition BURN_BASE_PERCENTAGE : nat := 1000.

Fixpoint matching_burn_rate (tier: nat) : option nat :=
  match tier with
  | O => Some 50
  | 1 => Some 200
  | 2 => Some 400
  | 3 => Some 600
  | _ => None
  end.

Fixpoint p2p_burn_rate (tier: nat) : option nat :=
  match tier with
  | O => Some 5
  | 1 => Some 20
  | 2 => Some 30
  | 3 => Some 60
  | _ => None
  end.


(** Sub-state of trader delegate *)
Record TraderDelegate : Type :=
  mk_trade_delegate {
      delegate_authorized_addrs: list address;
      delegate_filled: @tmap bytes32 uint256;
      delegate_cancelled: @tmap (prod address bytes32) bool;
      delegate_cutoffs: @tmap address uint256;
      (* TODO: add other fields of ITradedelegate *)
    }.


(** Global state of LPSC *)
Record LPSCState : Type :=
  mk_lpsc_state {
      broker_registry: BrokerRegistry;
      record_registry: OrderRegistry;
      trade_delegater: TraderDelegate;
      burn_rate_table: BurnRateTable;
    }.


(** Global state of all token contracts *)
Record ERC20State : Type :=
  mk_erc20_state {
      erc20_balances: a2v;
      erc20_allowed: aa2v;
    }.


(** Global state of all order owners *)
Record OrderOwnerState : Type :=
  mk_order_owner_state {
      owner_key_pair: KeyPair;
      (* token contract address -> token account address *)
      owner_tokens: @tmap address address;
    }.


(** Global state of wallets *)
Record WalletState : Type :=
  mk_wallet_state {
      wallet_key_pair: KeyPair;
    }.


(** Global state of ring miners *)
Record MinerState : Type :=
  mk_miner_state {
      miner_key_pair: KeyPair;
    }.


(** World state involving all parties of loopring protocol. *)

Record WorldState : Type :=
  mk_world_state {
      ws_lpsc: LPSCState;

      (* token address -> token state *)
      ws_tokens: @tmap address ERC20State;

      (* order owner address -> order owner state *)
      ws_order_owners: @tmap address OrderOwnerState;

      (* wallet address -> wallet state *)
      ws_wallets: @tmap address WalletState;

      (* miner address -> miner state *)
      ws_miners: @tmap address MinerState;
    }.

Inductive WorldEvent : Type :=
(* to be defined *)
.

Definition WorldEvents := list WorldEvent.