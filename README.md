# Formal Verification for Loopring Protocol Smart Contract version 2 

This repository contains the Coq code used in the formal model and the formal proofs of Loopring Protocol Smart Contract version 2 (LPSC).

## LPSC

Quote from Loopring whitepaper:
> Loopring Protocol Smart Contracts (LPSC): A set of public and free smart contracts that checks order-rings received from ring-miners, trustlessly settles and transfers tokens on behalf of users, incentivizes ring-miners and wallets with fees, and emits events.

A comprehensive introduction of Loopring protocol can be found in Loopring [whitepaper](https://github.com/Loopring/whitepaper/raw/master/en_whitepaper.pdf). Solidity contracts can be found at https://github.com/Loopring/protocol2.

## Why Formal Verification

Formal verification describes the target systems by mathematical models, and proves their correctness and security by mathematical proofs. It is based on the strict and rigorous mathematics and logic, and therefore can cover all behaviors of the system (*e.g.,* all possible combinations of inputs, all code path, etc.) and strictly guarantee the correctness and security which are precisely defined. Formal verification has been applied successfully in critical areas including astronautics, high-speed railway, nuclear power and aeronautics.

Smart contracts, especially those processing a large amount of assets, always puts high requirement for the correctness and security, which, we think, the formal verification can help a lot.

## Formal Verification of LPSC

The formal verification of LPSC is composed of two parts - a **formal model** of LPSC, and a bundle of **formal proofs** of properties about the correctness and security of LPSC.

The formal model describes the behaviors of LPSC. It models LPSC by an **abstract state machine**. The **machine state** or **world state** models storage variables of contracts in LPSC. The **state transition** describes how a message call to LPSC changes the storage (*i.e.,* the world state), emit events and return values.

Then we define a list of correctness and security properties of LPSC on the formal model, and prove they can be guaranteed by the formal model. As the formal model describes the behaviors of LPSC, we can imply LPSC can guarantee those properties as well.

### Formal Model

The machine state is defined by following files:

- World State: [Models/States.v](./Models/States.v)
- Message:     [Models/Messages.v](./Models/Messages.v)
- Event:       [Models/Events.v](./Models/Events.v)

The top-level state transition is defined by:

- [Models/TopModel.v](./Models/TopModel.v)

The state transition is further defined per contract:

- `BrokerInterceptor`: [Models/BrokerInterceptor.v](Models/BrokerInterceptor.v)
- `BrokerRegistry`:    [Models/BrokerRegistry.v](Models/BrokerRegistry.v)
- `BurnManager`:       [Models/BurnManager.v](Models/BurnManager.v)
- `BurnRateTable`:     [Models/BurnRateTable.v](Models/BurnRateTable.v)
- `FeeHolder`:         [Models/FeeHolder.v](Models/FeeHolder.v)
- `OrderBook`:         [Models/OrderBook.v](Models/OrderBook.v)
- `OrderRegistry`:     [Models/OrderRegistry.v](Models/OrderRegistry.v)
- `RingCanceller`:     [Models/RingCanceller.v](Models/RingCanceller.v)
- `RingSubmitter`:     [Models/RingSubmitter.v](Models/RingSubmitter.v)
- `TradeDelegate`:     [Models/TradeDelegate.v](Models/TradeDelegate.v)

Files in [Libs/](./Libs/) are libraries which define types and structures used in the formal model and proofs.

### Properties

Files in [Props/](./Props/) prove the following theorems for corresponding properties. A complete description can be found [here](./README.props.md).

## Quick Check Proofs

Both the formal model and the formal proofs are implemented in the interactive proof assistant [Coq](https://coq.inria.fr/). You can use Coq to automatically check the correctness of proofs.

1. Install OPAM by following [official instructions](https://opam.ocaml.org/doc/Install.html).

2. Install Coq and libraries via OPAM.

    ```
    $ opam init
    $ opam repo add coq-released http://coq.inria.fr/opam/released
    $ opam install coq.8.8.2
    $ opam install coq-mathcomp-ssreflect
    ```

3. Clone this repository.

    ```
    $ git clone https://github.com/sec-bit/loopring-protocol2-verification.git
    ```
    
4. Run Coq to check proofs.

    ```
    $ cd loopring-protocol2-verification
    $ make
    ```

## Contact Info

If you have any questions or suggestions for this repository, welcome to send them to following emails.

+ [hz@secbit.io](hz@secbit.io) 
+ [yu.guo@secbit.io](yu.guo@secbit.io)
