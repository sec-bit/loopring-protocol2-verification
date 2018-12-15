# Property List

Files in [Props/](./Props/) proves the following theorems for corresponding properties.

## Properties about Suspend and Kill

`TradeDelegate` provides `suspend()` and `kill()` to suspend and stop LPSC from filling and canceling orders. Following theorems proved in Coq file `Props/ControlProps.v` show the suspend and kill functions indeed work as expected.

- Theorem `no_further_LPSC_transaction_once_suspended`

    After `TradeDelegate::suspend()` is successfully called, if there is no further successful call to `TradeDelegate::resume()`, all further message calls to

    - `RingSubmitter::submitRings()`
    - all `cancel*()` functions in `RingCanceller`
    - `TradeDelegate::batchTransfer()`
    - `TradeDelegate::batchUpdateFilled()`
    - `TradeDelegate::setCancelled()` and all `set*Cutoffs*()` functions in `TradeDelegate`

    will always fail (revert), *i.e.,* no order can be filled or canceled.

- Theorem `no_further_LPSC_transaction_once_killed`

    After `TradeDelegate::kill()` is successfully called, regardless of whether `TradeDelegate::resume()` is called afterwards, all further message calls to

    - `RingSubmitter::submitRings()`
    - all `cancel*()` functions in `RingCanceller`
    - `TradeDelegate::batchTransfer()`
    - `TradeDelegate::batchUpdateFilled()`
    - `TradeDelegate::setCancelled()` and all `set*Cutoffs*()` functions in `TradeDelegate`

    will always fail (revert), *i.e.,* no order can be filled or canceled.

- Theorem `LPSC_cannot_be_resumed_once_killed`

    After `TradeDelegate::kill()` is successfully called, all further calls to `TradeDelegate::resume()` will fail, *i.e.,* a killed `TradeDelegate` cannot be resumed any more.


## Properties about Privileged Users

Some critical operations in LPSC must be operated by the contract owner or authorized users. Following theorems proved in Coq file `Props/ControlProps.v` show LPSC does guarantee them.

- Theorem `only_owner_is_able_to_control_LPSC`

    Only the contract owner who deploys `TradeDelegate` can suspend, resume and kill `TradeDelegate`. Combined with theorems in Section 3.1, we can conclude that only the contract owner can suspend, resume and stop LPSC from filling and canceling orders.

- Theorem `only_authorized_contracts_are_able_to_fill_or_cancel_orders`

    Functions in `TradeDelegate` that transfer tokens and cancels orders can only be called by authorized users.

## Properties about Valid Order-rings

LPSC puts several restrictions on submitted order-rings that can be successfully filled. Following theorems proved in Coq files `Props/{RingSubmitter, FilledRing}Props.v` show LPSC does guarantee them.

- Theorem `no_sub_rings`

    If an order-ring, submitted via `RingSubmitter::submitRings()`, contains sub-rings, *i.e.,* a token is sold in more than one orders in that ring, it will not be filled by `submitRings()`.

- Theorem `no_cancelled_orders`

    If an order-ring, submitted via `RingSubmitter::submitRings()`, contains canceled orders, it will not be filled by `submitRings()`.

- Theorem `no_token_mismatch_orders`

    If an order-ring, submitted via `RingSubmitter::submitRings()`, contains adjacent orders of which the buying token of the first one is not the selling token of the second one, it will not be filled by `submitRings()`.

- Theorems `soundness` and `completeness` in `Props/FilledRingProps.v`

	These two theorems prove that, in a simplified scenario where no fee and rounding error are considered, only the order-ring, of which the product of token exchange rates of all orders is not less than 1, can be finally filled by `RingSubmitter::submitRings()` and the filled token exchange rate of each order is not worse than the original one.


## Properties about Order Cancellation

`RingCanceller` provides a set of functions for order brokers to cancel orders. Following theorems proved in Coq file `Props/RingCancellerProps.v` show all those functions cannot undo the cancellation of any canceled order.

- Theorem `cancelOrders_no_side_effect`

    Every order ever canceled by `cancelOrders()` remains canceled, and is not affected by subsequent calls to `cancelOrders()`.

- Theorem `cancelAllOrdersForTradingPair_no_side_effect`

    Every order ever canceled by `cancelAllOrdersForTradingPair()` remains canceled, and is not affected by subsequent calls to `cancelAllOrdersForTradingPair()`.

- Theorem `cancelAllOrders_no_side_effect`

    Every order ever canceled by `cancelAllOrders()` remains canceled, and is not affected by subsequent calls to `cancelAllOrders()`.

- Theorem `cancelAllOrdersOfOwner_no_side_effect`

    Every order ever canceled by `cancelAllOrdersOfOwner()` remains canceled, and is not affected by subsequent calls to `cancelAllOrdersOfOwner()`.

- Theorem `cancelAllOrdersForTradingPairOfOwner_no_side_effect`

    Every order ever canceled by `cancelAllOrdersForTradingPairOfOwner()` remains canceled, and is not affected by subsequent calls to `cancelAllOrdersForTradingPairOfOwner()`.

## Properties about Fee Withdraw

`FeeHolder` provides `withdrawBurned()` and `withdrawToken()` to withdraw burned fees and fees. Following theorems proved in Coq file `Props/FeeHolderProps.v` show some of their properties.

- Theorem `withdrawBurned_noauth`

    If the caller is not authorized, its call to `withdrawBurned()` can never succeed. That is, non-authorized users cannot directly withdraw burned fees from `FeeHolder`.

	**Note**: It does not mean non-authorized users cannot burn the burned fees. They can still call `burn()` of `BurnManager` to burn the burned fees in LRC. `BurnManager` is authorized.

- Theorem `withdrawBurned_auth`

    If the caller is authorized and its call to `withdrawBurned(token, amount)` succeeds, then the following three effects must **all** present:

    - the reduction of the specified `amount` of `token` from the corresponding burned fee balance of `FeeHolder`,
    - a return value `true`, and
    - an event `TokenWithdrawn` that specifies an `amount` of `token` is withdrawn from the fee balance of `FeeHolder`.

- Theorem `withdrawToken_noauth`

    A successful call to `withdrawnToken(token, amount)` must present **all** following three effects:

    - the reduction of the specified `amount` of `token` from the corresponding fee balance of the caller,
    - a return value `true`, and
    - an event `TokenWithdrawn` that specifies the caller, the fee token, and the withdrawn amount.

## Properties about Fee Burning

`BurnManager` provides a public function `burn()`, which can be called by anyone to burn LRC fees from `FeeHolder`.

- Theorem `BurnManager_decrease_balance_of_fee_holder`

	This theorem in Coq file `Props/BurnManagerProps.v` proves that `burn()` only decreases the ERC20 balance of `FeeHolder`. ERC20 balances and allowances of other users are not affected.
