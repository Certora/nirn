/*
    This is a specification file for smart contract verification with the Certora prover.
    For more information, visit: https://www.certora.com/
*/

import "helpers/erc20.spec"

// TODO: harness internal functions (is this change still coming soon?)
// TODO: add support for the IErc20Adapter (if needed)
// TODO: add support for "DistributionParameters" (if needed)
// TODO: add support for IRewardsSellar (if needed)

////////////////////////////////////////////////////////////////////////////
//                      Methods                                           //
////////////////////////////////////////////////////////////////////////////

methods {
    // from sanity
    deposit(uint256) => DISPATCHER(true)
    withdraw(uint256) => DISPATCHER(true)
    withdrawAll() => DISPATCHER(true)
    withdrawUnderlying(uint256) => DISPATCHER(true)
    withdrawUnderlyingUpTo(uint256) => DISPATCHER(true)

    // Vault functions
    getCurrentLiquidityDeltas() returns (int256[])
    getAPR() returns (uint256)
    depositTo(uint256, address) returns (uint256)
    // withdrawInternal(uint256, uint256, IErc20Adapter[], uint256[], BalanceSheet)
    // withdrawToMatchAmount(IErc20Adapter[], uint256[], uint256[], uint256, uint256, uint256)
    rebalance()
    rebalanceWithNewWeights(uint256[])
    // currentDistribution() returns (DistributionParameters, uint256, uint256)
    // processProposedDistribution(DistributionParameters, uint256, IErc20Adapter[], uint256[]) returns (DistributionParameters)
    // rebalanceWithNewAdapters(IErc20Adapter[], uint256[])
    // _transferOut(address, uint256) // internal

    // Vault Base functions
    decimals() returns (uint8)
    // getAdaptersAndWeights() returns (IErc20Adapter[], uint256[])
    // setAdaptersAndWeights(IErc20Adapter[], uint256[])
    // removeAdapters(uint256[], uint256) // internal
    initialize(address, address, address, address)
    setMaximumUnderlying(uint256)
    setPerformanceFee(uint64)
    setReserveRatio(uint64)
    setFeeRecipient(address)
    // setRewardsSeller(IRewardsSeller)
    sellRewards(address, bytes)
    // withdrawFromUnusedAdapter(IErc20Adapter)
    // getBalanceSheet(IErc20Adapter[])
    getBalances() returns (uint256[])
    balance() returns (uint256)
    reserveBalance() returns (uint256)
    // calculateFee(uint256, uint256) // internal
    getPendingFees() returns (uint256)
    // claimFees(uint256, uint256) returns (uint256) // internal
    getPricePerFullShare() returns (uint256)
    getPricePerFullShareWithFee() returns (uint256)
    // beforeAddAdapter(IErc20Adapter)
    // beforeAddAdapters(IErc20Adapter[])
    // external method summaries

    // harness
    adaptersLength() returns uint envfree
}

////////////////////////////////////////////////////////////////////////////
//                       Invariants                                       //
////////////////////////////////////////////////////////////////////////////


// “The target balance t(w) is the amount of capital that should be held by a vault in a token adapter with weight w, 
// assuming that all of v(p) is liquid”For a given vault the target balance is equal to stored v(p) multiplied by given adapter weight w, 
// assuming v(p) is liquid 
// t(w) = v(p) * w
invariant target_balance_accurate() // TODO
    false
// Weights always above minimum values (they list this in the WP as a pre-requisite for rebalance)
// Section 3.3, point 5 of the WP
invariant min_weights() // TODO
    false

// (WP section 3.3 point 6), after a rebalance the weights should always increase the net APR (by >=5% of current value)
invariant rebalance_safety() // TODO
    false



//  total_supply > 0 <=> balance() > 0 
// see potential issues 
invariant total_supply_vs_balance() // TODO
    false

// each vault maps to an underlying (for underlying that apply?)
invariant vault_underlying_mapping() // TODO
    false

// mo underlying can map to more than one vault
invariant underlying_single_vault() // TODO
    false







////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// Withdraw more than reserves
// “Withdrawing an amount greater than current liquid reserves invokes a chain of withdrawals … . In the event that this happens, 
// the vault reserves are empty until the next deposit or rebalance.”
// amountOut = withdraw(shares)amountOut > current_liquid_reserves => vault reserves are empty

// “ take 10% of the yield earned by productive assets”
//  deposit and immediately withdraw results in the same amount (only on yield)
rule no_double_fee() {    // TODO
    assert false, "not yet implemented";
}

// deposit x and deposit y is the same as deposit x+ y
// see potential issues 
rule additive_deposit() { // TODO
    assert false, "not yet implemented";
}
// might as well write this to go with additive deposit
rule additive_withdraw() { // TODO
    assert false, "not yet implemented";
}

// only whitelisted adapters can be used
rule whitelist_adapter_only() { // TODO
    assert false, "not yet implemented";
}

////////////////////////////////////////////////////////////////////////////
//                       Helper Functions                                 //
////////////////////////////////////////////////////////////////////////////

// TODO: Any additional helper functions

