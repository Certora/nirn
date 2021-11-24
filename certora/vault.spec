/*
    This is a specification file for smart contract verification with the Certora prover.
    For more information, visit: https://www.certora.com/
*/

import "helpers/erc20.spec"

using DummyERC20Impl as underlyingToken
using SymbolicERC20Adapter as Adapter

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
    availableLiquidity() => DISPATCHER(true)

    // Vault functions
    deposit(uint256) returns (uint256)
    withdraw(uint256) returns (uint256)
    
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
    feeRecipient() returns (address) envfree
    priceAtLastFee() returns (uint128) envfree
    claimFees() envfree
    // setRewardsSeller(IRewardsSeller)
    sellRewards(address, bytes) => DISPATCHER(true)
    //0x00e00ebb => NONDET
    // withdrawFromUnusedAdapter(IErc20Adapter)
    // getBalanceSheet(IErc20Adapter[])
    getBalances() returns (uint256[])
    balance() returns (uint256) envfree
    totalSupply() returns uint256 envfree
    reserveBalance() returns (uint256)
    calculateFee(uint256, uint256) returns (uint256) envfree // internal normally
    getPendingFees() returns (uint256)
    // claimFees(uint256, uint256) returns (uint256) // internal
    getPricePerFullShare() returns (uint256)
    getPricePerFullShareWithFee() returns (uint256)

    balanceOf(address) returns(uint256) envfree
    
    // beforeAddAdapter(IErc20Adapter)
    // beforeAddAdapters(IErc20Adapter[])
    // external method summaries

    // harness
    adaptersLength() returns uint envfree
    weightsLength() returns uint envfree
    getAdapter(uint256) returns address envfree
    // adapter
    //TODO - need a symbolic adapter
    // balanceUnderlying() => CONSTANT

    // helpers
    // checkRemoveAdapters(uint256[], uint256 ) envfree // should be removed??
    getBalanceSheetTotalBalance() returns (uint256) envfree

    // isApprovedAdapter(address adapter) returns bool envfree
    isApprovedAdapter(address adapter) => symbolic_approver(adapter)
}

ghost symbolic_approver(address) returns bool;
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



invariant total_supply_vs_balance() // TODO
    totalSupply() == 0 <=> balance() == 0 
{
    preserved withdraw(uint256 amount) with (env e){
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    preserved withdrawFromUnusedAdapter(address adapter) with (env e){
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    preserved withdrawUnderlying(uint256 amount) with (env e){
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
}

invariant balance_GE_totalSupply() // TODO
    balance() >= totalSupply()
{
    preserved withdraw(uint256 amount) with (env e){
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    preserved withdrawFromUnusedAdapter(address adapter) with (env e){
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    preserved withdrawUnderlying(uint256 amount) with (env e){
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
}

// each vault maps to an underlying (for underlying that apply?)
invariant vault_underlying_mapping() // TODO
    false

// no underlying can map to more than one vault
invariant underlying_single_vault() // TODO
    false

invariant balanceSheet_equals_balance() // Passing
    balance() == getBalanceSheetTotalBalance()






////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// Withdraw more than reserves
// “Withdrawing an amount greater than current liquid reserves invokes a chain of withdrawals … . In the event that this happens, 
// the vault reserves are empty until the next deposit or rebalance.”
// amountOut = withdraw(shares)amountOut > current_liquid_reserves => vault reserves are empty

// deposit x and deposit y is the same as deposit x+ y
// see potential issues 
rule additive_deposit() { // Timing out
    env e;
    // require total supply = total balance 
    uint256 x; uint256 y;

    // store state
    storage initStorage = lastStorage;

    uint256 shares_x = deposit(e, x);
    uint256 shares_y = deposit(e, y);
    uint256 indexed_shares_seq = balanceOf(feeRecipient());
    // without these checks the dust (roundoff) bug is showed off
    require shares_x != 0;
    require shares_y != 0;

    uint256 balance_sequential = balance();

    // return to storage state
    uint256 shares_xy = deposit(e, x + y) at initStorage;
    uint256 indexed_shares_sum = balanceOf(feeRecipient());
    uint256 balance_additive = balance();

    assert balance_sequential == balance_additive, "additivity of balance failed";
    // assert shares_x + shares_y == shares_xy, "additivity of shares failed";
    assert indexed_shares_seq == indexed_shares_sum, "additivity of fees failed";
}
// might as well write this to go with additive deposit
rule additive_withdraw() { // TODO
    env e;
    uint256 x; uint256 y;
    // store state

    storage initStorage = lastStorage;

    uint256 x_out = withdraw(e, x);
    uint256 y_out = withdraw(e, y);

    uint256 balance_sequential = balance();
    uint256 indexed_shares_seq = balanceOf(feeRecipient());

    // return to storage state
    uint256 xy_out = withdraw(e, x + y) at initStorage;
    uint256 balance_additive = balance();
    uint256 indexed_shares_sum = balanceOf(feeRecipient());

    assert balance_sequential == balance_additive, "additivity of balance failed";
    assert x_out + y_out == xy_out, "additivity of output failed";
    assert indexed_shares_seq == indexed_shares_sum, "additivity of fees failed";
}

rule no_double_fee(method f) filtered {f -> f.selector == deposit(uint256).selector }{ 
    
    // (f.selector != rebalance().selector ||
    //                                          f.selector != rebalanceWithNewWeights(uint256[]).selector ||
    //                                          f.selector != rebalanceWithNewAdapters(address[],uint256[]).selector    
    //                                         )} { // filtered out functions that are timing out
    env e; calldataarg args;

    // assume sender is not the fee receipient or current contract
    // are there scenarios where this could happen?
    require e.msg.sender != feeRecipient();
    require e.msg.sender != currentContract;

    uint256 balance_pre = balance();
    uint256 supply_pre = totalSupply();
    uint256 indexed_shares_pre = balanceOf(feeRecipient());

    require indexed_shares_pre < supply_pre; // cex where indexed had all shares
    // require calculateFee(balance_pre, supply_pre) == 0; // we want to assume that fees have already been claimed
    
    claimFees();
    f(e, args);
    claimFees();
    
    uint256 supply_post = totalSupply();
    uint256 balance_post = balance();
    uint256 indexed_shares_post = balanceOf(feeRecipient());
    
    // if a fee was claimed the shares of index will go up, this 
    assert indexed_shares_pre != indexed_shares_post => balance_pre == balance_post && supply_pre == supply_post, "fee claimed on balance";
}

// only whitelisted adapters can be used
rule whitelist_adapter_only() { // TODO
    assert false, "not yet implemented";
}

// rule validity_removeAdapters() {
//     uint256[] toRemove;
//     uint256 len = 2;
//     require toRemove.length == 2; 
//     require adaptersLength() == 4;
//     require toRemove[0] <= adaptersLength()-1;
//     require toRemove[1] <= adaptersLength()-1;
//     invoke checkRemoveAdapters(toRemove, len);
//     assert !lastReverted;
// }
////////////////////////////////////////////////////////////////////////////
//                       Helper Functions                                 //
////////////////////////////////////////////////////////////////////////////

// TODO: Any additional helper functions

    invariant adapter_length_eq_weight()
    adaptersLength() == weightsLength()

    invariant adapters_are_unique(uint256 i, uint256 j)
    i != j => getAdapter(i) != getAdapter(j)

    invariant isApprovedAdapter(address adapter, env e)
    isApprovedAdapterInRegistry(e,adapter)
    // filtered{f -> f.selector != isApprovedAdapter_instate.selector }

    
    invariant adapters_lenght_ge_2()
    adaptersLength() >= 2

    
    // invariant reserveBalance_GE_20(env e)
    // reserveBalance(e) * 5 <= balance()

    rule deposit_GR_zero(){
        env e;
        require e.msg.sender != currentContract;
        require maximumUnderlying(e) > 0;

        uint256 amount;
        uint256 amountMinted = deposit(e,amount);

        assert amount > 0 <=> amountMinted > 0;
    }

    rule more_shares_more_withdraw(){
        env e;

        uint256 sharesX;
        uint256 sharesY;
        uint256 amountX;
        uint256 amountY;

        require e.msg.sender != currentContract && e.msg.sender != Adapter && e.msg.sender != underlyingToken && e.msg.sender != feeRecipient();
        // require sharesX <= balanceOf(e.msg.sender);

        storage init = lastStorage;

        amountX =  withdraw(e,sharesX);
        amountY =  withdraw(e,sharesY) at init;

        assert sharesX > sharesY => amountX >= amountY;
    }
    rule more_user_shares_less_underlying(method f) filtered {f -> f.selector != transfer(address,uint256).selector && f.selector != transferFrom(address,address,uint256).selector}{
        env e;

        uint256 Underlying_balance_before = underlyingToken.balanceOf(e,e.msg.sender);
        uint256 User_balance_before = balanceOf(e.msg.sender);

        require e.msg.sender != currentContract && e.msg.sender != Adapter && e.msg.sender != underlyingToken && 
                e.msg.sender != feeRecipient() && feeRecipient() != currentContract;


        calldataarg args;
        f(e,args);
     
        uint256 Underlying_balance_after = underlyingToken.balanceOf(e,e.msg.sender);
        uint256 User_balance_after = balanceOf(e.msg.sender);

        assert User_balance_after > User_balance_before <=> Underlying_balance_after < Underlying_balance_before;
        assert User_balance_after < User_balance_before <=> Underlying_balance_after > Underlying_balance_before;
    }

    rule price_monotonicity(method f, env e){
    claimFees();
    uint256 _price = priceAtLastFee();
    uint256 _supply = totalSupply();
    uint256 _balance = balance();

    claimFees();
    uint256 price_ = priceAtLastFee();
    uint256 supply_ = totalSupply();
    uint256 balance_ = balance();
    assert price_ >= _price;
    }
    
    invariant collect_fees_check(env e)
    balanceOf(feeRecipient()) < totalSupply() / 2 &&
            (e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract)
    // {
    //     preserved{
    //     require e.msg.sender != currentContract && e.msg.sender != Adapter &&
    //             e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
    //             feeRecipient() != currentContract;
    //     }
    // }