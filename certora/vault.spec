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

    underlying() returns (address) envfree

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
    balanceUnderlying() returns (uint256) =>  DISPATCHER(true)
    setBalanceUnderlying(uint256) => DISPATCHER(true)
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


definition outOfScope(method f) returns bool = 
                f.selector == rebalanceWithNewAdapters(address[], uint256[]).selector ||
                f.selector == rebalance().selector ||
                f.selector == rebalanceWithNewWeights(uint256[]).selector 
                ;

////////////////////////////////////////////////////////////////////////////
//                       Invariants                                       //
////////////////////////////////////////////////////////////////////////////


// “The target balance t(w) is the amount of capital that should be held by a vault in a token adapter with weight w, 
// assuming that all of v(p) is liquid”For a given vault the target balance is equal to stored v(p) multiplied by given adapter weight w, 
// assuming v(p) is liquid 
// t(w) = v(p) * w
//invariant target_balance_accurate() // TODO
  //  false





invariant total_supply_vs_balance()   // has some failures 
    totalSupply() == 0 <=> balance() == 0 
    filtered { f-> !outOfScope(f) && !f.isView}
{
    preserved withdraw(uint256 amount) with (env e){
        requireInvariant adapter_balance_underlying(e);
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    preserved withdrawFromUnusedAdapter(address adapter) with (env e){
        requireInvariant adapter_balance_underlying(e);
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    preserved withdrawUnderlying(uint256 amount) with (env e){
        requireInvariant adapter_balance_underlying(e);
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
}


/* STATUS: 
Passing
*/
invariant balanceSheet_equals_balance() 
    balance() == getBalanceSheetTotalBalance()
    filtered { f-> !outOfScope(f) && !f.isView}






////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// Withdraw more than reserves
// “Withdrawing an amount greater than current liquid reserves invokes a chain of withdrawals … . In the event that this happens, 
// the vault reserves are empty until the next deposit or rebalance.”
// amountOut = withdraw(shares)amountOut > current_liquid_reserves => vault reserves are empty

// deposit x and deposit y is the same as deposit x+ y
/* STATUS: 
*/
rule additive_deposit() {
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
/* STATUS: 
 timing out
*/
rule additive_withdraw() { 
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

/* STATUS: 
deposit: cex
withdraw: timeout
*/
rule no_double_fee(method f) filtered {f -> (f.selector == deposit(uint256).selector ||
                                            f.selector == depositTo(uint256, address).selector ||
                                             f.selector == withdraw(uint256).selector) }{ 
    
    // (f.selector != rebalance().selector ||
    //                                          f.selector != rebalanceWithNewWeights(uint256[]).selector ||
    //                                          f.selector != rebalanceWithNewAdapters(address[],uint256[]).selector    
    //                                         )} { // filtered out functions that are timing out
    env e; calldataarg args;

    // assume sender is not the fee receipient or current contract
    // are there scenarios where this could happen?
    require e.msg.sender != feeRecipient();
    require e.msg.sender != currentContract;

    // claimFees(); // should (with proper behavior) ensure there are no residual fees to collect    

    uint256 balance_pre = balance();
    uint256 supply_pre = totalSupply();
    uint256 indexed_shares_pre = balanceOf(feeRecipient());

    require calculateFee(balance_pre, supply_pre) == 0; // to reduce timeouts, trying to start the rule in the state where fees have been collected
    require indexed_shares_pre < supply_pre; // cex where indexed had all shares

    f(e, args);
    claimFees();
    
    uint256 supply_post = totalSupply();
    uint256 balance_post = balance();
    uint256 indexed_shares_post = balanceOf(feeRecipient());
    
    // if a fee was claimed the shares of index will go up, this 
    assert indexed_shares_pre == indexed_shares_post, "fee claimed on balance";
}

/* STATUS: 
PASSING - needs review if suggested improvements are important
*/
// reduce the starting balance and then claim fee, the fee should be 0
// hypothesis: this will timeout with two arbitray functions
rule no_double_fee_on_drop() { // add adapter harness to allow for reduction of underlying value                                                                        
    env e;

    uint256 balance_pre = balance();
    uint256 supply_pre = totalSupply();
    uint256 underlying_balance = Adapter.balanceUnderlying(e);

    require calculateFee(balance_pre, supply_pre) == 0;

    // drop balance underlying
    uint256 underlying_balance_drop;
    require underlying_balance_drop < underlying_balance;
    Adapter.setBalanceUnderlying(e, underlying_balance_drop);

    uint256 balance_drop = balance();
    uint256 supply_drop = totalSupply();
    assert calculateFee(balance_drop, supply_drop) == 0, "fee claimed on drop?";

    // balance underlying goes back up
    uint256 underlying_balance_end;
    require underlying_balance_end <= underlying_balance;
    require underlying_balance_end > underlying_balance_drop;
    Adapter.setBalanceUnderlying(e, underlying_balance_end);

    uint256 balance_raise = balance();
    uint256 supply_raise = totalSupply();
    assert calculateFee(balance_raise, supply_raise) == 0, "double fee claimed on raise";

    // this only checks calculate fee, does not go all the way through claim fee. TODO try on claim fee
    // this also does not check the scenario where the underlyingbalance goes up enogh that 
}

/* STATUS: 

*/
// this was specifically to show withdraw underlying fails this property, but is good to test on other functions
rule shares_correlate_balance(method f) filtered { f-> !outOfScope(f) && !f.isView }
{
    env e; calldataarg args;

    uint256 balance_pre = balance();
    uint256 supply_pre = totalSupply();

    f(e, args);

    uint256 balance_post = balance();
    uint256 supply_post = totalSupply();
    assert balance_pre != balance_post <=> supply_pre != supply_post, "balance or shares changed without the other";
}

/* STATUS: 
    generates counter examples:
    Balance is 2 with shares of 1, you can withdraw 1 token without burning your share
*/
rule withdraw_underlying_no_shares() {
    env e;

    uint256 amount;
    // require amount > 0;
    require amount > 10000; // taking 1 of a token isn't very interesting


    uint256 vault_balance_pre = balance(); 
    uint256 user_balance_pre = underlyingToken.balanceOf(e, e.msg.sender);
    uint256 vault_shares = totalSupply(); // for information
    uint256 user_shares = balanceOf(e.msg.sender);

    uint256 shares = withdrawUnderlying(e, amount);
    require shares == 0; 

    uint256 user_balance_post = underlyingToken.balanceOf(e, e.msg.sender);
    uint256 vault_balance_post = balance();

    assert shares == 0 => vault_balance_pre == vault_balance_post, "amount received with no shares burned";
    assert shares == 0 => user_balance_pre == user_balance_post, "balance increased at no share cost";
}


rule transfer_then_withdraw(method f) filtered { f-> !outOfScope(f) && !f.isView }
{
    env e; calldataarg args;

    // no vault will start with 0 in either
    require balance() > 0;
    require totalSupply() > 0; 

    uint256 transferAmount;
    require transferAmount > 1000; // to make things interesting (must be greater than 0 for a good cex to be generated)
    uint256 depositAmount;

    uint256 shares = deposit(e, depositAmount);

    // transfer to setup
    underlyingToken.transfer(e, underlying(), transferAmount);

    // storage postTransfer = lastStorage;

    uint256 underlyingBack = withdraw(e, shares);

    // I chose less than intentionally. If they are equal somebody could go even while causing a competitor to lose their funds
    assert underlyingBack < depositAmount + transferAmount, "value taken from vault";

    // f(e, args) at postTransfer;

    // uint256 underlyingBackwithF = withdraw(e, shares);

    // assert underlyingBackwithF < depositAmount + transferAmount, "transfer + arbitrary function siphons from vault";
}

// only whitelisted adapters can be used
rule whitelist_adapter_only() { // TODO
    assert false, "not yet implemented";
}


invariant integrity_adapter_list(uint i, uint j)
    // equal size
    adaptersLength() == weightsLength() &&
    // uniqueness
    ( i != j => getAdapter(i) != getAdapter(j) )
    filtered { f-> !outOfScope(f) && !f.isView}

invariant isApprovedAdapter(address adapter, env e)
    isApprovedAdapterInRegistry(e,adapter)
    filtered { f-> !outOfScope(f) && !f.isView}   
    // filtered{f -> f.selector != isApprovedAdapter_instate.selector }

    
    

rule deposit_GR_zero(){ //failing due to bugs in the code
    env e;
    require e.msg.sender != currentContract;
    require maximumUnderlying(e) > 0;

    uint256 amount;
    uint256 amountMinted = deposit(e,amount);

    assert amount > 0 <=> amountMinted > 0;
}

rule more_shares_more_withdraw(){ //failing 
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

rule more_user_shares_less_underlying(method f) // failures need to check 
        filtered {f -> f.selector != transfer(address,uint256).selector && f.selector != transferFrom(address,address,uint256).selector && !f.isView }{
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

rule price_monotonicity(method f, env e) filtered { f-> !outOfScope(f) && !f.isView} { //failing due to bug in the code
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
    balanceOf(feeRecipient()) < totalSupply() / 2 //&&
            // (e.msg.sender != currentContract && e.msg.sender != Adapter &&
            // e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            // feeRecipient() != currentContract)
    {
        preserved{
        requireInvariant adapter_balance_underlying(e);
        require e.msg.sender != currentContract && e.msg.sender != Adapter &&
                e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
                feeRecipient() != currentContract;
        }
    }

    invariant adapter_balance_underlying(env e)
    balance() == 0 => balanceUnderlying(e) == 0


////////////////////////////////////////////////////////////////////////////
//                       Helper Functions                                 //
////////////////////////////////////////////////////////////////////////////

