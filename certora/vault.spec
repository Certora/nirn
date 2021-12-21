/*
    This is a specification file for smart contract verification with the Certora prover.
    For more information, visit: https://www.certora.com/
*/

import "helpers/erc20.spec"

using DummyERC20Impl as underlyingToken
using SymbolicERC20Adapter as adapter

////////////////////////////////////////////////////////////////////////////
//                      Methods                                           //
////////////////////////////////////////////////////////////////////////////

methods {
    deposit(uint256) => DISPATCHER(true)
    withdraw(uint256) => DISPATCHER(true)

    // Vault functions
    deposit(uint256) returns (uint256)
    withdraw(uint256) returns (uint256)
    getCurrentLiquidityDeltas() returns (int256[])
    getAPR() returns (uint256)
    depositTo(uint256, address) returns (uint256)
    rebalance()
    rebalanceWithNewWeights(uint256[])

    withdrawAll() => DISPATCHER(true)
    withdrawUnderlying(uint256) => DISPATCHER(true)
    withdrawUnderlyingUpTo(uint256) => DISPATCHER(true)
    availableLiquidity() => DISPATCHER(true)
    underlying() returns (address) envfree

    // Vault Base functions
    decimals() returns (uint8)
    initialize(address, address, address, address)
    setMaximumUnderlying(uint256)
    setPerformanceFee(uint64)
    setReserveRatio(uint64)
    setFeeRecipient(address)
    feeRecipient() returns (address) envfree
    priceAtLastFee() returns (uint128) envfree
    claimFees() envfree
    sellRewards(address, bytes) => DISPATCHER(true)
    balanceUnderlying() returns (uint256) =>  DISPATCHER(true)
    setBalanceUnderlying(uint256) => DISPATCHER(true)
    getBalances() returns (uint256[])
    balance() returns (uint256) envfree
    totalSupply() returns uint256 envfree
    reserveBalance() returns (uint256)
    calculateFee(uint256, uint256) returns (uint256) envfree // internal normally
    getPendingFees() returns (uint256)
    getPricePerFullShare() returns (uint256)
    getPricePerFullShareWithFee() returns (uint256)

    // erc20 function
    balanceOf(address) returns(uint256) envfree

    // harness
    adaptersLength() returns uint envfree
    weightsLength() returns uint envfree
    getAdapter(uint256) returns address envfree
    // adapter
    // balanceUnderlying() => CONSTANT

    // helpers
    getBalanceSheetTotalBalance() returns (uint256) envfree
    adapter.externalUserAddress() returns (address) envfree
    // Registry 
    isApprovedAdapter(address adapter) => symbolic_approver(adapter)
    getAdapterWithHighestAPR(address _underlying) => symbolic_highest_adapter(adapter)
}

ghost symbolic_approver(address) returns bool;

ghost symbolic_highest_adapter(address) returns address;


definition outOfScope(method f) returns bool = 
                f.selector == rebalance().selector ||
                f.selector == rebalanceWithNewWeights(uint256[]).selector 
                ;

////////////////////////////////////////////////////////////////////////////
//                       Invariants                                       //
////////////////////////////////////////////////////////////////////////////

invariant total_supply_vs_balance()   // has some failures 
    totalSupply() == 0 <=> balance() == 0 
    filtered { f-> !outOfScope(f) && !f.isView}
{
    preserved with (env e) {
        requireInvariant adapter_balance_underlying(e,0);
        requireInvariant adapter_balance_underlying(e,1);
        global_requires(e);
        // require e.msg.sender != currentContract && e.msg.sender != adapter && e.msg.sender != underlyingToken && 
        //     e.msg.sender != feeRecipient() && feeRecipient() != currentContract && currentContract != underlyingToken;
        require underlying() == underlyingToken;
    }
    /*
    preserved withdrawFromUnusedAdapter(address adapter) with (env e){
        // requireInvariant adapter_balance_underlying(e);
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    preserved withdrawUnderlying(uint256 amount) with (env e){
        // requireInvariant adapter_balance_underlying(e);
    require e.msg.sender != currentContract && e.msg.sender != Adapter &&
            e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
            feeRecipient() != currentContract;
    }
    */
    preserved initialize(address _underlying, address _rewardsSeller, address _feeRecipient, address _owner) with (env e) {
        require underlyingToken.balanceOf(e, currentContract) == 0;   
        require symbolic_highest_adapter(_underlying) == adapter;
        require adapter.balanceUnderlying(e) == 0;
    }

    preserved transfer(address to, uint256 amount) with (env e) {
        requireInvariant adapter_balance_underlying(e,0);
        requireInvariant adapter_balance_underlying(e,1);
        global_requires(e);
        require to != adapter;
    }

    
    preserved transferFrom(address from, address to, uint256 amount) with (env e) {
        requireInvariant adapter_balance_underlying(e,0);
        requireInvariant adapter_balance_underlying(e,1);
        global_requires(e);
        require to != adapter && from != adapter;
    }
    
    preserved sellRewards(address rewardsToken, bytes params) with (env e){
        require underlying() == underlyingToken;
        requireInvariant adapter_balance_underlying(e,0);
        global_requires(e);
        require rewardsToken != currentContract && rewardsToken != underlyingToken;
        
    }
    
}

/* STATUS: 
Passing
*/
invariant balanceSheet_equals_balance() 
    balance() == getBalanceSheetTotalBalance()
    filtered { f-> !outOfScope(f) && !f.isView}


invariant totalSupply_GE_balance()
totalSupply() >= balance()
filtered { f-> !outOfScope(f) && !f.isView}
{
        preserved with (env e) {
        requireInvariant adapter_balance_underlying(e,0);
        requireInvariant adapter_balance_underlying(e,1);
        global_requires(e);
    }
    preserved transfer(address to, uint256 amount) with (env e) {
        requireInvariant adapter_balance_underlying(e,0);
        requireInvariant adapter_balance_underlying(e,1);
        global_requires(e);
        require to != adapter ;
    }    
    preserved transferFrom(address from, address to, uint256 amount) with (env e) {
        requireInvariant adapter_balance_underlying(e,0);
        requireInvariant adapter_balance_underlying(e,1);
        global_requires(e);
        require to != adapter && from != adapter;
    }
    preserved depositTo(uint256 amount, address to) with (env e) {
        requireInvariant adapter_balance_underlying(e,0);
        requireInvariant adapter_balance_underlying(e,1);
        global_requires(e);
        require to != adapter;
    }
    preserved initialize(address _underlying, address _rewardsSeller, address _feeRecipient, address _owner) with (env e) {
        require underlyingToken.balanceOf(e, currentContract) == 0;   
        require symbolic_highest_adapter(_underlying) == adapter;
        require adapter.balanceUnderlying(e) == 0;
    }
}
////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// deposit x and deposit y is the same as deposit x+ y
/* STATUS: 
*/
rule additive_deposit() {
    env e;
    // require total supply = total balance 
    uint256 x; uint256 y;

    // store state
    storage initStorage = lastStorage;

    global_requires(e);

    uint256 shares_x = deposit(e, x);
    uint256 shares_y = deposit(e, y);
    // without these checks the dust (roundoff) bug is showed off
    require shares_x != 0;
    require shares_y != 0;

    uint256 balance_sequential = balance();

    // return to storage state
    uint256 shares_xy = deposit(e, x + y) at initStorage;
    uint256 balance_additive = balance();

    assert balance_sequential == balance_additive, "additivity of balance failed";
}

rule same_deposit_same_shares(){
    env e;
    uint256 x; uint256 y;

    // requireInvariant totalSupply_GE_balance();

    uint256 balance_1 = balance();
    uint256 supply_1 = totalSupply();
    uint256 fee_1 = calculateFee(balance_1,supply_1);
    uint256 priceAtLastFee_1 = priceAtLastFee();
    
    require balance_1 == 0 && supply_1 == 0;

    uint256 shares_x = deposit(e, x);
    
    uint256 balance_2 = balance();
    uint256 supply_2 = totalSupply();
    uint256 fee_2 = calculateFee(balance_2,supply_2);
    uint256 priceAtLastFee_2 = priceAtLastFee();
    
    uint256 shares_y = deposit(e, y);
    
    uint256 balance_3 = balance();
    uint256 supply_3 = totalSupply();
    uint256 fee_3 = calculateFee(balance_3,supply_3);
    uint256 priceAtLastFee_3 = priceAtLastFee();

    require shares_x >= 1000 ;
    require performanceFee(e) <= 10^17;

    global_requires(e);

    // assert x == y => shares_x * 11 / 10 > shares_y;
    assert x == y => shares_x * 2  > shares_y;
    // assert x == y => shares_x == shares_y;

}
// might as well write this to go with additive deposit
/* STATUS: 
 timing out
*//*
rule additive_withdraw() { 
    env e;
    uint256 x; uint256 y;
    // store state

    storage initStorage = lastStorage;

    global_requires(e);

    uint256 x_out = withdraw(e, x);
    uint256 y_out = withdraw(e, y);

    uint256 balance_sequential = balance();

    // return to storage state
    uint256 xy_out = withdraw(e, x + y) at initStorage;
    uint256 balance_additive = balance();

    assert balance_sequential == balance_additive, "additivity of balance failed";
    // assert x_out + y_out == xy_out, "additivity of output failed";
}*/

/* STATUS: 
generates cex on deposit and withdraw
on deposit the rounding error causes the value per share to be valued, calling a second fee, which mints indexed an extra share on a deposit of 1
on withdraw a new affect of a previously found error. In the case where a user withdraws but does not receive any underlying, shares are burned but no 
balance is withdrawn. This changes the ratio of balance to shares, causing the system to take fees again
*/
rule no_double_fee(method f) filtered {f -> (f.selector == deposit(uint256).selector ||
                                            f.selector == withdrawUnderlying(uint256).selector ||
                                             f.selector == withdraw(uint256).selector) }
{     
    env e; calldataarg args;

    require e.msg.sender != feeRecipient();
    require e.msg.sender != currentContract;

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
    
    assert indexed_shares_pre == indexed_shares_post, "fee claimed on balance"; 
    assert calculateFee(balance_post, supply_post) == 0, "repeated fee left to claim";
}

// special condition for depositTo
rule no_double_fee_depositTo() {
env e; calldataarg args;

    global_requires(e);

    // claimFees(); // should (with proper behavior) ensure there are no residual fees to collect    

    uint256 balance_pre = balance();
    uint256 supply_pre = totalSupply();
    uint256 indexed_shares_pre = balanceOf(feeRecipient());

    require calculateFee(balance_pre, supply_pre) == 0; // to reduce timeouts, trying to start the rule in the state where fees have been collected
    require indexed_shares_pre < supply_pre; // cex where indexed had all shares

    uint amount;
    
    address to;
    require to != feeRecipient();

    depositTo(e, amount, to);
    
    uint256 supply_post = totalSupply();
    uint256 balance_post = balance();
    uint256 indexed_shares_post = balanceOf(feeRecipient());
    
    // if a fee was claimed the shares of index will go up, this 
    assert indexed_shares_pre == indexed_shares_post, "fee claimed on balance"; // no cex when this is the only assert
    assert calculateFee(balance_post, supply_post) == 0, "repeated fee left to claim";
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
    uint256 underlying_balance = adapter.balanceUnderlying(e);

    require calculateFee(balance_pre, supply_pre) == 0;

    // drops balance underlying
    uint256 underlying_balance_drop;
    require underlying_balance_drop < underlying_balance;
    require adapter.externalUserAddress() != currentContract;
    adapter.setBalanceUnderlying(e, underlying_balance_drop);

    uint256 balance_drop = balance();
    uint256 supply_drop = totalSupply();
    assert calculateFee(balance_drop, supply_drop) == 0, "fee claimed on drop?";

    // balance underlying goes back up
    uint256 underlying_balance_end;
    require underlying_balance_end <= underlying_balance;
    require underlying_balance_end > underlying_balance_drop;
    adapter.setBalanceUnderlying(e, underlying_balance_end);

    uint256 balance_raise = balance();
    uint256 supply_raise = totalSupply();
    assert calculateFee(balance_raise, supply_raise) == 0, "double fee claimed on raise";
}

/* STATUS: 

*/
// this was specifically to show withdraw underlying fails this property, but is good to test on other functions
/*
rule shares_correlate_balance(method f) filtered { f-> !outOfScope(f) && !f.isView }
{
    env e; calldataarg args;

    uint256 balance_pre = balance();
    uint256 supply_pre = totalSupply();

    global_requires(e);

    if f.selector == sellRewards(address ,bytes).selector{
        address rewardsToken;
        bytes   params;
        require rewardsToken != currentContract && rewardsToken != underlyingToken;
        sellRewards(e,rewardsToken,params);
    }
    else
    f(e, args);

    uint256 balance_post = balance();
    uint256 supply_post = totalSupply();
    assert balance_pre != balance_post <=> supply_pre != supply_post, "balance or shares changed without the other";
}*/

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

    uint256 balance = balance();
    uint256 supply = totalSupply();
    require balance > 0;
    require supply > 0;

    // times out with the ratio atm
    // uint256 ratio = balance * 10 / supply;
    // require ratio < 20 && ratio > 5; // capping at balance:supply of 2:1 for now to simulate a relatively healthy vault

    uint256 transferAmount;
    require transferAmount > 1000; // to make things interesting (must be greater than 0 for a good cex to be generated)

    uint256 shares; 
    uint256 depositAmount = shares * balance() / totalSupply();

    // transfer to setup
    underlyingToken.transfer(e, underlying(), transferAmount);

    uint256 underlyingBack = withdraw(e, shares);
    assert underlyingBack <= depositAmount + transferAmount, "value taken from vault";
}


invariant integrity_adapter_list(uint i, uint j)
    // equal size
    adaptersLength() == weightsLength() &&
    // uniqueness
    ( i != j => getAdapter(i) != getAdapter(j) )
    filtered { f-> !outOfScope(f) && !f.isView}

invariant onlyApprovedAdapter(address adapter, uint256 i, env e)
    getAdapter(i) == adapter => isApprovedAdapterInRegistry(e,adapter)
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

    global_requires(e);

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

    global_requires(e);

    if f.selector == depositTo(uint256,address).selector{
        uint256 amount;
        depositTo(e, amount, e.msg.sender);
    }
    else 
    if f.selector == sellRewards(address ,bytes).selector{
        address rewardsToken;
        bytes   params;
        require rewardsToken != currentContract && rewardsToken != underlyingToken;
        sellRewards(e,rewardsToken,params);
    }
    else{
        calldataarg args;
        f(e,args);
    }
    
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
/*    
    invariant collect_fees_check(env e)
    balanceOf(feeRecipient()) < totalSupply() / 2 
    {
        preserved{
        requireInvariant adapter_balance_underlying(e,0);
        require e.msg.sender != currentContract && e.msg.sender != adapter &&
                e.msg.sender != underlyingToken && e.msg.sender != feeRecipient() &&
                feeRecipient() != currentContract;
        }
    }
*/
    invariant adapter_balance_underlying(env e, uint256 i)
    balance() == 0 && getAdapter(i) == adapter => adapter.balanceUnderlying(e) == 0 {
        preserved {
            require adaptersLength() <= 3;
            requireInvariant integrity_adapter_list(i,0);
            requireInvariant integrity_adapter_list(i,1);
            requireInvariant integrity_adapter_list(i,2);
        }
    }


////////////////////////////////////////////////////////////////////////////
//                       Helper Functions                                 //
////////////////////////////////////////////////////////////////////////////

function global_requires(env e){
require e.msg.sender != currentContract && e.msg.sender != adapter && e.msg.sender != underlyingToken && 
    e.msg.sender != feeRecipient() && feeRecipient() != currentContract && feeRecipient() != adapter && 
    currentContract != underlyingToken && rewardsSeller(e) != adapter;
}