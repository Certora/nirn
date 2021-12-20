/*
    This is a specification file for smart contract verification with the Certora prover.
    For more information, visit: https://www.certora.com/
*/

import "helpers/erc20.spec"

import "vault.spec"
using NirnVault as Vault

////////////////////////////////////////////////////////////////////////////
//                      Methods                                           //
////////////////////////////////////////////////////////////////////////////

methods {
    // contract methods
    addVaultFactory(address)
    removeVaultFactory(address)
    addVault(address)
    removeVault(address)
    addProtocolAdapter(address) returns (uint256)
    removeProtocolAdapter(address)
    addTokenAdapter(address)
    addTokenAdapters(address[])
    removeTokenAdapter(address)
    getVaultsList() returns (address[])
    haveVaultFor(address) returns (bool)
    getProtocolAdaptersAndIds() returns (address[], uint256[])
    getProtocolMetadata(uint256) returns (address, string)
    getProtocolForTokenAdapter(address) returns (address)
    isSupported(address) returns (bool)
    getSupportedTokens() returns (address[])
    isApprovedAdapter(address) returns (bool)
    getAdaptersList(address) returns (address[])
    getAdapterForWrapperToken(address) returns (address)
    getAdaptersCount(address) returns (uint256)
    getAdaptersSortedByAPR(address) returns (address[], uint256[])
    getAdaptersSortedByAPRWithDeposit(address, uint256, address) returns (address[], uint256[])
    getAdapterWithHighestAPR(address) returns (address, uint256)
    getAdapterWithHighestAPRForDeposit(address, uint256, address) returns (address, uint256)

    vaultsByUnderlying(address) returns (address) envfree
    protocolAdapters(uint256) returns (address) envfree
    protocolAdapterIds(address) returns (uint256) envfree
    
    // harness
    vaultsContains(address) returns (bool) envfree
    isProtocolOrOwner(address) returns (bool) envfree
    getVaultUnderlying(address) returns (address) envfree

    // attempt to dispatch this function with the vault while not linking
    // Vault.underlying() returns (address) => DISPATCHER(true);
    underlying() returns (address) => DISPATCHER(true)

}

////////////////////////////////////////////////////////////////////////////
//                       Invariants                                       //
////////////////////////////////////////////////////////////////////////////

// underlying corresponds to a single vault
/* STATUS
FAILS only on ADDVAULT - seems they allow for this behavior - should we reccomend that they don't?
*/
invariant underlying_single_vault(address x, address y)
    vaultsByUnderlying(x) != 0 => vaultsByUnderlying(x) != vaultsByUnderlying(y)
{ preserved {
    require x != y;
    require x != 0;
    require y != 0;
}}


// if a vault exists and is registered, then the underlying of that vault should properly map back to itself
/* 
STATUS
PASSING
*/
invariant vaults_correlate_underlying(address vault)
    vaultsContains(vault) => vaultsByUnderlying(getVaultUnderlying(vault)) == vault
{ preserved {
    require vault == Vault;
} preserved removeVault(address removed_vault) with (env e) {
    require removed_vault == vault;
}}
////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// only owner or whitelist protocol can add or edit adapters
/* Status
PASSING
*/
rule adapter_mutate_safe(method f) { // TODO
    env e; calldataarg args;
    uint256 ID;
    address adapter_pre = protocolAdapters(ID);

    f(e, args);

    address adapter_post = protocolAdapters(ID);

    // this is what they do in their code, I'm not sure if this will show anything
    assert adapter_pre != adapter_post => isProtocolOrOwner(e.msg.sender), "non protocol or owner changed adapters";
}



