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

    // attempt to dispatch this function with the vault while not linking
    // Vault.underlying() returns (address) => DISPATCHER(true);

}

////////////////////////////////////////////////////////////////////////////
//                       Invariants                                       //
////////////////////////////////////////////////////////////////////////////

// underlying corresponds to a single vault
// originally the rule was there can't be more than 1 vault for a single underlying, but their mapping doesn't even allow this
// Q: is this invariant something the syste should hold
invariant underlying_single_vault(address underlying1, address underlying2)
    vaultsByUnderlying(underlying1) != vaultsByUnderlying(underlying2)
    

////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// only owner or whitelist protocol can add or edit adapters
rule adapter_mutate_onlyOwnerOrProtocol(method f) { // TODO
    env e; calldataarg args;
    uint256 ID;
    address adapter_pre = protocolAdapters(ID);

    f(e, args);

    address adapter_post = protocolAdapters(ID);

    // this is what they do in their code, I'm not sure if this will show anything
    assert adapter_pre != adapter_post => isProtocolOrOwner(e.msg.sender), "non protocol or owner changed adapters";
}

invariant vaults_correlate_underlying(address vault)
    vaultsContains(vault) => underlying() == vaultsByUnderlying(vault)

