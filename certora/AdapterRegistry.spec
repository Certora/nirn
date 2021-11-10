/*
    This is a specification file for smart contract verification with the Certora prover.
    For more information, visit: https://www.certora.com/
*/

import '../helpers/erc20.spec'


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
    _addTokenAdapter(IErc20Adapter, uint256)
    addTokenAdapter(address)
    addTokenAdapters(address[])
    removeTokenAdapter(address)
    getVaultsList() returns (address[])
    haveVaultFor(address) returns (bool)
    getProtocolAdaptersAndIds() returns (address[], uint256[])
    getProtocolMetadata(uint256) returns (address, string)
    getProtocolForTokenAdapter(address) returns (address)
    isSupported(address) returns (bool)
    getSupportedTokens() returns (address[]
    isApprovedAdapter(address) returns (bool)
    getAdaptersList(address) returns (address[])
    getAdapterForWrapperToken(address) returns (address)
    getAdaptersCount(address) returns (uint256)
    getAdaptersSortedByAPR(address) returns (address[], uint256[])
    getAdaptersSortedByAPRWithDeposit(address, uint256, address) returns (address[], uint256[])
    getAdapterWithHighestAPR(address) returns (address, uint256)
    getAdapterWithHighestAPRForDeposit(address, uint256, address) returns (address, uint256)

    // external method summaries
}

////////////////////////////////////////////////////////////////////////////
//                       Invariants                                       //
////////////////////////////////////////////////////////////////////////////

// Adapters cant go over the maximum amount
invariant adapter_constrained_max_length() // TODO

////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

// only owner or whitelist protocol can add or edit adapters
rule adapter_mutate_onlyOwnerOrProtocol() { // TODO
    assert false, "not yet implemented";
}

// we discussed this but I'm not sure how it would play out
rule state_change_onlyOwner() { // TODO
    assert false, "not yet implemented"
}
