methods {
    vaultsByUnderlying(address) returns (address) envfree
    protocolAdapters(uint256) returns (address) envfree
    protocolAdapterIds(address) returns (uint256) envfree

    // harness
    vaultsContains(address) returns (bool) envfree
    isProtocolOrOwner(address) returns (bool) envfree
    getVaultUnderlying(address) returns (address) envfree

    underlying() returns (address) => DISPATCHER(true)
}

rule sanity(method f) {
	// let's make it harder
	env e;
	calldataarg arg;
	sinvoke f(e, arg);
	assert false;
}