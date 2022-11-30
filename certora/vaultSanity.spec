methods {
	deposit(uint256) => DISPATCHER(true)
	withdraw(uint256) => DISPATCHER(true)
	withdrawAll() => DISPATCHER(true)
	withdrawUnderlying(uint256) => DISPATCHER(true)
	withdrawUnderlyingUpTo(uint256) => DISPATCHER(true)


	// harness
	adaptersLength() returns uint envfree
}

rule sanity(method f) {
	// let's make it harder
	require adaptersLength() > 0;
	env e;
	calldataarg arg;
	sinvoke f(e, arg);
	assert false;
}