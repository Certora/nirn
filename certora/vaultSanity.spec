methods {
	deposit(uint256) => DISPATCHER(true)
	withdraw(uint256) => DISPATCHER(true)
	withdrawAll() => DISPATCHER(true)
	withdrawUnderlying(uint256) => DISPATCHER(true)
	withdrawUnderlyingUpTo(uint256) => DISPATCHER(true)
}

rule sanity(method f) {
	env e;
	calldataarg arg;
	sinvoke f(e, arg);
	assert false;
}