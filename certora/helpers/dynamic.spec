methods {
    declareAndThrowAway() returns uint envfree
    regularDeclareAndThrowAway() returns uint envfree
    push1to2(uint256, uint256) returns uint, uint envfree
}

rule checkLengthIsLessThanOrEqual {
    assert declareAndThrowAway() <= regularDeclareAndThrowAway();
}

rule checkSize0 {
    assert declareAndThrowAway() == 0;
}

rule checkPushTwoDynArrays {
    uint a;
    uint b;
    uint a1;
    uint b1;
    a1, b1 = push1to2(a, b);
    assert a1 == a && b1 == b;
}