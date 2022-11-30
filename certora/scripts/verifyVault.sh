certoraRun contracts/vaults/NirnVault.sol certora/harness/DummyERC20Impl.sol certora/harness/SymbolicERC20Adapter.sol \
    --verify NirnVault:certora/vault.spec \
    --optimistic_loop --loop_iter 1 \
    --rule $1 \
    --settings -copyLoopUnroll=1,-depth=16,-t=400,-postProcessCounterExamples=true --cache indexed \
    --msg "indexed vault $1 $2" \
    --link NirnVault:underlying=DummyERC20Impl \
    --solc solc7.6 \
    --staging