certoraRun contracts/AdapterRegistry.sol certora/harness/DummyERC20Impl.sol certora/harness/SymbolicERC20Adapter.sol \
    --verify AdapterRegistry:certora/vaultSanity.spec \
    --optimistic_loop --loop_iter 1 \
    --settings -copyLoopUnroll=1,-depth=1,-t=60 \
    --msg "AdapterRegistry Sanity" \
    --solc solc7.6 \
    --staging 

    # --link AdapterRegistry:underlying=DummyERC20Impl \
