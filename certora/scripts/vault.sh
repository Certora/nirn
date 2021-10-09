certoraRun.py contracts/vaults/NirnVault.sol certora/harness/DummyERC20Impl.sol \
    --verify NirnVault:certora/vaultSanity.spec \
    --optimistic_loop --loop_iter 1 \
    --settings -copyLoopUnroll=1,-depth=1,-t=60 \
    --msg "nirn initial run on vault" \
    --link NirnVault:underlying=DummyERC20Impl \
    --solc solc7.6 --staging shelly/forOZ # --method "rebalance()"