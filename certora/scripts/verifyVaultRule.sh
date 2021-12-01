if [ -z "$2" ]
  then
    echo "Incorrect number of arguments"
    echo ""
    echo "Usage: (from git root)"
    echo "  ./certora/scripts/`basename $0` [rule] [message describing the run]"
    echo ""
    exit 1
fi

rule=$1
msg=$2
shift 2

certoraRun contracts/vaults/NirnVault.sol certora/harness/DummyERC20Impl.sol certora/harness/SymbolicERC20Adapter.sol \
    --verify NirnVault:certora/vault.spec \
    --optimistic_loop --loop_iter 1 \
    --settings -copyLoopUnroll=1,-depth=1,-t=600,-postProcessCounterExamples=true \
    --cache indexed \
    --msg "indexed vault ${rule} ${msg}" \
    --rule ${rule} \
    --link NirnVault:underlying=DummyERC20Impl \
    --solc solc7.6 \
    --staging
