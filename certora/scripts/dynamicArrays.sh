spec=${1}
if [ -z ${spec} ]; then
    echo "missing spec file name argument, e.g. sanity";
    exit 1;
fi

certoraRun.py certora/harness/DynamicArraysHarness.sol \
    --verify DynamicArraysHarness:certora/${spec}.spec \
    --settings -copyLoopUnroll=4,-depth=1,-t=60 \
    --solc solc7.6