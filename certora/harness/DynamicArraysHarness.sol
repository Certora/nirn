import "../../contracts/libraries/DynamicArrays.sol";

contract DynamicArraysHarness {
    using DynamicArrays for uint256[];

    uint len;
    function declareAndThrowAway() public returns (uint256) {
        uint256[] memory a = DynamicArrays.dynamicUint256Array(len);
        return a.length;
    }

    function regularDeclareAndThrowAway() public returns (uint256) {
        uint256[] memory a = new uint256[](len);
        return a.length;
    }

    function push1to2(uint256 a, uint256 b) public returns (uint256, uint256) {
        require (len > 1);
        uint256[] memory aa = DynamicArrays.dynamicUint256Array(len);
        aa.dynamicPush(a);
        uint256[] memory ab = DynamicArrays.dynamicUint256Array(len);
        ab.dynamicPush(b);
        return (aa[aa.length-1], ab[ab.length-1]);
    }

}