import "./IERC20.sol";
import "./SafeMath.sol";

contract SymbolicERC20Adapter {
    using SafeMath for uint256;

/* ========== Metadata ========== */

  address _underlying; 
  address _token;
  string _name;
  
  // to be forced as nondet
  uint _availableLiquidityDummy;
  uint _toUnderlyingAmountDummy;
  uint _toWrappedAmountDummy;
  uint _aprDummy;
  uint _hypotheticalAprDummy;
  uint _balanceWrappedDummy; // probably can connect to something
  uint _balanceUnderlyingDummy; // probably can connect to something

  function underlying() external view returns (address) { return _underlying; }

  function token() external view returns (address) { return _token; }

  function name() external view returns (string memory) { return _name; }

  function availableLiquidity() external view returns (uint256) { return _availableLiquidityDummy; }

/* ========== Conversion ========== */

  function toUnderlyingAmount(uint256 tokenAmount) external view returns (uint256) { return _toUnderlyingAmountDummy; }

  function toWrappedAmount(uint256 underlyingAmount) external view returns (uint256) { return _toWrappedAmountDummy; }

/* ========== Performance Queries ========== */

  function getAPR() external view returns (uint256) { return _aprDummy; }

  function getHypotheticalAPR(int256 liquidityDelta) external view returns (uint256) { return _hypotheticalAprDummy; }

  // it looks like this function is only used by UI
  function getRevenueBreakdown()
    external
    view
    returns (
      address[] memory assets,
      uint256[] memory aprs
    ) {}

/* ========== Caller Balance Queries ========== */

  function _balanceWrapped() private view returns (uint256) { return _balanceWrappedDummy; }
  function balanceWrapped() external view returns (uint256) { return _balanceWrapped(); }

  function balanceUnderlying() external view returns (uint256) { return _balanceUnderlyingDummy; }

/* ========== Interactions ========== */

  mapping (uint => mapping (uint => uint)) underlyingToAmount;
  mapping (uint => mapping (uint => uint)) amountToUnderlying;
  uint exchangeMapIdx;

  bool doesSelfTrack;
  mapping (address => uint) mintTracking;

  function deposit(uint256 amountUnderlying) external returns (uint256 amountMinted) {
      amountMinted = underlyingToAmount[exchangeMapIdx++][amountUnderlying];
      IERC20(_underlying).transferFrom(msg.sender, address(this), amountUnderlying);
      if (doesSelfTrack) {
          mintTracking[msg.sender] = mintTracking[msg.sender].add(amountMinted);
      }
  }

  function _withdraw(uint256 amountToken) private returns (uint256 amountReceived) {
      amountReceived = amountToUnderlying[exchangeMapIdx++][amountToken];
      IERC20(_underlying).transferFrom(msg.sender, address(this), amountReceived);
      if (doesSelfTrack) {
          mintTracking[msg.sender] = mintTracking[msg.sender].sub(amountToken);
      }
  }
  function withdraw(uint256 amountToken) external returns (uint256 amountReceived) {
      _withdraw(amountToken);
  }

  function withdrawAll() external returns (uint256 amountReceived) {
    if (!doesSelfTrack) { 
        _withdraw(_balanceWrapped());
    } else { 
        _withdraw(mintTracking[msg.sender]);
    }
  }

  function withdrawUnderlying(uint256 amountUnderlying) external returns (uint256 amountBurned) {
        amountBurned = underlyingToAmount[exchangeMapIdx++][amountUnderlying];
        _withdraw(amountBurned);
  }

  function withdrawUnderlyingUpTo(uint256 amountUnderlying) external returns (uint256 amountReceived) {
      amountReceived = underlyingToAmount[exchangeMapIdx++][amountUnderlying];
      uint bal;
      if (!doesSelfTrack) {
          bal = _balanceWrapped();         
      } else {
          bal = mintTracking[msg.sender];
      }

      uint min = amountReceived > bal ? bal : amountReceived;

      _withdraw(min);
  }
}
