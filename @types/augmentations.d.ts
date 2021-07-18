import { Wallet } from "@ethersproject/wallet";
import { BigNumber } from "ethers";
import { IERC20 } from "../typechain/IERC20";
import { IErc20Adapter } from "../typechain/IErc20Adapter";

interface ConvertHelper {
  liquidityHolder(token: IERC20): Promise<string>;
  toWrapped(token: IERC20, amount: BigNumber, withdrawUnderlying?: boolean): Promise<BigNumber>;
  toUnderlying(token: IERC20, amount: BigNumber): Promise<BigNumber>;
  reduceLiquidity?: (token: IERC20, amount: BigNumber) => Promise<void>;
  protocolName: string;
  symbolPrefix: string;
}

declare module "mocha" {
  interface Context {
    // Util functions
    getImplementation: () => Promise<IErc20Adapter>
    initialize: (adapter: IErc20Adapter, underlying: IERC20, token: IERC20) => Promise<any>
    resetTests: (deposit?: boolean) => Promise<void>
    toUnderlying: (amount: BigNumber) => Promise<BigNumber>
    toWrapped: (amount: BigNumber, withdrawUnderlying?: boolean) => Promise<BigNumber>
    getTokenAmount: (n: number) => BigNumber
    getTokens: (n: number) => Promise<BigNumber>

    // Context data
    decimals: number
    /** @param depositSenderWrapped Address that the minted tokens are transferred from. */
    depositSenderWrapped: string
    /** @param depositReceiverWrapped Address that receives the minted tokens. */
    depositReceiverWrapped: string
    /** @param withdrawalSenderUnderlying Address that sends the redeemed tokens for a withdrawal. */
    withdrawalSenderUnderlying: string
    wallet: Wallet
    wallet1: Wallet
    wallet2: Wallet
    amountDeposited: BigNumber

    // Contracts
    adapter: IErc20Adapter
    wrapper: IERC20
    underlying: IERC20
    converter: ConvertHelper
  }
}