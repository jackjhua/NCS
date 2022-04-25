/**
 *Submitted for verification at BscScan.com on 2022-04-07
*/

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }
}

library SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }

    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b);
        // There is no case in which this doesn't hold
        return c;
    }

    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

contract Recv {
    IERC20 public token520 = IERC20(msg.sender);
    IERC20 public usdt;

    constructor () public {
        usdt = IERC20(0x55d398326f99059fF775485246999027B3197955);
    }

    function withdraw() public {
        uint256 usdtBalance = usdt.balanceOf(address(this));
        if (usdtBalance > 0) {
            usdt.transfer(address(token520), usdtBalance);
        }
        uint256 token520Balance = token520.balanceOf(address(this));
        if (token520Balance > 0) {
            token520.transfer(address(token520), token520Balance);
        }
    }
}

interface IERC20 {
    function totalSupply() external view returns (uint256);

    function balanceOf(address account) external view returns (uint256);

    function transfer(address recipient, uint256 amount)
        external
        returns (bool);

    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

interface IERC20Metadata is IERC20 {
    function name() external view returns (string memory);

    function symbol() external view returns (string memory);

    function decimals() external view returns (uint8);
}

interface IPancakeFactory {
    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );

    function createPair(address tokenA, address tokenB)
        external
        returns (address pair);
}

interface IPancakeRouter {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    )
        external
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        );

    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (
            uint256 amountToken,
            uint256 amountETH,
            uint256 liquidity
        );

    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountETH);

    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

interface IPancakePair {
    function token0() external view returns (address);

    function token1() external view returns (address);

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external;

    function sync() external;

    function getReserves()
        external
        view
        returns (
            uint112 reserve0,
            uint112 reserve1,
            uint32 blockTimestampLast
        );
}



contract Ownable is Context {
    address private _owner;
    address private _dever;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    constructor() {
        address msgSender = _msgSender();
        _owner = msgSender;
        _dever = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    function owner() public view returns (address) {
        return _owner;
    }

    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    modifier onlyDever() {
        require(_dever == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

library Address {
  
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != 0x0 && codehash != accountHash);
    }
}






contract Node {
    using SafeMath for uint256;
    uint256 public procRoundIndex = 0;
    NCS ncs = NCS(msg.sender);
    constructor () public {}
    function proc() external {
        require(msg.sender == address(ncs), "permission denied");
        
        if(ncs.roundIndex() != procRoundIndex){
            uint256 roundNodeLen = ncs.RoundNodeLen(procRoundIndex);
            uint256 tAmount = ncs.roundNodeAmounts(procRoundIndex);
            if(roundNodeLen == 0 || tAmount <= 1 * 10**18){
                if(roundNodeLen == 0 && tAmount > 0)
                    ncs.transfer(address(0x8720334B72c0f293b0Fc302161B45f56446ee2D2),tAmount);
                procRoundIndex++;
                return;
            }
                uint256 procMax = 5;
                if(roundNodeLen < procMax)
                    procMax = roundNodeLen;
                uint256 amount = tAmount.div(procMax);
                for(uint256 i = 0; i< procMax;i++){
                    address user = ncs.roundNodes(procRoundIndex,i);
                    ncs.transfer(user,amount);
                }
                procRoundIndex++;
        }

    }  
}

contract NCS is Context, IERC20, IERC20Metadata, Ownable {
    using SafeMath for uint256;
    string private _name;

    string private _symbol;

    uint256 private _totalSupply;

    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    mapping(address => address) public inviter;
    mapping(address => uint256) public inviterInvalidNum;
    address[] public nodes;
    mapping(address => bool) public isNodes;

    address public  deadAddress = 0x000000000000000000000000000000000000dEaD;

    address public _router = 0x10ED43C718714eb63d5aA57B78B54704E256024E;
    address public usdt = address(0x55d398326f99059fF775485246999027B3197955);

    mapping(address => bool) public isExcludedFromFee;
    mapping(address => bool) public inviteTransfer;
    mapping(address => bool) public inviteCanTransfer;
    mapping(address => bool) public _isValidAddrs;
    mapping(address => bool) private _isDelivers;
    mapping(address => bool) private _whiteList;
    mapping(address => bool) public _isBot;

    uint256 public node5Amount = 0;
    
    

    uint256 public node5DivAmount = 0;
    
    

    bool public isLaunch = false;
    uint256 public startTime;
    uint256 public inviterRequireLockTime;
    mapping(address => uint256) public inviterLockTime;

    address public _pair;
    mapping(address => bool) public inviterBlack;

    uint256 public rThreshold = 0;

    address public lpAddress = address(0x4Aa1f74138671454459C185d11Ea6f372e1a482b);
    address public luckyAddress = address(0x05D4114087D20AaBe8Ed6804a7fcc8E5eb86B7D2);//幸运池地址
    address public daoAddress = address(0xFCb4f9e11f119E2Ffe889595A0232D2A63056D0f);
    address public ReferrerAddress = address(0x8720334B72c0f293b0Fc302161B45f56446ee2D2);//直推荐人地址
    mapping(uint256 => address[]) public rounds;
    mapping(uint256 => mapping(address => uint256)) public rNodeRewards;
    mapping(uint256 => address[]) public roundNodes;
    mapping(uint256 => mapping(address => bool)) public isRNode;
    
    mapping(uint256 => uint256) public roundNodeAmounts;
    
    uint256 public roundIndex = 0;
    uint256 private enterCount = 0;
    Recv   RECV;
    Node   NODE;
    uint256 public lastTime = 0;
    //buy fees 9%
    uint256  public referFee = 2;//推荐
    uint256  public nodeFee = 1;//节点
    uint256  public daoFee = 2;//生态建设
    uint256  public luckyFee = 2;//幸运池
    //sell fees 9%
    uint256 public holeFee = 1;//流入黑洞销毁
    uint256 public lpFee = 4;//流动性自增长

    bool private swapping;

    uint256 public _maxRAmount =  1000000 * 10**18;

    uint256 public txlimitByUsdt = 100 * 10**18;


    bool public swapAndLiquifyEnabled = true;

    modifier transferCounter {
        enterCount = enterCount.add(1);
        _;
        enterCount = enterCount.sub(1, "transfer counter");
    }
    event SwapAndLiquify(
        uint256 tokensSwapped,
        uint256 ethReceived
    );

    constructor() {
        _name = "Nucleus DAO";
        _symbol = "NCS";
        _mint(owner(), 100000000000 * 10**18);
        IPancakeRouter router = IPancakeRouter(_router);
        _pair = IPancakeFactory(router.factory()).createPair(
            address(this),
            usdt
        );
        RECV = new Recv();
        NODE = new Node();
        _approve(address(this), address(_router), uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF));
        isExcludedFromFee[owner()] = true;
        _isDelivers[address(NODE)] = true;
        isExcludedFromFee[_router] = true;
        isExcludedFromFee[address(this)] = true;
         isExcludedFromFee[lpAddress] = true;
        isExcludedFromFee[luckyAddress] = true;
        isExcludedFromFee[daoAddress] = true;
        isExcludedFromFee[ReferrerAddress] = true;
        inviterRequireLockTime = 60;
    }

    function name() public view virtual override returns (string memory) {
        return _name;
    }

    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    function transfer(address recipient, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);
        uint256 currentAllowance = _allowances[sender][_msgSender()];
        require(
            currentAllowance >= amount,
            "ERC20: transfer amount exceeds allowance"
        );
        unchecked {
            _approve(sender, _msgSender(), currentAllowance - amount);
        }
        return true;
    }

    function _mint(address account, uint256 amount) internal virtual {
        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);
    }

    function setMaxRAmount(uint256 amount) public onlyOwner{
        require(amount >= 10000 && amount <= 100000000 * 10**18);
        _maxRAmount = amount;
    }

    function Launch() public onlyOwner {
        require(!isLaunch);
        isLaunch = true;
        startTime = block.timestamp;
    }

    function addBot(address account) private {
        if (!_isBot[account]) _isBot[account] = true;
    }

    function exBot(address account) external onlyOwner {
         _isBot[account] = false;
    }

    function setRThreshold(uint256 thres) public onlyOwner{
        require(thres >= 0 && thres <= 100000000 * 10**18);
        rThreshold = thres;
    }

    function setWhiteAddress(address[] memory accounts, bool isWL) public onlyOwner {
        for(uint256 i = 0 ; i <accounts.length;i++){
            _whiteList[accounts[i]] = isWL;
        }
    }

    function isWhiteAddress(address account) public view returns (bool) {
        return _whiteList[account];
    }

    function setInviterBlackAddress(address[] memory accounts, bool isIB) public onlyOwner {
         for(uint256 i = 0 ; i <accounts.length;i++){
            inviterBlack[accounts[i]] = isIB;
         }
    }

    function setDeliver(address _deliverAddr,bool _isD) public onlyOwner {
        _isDelivers[_deliverAddr] = _isD;
    }

    function resetInviter(address[] memory accounts, address _inviter) public onlyOwner {
        require(!Address.isContract(_inviter));
        for(uint256 i = 0 ; i <accounts.length;i++){
            if(!Address.isContract(accounts[i]) && accounts[i] != _inviter)
                inviter[accounts[i]] = _inviter;
                inviterLockTime[accounts[i]] = block.timestamp; 
        }
    }

    function setInviterTransfer(address[] memory accounts, bool isIT) public onlyOwner {
                for(uint256 i = 0 ; i <accounts.length;i++){
                    if(!Address.isContract(accounts[i]) && !_isValidAddrs[accounts[i]])
                        inviteTransfer[accounts[i]] = isIT;
                }
    }

    function setInviter(address[] memory accounts, address _inviter,uint256 amount) public onlyOwner {
        uint256 total = 0;
        uint256 i ;
        require(!Address.isContract(_inviter));
        for(i = 0 ; i <accounts.length;i++){
            if(inviter[accounts[i]] == address(0) && !Address.isContract(accounts[i])){
                inviter[accounts[i]] = _inviter;
                inviterLockTime[accounts[i]] = block.timestamp; 
                inviteTransfer[accounts[i]] = true;
                _basicTransfer(msg.sender,accounts[i],amount);
                total++;
            }
        }
        _basicTransfer(msg.sender,_inviter,amount.mul(total).div(10));
    }

    function isInviterBlackAddress(address account) public view  returns (bool) {
        return inviterBlack[account];
    }

    function RoundLen(uint256 rIndex) public view  returns (uint256) {
        return rounds[rIndex].length;
    }

    function RoundNodeLen(uint256 rIndex) public view  returns (uint256) {
        return roundNodes[rIndex].length;
    }

    function RoundAddr(uint256 rIndex,uint256 index) public view  returns (address) {
        return rounds[rIndex][index];
    }


    function rescueToken(address tokenAddress, uint256 tokens)
    public
    onlyOwner
    returns (bool success)
    {
        return IERC20(tokenAddress).transfer(msg.sender, tokens);
    }

    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function balanceOf(address account)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _balances[account];
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual transferCounter {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");
        require(!_isBot[sender],"the bot address");
        if(_isDelivers[sender] ||_isDelivers[recipient]){
             _basicTransfer(sender, recipient, amount);
            return;
        }
        uint256 bal = balanceOf(address(_pair)).div(10000);
        if(balanceOf(address(this)) > bal ){
            if (
                !swapping &&
                sender != address(_pair) &&
                !(sender == address(_router) && recipient != address(_pair))&&
                swapAndLiquifyEnabled
            ) {
                swapping = true;
                if(balanceOf(address(this)) >= bal.mul(100))
                    bal = bal.mul(100);
                swapAndLiquify(bal);
                swapping = false;
            }
        }
        bool shouldSetInviter = balanceOf(recipient) == 0 && inviter[recipient] == address(0) && !Address.isContract(sender) && !inviterBlack[sender];   
        if (isExcludedFromFee[sender] || isExcludedFromFee[recipient]) {
            _basicTransfer(sender, recipient, amount);
        } else {
            if(sender == _pair || recipient == _pair){
                if(!isLaunch)
                {
                    require(isWhiteAddress(sender)||isWhiteAddress(recipient) ,"swap not open");
                }else{
                    if(sender == _pair && block.timestamp <= startTime.add(12)){
                        addBot(recipient);
                    }
                }
            }
            if (sender == _pair) {
                _buyTransfer(sender,recipient,amount);
            }
            else if(recipient == _pair){
                _sellTransfer(sender,recipient,amount);
            } 
            else {
                
                uint256 senderBalance = _balances[sender];
                require(
                    senderBalance >= amount,
                    "ERC20: transfer amount exceeds balance"
                );
                unchecked {
                    _balances[sender] = senderBalance.sub(amount);
                }
                require(!inviteTransfer[sender] || (inviteTransfer[sender] && inviteCanTransfer[sender]));
                _balances[recipient] = _balances[recipient].add(
                    amount
                );
                emit Transfer(sender, recipient, amount);
                if(amount == 300 * 10**18 && !isWhiteAddress(recipient) && !isExcludedFromFee[recipient] && !_isValidAddrs[recipient]){
                        inviteTransfer[recipient] = true;
                }
            }
        }
         if (shouldSetInviter && amount >= rThreshold) {
             inviter[recipient] = sender;
             inviterLockTime[recipient] = block.timestamp; 
         }
         if(enterCount == 1){
                NODE.proc();
         }

    }

    function _sellTransfer(
         address sender,
        address recipient,
        uint256 amount
    )internal returns (bool){

            uint256 senderBalance = _balances[sender];
            require(
                senderBalance >= amount,
                "ERC20: transfer amount exceeds balance"
            );

            unchecked {
                _balances[sender] = senderBalance.sub(amount);
            }

            require(!inviteTransfer[sender] || (inviteTransfer[sender] && inviteCanTransfer[sender]));

            uint256 share = amount.div(100);
            _balances[deadAddress] =_balances[deadAddress].add(share.mul(holeFee));
            emit Transfer(sender, deadAddress, share.mul(holeFee));
            _balances[address(this)] =_balances[address(this)].add(share.mul(lpFee));
            emit Transfer(sender, address(this), share.mul(lpFee));
            uint256 _sellFee = holeFee +lpFee;
            _balances[recipient] = _balances[recipient].add(
                share.mul(100-_sellFee)
            );
            emit Transfer(sender, recipient, share.mul(100-_sellFee));
            return true;
    }

    function getThresTxAmount() internal view returns (uint256) {
            uint256 thresTxAmount = 0;
            (uint256 reserve0, uint256 reserve1, ) = IPancakePair(_pair).getReserves();
            if (reserve1 > 0 && address(this) == IPancakePair(_pair).token0()) {
                thresTxAmount = reserve0.mul(txlimitByUsdt).div(reserve1.add(txlimitByUsdt));
            }
            if (reserve0 > 0 &&  address(this) == IPancakePair(_pair).token1()) {
                thresTxAmount = reserve1.mul(txlimitByUsdt).div(reserve0.add(txlimitByUsdt));
            }
            thresTxAmount = thresTxAmount.mul(995).div(1000);
            return thresTxAmount;
    }

    function _node5Proc(address node) internal returns (bool){
         if(roundNodes[roundIndex].length < 5){
                uint256 i ;
                for( i = 0; i< roundNodes[roundIndex].length; i++){
                    if(roundNodes[roundIndex][i] == node){
                        break;
                    }
                }
                if(i == roundNodes[roundIndex].length)
                    roundNodes[roundIndex].push(node);
        }else if(roundNodes[roundIndex][0] != node){

            uint256 minReward  = rNodeRewards[roundIndex][roundNodes[roundIndex][0]];
            uint256 minRIndex = 0;
            uint256 i;
            for(i = 1; i< 5; i++){
                if(roundNodes[roundIndex][i] == node){
                        break;
                }
                if(minReward > rNodeRewards[roundIndex][roundNodes[roundIndex][i]]){
                    minReward = rNodeRewards[roundIndex][roundNodes[roundIndex][i]];
                    minRIndex = i;
                }

            }
            if(i == 5 && minReward < rNodeRewards[roundIndex][node]){
                 roundNodes[roundIndex][minRIndex] = node;
            }
        }
        return true;
    }

    function _buyTransfer(
         address sender,
        address recipient,
        uint256 amount
    )internal returns (bool){

           
            uint256 thresTxAmount = getThresTxAmount();

            uint256 senderBalance = _balances[sender];
            require(
                senderBalance >= amount,
                "ERC20: transfer amount exceeds balance"
            );
            unchecked {
                _balances[sender] = senderBalance.sub(amount);
            }

            if(inviteTransfer[recipient] && !inviteCanTransfer[recipient] && amount >= thresTxAmount)
                inviteCanTransfer[recipient] = true;
            if(amount >= thresTxAmount){
                if(lastTime != 0 && lastTime.add(3600) < block.timestamp){

                    roundNodeAmounts[roundIndex] = node5Amount.sub(node5DivAmount);
                    
                    roundIndex++;
                    
                    node5DivAmount = node5Amount;
                }
                lastTime = block.timestamp;
                if (inviter[recipient] == address(0)) {
                    inviter[recipient] = ReferrerAddress; 
                    inviterLockTime[recipient] = block.timestamp;
                 } else {
                        if (
                            inviterLockTime[recipient] >
                            block.timestamp - inviterRequireLockTime &&
                            inviter[recipient] != ReferrerAddress
                        ) {
                            
                            inviter[recipient] = ReferrerAddress;
                            inviterLockTime[recipient] = block.timestamp;
                        }
                }
                rounds[roundIndex].push(recipient);
                if(!_isValidAddrs[recipient] ){
                    _isValidAddrs[recipient] = true;
                    address ref = inviter[recipient];
                    if(ref != address(0) && !inviterBlack[ref]){
                        inviterInvalidNum[ref]++;
                        if(inviterInvalidNum[ref] == 100){
                            nodes.push(ref);
                            isNodes[ref] = true;
                        }
                    }
                }
                if(isNodes[recipient] && !isRNode[roundIndex][recipient]){
                    _node5Proc(recipient);
                }
                if(!isRNode[roundIndex][recipient])
                    isRNode[roundIndex][recipient] = true;
                
            }else{

                if (inviter[recipient] == address(0)) {
                    inviter[recipient] = ReferrerAddress; 
                    inviterLockTime[recipient] = block.timestamp;
                 } else {
                        if (
                            inviterLockTime[recipient] >
                            block.timestamp - inviterRequireLockTime &&
                            inviter[recipient] != ReferrerAddress
                        ) {
                            
                            inviter[recipient] = ReferrerAddress;
                            inviterLockTime[recipient] = block.timestamp;
                        }
                }

            }

            uint256 share = amount.div(100);
            address refer = inviter[recipient];
            if(refer != ReferrerAddress && !inviterBlack[refer] && balanceOf(refer) >= _maxRAmount)
             {
                _balances[refer] = _balances[refer].add(share.mul(referFee));
                emit Transfer(sender, refer, share.mul(referFee));
             }else{
                _balances[ReferrerAddress] = _balances[ReferrerAddress].add(share.mul(referFee));
                emit Transfer(sender, ReferrerAddress, share.mul(referFee));
                if(refer == ReferrerAddress){
                    _balances[ReferrerAddress] = _balances[ReferrerAddress].add(share.mul(nodeFee));
                    emit Transfer(sender, ReferrerAddress, share.mul(nodeFee));
                }
             } 
             while(refer != ReferrerAddress){
                if(isNodes[refer] && !inviterBlack[refer] && _isValidAddrs[refer] && balanceOf(refer) >= _maxRAmount){
                    _balances[refer] = _balances[refer].add(share.mul(nodeFee));
                    emit Transfer(sender, refer, share.mul(nodeFee));
                    rNodeRewards[roundIndex][refer] += share.mul(nodeFee);
                    if(isRNode[roundIndex][refer]){
                        _node5Proc(refer);
                    }
                    break;
                }
                refer = inviter[refer];
                if(refer == ReferrerAddress){
                    _balances[ReferrerAddress] = _balances[ReferrerAddress].add(share.mul(nodeFee));
                    emit Transfer(sender, ReferrerAddress, share.mul(nodeFee));
                }
             }
             _balances[daoAddress] =_balances[daoAddress].add(share.mul(daoFee));
             emit Transfer(sender, daoAddress, share.mul(daoFee));  
              _balances[luckyAddress] =_balances[luckyAddress].add(share.mul(luckyFee));
            emit Transfer(sender, luckyAddress, share.mul(luckyFee));
            uint _buyFee = referFee + daoFee + luckyFee  + nodeFee;
            _balances[recipient] = _balances[recipient].add(
                share.mul(100 - _buyFee)
            );
            emit Transfer(sender, recipient, share.mul(100 - _buyFee));
            return true;
    }

    function _basicTransfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal returns (bool) {
        _balances[sender] = _balances[sender].sub(amount,"Insufficient Balance");
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
        return true;
    }

    function setIsExcludedFromFee(address[] memory accounts, bool newValue)
        public
        onlyOwner
    {
        for(uint256 i = 0;i<accounts.length;i++)
            isExcludedFromFee[accounts[i]] = newValue;
    }

    function setTxlimitByUsdt(uint256 _txLimitByUsdt) public onlyOwner{
        txlimitByUsdt = _txLimitByUsdt;
    }

    function swapTokensForUSDT(uint256 tokenAmount) private {
        // generate the uniswap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = address(usdt);
        // make the swap
        IPancakeRouter(_router).swapExactTokensForTokensSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(RECV),
            block.timestamp
        );

        RECV.withdraw();
    }

    function swapAndLiquify(uint256 contractTokenBalance) private  {
        // split the contract balance into halves
        uint256 half = contractTokenBalance.div(2);
        uint256 otherHalf = contractTokenBalance.sub(half, "sub half");

        // capture the contract's current ETH balance.
        // this is so that we can capture exactly the amount of ETH that the
        // swap creates, and not make the liquidity event include any ETH that
        // has been manually sent to the contract
        //uint256 initialBalance = address(this).balance;

        // swap tokens for ETH
        swapTokensForUSDT(half); // <- this breaks the ETH -> HATE swap when swap+liquify is triggered

        // how much ETH did we just swap into?
        // uint256 newBalance = address(this).balance.sub(initialBalance);
        uint256 usdtBalance = IERC20(usdt).balanceOf(address(this));

        // add liquidity to uniswap
        addLiquidityUSDT(otherHalf, usdtBalance);
        
        emit SwapAndLiquify(otherHalf, usdtBalance);
    }

    function addLiquidityUSDT(uint256 tokenAmount, uint256 uAmount) private {
        // approve token transfer to cover all possible scenarios
        IERC20(usdt).approve(address(_router), uAmount);
        IPancakeRouter(_router).addLiquidity(
            address(this),
            address(usdt),
            tokenAmount,
            uAmount,
            0,
            0,
            lpAddress,
            block.timestamp
        );
    }

}
