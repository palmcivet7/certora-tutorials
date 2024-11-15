/// Verification of EnglishAuction

/*//////////////////////////////////////////////////////////////
                            METHODS
//////////////////////////////////////////////////////////////*/
methods {
    function highestBid() external returns (uint256) envfree;
    function bids(address) external returns (uint256) envfree;
    function highestBidder() external returns (address) envfree;
    function bid(uint) external;
}

// highest bid is higher than of equal to any other bid
invariant highestBid(address a)
    highestBid() >= bids(a);
    
invariant highestBidder()
    (highestBidder() != 0) => highestBid() == bids(highestBidder());

// Use a ghost and a hook to indicate that someone placed some bid.
ghost bool someoneBid {
    init_state axiom !someoneBid;
}

// mapping(address => uint) public bids;
hook Sstore bids[KEY address voter] uint newVal (uint oldVal) {
    someoneBid = someoneBid || newVal > oldVal;
}

// rule bidPlacedCorrectly(method f) {
//     env e;
//     calldataarg args;
//     f(e, args);

//     assert f.selector == sig:bid(uint).selector || f.selector == sig:bidFor(address,uint).selector 
//         => someoneBid;
// }

// Prove that highestBid is strictly greater than all other bids, provided someone has placed a bid.
invariant highestBidStrictlyGreater(address bidder)
    someoneBid && bidder != highestBidder() => highestBid() > bids(bidder) {
        preserved {
            requireInvariant highestBid(bidder);
        }
    }