/**
 * # Spec for funds manager `IManager.sol`
 */
methods {
    function getCurrentManager(uint256) external returns (address) envfree;
    function getPendingManager(uint256) external returns (address) envfree;
    function isActiveManager(address) external returns (bool) envfree;
}

function isManaged(uint256 fundId) returns bool {
    return getCurrentManager(fundId) != 0;
}

invariant activeManager(uint256 fundId)
    isManaged(fundId) <=> isActiveManager(getCurrentManager(fundId))
    {
        preserved claimManagement(uint256 fundId2) with (env e) {
            requireInvariant uniqueManager(fundId, fundId2);
        }
    }

invariant uniqueManager(uint256 fundId, uint256 fundId2)
    fundId != fundId2 && isManaged(fundId) => getCurrentManager(fundId) != getCurrentManager(fundId2)
    {
        preserved {
            requireInvariant activeManager(fundId);
            requireInvariant activeManager(fundId2);
        }
    }

// The exercise now is to prove that every active manager manages a fund.
// Use a ghost when writing the invariants and verify them using the Certora Prover.

ghost mapping(address => uint256) g_activeManagers {
    axiom forall address a. g_activeManagers[a] < max_uint256;
    init_state axiom forall address a. g_activeManagers[a] == 0;
}

hook Sstore _isActiveManager[KEY address manager] bool newVal (bool oldVal) {
    g_activeManagers[manager] = newVal;
}

invariant everyActiveManagerManagesAFund()
    {
        preserved {
            requireInvariant 
        }
    }
