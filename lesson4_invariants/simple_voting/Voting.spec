/**
 * # Simple voting invariant example
 *
 * A simple invariant example. Additionally there are two rules, one is a correct
 * translation of the invariant to a rule, and the other is a wrong translation.
 */

methods
{
    function votesInFavor() external returns (uint256) envfree;
    function votesAgainst() external returns (uint256) envfree;
    function totalVotes() external returns (uint256) envfree;
    function hasVoted(address voter) external returns (bool) envfree;
}

// Use a ghost and an invariant to prove that if _hasVoted changed then the vote method was called.

// Use a ghost and an invariant to prove that the values of _hasVoted can only change from false to true.

ghost mathint numVoted {
    init_state axiom numVoted == 0;
}

ghost bool illegalStore {
    init_state axiom !illegalStore;
}

hook Sstore _hasVoted[KEY address voter] bool newVal (bool oldVal) {
    if (newVal && !oldVal) {
        numVoted = numVoted + 1;
    }

    // If oldVal is true, it means _hasVoted[voter] was already set to true for this voter,
    // and we are trying to update it again (which is illegal in the voting context).
    // illegalStore is updated to true if oldVal is already true,
    // indicating an illegal attempt to rewrite _hasVoted.
    // This setup ensures that once illegalStore is set to true, it stays true permanently,
    // indicating an illegal modification occurred at some point.
    illegalStore = illegalStore || oldVal;
}

invariant voteOnlyChangesFromFalseToTrue()
    !illegalStore;

rule stateChangesOnlyWithVoteFunc(method f) {
    env e;
    // precondition
    require !hasVoted(e.msg.sender);
    
    calldataarg args;
    f(e, args);

    // postcondition
    assert hasVoted(e.msg.sender) => f.selector == sig:vote(bool).selector;
}

rule oneVoteResultsInOneForOrAgainst(method f) {
    mathint votesInFavorBefore = votesInFavor();
    mathint votesAgainstBefore = votesAgainst();
    mathint totalVotesBefore = totalVotes();

    env e;
    require !hasVoted(e.msg.sender);
    calldataarg args;
    f(e, args);

    mathint votesInFavorAfter = votesInFavor();
    mathint votesAgainstAfter = votesAgainst();
    mathint totalVotesAfter = totalVotes();

    assert hasVoted(e.msg.sender) => f.selector == sig:vote(bool).selector => 
        totalVotesAfter == totalVotesBefore + 1 && 
        (votesInFavorAfter == votesInFavorBefore + 1 || votesAgainstAfter == votesAgainstBefore + 1);
}

rule revertIfAlreadyVoted(method f, bool isInFavor) {
    env e;
    require hasVoted(e.msg.sender);
    vote@withrevert(e, isInFavor);

    assert lastReverted;
}

rule hasVotedShouldBeTrueAfterVoting(method f) {
    env e;
    // precondition
    require !hasVoted(e.msg.sender);
    
    calldataarg args;
    f(e, args);

    // postcondition
    assert f.selector == sig:vote(bool).selector => hasVoted(e.msg.sender);
}

/// @title Anyone can vote once
rule anyoneCanVote(address voter, bool isInFavor) {
    bool preHasVoted = hasVoted(voter);
    uint256 preTotal = totalVotes();

    env e;
    require e.msg.sender == voter;

    // Limit the overflow cases - this means we need only check `totalVotes`
    requireInvariant sumResultsEqualsTotalVotes();

    vote@withrevert(e, isInFavor);    


    // the <= and => operators mean logical "if and only if" (also known as logical equivalence or biconditional).
    // the syntax <= or => as combined in <= (written as <=>) specifies a condition where both sides of the expression
    // must either both be true or both be false.
    // This expression asserts that the result of lastReverted (a boolean indicating whether the transaction reverted)
    // should be true if and only if (i.e., <=>) any of the three conditions on the right side of the <=> are true.

    assert (
        lastReverted <=> (
            preHasVoted  // Revert since voted before
            || e.msg.value > 0  // Sending ETH will cause revert
            || preTotal == max_uint256  // Revert due to overflow
        )
    ), "Can vote first time";
}









/// @title Sum of voter in favor and against equals total number of voted
invariant sumResultsEqualsTotalVotes()
    votesInFavor() + votesAgainst() == to_mathint(totalVotes());


/// @title This rule is a correct translation of the invariant
rule sumResultsEqualsTotalVotesAsRule(method f) {
    // Precondition
    require votesInFavor() + votesAgainst() == to_mathint(totalVotes());

    env e;
    calldataarg args;
    f(e, args);
    
    assert (
        votesInFavor() + votesAgainst() == to_mathint(totalVotes()),
        "Sum of votes should equal total votes"
    );
}