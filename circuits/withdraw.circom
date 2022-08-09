include "../node_modules/circomlib/circuits/bitify.circom";
include "../node_modules/circomlib/circuits/comparators.circom";
include "../node_modules/circomlib/circuits/pedersen.circom";
include "merkleTree.circom";

// computes Pedersen(nullifier + secret)
template CommitmentHasher() {
    signal input nullifier;
    signal input secret;
    signal output commitment;
    signal output nullifierHash;

    component commitmentHasher = Pedersen(496);
    component nullifierHasher = Pedersen(248);
    component nullifierBits = Num2Bits(248);
    component secretBits = Num2Bits(248);
    nullifierBits.in <== nullifier;
    secretBits.in <== secret;
    for (var i = 0; i < 248; i++) {
        nullifierHasher.in[i] <== nullifierBits.out[i];
        commitmentHasher.in[i] <== nullifierBits.out[i];
        commitmentHasher.in[i + 248] <== secretBits.out[i];
    }

    commitment <== commitmentHasher.out[0];
    nullifierHash <== nullifierHasher.out[0];
}

// Returns 1 if the two lists are exactly equal, 0 otherwise
template ListEqual(length) {
    signal input paths[2][length];
    signal output out;

    component indexEq[length];
    var sum = 0;
    for (var i = 0; i < length; i++) {
        indexEq[i] = IsEqual();
        indexEq.in[0] <== paths[0][i];
        indexEq.in[1] <== paths[1][i];
        sum += indexEq.out;
    }
    signal sout <== sum;

    component allEqual = IsEqual();
    allEqual.in[0] <== sout;
    allEqual.in[1] <== levels;
    out <== allEqual.out;
}

// Verifies that commitment that corresponds to given secret and nullifier is included in the merkle tree of deposits
// Verifies that the commitment is not in a blacklist, where the blacklist is defined by a hash to reduce onchain publication costs
template Withdraw(levels, blacklistLength) {
    signal input root;
    signal input nullifierHash;
    signal input blacklistHash;
    signal input recipient; // not taking part in any computations
    signal input relayer;  // not taking part in any computations
    signal input fee;      // not taking part in any computations
    signal input refund;   // not taking part in any computations
    signal private input nullifier;
    signal private input secret;
    signal private input pathElements[levels];
    signal private input pathIndices[levels];
    signal private input blacklist[blacklistLength][levels];

    component hasher = CommitmentHasher();
    hasher.nullifier <== nullifier;
    hasher.secret <== secret;
    hasher.nullifierHash === nullifierHash;

    component tree = MerkleTreeChecker(levels);
    tree.leaf <== hasher.commitment;
    tree.root <== root;
    for (var i = 0; i < levels; i++) {
        tree.pathElements[i] <== pathElements[i];
        tree.pathIndices[i] <== pathIndices[i];
    }

    // Make sure the merkle proof isn't on the blacklist
    component samepath[blacklistLength];
    for (var i = 0; i < blacklistLength) {
        samePath[i] = ListEqual(levels);
        for (var j = 0; j < levels; j++) {
            samePath.in[0][j] <== pathIndices[j];
            samePath.in[1][j] <== blackList[i][j];
        }
        samePath[i].out === 0;
    }

    // Make sure the blacklist hash matches the blacklist
    component blacklistHasher = Pedersen(blacklist * levels);
    for (var i = 0; i < blacklistLength) {
        for (var j = 0; j < levels; j++) {
            blacklistHasher[i*j + j] <== blacklist[i][j];
        }
    }
    blacklistHasher.out[0] === blacklistHash;

    // Add hidden signals to make sure that tampering with recipient or fee will invalidate the snark proof
    // Most likely it is not required, but it's better to stay on the safe side and it only takes 2 constraints
    // Squares are used to prevent optimizer from removing those constraints
    signal recipientSquare;
    signal feeSquare;
    signal relayerSquare;
    signal refundSquare;
    recipientSquare <== recipient * recipient;
    feeSquare <== fee * fee;
    relayerSquare <== relayer * relayer;
    refundSquare <== refund * refund;
}

component main = Withdraw(20, 1000);
