# Anchored literal arrays and all three bond types

## Abstract

Literal eight-colour six-column arrays and their exact weighted pair transfer.

The pair fibres are {0,7}, {1,6}, {2,5}, and {3,4}. Scanner flags retain actual earlier occurrences of colours one, two, and three. The generic literal counting decomposition is HardinA233196Strip.width_counting_bridge.

**Definition 1.1 (Colour rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Row`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Six ordered individual colours from zero through seven.

**Definition 1.2 (Pair-label rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.PairRow`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.PairRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Six ordered labels for the four complementary pairs.

**Definition 1.3 (Labelled boundaries).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Boundary`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All six labels of the preceding row.

**Definition 1.4 (Strict row-major index).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rho`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index of cell (i,j) is six times i plus j.

**Definition 1.5 (Horizontal exclusions).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rowLegal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every adjacent pair in a row is unequal and has natural-number sum different from seven.

**Definition 1.6 (Vertical and antidiagonal exclusions).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.bonds`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each preceding cell is bonded to the next row in the same column. Each preceding cell in column j+1 is also bonded to the next cell in column j. Both exclusions forbid equality and natural-number sum seven.

**Definition 1.7 (The literal array predicate).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Legal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper-left colour is zero and every contained horizontal, vertical, and antidiagonal bond satisfies the exclusions. Colours two through six require a strictly earlier one; three, four, and five require a strictly earlier two; four requires a strictly earlier three. Earlier means a smaller rho value. No occurrence of an unused colour is required.

**Definition 1.8 (The positive-height literal count).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.a`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count all individual functions from the positive-height six-column rectangle to eight colours that satisfy Legal.

**Definition 1.9 (The preceding boundary).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.pairs`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the existing complementary-pair map to every cell of the row.

**Definition 1.10 (The individual next-row test).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.compatible`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pair labels express the six vertical and five antidiagonal exclusions.

**Definition 1.11 (Proper label rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rowProper`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rowProper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Consecutive labels differ.

**Definition 1.12 (Cross-row compatibility).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.labelCompatible`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.labelCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All six vertical and five antidiagonal pairs have distinct labels.

**Definition 1.13 (The successor boundary).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.labelBoundary`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.labelBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain the entire labelled row.

**Definition 1.14 (Weighted continuation transfer).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.pairV`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.pairV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty continuation has value one. For each additional row sum over all proper compatible label rows, multiplying their exact scanner multiplicity by the next continuation value.

**Theorem 1.15 (Every continuation height and state).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.continuation_pair_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.continuation_pair_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural continuation height, every initial three-flag state, and every labelled boundary, the existing eight-colour continuation equals pairV. The exact scanner pushforward replaces each individual-colour row sum. The source.state_binder audit binding is unfinished under https://github.com/the-omega-institute/trureturing/issues/28653.

**Theorem 1.16 (The exact anchored readout).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.literal_pair_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.literal_pair_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n the literal count at height n+1 equals the weighted sum over five-label words q. Prepend label zero and retain the summand only when that six-label word is proper. The summand is rowWeight from the three false flags along q, times pairV at n with rowFinish along q and boundary obtained by prepending zero. The fixed first colour has multiplicity one and leaves all flags false. This identity includes every positive height and gives the literal input for the 58-state reduction.

**Definition 1.17 (Historical scanner stage).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeStage`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeStage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 58 states contain one canonical proper boundary with two available pair labels, sixteen with three available labels, and forty-one with four available labels. The stage is the number of available labels minus one.

**Definition 1.18 (Canonical proper boundaries).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeRepresentative`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each boundary is a restricted growth word beginning zero, one. Rows related by a permutation of the already available labels have the same continuation; unavailable labels are fixed. Canonicalization retains the historical stage even if an available label is absent from the current boundary.

**Definition 1.19 (Stage-preserving boundary class).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeClassOf`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeClassOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a proper six-label boundary using only labels zero through its positive stage, relabel by order of first occurrence and select the corresponding state at that same stage.

**Definition 1.20 (The exact finite weighted transfer).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeT`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entry (i,j) sums rowWeight over every proper six-label row compatible with representative i whose final scanner stage and normalized boundary have class j. Compatibility includes six vertical and five antidiagonal bonds. The scanner starts at the three flags encoded by stage i. Every weighted nonzero successor has a valid positive stage and uses only labels available at its final stage.

**Definition 1.21 (Anchored initial vector).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeInitial`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeInitial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Component i sums the exact rowWeight of all five-label words q for which zero prepended to q is proper and its final stage and boundary have class i. The individual first colour is fixed to zero and has weight one; no unused label is required to occur.

**Theorem 1.22 (All positive heights as a finite linear readout).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.native_linear_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.native_linear_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n the original literal count a(n+1), cast to the integers, equals the dot product of nativeInitial with nativeT to the power n applied to the constant-one vector. The proof transports the exact pairV continuation through permutations of already available labels and retains every scanner stage. The terminal readout is one in all 58 states. This is the all-height semantic bridge used by HardinA233200Recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.PairRow`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.continuation_pair_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.labelBoundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.labelCompatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.literal_pair_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeClassOf`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeInitial`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeRepresentative`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeStage`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.nativeT`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.native_linear_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.pairV`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rho`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.rowProper`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200LiteralBridge](HardinA233200LiteralBridge.md)
