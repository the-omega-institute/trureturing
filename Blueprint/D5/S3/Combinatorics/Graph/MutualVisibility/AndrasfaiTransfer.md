# The corrected transfer-trace series

## Abstract

Exact formal-series algebra for the four-state transfer traces.

**Definition 1.1 (The labelled-edge matrix).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.transfer`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In state order 0,1,2,3 the rational matrix M has rows (1,1,0,0), (1,0,1,0), (0,0,0,1), (0,2,0,0). The entry two retains the two distinct labels on the transition from state 3 to state 1.

**Definition 1.2 (The uncorrected full trace series).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.traceSeries`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.traceSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series is X times the power series with coefficient j equal to tr(M^(3j+2)) for every natural j. Thus its constant coefficient is zero and its coefficient at every positive index n is tr(M^(3n-1)). The index-zero matrix trace is not a graph G_0.

**Definition 1.3 (The denominator).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.denominator`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.denominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D = 1 - 10X + 29X^2 - 32X^3 + 8X^4 in Q[[X]]. Its constant coefficient is one, so its formal multiplicative inverse is valid.

**Theorem 1.4 (The complete corrected trace identity).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.corrected_trace_series`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.corrected_trace_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity is traceSeries + X = X(4 - 19X + 33X^2 - 40X^3 + 8X^4) D^(-1). For B=M^3 the explicitly checked rows are (3,2,1,1), (2,3,1,0), (2,0,2,0), (2,2,0,2). Kernel-checked rational arithmetic gives B^4 = 10B^3 - 29B^2 + 32B - 8I. Multiplying by M^2 B^j and taking the trace proves the recurrence at every natural j. The first four traces are 3,21,127,749, recomputed from the matrix definitions. If H has these trace coefficients, coefficient extensionality gives D H = 3 - 9X + 4X^2 - 8X^3, with all higher coefficients zero by the proved recurrence. Multiplying by X and adding X D yields the displayed numerator. The standard formal-series inverse theorem applies because D has constant coefficient one; no convergence or fitted recurrence is used.

This is a theorem about the displayed transfer matrix. The bijection between actual original-host visible subsets and uniquely lifted closed labelled automaton walks is a separate unproved obligation. The addition of X is explicit; identifying it with the original index-one correction requires that counting correspondence.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.corrected_trace_series`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.denominator`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.traceSeries`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer.transfer`
