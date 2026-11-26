# Initial residual certificate

## Abstract

The initial signed residual certificate for A235301.

**Theorem 1.1 (Initial residual identities).**

$$\operatorname{residualHist}\left(2\right) = \operatorname{normalize}\left(stateKey, \operatorname{scaleHist}\left(-3, \operatorname{residualHist}\left(1\right)\right) ++ \operatorname{scaleHist}\left(-2, \operatorname{residualHist}\left(0\right)\right)\right) \land \operatorname{groupMask}\left(\operatorname{residualHist}\left(0\right)\right) = [] \land \operatorname{groupMask}\left(\operatorname{residualHist}\left(1\right)\right) = []$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initial_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel checks three identities on signed histories. The third residual is the normalized concatenation of the preceding two with coefficients minus three and minus two. Grouping the first two histories by mask gives the empty list in each case.

**Definition 1.2 (Initial transfer histories).**

$$initialPath: \operatorname{Fin}\left(10\right) \to \operatorname{Hist}\left(State\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initialPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries are the stored histories for heights one through ten.

**Theorem 1.3 (Correctness of the initial histories).**

$$\forall i: \operatorname{Fin}\left(10\right), \operatorname{path}\left(\operatorname{val}\left(i\right)+1\right) = \operatorname{initialPath}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initial_path_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each entry uses the corresponding checked row-transfer identity. The square recurrence uses these histories to compute the initial literal counts.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initialPath`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initial_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initial_path_eq`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer](HardinA235301Transfer.md)
