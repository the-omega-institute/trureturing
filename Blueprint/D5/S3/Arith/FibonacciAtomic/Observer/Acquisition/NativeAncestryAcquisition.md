# Native ancestry acquisition

## Abstract

Literal replies reveal independent three-leaf bracket choices one support at a time.

The native family replaces any subset of the original three-leaf B subtrees by D. The two fillings have the same ordered leaf labels and different brackets. Addresses are arbitrary finite left and right words, including the root and absent nodes. A raw history retains every query, its actual four-valued reply and its chronological position.

**Definition 1.1 (Six changed literal addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.support`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support at p consists of pL, pR, pLL, pLR, pRL and pRR. At every one of these addresses the B and D replies differ, even after identifying branch with absent. All other replies agree.

**Theorem 1.2 (Equality away from changed supports).**

$$\forall t: \operatorname{Source}, (\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), (\forall B: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(t\right)\right)) \implies ((\operatorname{Subset}\left(B, \operatorname{positions}\left(t\right)\right)) \implies (\forall q: \operatorname{Address}, ((\forall p: \operatorname{Address}, ((p \in \operatorname{symmDiff}\left(A, B\right)) \implies (\neg (q \in \operatorname{support}\left(p\right))))) \implies (\operatorname{readout}\left(q, \operatorname{variant}\left(t, A\right)\right) = \operatorname{readout}\left(q, \operatorname{variant}\left(t, B\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.outside_support_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite source, simultaneously changing any collection of its original B positions preserves the reply at each address outside the supports of the changed positions. There is no depth bound on the source or the query. The proof follows the actual tree, with the six local differences handled at a B root.

**Definition 1.3 (The positions tested by a record).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.hit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.hit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A position is hit exactly when one of its six support addresses occurs in the history. Repeated queries and queries outside every support add no positions.

**Definition 1.4 (Agreement with the whole raw record).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.Consistent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.Consistent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A choice is consistent when every recorded query has exactly the recorded reply in its actual native source.

**Definition 1.5 (The complete compatible subset family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.compatible`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the full powerset of original positions by consistency with the raw history.

**Definition 1.6 (The compatible actual trees).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.compatibleSources`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.compatibleSources` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map every compatible subset to its actual simultaneously filled source. The native cube injectivity distinguishes all of these sources.

**Definition 1.7 (Uniform-prior conditioning).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.posterior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.posterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every original subset has prior weight one divided by two to the number of original positions. On the compatible family, divide this common weight by its total over that family. A truthful history makes that total positive.

**Theorem 1.8 (An exact face and its conditional entropy).**

$$\forall n: \operatorname{Nat}, ((3 \leq n) \implies (\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\forall h: \operatorname{RawHistory}, ((\operatorname{Consistent}\left(\operatorname{T}\left(n\right), A, h\right)) \implies ((\forall B: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(B, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies ((\operatorname{Consistent}\left(\operatorname{T}\left(n\right), B, h\right)) \iff (\operatorname{inter}\left(B, \operatorname{hit}\left(\operatorname{T}\left(n\right), h\right)\right) = \operatorname{inter}\left(A, \operatorname{hit}\left(\operatorname{T}\left(n\right), h\right)\right))))) \land (\operatorname{card}\left(\operatorname{compatible}\left(\operatorname{T}\left(n\right), h\right)\right) = 2^{\operatorname{natSub}\left(\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right), \operatorname{card}\left(\operatorname{hit}\left(\operatorname{T}\left(n\right), h\right)\right)\right)}) \land (\operatorname{card}\left(\operatorname{compatibleSources}\left(\operatorname{T}\left(n\right), h\right)\right) = 2^{\operatorname{natSub}\left(\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right), \operatorname{card}\left(\operatorname{hit}\left(\operatorname{T}\left(n\right), h\right)\right)\right)}) \land (\forall B: \operatorname{compatible}\left(\operatorname{T}\left(n\right), h\right), (\operatorname{posterior}\left(\operatorname{T}\left(n\right), h, B\right) = \frac{1}{\operatorname{card}\left(\operatorname{compatible}\left(\operatorname{T}\left(n\right), h\right)\right)})) \land (\frac{\operatorname{shannonEntropy}\left(\operatorname{posterior}\left(\operatorname{T}\left(n\right), h\right)\right)}{\operatorname{log}\left(2\right)} = \operatorname{natSub}\left(\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right), \operatorname{card}\left(\operatorname{hit}\left(\operatorname{T}\left(n\right), h\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.native_record_face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For generation n at least three, let P be the original positions and K equal fib(n minus two). A truthful history fixes precisely the choices on H, the hit set. The compatible subsets are an interval from A intersect H to its union with P minus H, so there are exactly two to the power K minus the size of H. Conditioning the uniform law on all subsets gives the uniform law on this face. Its Shannon entropy divided by log two is K minus the size of H. Whenever this history is a successful run of a fixed source-independent deterministic policy, execute_transfer gives the same terminal history and answer on every compatible source. A first hit fixes one previously free bit; repetitions and unrelated queries leave the face unchanged. This prior is distinct from the half-canonical, half-singleton prior used for classification.

**Definition 1.9 (A source-independent terminating policy).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.CubeRun`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.CubeRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One history policy is shared by all subsets of the original positions. Each subset has a finite actual execute run from the empty history, with its recorded terminal trace and Boolean answer. True denotes the canonical source.

**Definition 1.10 (Canonical versus defect correctness).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.Correct`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.Correct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal answer is true exactly for the empty defect subset, on the entire native family.

**Theorem 1.11 (Exact worst-case first-address cost).**

$$\forall n: \operatorname{Nat}, ((3 \leq n) \implies ((\forall R: \operatorname{CubeRun}\left(\operatorname{T}\left(n\right)\right), ((\operatorname{Correct}\left(\operatorname{T}\left(n\right), R\right)) \implies (\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right) \leq \operatorname{card}\left(\operatorname{paid}\left(\operatorname{trace}\left(R, \emptyset\right)\right)\right)))) \land (\exists R: \operatorname{CubeRun}\left(\operatorname{T}\left(n\right)\right), ((\operatorname{Correct}\left(\operatorname{T}\left(n\right), R\right)) \land (\operatorname{FactorsThrough}\left(\operatorname{policy}\left(R\right), \operatorname{kappaHist}\right)) \land (\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\operatorname{card}\left(\operatorname{paid}\left(\operatorname{trace}\left(R, A\right)\right)\right) \leq \operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right)))) \land (\operatorname{card}\left(\operatorname{paid}\left(\operatorname{trace}\left(R, \emptyset\right)\right)\right) = \operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.optimal_canonical_queries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every correct policy must hit all K supports on the empty defect subset: an unhit singleton defect otherwise replays the same terminal run with the opposite correct answer. Distinct supports are disjoint and therefore require distinct paid literal addresses. Querying pL once for every original p gives a correct policy on every subset, always pays K addresses, and attains the lower bound. This scan factors through the coarse history that identifies branch and absent replies. Only first-use literal source reads are counted; address generation, address length, program and memory costs are separate quantities.

**Definition 1.12 (The half-canonical, half-singleton score).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.success`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.success` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty subset has weight one half. Every singleton defect has weight one divided by twice K. The score is the resulting average correct-classification probability for a fixed policy.

**Definition 1.13 (Correct classification on one input).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.reward`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.reward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reward is one exactly when the terminal Boolean answer matches whether the defect subset is empty, and zero otherwise.

**Theorem 1.14 (Exact success under a hard support budget).**

$$\forall n: \operatorname{Nat}, ((3 \leq n) \implies (\forall q: \operatorname{Nat}, ((q \leq \operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right)) \implies ((\forall R: \operatorname{CubeRun}\left(\operatorname{T}\left(n\right)\right), ((\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\operatorname{card}\left(\operatorname{hit}\left(\operatorname{T}\left(n\right), \operatorname{trace}\left(R, A\right)\right)\right) \leq q))) \implies (\operatorname{success}\left(\operatorname{T}\left(n\right), R\right) \leq \frac{1}{2}+\frac{q}{2\times\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right)}))) \land (\exists R: \operatorname{CubeRun}\left(\operatorname{T}\left(n\right)\right), ((\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\operatorname{card}\left(\operatorname{hit}\left(\operatorname{T}\left(n\right), \operatorname{trace}\left(R, A\right)\right)\right) \leq q))) \land (\operatorname{success}\left(\operatorname{T}\left(n\right), R\right) = \frac{1}{2}+\frac{q}{2\times\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right)}))) \land (\forall O: \operatorname{Type}, ((\operatorname{MeasurableSpace}\left(O\right)) \implies (\forall m: \operatorname{ProbabilityMeasure}\left(O\right), (\forall R: O \to \operatorname{CubeRun}\left(\operatorname{T}\left(n\right)\right), ((\operatorname{Measurable}\left(\operatorname{seedScore}\left(\operatorname{T}\left(n\right), R\right)\right)) \implies ((\forall s: O, (\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\operatorname{card}\left(\operatorname{hit}\left(\operatorname{T}\left(n\right), \operatorname{trace}\left(\operatorname{R}\left(s\right), A\right)\right)\right) \leq q)))) \implies (\operatorname{integralScore}\left(m, \operatorname{T}\left(n\right), R\right) \leq \frac{1}{2}+\frac{q}{2\times\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right)}))))))) \land (\forall O: \operatorname{Type}, ((\operatorname{MeasurableSpace}\left(O\right)) \implies (\forall m: \operatorname{ProbabilityMeasure}\left(O\right), (\forall R: O \to \operatorname{CubeRun}\left(\operatorname{T}\left(n\right)\right), (\forall d: \operatorname{Real}, ((d < \frac{1}{2}) \implies ((\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\operatorname{Measurable}\left(\operatorname{seedAnswer}\left(R, A\right)\right)))) \implies ((\forall s: O, (\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\operatorname{card}\left(\operatorname{hit}\left(\operatorname{T}\left(n\right), \operatorname{trace}\left(\operatorname{R}\left(s\right), A\right)\right)\right) \leq q)))) \implies ((\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (1-d \leq \operatorname{integralReward}\left(m, R, A\right)))) \implies ((1-2\times d)\times\operatorname{fib}\left(\operatorname{natSub}\left(n, 2\right)\right) \leq q))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.optimal_single_defect_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonnegative integer q at most K, impose at most q hit supports on every cube input and every fixed random seed. Along the canonical run, every unhit singleton has the same answer. If that answer is canonical, only hit singleton defects can add success; if it is defect, the entire singleton contribution is at most one half. Thus success is at most one half plus q divided by twice K. A fixed scan of any q distinct original positions attains equality, including q zero, q K and K one. Integrating over any source-independent probability law preserves the upper bound for measurable terminal scores. If every candidate has expected correct reward at least one minus delta, with delta less than one half, then q is at least one minus twice delta times K.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.Consistent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.Correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.CubeRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.compatible`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.compatibleSources`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.hit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.native_record_face`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.optimal_canonical_queries`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.optimal_single_defect_success`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.outside_support_invariance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.posterior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.reward`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.success`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.support`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory](../../ActualCoarseReadoutHistory.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube](../../Geometry/NativeAncestryDefectCube.md)
- Dependency: [D5/S3/Entropy/EntropyEquality](../../../../Entropy/EntropyEquality.md)
