# One original source and all its signed observations

## Abstract

Exact signed observation extraction

Sources are arbitrary nonempty finite ordered Boolean trees. The unary operation is the interpreted native substitution: alpha becomes beta, beta becomes the ordered pair of beta and alpha, and substitution preserves pairs. All occurrences of one frontier name use one whole tree. Different names may receive equal trees.

**Definition 1.1 (Mixed-epoch endpoint expressions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.endpoint`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Navigation follows the original finite skeleton. At the requested endpoint the entire remaining term is shifted by the actual epoch. An early original ground leaf is evolved explicitly before its descendants are inspected, so descendants born under substitution are included. A proper descent into an unspecified frontier is rejected. If the requested address is shorter than the original skeleton depth, that last case cannot occur. Evaluation of the returned optional mixed expression is exactly the actual optional whole subtree.

**Definition 1.2 (Both guards precede either sign).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.comparison`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.comparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both optional endpoints must be present. A reached pair contributes one equality or one disequality of whole mixed native expressions. An absent endpoint rejects a negative comparison too. The sign does not turn absence into evidence of disequality.

**Definition 1.3 (Literal and positive records).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.compileRecord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.compileRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal replies are constant over all fillings of a sufficiently deep original skeleton, at every supplied epoch. They can therefore be tested on one fixed filling. Positive whole-subtree records retain their actual epochs, both addresses and both reached guards.

**Definition 1.4 (Conjunction without dropping occurrences).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.compileList`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.compileList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite list compiler preserves order and repetitions. None denotes a rejected branch, while some empty list denotes the empty conjunction. Every negative record uses the same source term and the same variable valuation as every positive record.

**Definition 1.5 (Complete rows remain explicit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.ExtractedHolds`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.ExtractedHolds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extracted predicate keeps the complete symbolic old and target row records, including concrete exteriors, reached holes, all equality pairs and all cross-class disequalities. Uncut frontier variables remain in the symbolic exterior. The two compiled signed programs are imposed on those same variables. This predicate is an exact observation reduction; its row constraints have not yet been eliminated into a positive native image chart.

**Definition 1.6 (An input-computed finite case depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.requiredDepth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.requiredDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take one plus the maximum length of every old and new cut address and every literal, positive and negative endpoint address. The maximum of an empty set is zero. Epoch magnitudes do not enter this bound. Pattern at that depth is a finite type, and each pattern retains every reached frontier position.

**Theorem 1.7 (Exact same-original finite pattern reduction).**

$$\forall P, Q: CutSet, (((\operatorname{CutPrefixFree}\left(P\right) \land \operatorname{CutPrefixFree}\left(Q\right)) \implies \forall old, target: Row, (\forall H: \operatorname{List}\left(Record\right), (\forall K: \operatorname{List}\left(NegativeRecord\right), (\forall u: Source, ((\operatorname{InputHolds}\left(P, Q, old, target, H, K, u\right) \iff \exists p: \operatorname{Pattern}\left(\operatorname{requiredDepth}\left(P, Q, H, K\right)\right), (\exists v: \operatorname{Frontier}\left(p\right) \to Source, ((\operatorname{fill}\left(p, v\right) = u \land \operatorname{ExtractedHolds}\left(P, Q, old, target, H, K, \operatorname{patternTerm}\left(p, id\right), v\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.entire_input_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite prefix-free cuts P and Q, arbitrary complete row labels old and target, arbitrary lists H of literals and positive records and K of negative records, and every original source u, the entire input holds exactly when one pattern p at requiredDepth P Q H K and one unrestricted frontier valuation v reconstruct u itself and satisfy ExtractedHolds for patternTerm p id. Contradictory inputs have no satisfying valuation. Empty cuts, empty lists, root cuts, partly absent cuts and patterns with no frontier variables remain included.

The endpoint proof descends through original pair nodes, uses preservation of pairing by every native power, and computes descendants of early evolved leaves literally. It then proves both guarded signs and concatenation of every supplied record. Exact symbolic recutting supplies both complete row records. Finally the existing depth equivalence selects the actual pattern and actual frontier subtrees of u; filling them returns that same original u.

This result supplies finite signed observation extraction within the complete original-source stratum construction. It does not synthesize positive whole-tuple native image charts, eliminate the symbolic row constraints, recognize the image-saturation class, construct a completed limit, fix cofinal finite parameters or decide the all-depth alternative. Paid acquisition, complete accessible-state factoring and authentic service epochs remain separate operational premises. Symbolic coordinates supply no original-register read, inverse, reset, clone or free equality operation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.ExtractedHolds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.comparison`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.compileList`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.compileRecord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.endpoint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.entire_input_extraction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.requiredDepth`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells](../NativeHistoryCells.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation](../NativePayloadHistoryInstallation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation](../NativeSimultaneousPrefixSeparation.md)
