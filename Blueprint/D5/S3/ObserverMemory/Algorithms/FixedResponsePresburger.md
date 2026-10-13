# Fixed Response Presburger Formulas

## Abstract

Computed Presburger formulas realize fixed paths and final-update crossings exactly.

**Definition 1.1 (Computed constants and one quantified variable).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.progressionFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.progressionFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural coefficients a and C, the formula has one free count variable d. If C is zero it is d equals a. Otherwise it is exists m, d equals a plus C times m, with C times m represented by repeated addition. These are actual Mathlib Language.presburger terms and bounded formulas.

**Definition 1.2 (Endpoint-filtered finite disjunction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathListFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathListFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A list fold joins the progression formulas whose actual endpoints equal the requested control y. All other records contribute false. An empty list gives false. No choice-based finite-set conversion or sum is used.

**Definition 1.3 (The final edge must be a genuine update).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingListFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingListFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a record ending at some z, inspect the same table at z. Retain it only if that instruction is update y, and increase its offset by one. Read and halt endpoints and the sink contribute false. Positive path weight alone is insufficient: a path ending after reads need not cross by an update into that endpoint.

**Definition 1.4 (Fixed-response path syntax).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the finite endpoint records for the supplied table, response field and initial control, then fold their endpoint-filtered formulas. The output is executable syntax with one free natural count variable.

**Definition 1.5 (Final-update crossing syntax).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the same computed records and the same table to construct the disjunction over real final-update predecessors.

**Theorem 1.6 (Exact realization of both native relations).**

$$\forall Q, A, R: \operatorname{Type},\ [\operatorname{Fintype}(Q)], [\operatorname{DecidableEq}(Q)],\ \forall f: Q \to \operatorname{Instruction}(Q, A, R), v: A \to R,\ \forall x, y\in Q, d\in \mathbb{N},\ (\operatorname{Realize}(\operatorname{pathFormula}(f, v, x, y), \operatorname{const}(d)) \iff \operatorname{FixedPath}(f, v, x, y, d)) \land\ (\operatorname{Realize}(\operatorname{crossingFormula}(f, v, x, y), \operatorname{const}(d)) \iff \operatorname{Crossing}(f, v, x, y, d))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.fixed_response_formulas_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite control type with explicit Fintype and DecidableEq instances, arbitrary address and reply types, program f, response field v, controls x and y, and natural count d, realization of the path formula at d is equivalent to FixedPath f v x y d, and realization of the crossing formula at d is equivalent to Crossing f v x y d. Both conjuncts use the same program and vector.

Mathlib realizes computed numerals and natural scalar multiples as their natural arithmetic values. Mathlib's realization theorem for list disjunctions identifies the fold with finite progression support. The exact native-path support theorem supplies both directions. For crossing, the retained predecessor supplies the real final update constructor, and the offset shift records its unit weight.

Zero-weight cycles collapse to singleton weights while retaining endpoints. Empty paths and transient halt endpoints remain reachable; a halt has no final outgoing update. The theorem quantifies over every natural count without imposing an instruction or update bound.

This completes the fixed-response arithmetic component. Synthesis of the shared-source guards, effective rank and descriptor formulas, and their full phase composition are separate obligations. The definitions do not assert a uniform Computable theorem for an external program encoding. No literature novelty is asserted.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingListFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.fixed_response_formulas_correct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathListFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.progressionFormula`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic](FixedResponseArithmetic.md)
