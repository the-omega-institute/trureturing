# Arbitrary-alphabet ordinary-word Solovay–Kitaev candidate

## Abstract

The registered arbitrary finite inverse-closed dense SU(2) alphabet event is stated with literal ordinary words; the licensed SU(2) algebra and same-word list invariant compile, while the quantitative closure remains open.

**Definition 1.1 (The licensed quaternion matrix).**

$$su2$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.su2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix su2(w,x,y,z) is the unit-quaternion 2 by 2 complex matrix. The source attribution is Csd@9b2d2c17e926ae13795119c5f2f62e85ea240c2d, CsdLean4/Mathlib/QuantumInfo/SU2Rotation.lean (declarations su2, su2_mul, su2_det, axisRot, axisRot_det, su2_star, su2_mem_unitary, and axisRot_mem_unitary), under Apache 2.0; the full license is retained at docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.

**Theorem 1.2 (Quaternion multiplication).**

$$su2Mul$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.su2_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix multiplication is the displayed quaternion product. This is the algebraic support used by the balanced commutator construction.

**Theorem 1.3 (Axis rotations have determinant one).**

$$axisRotDet$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.axisRot_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real unit axis, every axisRot(a,b,c,theta) has determinant one. No density or word-length assertion is hidden in this algebraic support.

**Theorem 1.4 (Compactness gives a finite net).**

$$compactFiniteNet$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.compact_exists_finite_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the compactness finite-net lemma retained from the licensed CSD CliffordTNet source. A compact set in the closure of D has a finite net drawn from D; it supplies the base compactness step without a quantitative cardinality.

**Definition 1.5 (The determinant-one unitary subset).**

$$su2Set$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.SU2Set` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SU2Set is the closed subset of 2 by 2 matrices satisfying the SU2 carrier predicate.

**Theorem 1.6 (The SU2 subset is closed).**

$$isClosedSu2Set$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.isClosed_SU2Set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closedness uses the existing unitary closed-set theorem and continuity of the matrix determinant.

**Theorem 1.7 (The SU2 subset lies in the unit ball).**

$$su2SetClosedBall$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.su2Set_subset_closedBall` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unitary has operator norm one, giving the closed-ball bound used by the compactness proof.

**Theorem 1.8 (The SU2 subset is compact).**

$$isCompactSu2Set$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.isCompact_SU2Set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unitary norm bound places SU2Set in the closed unit ball, so closedness yields compactness.

**Theorem 1.9 (Density reaches the compact SU2 carrier).**

$$su2SetClosureEval$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.SU2Set_subset_closure_evalGamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density premise is converted into inclusion of SU2Set in the closure of the actual ordinary-word evaluations.

**Theorem 1.10 (A finite actual-word base net with maximum length).**

$$finiteWordNet$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.exists_finite_word_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive radius, compactness and density produce a finite Fin(Fin m) word set, a maximum actual List length L0, and an approximation witness for every SU2 target. The theorem records existence only and gives no effectiveness or cardinality bound.

**Theorem 1.11 (Near-identity commutators are quadratic).**

$$commutatorQuadratic$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_mul_sub_mul_comm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm of VW-WV is bounded by twice the product of the two distances to identity. This is the licensed balanced-commutator contraction support.

**Theorem 1.12 (Unitary commutator factorization).**

$$commutatorIdentity$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.groupCommutator_sub_one_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unitary factors, the group commutator minus identity factors through VW-WV and the trailing adjoint product.

**Theorem 1.13 (Basic commutator contraction bound).**

$$commutatorBasic$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_groupCommutator_sub_le_basic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unitary factors near identity give the standard quadratic group-commutator bound.

**Theorem 1.14 (Two-factor perturbation estimate).**

$$productPerturbation$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_mul_sub_mul_le_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A product difference is bounded by the two factor differences weighted by the companion norms.

**Theorem 1.15 (Perturbing both commutator factors).**

$$commutatorFactorStability$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_mul_sub_mul_comm_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of two factor commutators is bounded by 4*a*delta when all four factors are within a of identity and each replacement has error at most delta.

**Theorem 1.16 (Balanced-commutator stability).**

$$commutatorStability$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_groupCommutator_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The licensed perturbation estimate bounds the change in a unitary group commutator by 4*a*delta*(1+a), the stability shape needed before the 3/2 error recurrence can be closed.

**Definition 1.17 (The determinant-one unitary carrier).**

$$SU2$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.SU2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SU2 U means that U is a unitary 2 by 2 complex matrix and has determinant one.

**Definition 1.18 (Density of actual ordinary words).**

$$denseAlphabet$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.DenseAlphabet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every determinant-one unitary U and every positive eta, some actual List(Fin m) word has L2 operator-norm error strictly less than eta.

**Definition 1.19 (Uniform polylogarithmic ordinary-word conclusion).**

$$uniformPolylog$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.UniformPolylog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

UniformPolylog Gamma asks for K>0 and 0<epsilon0<1 and one actual word for each U and 0<epsilon<=epsilon0, satisfying both the error and real length bounds.

**Definition 1.20 (Residual from the previous-level word).**

$$residual$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The residual is U * star(evalGamma u), so the successor construction starts from the previous-level witness u rather than a fixed initial-net word.

**Definition 1.21 (Left-to-right ordinary-word evaluation).**

$$evalGamma$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.evalGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Gamma : Fin m -> Matrix (Fin 2) (Fin 2) Complex, evalGamma [] is the identity and evalGamma (i :: w) is Gamma i multiplied by evalGamma w. The order is literal and is used unchanged by every successor witness.

**Definition 1.22 (The selector-defined inverse word).**

$$inverseWord$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.inverseWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inverseWord inverseLetter w is reverse.map inverseLetter. The selector is not required to be involutive; the compiled inverse evaluation theorem uses only Gamma (inverseLetter i) = star (Gamma i).

**Theorem 1.23 (Inverse words preserve actual length).**

$$inverseWordLength$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.inverseWord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing and mapping the selector preserves the exact List length. This is the length used by the produced ordinary witness.

**Definition 1.24 (The literal balanced successor word).**

$$balancedCommutatorWord$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.balancedCommutatorWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successor is exactly v ++ w ++ inv(v) ++ inv(w) ++ u. Its residual is formed from the previous-level u, and the same produced list is used for the value identity and for its length.

**Theorem 1.25 (The literal successor length).**

$$successorWordLength$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.successorWord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same successor list has length length(v)+length(w)+length(v)+length(w)+length(u). No scalar skLength or compressed-word convention is used.

**Theorem 1.26 (Evaluation of the same successor witness).**

$$successorWordValue$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.successorWord_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal list evaluates to eval(v) * eval(w) * star(eval(v)) * star(eval(w)) * eval(u). This preserves the source's ordinary-list inverse mechanism and does not infer length from a scalar cost function.

**Theorem 1.27 (Residual transport through the same successor).**

$$residualSuccessorValue$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.residual_successorWord_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the residual U*star(eval(u)) by the produced successor keeps the previous level word u explicit and exposes the balanced commutator factor in one identity.

**Definition 1.28 (The exact registered event telescope).**

$$ordinaryWordSolovayKitaevEvent$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.OrdinaryWordSolovayKitaevEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m, including m = 0, and every finite Gamma : Fin m -> Mat2, assume each letter is unitary, inverse closure holds by an existential selector, and every determinant-one unitary is approximated by an ordinary List(Fin m) in the complex Euclidean L2 operator norm. The conclusion asks for K > 0 and 0 < epsilon0 < 1, uniformly for all U and 0 < epsilon <= epsilon0, with the same word satisfying the error bound and real(length(w)) <= K * (log(1/epsilon))^(log(5)/log(3/2)).

The event makes no effectiveness, numerical constant, runtime, optimality, physical implementation, growing-dimension, or compressed-word claim.

**Definition 1.29 (The remaining quantitative bridge).**

$$quantitativeClosure$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.QuantitativeClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The candidate records the still-open density-derived finite seed, balanced-commutator stability, and same-word induction obligations. This proposition is not presented as a proof of the registered event and carries no freeze or coverage claim.

## References

- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.DenseAlphabet`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.OrdinaryWordSolovayKitaevEvent`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.QuantitativeClosure`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.SU2`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.SU2Set`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.SU2Set_subset_closure_evalGamma`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.UniformPolylog`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.axisRot_det`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.balancedCommutatorWord`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.compact_exists_finite_net`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.evalGamma`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.exists_finite_word_net`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.groupCommutator_sub_one_eq`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.inverseWord`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.inverseWord_length`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.isClosed_SU2Set`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.isCompact_SU2Set`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_groupCommutator_sub_le`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_groupCommutator_sub_le_basic`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_mul_sub_mul_comm_le`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_mul_sub_mul_comm_sub_le`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_mul_sub_mul_le_weighted`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.residual`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.residual_successorWord_value`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.su2`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.su2Set_subset_closedBall`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.su2_mul`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.successorWord_length`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.successorWord_value`
