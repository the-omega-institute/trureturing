# ActualMinorLift

## Abstract

The selected lift from the actual primitive normalized source minors

The source is VI, Definition 4.1 and equations (4.2)-(4.4). The twenty-eight rows remain r^13 E0 through E0 followed by r^13 E1 through E1, in twenty-nine columns r^28 through 1. The literal source polynomials are instantiated over the integer polynomial ring in b. Retaining the first twenty-seven columns and then the r or constant column defines the integer determinant polynomials a0 and c0. Evaluation is transported through coefficient extraction, the two fixed column selections, and the determinant ring-homomorphism identity. Thus their evaluations are exactly the original real fixed minors.

Let g be the gcd of a0 and c0 in Q[b]. Clear its denominators, take the integer primitive part, and normalize the leading sign to obtain h. The proof establishes that h is primitive, has positive leading coefficient, and maps to a nonzero rational scalar times g. These properties identify the source operation pp_+(g). Gauss's lemma transports the divisibility of g back to h dividing both integer determinant polynomials. Consequently the exact rational quotients a=a0/h and c=c0/h are maps of integer polynomials.

At b=criticalRoot and r=liftedR(b), selected_minor_nonzero supplies the nonzero original leading determinant and selected_root_common_zero supplies r a0(b)+c0(b)=0. Factoring a0=h A and c0=h C shows that both h(b) and A(b) are nonzero. Cancellation of this same evaluated common factor gives r=-C(b)/A(b). The exact quotient maps then identify this ratio with the source-normalized rational polynomials actualReducedA and actualReducedC. The nonzero rational scalar used to represent the gcd does not affect the ratio because the same factor is removed from both determinants.

This is a local identification at the actual selected algebraic parameter. The global determinant factorization and degree claims in VI (4.3), the universal complex-root and three-equation assertions, and the broader parents 15.2 and 15.3 remain open. The clock-five/six/seven source equations and the complete-world distinctions retain their original scope.

Utility classification: none. This module transports exact polynomial and determinant identities and cancels a common factor; it introduces no new finite certificate, enumeration or numerical reduction. Its selected-root proof consumes the existing same-unit common-zero and nonzero-minor certificates on the actual source proof path.

**Definition 1.1 (actual leading fixed determinant).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorA0`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorA0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer polynomial determinant of the literal fixed minor retaining columns r^28 through r. Its entries are the b-polynomial coefficients of the original shifted source equations.

**Definition 1.2 (actual constant fixed determinant).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorC0`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorC0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer polynomial determinant retaining columns r^28 through r^2 and the constant column, in the original order.

**Definition 1.3 (real evaluation of an integer polynomial).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.evalB`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.evalB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each real b, evalB(b) is the ring homomorphism from integer polynomials to the reals that casts integer coefficients and evaluates the variable at b.

**Definition 1.4 (positive primitive integer representative).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.positivePrimitive`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.positivePrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a rational polynomial f, clear denominators by integerNormalization, take the integer primitive part, and normalize its leading sign. For nonzero f this gives a primitive integer polynomial with positive leading coefficient whose rational image is associated with f.

**Definition 1.5 (gcd over the rational polynomial ring).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.actualGcdQ`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.actualGcdQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized gcd in Q[b] of the rational images of actualMinorA0 and actualMinorC0.

**Definition 1.6 (source positive primitive common factor).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.actualPrimitiveGcd`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.actualPrimitiveGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive primitive integer representative of actualGcdQ, implementing h=pp_+(gcd(a0,c0)).

**Definition 1.7 (exact reduced leading source minor).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedA`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational polynomial quotient actualMinorA0/actualPrimitiveGcd. The selected-source theorem proves exact factorization and that this quotient has integer coefficients.

**Definition 1.8 (exact reduced constant source minor).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedC`

*Formalization.* `D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational polynomial quotient actualMinorC0/actualPrimitiveGcd, with exact factorization and integer coefficients supplied by the same theorem.

**Theorem 1.9 (actual selected source-normalized lift).**

Lean statement: `D5/S3/Observer/CubicGain/ActualMinorLift.selected_source_normalized_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ActualMinorLift.selected_source_normalized_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Without added hypotheses, h is primitive and has positive leading coefficient, and there exists a nonzero rational u with h mapped to Q[b] equal to u times the actual rational gcd. There exist integer polynomials A,C with a0=h A and c0=h C, whose rational images equal the exact quotients actualReducedA and actualReducedC. At criticalRoot, h and the reduced leading minor are nonzero, and liftedR(criticalRoot) equals minus the evaluation of actualReducedC divided by the evaluation of actualReducedA.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.actualGcdQ`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorA0`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorC0`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.actualPrimitiveGcd`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedA`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedC`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.evalB`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.positivePrimitive`
- Truth anchor: `D5/S3/Observer/CubicGain/ActualMinorLift.selected_source_normalized_lift`
- Dependency: [D5/S3/Observer/CubicGain/SelectedMinorNonzero](SelectedMinorNonzero.md)
- Dependency: [D5/S3/Observer/CubicGain/SelectedRootCommonZero](SelectedRootCommonZero.md)
