# The algebraic reduction of prescribed coset powers

## Abstract

Equation (43) and recursive triangular transport convert independent ordered commutator-value coverage into prescribed coset-power surjectivity, preserving the exponent and exact length.

Work in an arbitrary group G. For the subgroup statements, N is any normal subgroup of G. The exponent q and length m are arbitrary natural numbers, including zero, and h is any prescribed tuple from Fin m to G. Finiteness, simplicity and a quantitative bound are not hypotheses of this algebraic reduction.

**Definition 1.1 (Right conjugation).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperConj`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperConj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x and g in G, paperConj(x,g) is g inverse times x times g. This is the paper's right conjugation convention.

**Definition 1.2 (The paper's commutator).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperComm`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperComm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x and y in G, paperComm(x,y) is x inverse times y inverse times x times y. The multiplication order is part of the definition.

**Lemma 1.3 (Conjugation in Mathlib's convention).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperConj_eq_mathlib`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperConj_eq_mathlib` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all x and g in G, paperConj(x,g) equals MulAut.conj(g inverse) applied to x.

**Lemma 1.4 (Commutators in Mathlib's convention).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperComm_eq_mathlib`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperComm_eq_mathlib` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all x and y in G, paperComm(x,y) equals Mathlib's commutator element of x inverse and y inverse. These identities allow the collection formula to use the paper's order throughout.

**Definition 1.5 (Ordered products).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.orderedProduct`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.orderedProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a tuple f from Fin m to G, orderedProduct(f) multiplies f(0) through f(m-1) in increasing index order. The empty product is the identity.

**Definition 1.6 (Prefixes before a position).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.prefixProduct`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.prefixProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a tuple f from Fin m to G and a natural i, prefixProduct(f,i) is the ordered product of the first i entries, or the whole tuple if i exceeds m. At a position i in Fin m it ends strictly before that position.

**Definition 1.7 (Inverse power prefixes).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.powerPrefix`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.powerPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For q natural, h from Fin m to G and i in Fin m, powerPrefix(q,h,i) is the inverse of the ordered product of h(j) to the qth power over j strictly less than i. This is the paper's tau at position i.

**Theorem 1.8 (Collecting conjugated factors).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.conjugated_product_collection`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.conjugated_product_collection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and tuples z and b from Fin m to G, the ordered product of paperConj(z(i),b(i)) equals the ordered product of paperConj(paperComm(b(i),z(i) inverse),prefixProduct(z,i) inverse), followed on the right by orderedProduct(z). Induction on the tuple length retains every inverse-prefix conjugation; the identity is valid in noncommutative groups.

**Definition 1.9 (Changing the coset variables).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.cosetChange`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.cosetChange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For tuples x, b and h from Fin m to G, cosetChange(x,b,h,i) is paperConj(x(i),b(i)) times paperComm(b(i),h(i) inverse). Multiplying it by h(i) gives paperConj(x(i)*h(i),b(i)).

**Theorem 1.10 (Equation (43) with its rightmost factor).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.equation43`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.equation43` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q, m and tuples x, b, h, let psi(x) be the ordered product of (x(i)*h(i)) to the qth power, followed by the inverse of the ordered product of h(i) to the qth power. Then psi(cosetChange(x,b,h)) equals the ordered product of paperConj(paperComm(b(i),((x(i)*h(i)) to the qth power) inverse),powerPrefix(q,x*h,i)), followed by psi(x) on the right. The product order, inverse prefixes and final psi(x) are all retained.

**Definition 1.11 (Corrected conjugating elements).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedElement`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedElement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For q natural, h from Fin m to G and i in Fin m, correctedElement(q,h,i) is paperConj(h(i) inverse,powerPrefix(q,h,i)). Thus the inverse of h(i), conjugated by the inverse ordered power prefix, determines the paper's corrected right action.

**Definition 1.12 (The corrected action on a normal subgroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedAutomorphisms`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedAutomorphisms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For normal N, correctedAutomorphisms(N,q,h,i) is MulAut.conjNormal of correctedElement(q,h,i) inverse, acting on N. Normality ensures that this ambient conjugation restricts to an automorphism of N.

**Theorem 1.13 (The generated action group is preserved).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedAutomorphisms_generated`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedAutomorphisms_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every normal N, q, m and prescribed h, the subgroup of MulAut(N) generated by the corrected automorphisms equals the subgroup generated by MulAut.conjNormal(h(i)). Induction shows that conjugating successive generators by earlier power prefixes preserves the ambient generated subgroup, and its image under normal conjugation gives this equality. Any property depending only on the generated action group, including its orbits and transitivity in a specified action, therefore transfers.

**Definition 1.14 (The independent ordered value-set premise).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.PrescribedCommutatorCoverage`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.PrescribedCommutatorCoverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any group A, natural q and m and prescribed automorphisms k indexed by Fin m, PrescribedCommutatorCoverage(A,q,m,k) means: there exists y from Fin m to A such that for every t in A there exists c from Fin m to A whose ordered product of c(i) inverse times ((k(i)*MulAut.conj(y(i) inverse)) to the qth power)(c(i)) equals t. Automorphism multiplication uses Mathlib's composition convention. The inner tuple y is chosen before every target t; c may depend on t. This requires equality of actual ordered value sets with A, a stronger condition than generation by commutator values.

**Theorem 1.15 (Realizing every inner correction recursively).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.triangular_transport`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.triangular_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every normal N, natural q and m, prescribed h from Fin m to G and y from Fin m to N, there exists x from Fin m to N such that at every i, paperConj((x(i)*h(i)) inverse,powerPrefix(q,x*h,i)) equals y(i)*correctedElement(q,h,i), with subgroup elements read in G. The construction is recursive: the prefix at i depends only on earlier coordinates. Equality of the two prefix products in G/N supplies their difference in N, and normal conjugation constructs the next x(i). This realizes the chosen inner action exactly.

**Theorem 1.16 (Exact prescribed coset-power surjectivity under the value-set premise).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.coset_power_surjective_of_prescribed_commutator_coverage`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.coset_power_surjective_of_prescribed_commutator_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every normal N, natural q and m and prescribed h from Fin m to G, assume PrescribedCommutatorCoverage(N,q,m,correctedAutomorphisms(N,q,h)). Then for every a in N there exists b from Fin m to N such that the ordered product of (b(i)*h(i)) to the qth power equals a times the ordered product of h(i) to the qth power. Both sides use the same q and exact m. Choose the inner tuple, realize it by triangular transport, and use its value-set premise at a*psi(x) inverse. Equation (43) then gives the required coset equation.

The source is Nikolov and Segal, On finitely generated profinite groups, I, DOI 10.4007/annals.2007.165.171, printed pages 227–228. The uniform transitive commutator-value theorem of Proposition 10.2 and its quantitative simple-group inputs remain unproved here. The conditional coset equation alone supplies no uniform width, restricted Burnside bound or strong completeness theorem.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.PrescribedCommutatorCoverage`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.conjugated_product_collection`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedAutomorphisms`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedAutomorphisms_generated`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.correctedElement`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.cosetChange`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.coset_power_surjective_of_prescribed_commutator_coverage`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.equation43`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.orderedProduct`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperComm`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperComm_eq_mathlib`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperConj`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.paperConj_eq_mathlib`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.powerPrefix`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.prefixProduct`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge.triangular_transport`
- Dependency: [D5/S3/Factorization/Galois/ProfinitePowerTransfer](../../Factorization/Galois/ProfinitePowerTransfer.md)
