# Actual off-diagonal top maps

## Abstract

The nonidentity Frobenius summands in the actual original kernel.

**Theorem 1.1 (An actual subgroup of order p^(n(n−1))).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be any odd prime, n at least one, and K any finite field in any universe of order p^n with its given F=ZMod p algebra structure. Write Phi(x)=x^p. Every unrestricted F-linear endomorphism has unique linearized coordinates sum_(i<n) a_i Phi^i. The coordinate supplier is the attributed upstream CFSG adaptation in FiniteJetCoefficients. Define W0 by a_0=0, equivalently the direct sum of K Phi^i for 1≤i<n. This condition is neither the vanishing of the ordinary trace nor the condition T(1)=0.

For every normalized q, the map T↦(1+top(T),identity original label) embeds the additive group of all top maps into the actual kernel of the label projection. Products of two top operators vanish, so multiplication of these units adds T. Uniqueness of the actual commutant coordinates proves injectivity. Restricting the embedding to W0 gives a subgroup with exactly n−1 free K coordinates, hence order p^(n(n−1)). For n=1 it is trivial. This count alone makes no assertion that this subgroup is the commutator subgroup.

**Theorem 1.2 (Exactly the scalar-action difference image).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.scalar_difference_range`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.scalar_difference_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one constant field scalar a for which W0 is exactly the image of T↦a T a^(-1)−T. Scalar conjugation multiplies the i-th linearized coefficient by a^(1−p^i), fixing the identity coefficient. Choose a generator of K's multiplicative group. For 1≤i<n, the integer p^i−1 lies strictly between zero and p^n−1, so a^(1−p^i)−1 is nonzero. Dividing each off-diagonal coefficient by this factor gives the converse inclusion, as equality of unrestricted prime-field-linear maps.

**Theorem 1.3 (Exact actual kernel commutator subgroup).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.actual_commutator_structure`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.actual_commutator_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutator subgroup of the actual label-projection kernel is precisely the embedded W0 top subgroup, of order p^(n(n−1)). To prove the reverse inclusion, expand XY−YX using the actual commutant multiplication formula. The scalar polynomial families and the symmetric top convolution cancel. The remaining top map is a sum of scalar-composition brackets, whose identity-Frobenius coefficients vanish. Right composition by the leading scalars of the two inverse operators preserves W0. Thus the group commutator, obtained by right multiplying XY−YX by X^(-1)Y^(-1) and adding one, is a W0 top unit. The other inclusion is realized by constant-scalar commutators. The same structural theorem retains the actual embedded principal-unit subgroup: it is abelian, every element has p-th power one, and its order is p^(n(p−2)+n²). The conjunction also states that the actual original first derived subgroup is nontrivial, including n=1 and p=3. No section of the label stabilizer onto its Galois image is used.

**Theorem 1.4 (Inclusion in the actual kernel commutator subgroup).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_le_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_le_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual top unit associated to T in W0 belongs to the actual kernel's commutator subgroup. Constant scalar units embed with identity original labels. Their conjugation on top maps is T↦a T a^(-1). Since top products vanish, the commutator with 1+top(S) is exactly 1+top(a S a^(-1)−S). The scalar-action image theorem realizes every T in W0 in this way. Together with the reverse inclusion, this gives the exact subgroup theorem.

**Theorem 1.5 (The exact actual Galois-image boundary).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_two_eq_bot_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_two_eq_bot_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second derived subgroup of the actual original group is trivial if and only if its actual Galois image is trivial. For the converse, choose an actual g with nonidentity Galois coordinate sigma. There is a unit a with b=sigma(a)/a and b^p not equal to b. If all ratios were fixed by Frobenius, applying this condition to x and x+1 would force sigma(x)=x, using that the roots of X^p−X lie in the prime subfield. Form the actual first-derived element x=[g,M_a], where M_a is coefficientwise multiplication and has identity original label. Its leading scalar is b. The pure Frobenius top unit t=1+top(Phi) lies in the actual kernel commutator and hence in the first derived subgroup; the ratio witness ensures n>1. If the second derived subgroup were trivial, x would commute with t. The actual commutant multiplication, evaluated on the top divided monomial, would then force b=b^p, a contradiction. The chosen g can have an arbitrary accompanying scalar label; no pure-Frobenius lift is used.

**Theorem 1.6 (Universal exact derived length of the actual original group).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_structure`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p>2 be any prime, including three; let K be a finite field in any universe of order p^n with n≥1; and let q be any F=ZMod p linear endomorphism with q(1)=0. For the actual original intertwiner group G and its actual label Galois image H, the theorem states all three conclusions together: G^(3)=1; G^(2)=1 if and only if H=1; and G^(1) is nontrivial. Thus the exact derived length is two for trivial H and three for nontrivial H. Every normalized q and every prime-field-linear top map remain in scope. The actual label stabilizer is retained, including cases where its projection onto H does not split.

**Theorem 1.7 (The actual original group is nonabelian).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_one_ne_bot`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_one_ne_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd prime p, every finite field K in an arbitrary universe with order p^n and n≥1, and every unrestricted F-linear q with q(1)=0, the first derived subgroup of the actual original group is nontrivial. If n>1, the exact kernel commutator has order p^(n(n−1))>1. At n=1, normalization forces q=0. The original additive label x↦−x then has an actual intertwiner by the existing coefficient classification. An abelian original group would commute with every original representation operator; faithfulness of that representation would force every actual label to be the identity. Applying this to −1 contradicts p>2. The argument retains p=3. It does not assert a derived-length upper bound or the Galois-image equivalence.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.actual_commutator_structure`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_cardinality`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.offDiagonalTop_le_commutator`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_one_ne_bot`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_structure`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.original_derived_two_eq_bot_iff`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop.scalar_difference_range`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGalois](OddPrimeJetGalois.md)
