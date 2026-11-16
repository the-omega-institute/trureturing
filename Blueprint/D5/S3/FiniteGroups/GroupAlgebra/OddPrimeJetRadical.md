# The radical and principal units

## Abstract

The leading-zero ideal of the actual odd-prime jet commutant.

Let p be any odd prime, K any field in an arbitrary universe with its given algebra structure over F=ZMod p, and q:K→K any F-linear map satisfying q(1)=0. All operators act on the original polynomial space of degree less than p. The commutant algebra consists of the actual F-linear operators commuting with every original representation operator. Restriction to constants gives a ring homomorphism to K; its kernel J is the leading-zero ideal. No finiteness hypothesis is needed for these structural statements.

**Theorem 1.1 (Commutativity of the ideal).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_commute`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two members of J commute under actual operator composition. In the unique divided-degree coordinates the leading scalar is zero. The scalar convolution and the scalar contribution to the top map are symmetric, and both ordered top-scalar terms vanish. The highest coefficient remains an unrestricted F-linear endomorphism of K.

**Theorem 1.2 (Elementwise nilpotence).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_element_pow`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_element_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X in J, X^p=0. This directly uses the derivative-filtration theorem for operators commuting with differentiation and annihilating constants from the commutant normal-form source.

**Theorem 1.3 (Joint ideal-power nilpotence).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_pow_eq_bot`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_pow_eq_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire ideal power J^p is zero. For each r, every element of J^r annihilates the kernel of D^r. To advance this assertion, write a generator of J^(r+1) as XY with X in J and Y in J^r. If D^(r+1)v=0, then D(Yv)=Y(Dv)=0, so Yv is constant and X annihilates it. Ideal closure extends the assertion to sums. Finally D^p=0 on the original polynomial carrier.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_commute`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_element_pow`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.radical_pow_eq_bot`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutant](OddPrimeJetCommutant.md)
