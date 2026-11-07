# Neutral words and finite energy recombination

## Abstract

The original normal-product word estimates and orthogonal recombination used by both lattice energy bounds.

**Theorem 1.1 (Hm grade orthogonal).**

Lean statement: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.Hm_grade_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.Hm_grade_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original LatticeData D and complex H satisfying both inverse-Gram equations, original u,v in distinct integer Sugawara grades E,F have Hm(u,v)=0. The actual original L0 pairing identity proves the result; the within-grade form remains non-diagonal.

**Theorem 1.2 (normD orthogonal sum).**

Lean statement: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.normD_orthogonal_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.normD_orthogonal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive original lattice Gram form, finite index set s and original family f with Hm(f(i),f(j))=0 for distinct indices in s, normD of its sum squared equals the sum of normD(f(i)) squared.

**Theorem 1.3 (energy power grade).**

Lean statement: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.energy_power_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.energy_power_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original D,H with both inverse-Gram equations, every integer E, original v in grade E and natural N, (1+L0)^N v=((E:Complex)+1)^N times v.

**Theorem 1.4 (stateEnergies nonneg).**

Lean statement: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.stateEnergies_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.stateEnergies_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive original lattice Gram form and original finite v, every integer E in stateEnergies D v is nonnegative, by actual charge-energy positivity and nonnegative oscillator energy.

This support module keeps the original private neutral proof components in the OriginalChargedEnergy namespace. Its only original data are LatticeData D, the original Carrier, Hm and normD. Positivity is derived by OriginalCurrentEnergy. For energy recombination the complex H satisfies both inverse equations with gramComplex(D). No diagonal restriction, oscillator cutoff, support bound, alternate carrier or half-frequency form is introduced.

The private original_word_energy_le specializes the single seed-parametrized arbitrary-charge induction in OriginalWordEnergy to charge zero with the literal identity seed (1,0). It estimates literal original normal-product words at a general mode between grades E,F at most M. Its left branch retains negative currents and its right branch retains nonnegative currents. The intermediate derivative strip vanishes by the actual binomial coefficient. Positive energy gives finite branch ranges, with surviving intermediate grades between 0 and M. The recursive constant is K(empty)=1 and K((i,r)::tail)=(r+2)*((r+1)^r/r!)*sqrt(3*G(i,i))*K(tail); the word exponent is weight plus length, at most twice the weight. No factors are commuted and no contractions are dropped.

The polynomial constant is 1+sum_e |coeff(p,e)|*K(occurrences(e)), positive also when p=0. Weighted homogeneity and the literal polynomial field expansion give the fixed-grade neutral bound. The private energy_bound_of_grades uses exact Hm orthogonality of distinct actual Sugawara grades and finite grade projections. Distinct shifted output energies remain orthogonal, so the full finite mixed-state estimate has no input-support multiplier. OriginalNeutralEnergy retains the unchanged private original_neutral_energy_le; OriginalChargedEnergy consumes it to prove its existing public neutral bound and consumes the grade estimate and recombination in the charged bound.

The shared grade orthogonality, power and recombination results directly supply the original Sobolev and heat analysis; the word bounds remain consumed proof components. Existing source suppliers retain their Bakalov-Kac, Matsuo-Nagatomo, Carnahan and Mathlib attributions. Smeared fields, closability, strong locality, full string theory and AdS/CFT remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.Hm_grade_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.energy_power_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.normD_orthogonal_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy.stateEnergies_nonneg`
- Dependency: [D5/S3/VertexAlgebra/Energy/OriginalWordEnergy](OriginalWordEnergy.md)
