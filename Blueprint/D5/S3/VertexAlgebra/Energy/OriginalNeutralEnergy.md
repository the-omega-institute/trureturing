# Neutral words and finite energy recombination

## Abstract

The original normal-product word estimates and orthogonal recombination used by both lattice energy bounds.

This support module keeps the original private neutral proof components in the OriginalChargedEnergy namespace. Its only original data are LatticeData D, the original Carrier, Hm and normD. Positivity is derived by OriginalCurrentEnergy. For energy recombination the complex H satisfies both inverse equations with gramComplex(D). No diagonal restriction, oscillator cutoff, support bound, alternate carrier or half-frequency form is introduced.

The private original_word_energy_le specializes the single seed-parametrized arbitrary-charge induction in OriginalWordEnergy to charge zero with the literal identity seed (1,0). It estimates literal original normal-product words at a general mode between grades E,F at most M. Its left branch retains negative currents and its right branch retains nonnegative currents. The intermediate derivative strip vanishes by the actual binomial coefficient. Positive energy gives finite branch ranges, with surviving intermediate grades between 0 and M. The recursive constant is K(empty)=1 and K((i,r)::tail)=(r+2)*((r+1)^r/r!)*sqrt(3*G(i,i))*K(tail); the word exponent is weight plus length, at most twice the weight. No factors are commuted and no contractions are dropped.

The polynomial constant is 1+sum_e |coeff(p,e)|*K(occurrences(e)), positive also when p=0. Weighted homogeneity and the literal polynomial field expansion give the fixed-grade neutral bound. The private energy_bound_of_grades uses exact Hm orthogonality of distinct actual Sugawara grades and finite grade projections. Distinct shifted output energies remain orthogonal, so the full finite mixed-state estimate has no input-support multiplier. OriginalNeutralEnergy retains the unchanged private original_neutral_energy_le; OriginalChargedEnergy consumes it to prove its existing public neutral bound and consumes the grade estimate and recombination in the charged bound.

All declarations here are consumed private proof components, without public wrappers, standalone novelty or a new public-theorem registration target. Existing source suppliers retain their Bakalov-Kac, Matsuo-Nagatomo, Carnahan and Mathlib attributions. Smeared fields, closability, strong locality, full string theory and AdS/CFT remain separate obligations.

## References

- Dependency: [D5/S3/VertexAlgebra/Energy/OriginalWordEnergy](OriginalWordEnergy.md)
