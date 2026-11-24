# Identical first-degree data and different directed-gap energies

## Abstract

Two integer spectra share their first-degree data and have different disjoint residual masses.

**Theorem 1.1 (A five-point witness).**

$$R_{2}(A) = 8, R_{2}(B) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.exists_equal_first_data_distinct_degree_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectra A and B have unit weights at the respective points (0,1,5,6,13) and (0,2,3,7,13). Both sums of the points are 25, both sums of the squares are 231, and both bands have endpoints 0 and 13.

For any resolution η from zero inclusive to one exclusive, only equal integer frequencies count as close. Thus the degree-one mass is five in each spectrum and all five pairs are diagonal. The directed-gap collision counts are 28 for A and 20 for B. The shared-endpoint correction subtracts 40 and adds 20 in each spectrum.

The arithmetic relation 0+6=1+5 accounts for all nonzero disjoint degree-two mass of A. The two pair orders and the two orders within each pair give total mass eight. B has zero disjoint mass at the same resolutions.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.exists_equal_first_data_distinct_degree_two`
- Dependency: [D5/S3/Fourier/Concentration/DegreeTwoResidualDifferenceEnergy](DegreeTwoResidualDifferenceEnergy.md)
