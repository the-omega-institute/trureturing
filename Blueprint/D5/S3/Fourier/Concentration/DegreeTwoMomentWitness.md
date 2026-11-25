# Identical first-degree data and different directed-gap energies

## Abstract

Two integer spectra share their first-degree data and have different disjoint residual masses.

**Theorem 1.1 (A five-point witness).**

$$\begin{aligned}&\exists A,B: \operatorname{Fin}\left(5\right) \Rightarrow \mathbb{Z},\\&\sum_{i} A\left(i\right) = \sum_{i} B\left(i\right) = 25,\quad\sum_{i} A\left(i\right)^{2} = \sum_{i} B\left(i\right)^{2} = 231,\\&(\forall i: \operatorname{Fin}\left(5\right), A\left(i\right),B\left(i\right) \in [0,13]) \land A\left(0\right) = B\left(0\right) = 0 \land A\left(4\right) = B\left(4\right) = 13,\\&\forall eta \in [0,1),\quad\left(M_{1}\right)\left(A, eta\right) = \left(M_{1}\right)\left(B, eta\right) = 5,\\&\quad\left(R_{2}\right)\left(A, eta\right) = 8,\quad\left(R_{2}\right)\left(B, eta\right) = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.exists_equal_first_data_distinct_degree_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectra A and B have unit weights at the respective points (0,1,5,6,13) and (0,2,3,7,13). Both sums of the points are 25, both sums of the squares are 231, and both bands have endpoints 0 and 13.

Here M₁ is the unit-weight degree-one near-collision mass including the diagonal, and R₂ is the unit-weight degree-two mass with disjoint supports. For any resolution η from zero inclusive to one exclusive, only equal integer frequencies count as close. Thus the degree-one mass is five in each spectrum and all five pairs are diagonal. The directed-gap collision counts are 28 for A and 20 for B. The shared-endpoint correction subtracts 40 and adds 20 in each spectrum.

The arithmetic relation 0+6=1+5 accounts for all nonzero disjoint degree-two mass of A. The two pair orders and the two orders within each pair give total mass eight. B has zero disjoint mass at the same resolutions.

**Definition 1.2 (Determination by first-degree observations).**

$$\begin{aligned}&Determination \iff \forall A,B: \operatorname{Fin}\left(5\right) \Rightarrow \mathbb{Z},\\&(\sum_{i} A\left(i\right) = \sum_{i} B\left(i\right) \land \sum_{i} A\left(i\right)^{2} = \sum_{i} B\left(i\right)^{2} \land (\forall i: \operatorname{Fin}\left(5\right), A\left(i\right),B\left(i\right) \in [0,13]) \land A\left(0\right) = B\left(0\right) = 0 \land A\left(4\right) = B\left(4\right) = 13\\&\quad \land (\forall eta \in [0,1), \left(M_{1}\right)\left(A, eta\right) = \left(M_{1}\right)\left(B, eta\right)))\\&\quad\longrightarrow (\forall eta \in [0,1), \left(R_{2}\right)\left(A, eta\right) = \left(R_{2}\right)\left(B, eta\right)).\end{aligned}$$

*Formalization.* `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.degreeOneDeterminesDegreeTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For unit-weight, integer-valued maps on five indices with band [0,13], the premise fixes the endpoints at indices 0 and 4 in both maps. It also requires equal sums, equal sums of squares, and equal degree-one masses at every resolution in [0,1). The claim asks whether the degree-two disjoint masses must agree at every such resolution.

**Theorem 1.3 (The determination claim is false).**

$$\neg Determination$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.degree_one_does_not_determine_degree_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two spectra above satisfy all the premises. At resolution zero their degree-two disjoint masses differ.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.degreeOneDeterminesDegreeTwo`
- Truth anchor: `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.degree_one_does_not_determine_degree_two`
- Truth anchor: `D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.exists_equal_first_data_distinct_degree_two`
- Dependency: [D5/S3/Fourier/Concentration/DegreeTwoResidualDifferenceEnergy](DegreeTwoResidualDifferenceEnergy.md)
