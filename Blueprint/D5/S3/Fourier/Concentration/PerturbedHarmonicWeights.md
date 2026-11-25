# Collision Budgets for Perturbed Cutoffs and Recomputed Weights

## Abstract

An enlarged reference test bounds the weighted collision excess on a perturbed cutoff.

Let J have decidable equality. Let g and h be real reference and perturbed frequencies, with |h(j)−g(j)|≤r(j)≤R. Let V be a finite support containing every index with X−R<g(j)≤T+R, and assume r(j)<g(j) on V. Write U for the indices in V with X<h(j)≤T. Fix a≥0, a natural degree p and a resolution η≥0.

For a positive ordinate x write w(x)=x/(a+x²). The realized weights u on U are w(h(j)). The weights v on V are [g(j)/(g(j)−r(j))]w(g(j)). For a finite support A, write E(A,z) for the degree-p near-collision mass with frequencies h restricted to A and weights z, minus the diagonal mass.

**Theorem 1.1 (Transfer from the enlarged support to the realized cutoff).**

$$\left(\forall j \in J,\; X<\operatorname{h}\left(j\right)\leq T \Rightarrow j \in V\right) \land \operatorname{E}\left(U, u\right) \le \operatorname{E}\left(V, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/PerturbedHarmonicWeights.collision_excess_le_on_perturbed_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displacement bound places every actual cutoff index in the enlarged reference cutoff. On V, write x=g(j), y=h(j) and r=r(j). The inequalities y(x−r)≤y² and y(x−r)≤x² follow from x−r≤y≤x+r. Multiply by the positive denominators and combine these inequalities with a≥0 to obtain u(j)≤v(j). As a uniform factor over a≥0 the factor x/(x−r) is attained when a=0 and y=x−r.

Extend each degree vector on U by zero on V. The extension preserves total degree and frequency. It also preserves the multinomial coefficient because the added coordinates have factorial 0!=1. The corresponding monomial product can only increase under the dominating weights. Diagonal subtraction leaves a sum over distinct ordered pairs, whose members stay distinct under the injection. The other terms on V are nonnegative.

A bound on the excess for the fixed support and weights therefore applies to the realized test at the same resolution. The frequencies on both supports come from the same perturbation. This transfer applies to comparison spectra for which the enlarged tests have certified budgets.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/PerturbedHarmonicWeights.collision_excess_le_on_perturbed_cutoff`
- Dependency: [D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations](ContinuousSpectralPerturbations.md)
