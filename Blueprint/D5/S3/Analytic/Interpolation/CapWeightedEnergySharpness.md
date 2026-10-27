# Attaining the cap and energy bound

## Abstract

An explicit integrable scalar family proves optimality of the abstract cap and weighted-energy coefficient.

Fix real 0<alpha<1. For B>=0 and cutoff a>0, take w(t)=B for t<=a and w(t)=B(a/t)^(alpha+1) for t>a. Only the positive half-line is integrated. The profile is measurable, nonnegative and bounded by B there. The following statements include actual integrability; they do not rely on a nonintegrable Bochner integral being assigned zero.

**Definition 1.1 (The cap and free-optimizer profile).**

Lean statement: `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer`

*Formalization.* `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition is total on all real parameters. Its analytic interpretation here uses 0<alpha<1, B>=0 and a>0.

**Theorem 1.2 (Admissibility and both exact moments).**

Lean statement: `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer_admissible_and_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer_admissible_and_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real alpha,B,a with 0<alpha<1, B>=0 and a>0, this profile is almost everywhere strongly measurable on (0,infinity), its norm is at most B almost everywhere, its energy t times norm(w(t)) squared is integrable with integral B^2 a^2(alpha+1)/(2alpha), and t^(-alpha)w(t) is integrable with integral B a^(1-alpha)(1/(1-alpha)+1/(2alpha)). The proof splits at a and uses the exact power integrals already supplied by CapWeightedEnergy.

**Theorem 1.3 (No smaller uniform coefficient).**

Lean statement: `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.sharp_constant_le_of_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.sharp_constant_le_of_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real alpha,C with 0<alpha<1, suppose the norm bound C B^alpha delta^((1-alpha)/2) holds for every real-valued almost everywhere strongly measurable w on (0,infinity), every B>=0 and delta>=0, whenever its norm is bounded by B almost everywhere and its actual integrable weighted energy has integral at most delta. Then sharpConstant(alpha)<=C. This lower bound already follows from the scalar profile B=a=1 and its exact moments. Together with the Banach-space upper bound, it proves that coefficient is optimal for the abstract class.

These are classical extremal integral calculations. No literature novelty is asserted. Sharpness in the whole abstract class does not establish that an actual modular resolvent difference, or an actual Petz recovery channel, realizes the same profile or the same optimal constant.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer`
- Truth anchor: `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer_admissible_and_moments`
- Truth anchor: `D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.sharp_constant_le_of_uniform_bound`
- Dependency: [D5/S3/Analytic/Interpolation/CapWeightedEnergy](CapWeightedEnergy.md)
