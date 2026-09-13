# A397434: adjacent reduced-coefficient counts

## Abstract

The reduced-coefficient count sequence has adjacent values equal exactly when the lower dimension is two modulo four.

The Lean module defines a(n) from reducedCoeffBit, and thresholdAnfSupport filters that same reduced bit. It proves the adjacent classification for this reduced-coefficient count sequence. The intended identification with the OEIS ANF support counts uses Meaux's ANF coefficient reduction, stated separately below, but the main proof does not consume that declaration; the Boolean-function -> Mobius-coefficients -> reduced-bit -> support-count semantic bridge is therefore not machine-closed in this module.

**Theorem 1.1 (Threshold coefficients reduce to one binomial coefficient).**

$$\forall t \in \mathbb{N},\; \forall d \in \mathbb{N},\; \left(1 \le t \land 1 \le d\right) \Rightarrow thresholdAnfCoeff\left(t, d\right) = cast\left(choose\left(d - 1, t - 1\right), ZMod\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A397434ThresholdAnf.threshold_anf_coefficient_reduction` (`✓ std3`). ∎

*Citation.* Pierrick Meaux (2021). *On the Fast Algebraic Immunity of Threshold Functions*. DOI: [10.1007/s12095-021-00505-y](https://doi.org/10.1007/s12095-021-00505-y).

*Commentary.*

Boolean-lattice Mobius inversion gives the sum of choose(d,j) from j=t through d. The complete binomial sum vanishes in characteristic two, and Pascal cancellation leaves choose(d-1,t-1).

**Theorem 1.2 (Adjacent counts agree exactly at residue two modulo four).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(a\left(n\right) = a\left(n + 1\right) \Leftrightarrow n \bmod 4 = 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tanguy Gautier Loic Le Mer (2026). *OEIS A397434, monomial counts for threshold Boolean functions*. URL: <https://oeis.org/A397434>.

*Commentary.*

The direct definitions identify the filtered reduced-bit support cardinality with the binomially weighted count defining a. The two cardinality statements are used when deriving the exact difference between adjacent even and odd rows.

For an even lower dimension 2m, the difference is twice a nonnegative binomial sum over degrees d for which both choose(d-1,m) and choose(d,m) are odd. This degree set is empty for odd m; for positive even m it contains m+1, making the sum positive.

At an odd lower dimension, adding a variable contributes a positive shifted row, so equality is impossible. Combining the odd and even cases gives the residue-class characterization.

## References

- Truth anchor: `D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four`
- Truth anchor: `D5/S3/ArithSums/A397434ThresholdAnf.threshold_anf_coefficient_reduction`
