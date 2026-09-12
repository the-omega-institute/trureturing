# A397434: adjacent threshold ANF support counts

## Abstract

The threshold Boolean ANF support counts at adjacent dimensions agree exactly when the lower dimension is two modulo four.

For n variables, take the Boolean function that is one when at least ceil(n/2) variables are one. Its algebraic normal form over GF(2) has one squarefree monomial for each supported subset, and a(n) is the cardinality of this support.

**Theorem 1.1 (Threshold coefficients reduce to one binomial coefficient).**

$$\forall t \in \mathbb{N},\; \forall d \in \mathbb{N},\; \left(1 \le t \land 1 \le d\right) \Rightarrow thresholdAnfCoeff\left(t, d\right) = cast\left(choose\left(d - 1, t - 1\right), ZMod\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A397434ThresholdAnf.threshold_anf_coefficient_reduction` (`✓ std3`). ∎

*Citation.* Pierrick Meaux (2019). *On the Fast Algebraic Immunity of Majority Functions*. URL: <https://eprint.iacr.org/2019/999>.

*Commentary.*

Boolean-lattice Mobius inversion gives the sum of choose(d,j) from j=t through d. The complete binomial sum vanishes in characteristic two, and Pascal cancellation leaves choose(d-1,t-1).

**Theorem 1.2 (Adjacent counts agree exactly at residue two modulo four).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(a\left(n\right) = a\left(n + 1\right) \Leftrightarrow n \bmod 4 = 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tanguy Gautier Loic Le Mer (2026). *OEIS A397434, monomial counts for threshold Boolean functions*. URL: <https://oeis.org/A397434>.

*Commentary.*

Grouping supported subsets by degree identifies their cardinality with the binomially weighted count defining a. The two cardinality statements are used when deriving the exact difference between adjacent even and odd rows.

For an even lower dimension 2m, the difference is twice a nonnegative binomial sum over degrees d for which both choose(d-1,m) and choose(d,m) are odd. This degree set is empty for odd m; for positive even m it contains m+1, making the sum positive.

At an odd lower dimension, adding a variable contributes a positive shifted row, so equality is impossible. Combining the odd and even cases gives the residue-class characterization.

## References

- Truth anchor: `D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four`
- Truth anchor: `D5/S3/ArithSums/A397434ThresholdAnf.threshold_anf_coefficient_reduction`
