# Mixed Exclusion Spectrum

## Abstract

Colored nearest-neighbor exclusion has a quadratic law and a fermionic trace term.

**Theorem 1.1 (Colored exclusion has a quadratic transfer law).**

$$\forall m,K,n \in \mathbb{N},\ n>0 \Rightarrow\ A_m(K+2)=A_m(K+1)+mA_m(K) \land\ \operatorname{charpoly}(T_m)(X)=X^{2}-X-m \land\ \operatorname{Spec}(M)=\{2,-1,0\} \land\ \operatorname{tr}(M^n)-2^n=(-1)^n.$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/MixedExclusionSpectrum.mixed_exclusion_recurrence_and_two_color_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A_m(K) be the weighted count of occupied subsets of K consecutive positions with no adjacent occupied pair, where each occupied position has m possible colors. Splitting on the last position gives A_m(K+2) = A_m(K+1) + m A_m(K). The corresponding two-state transfer matrix therefore has characteristic polynomial X^2 - X - m.

For m = 2, retaining the two colors as separate states gives the explicit three-state transfer matrix with spectrum {2, -1, 0}. A rational eigenbasis conjugates it to that diagonal matrix, so conjugation invariance of trace yields tr(M^n) - 2^n = (-1)^n for positive n.

The recurrence is a direct specialization of the repository theorem wordSum_succ_succ. Pinned Mathlib was searched before proving; no theorem packaging the two-color spectrum and trace identity was found. The proof uses spectrum.units_conjugate, spectrum_diagonal, Units.conj_pow, and Matrix.trace_units_conj.

This formalizes the mixed-law and m = 2 degeneracy clauses of source theorem 6.50. The k-bonacci ladder, Shannon-capacity identifications, numerical RLL comparisons, and physical dictionary are not asserted by this declaration.

## References

- Truth anchor: `D5/S1/Eigenstructure/MixedExclusionSpectrum.mixed_exclusion_recurrence_and_two_color_spectrum`
- Dependency: [D5/S1/Recurrence/TraceMap](../Recurrence/TraceMap.md)
