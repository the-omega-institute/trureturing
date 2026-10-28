# Mean-sensitive finite-colour concentration

## Abstract

The actual mean controls the lower tail when only each colour fibre is mutually independent.

**Theorem 1.1 (Moment-generating function).**

Lean statement: `D5/S3/Combinatorics/Probability/FiniteColourLowerTail.mgf_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/FiniteColourLowerTail.mgf_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any probability space P, let I be finite and let X_i be real a.e. measurable variables in [0,1] almost everywhere. Let k>0 and colour:I to Fin k be deterministic. For each j, the entire family indexed by the subtype colour(i)=j is mutually independent. There is no independence hypothesis between fibres. Put S=sum X_i and mu=sum of their actual integrals. For every real t the MGF is at most exp((mu/k)(exp(k t)-1)). Empty I, empty fibres and mu=0 are included.

The bounded exponential chord and scalar add_one_le_exp bound each factor. The pinned Mathlib iIndepFun.mgf_sum₀ factors only the individual fibres. ENNReal.lintegral_prod_norm_pow_le with weights 1/k combines them. Exponential integrability follows from the interval bounds. ofReal conversion preserves the finite real expectations; no order argument at infinity is used. The scalar inequality works at negative tilts, where prod_one_add_le_exp_sum is inapplicable. This is a classical Holder-Chernoff derivation, with no mathematical novelty claim.

**Theorem 1.2 (Closed lower-tail event).**

Lean statement: `D5/S3/Combinatorics/Probability/FiniteColourLowerTail.lower_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/FiniteColourLowerTail.lower_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same assumptions, for every delta>=0, P.real{S<=(1-delta)mu} is at most exp(-delta^2 mu/(2k)). The finite tilt -delta/k and the comparison exp(-delta)<=1-delta+delta^2/2 prove this using the existing exponential Markov supplier. No division by mu occurs; delta=0 and all zero-mean cases remain valid. The real-valued measure is used, with no assumption that the sample space is finite, countable or complete. Mutual independence, rather than pairwise independence, and the unit upper bound are load-bearing. TripleReservoir consumes this theorem after proving actual event probabilities and fibre independence.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/FiniteColourLowerTail.lower_tail`
- Truth anchor: `D5/S3/Combinatorics/Probability/FiniteColourLowerTail.mgf_sum_le`
