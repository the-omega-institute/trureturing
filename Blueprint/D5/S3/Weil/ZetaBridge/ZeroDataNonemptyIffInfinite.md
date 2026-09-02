# ZeroData Nonemptiness and Infinitely Many Nontrivial Zeros

## Abstract

ZeroData is inhabited exactly when the set of nontrivial zeta zeros is infinite.

**Theorem 1.1 (Exact nonvacuity characterization).**

$$\operatorname{Nonempty}\left(ZeroData\right) \iff \operatorname{Infinite}\left(\{\rho \mid \operatorname{IsNontrivialZero}\left(\rho\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward, the injective ZeroData enumeration embeds the natural numbers in the nontrivial-zero set. Backward, Mathlib's closed and discrete zeta-zero set is countable and compact-finite; an infinite countable subtype can therefore be enumerated without duplicates. Analytic order supplies its unique positive multiplicities, while the zeta functional equation and conjugation identity preserve those multiplicities and induce the required permutations.

This theorem neither proves infinitude nor exhibits a zero. It does not establish O-6 nonvacuity; it reduces ZeroData nonvacuity exactly to the open infinitude of the nontrivial-zero set.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite`
