# Least-Digit Zeckendorf Decomposition

## Abstract

Positive canonical W digits split uniquely according to their least occupied position.

**Theorem 1.1 (Canonical W digits have a unique three-way least-digit form).**

$$\forall r\neq0,\ C(r) \Rightarrow \left((r_0,r_1)=(0,0) \land \exists! t\neq0,\ C(t) \land r=\sigma_2(t)) \lor (r_0,r_1)=(1,0) \land \exists! t,\ C(t) \land r=e_0+\sigma_2(t) \lor (r_0,r_1)=(0,1) \land \exists! t,\ C(t) \land r=e_1+\sigma_3(t)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/LeastDigitDecomposition.canonical_raw_least_digit_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a canonical raw W string, each coefficient is zero or one and adjacent occupied positions are forbidden. The first two coefficients therefore have exactly the patterns 00, 10, or 01. These are the three branches selected by the theorem.

The operation shiftDigits is the raw-digit realization of sigma: it moves every occupied index upward by a fixed offset. The inverse tail is constructed with Finsupp.comapDomain. Finite support and zero low coefficients let Finsupp.mapDomain_comapDomain recover the original string, while injectivity of index addition gives uniqueness.

Pinned Mathlib and D5 were searched before proving. Mathlib provides the Zeckendorf representation and its uniqueness, and D5 already bridges that representation to CanonicalRaw. Neither contains this least-digit three-way decomposition, so the proof combines those checked parts.

This closes only the three-way decomposition lemma in part one of source remark 27.158. The beta homogeneity claim, the renormalization equation, its numerical checks, and the diagnostic conclusions are not asserted.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/LeastDigitDecomposition.canonical_raw_least_digit_decomposition`
- Dependency: [D5/S1/Digit/Raw](../Raw.md)
