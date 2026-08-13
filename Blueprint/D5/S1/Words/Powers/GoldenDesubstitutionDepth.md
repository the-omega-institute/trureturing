# Golden Desubstitution Depth

## Abstract

Measure golden desubstitution paths exactly and decode the resulting terminal digits.

**Theorem 1.1 (Exact desubstitution path length).**

$$\forall n m r\in \mathbb{N},\ \left(\exists xs, length(xs)=r \land \operatorname{IsChain}(\operatorname{desubStep} n, xs) \land \operatorname{getLast}(n, xs)=m\right) \iff \left(m\neq0 \lor r=0\right) \land \operatorname{wdigits}(n)=\operatorname{map}(k \mapsto k+r, \operatorname{wdigits}(m))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionDepth.golden_desubstitution_exact_length_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero endpoint admits exactly the number of steps recorded by the uniform Zeckendorf shift; zero is permitted only at depth zero.

**Theorem 1.2 (Normal form is the closed shifted-digit decode).**

$$\forall n\in \mathbb{N},\ \operatorname{nf}(\operatorname{desubStep}, \operatorname{desubStepTermination}, \operatorname{desubStepLocalConfluence}, n)=\operatorname{decode}(\operatorname{map}(k \mapsto k-shift, \operatorname{wdigits}(n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionDepth.golden_desubstitution_nf_eq_wdigits_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique terminal is obtained by shifting every occupied Fibonacci index down until the least digit reaches its floor, with zero handled separately.

## References

- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionDepth.golden_desubstitution_exact_length_iff`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionDepth.golden_desubstitution_nf_eq_wdigits_decode`
- Dependency: [D5/S0/Rewriting/NormalFormFunction](../../../S0/Rewriting/NormalFormFunction.md)
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf](GoldenDesubstitutionZeckendorf.md)
