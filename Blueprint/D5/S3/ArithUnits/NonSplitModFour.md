# A Non-Split Quotient of Finite Cyclic Groups

## Abstract

The additive quotient from ZMod 4 to ZMod 2 has no additive section.

**Theorem 1.1 (The mod-four quotient has no additive section).**

$$\neg \exists s: \operatorname{AddHom}(\operatorname{ZMod}(2), \operatorname{ZMod}(4)),\ q \circ s = \operatorname{id}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/NonSplitModFour.mod_four_quotient_has_no_additive_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be the canonical additive quotient map from ZMod 4 to ZMod 2. There is no additive homomorphism s from ZMod 2 to ZMod 4 for which q composed with s is the identity. Equivalently, this quotient of finite cyclic additive groups does not split.

If such a section existed, additivity would force twice s(1) to vanish because twice 1 already vanishes in ZMod 2. Every element of ZMod 4 annihilated by two reduces to zero in ZMod 2, whereas the right-inverse law requires the reduction of s(1) to be one. These conclusions contradict each other.

This deposit closes only the nonsplitting ZMod 4 quotient clause of residual appendix E.136. It does not assert the surrounding projection, quantum-extension, Stinespring, entropy-tax, or duality claims from the same source atom.

Repository searches found no D5 declaration with this statement. Pinned Mathlib and the local smart-search script supplied ZMod.castHom and ZMod.lift, but no complete nonsplitting theorem. The configured GitHub API credential was expired, and its code-search request returned API key is failed; this failed request is not counted as a no-hit search. A NyxID-proxied Tavily search over GitHub, Loogle, and LeanSearch indexes found the quotient-map infrastructure but no exact theorem. The Lean proof therefore uses Mathlib's canonical quotient map and checks only the finite two-torsion implication locally.

## References

- Truth anchor: `D5/S3/ArithUnits/NonSplitModFour.mod_four_quotient_has_no_additive_section`
