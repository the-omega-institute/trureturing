# Two-tail shadowing for quasi-finite type

## Abstract

Two-tail shadowing for quasi-finite type

Jonathan Meddaugh and Elyssa Stephens ask for a shadowing characterization of quasi-finite type in Question 5.4 of arXiv:2509.04312v1. Definition 3.5 permits a replacement of exactly the common bridge length between two exterior contexts.

**Theorem 1.1 (Exact-length replacement and gluing of infinite tails).**

Lean statement: `D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_exactTailSplicing`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_exactTailSplicing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a two-sided finite-alphabet subshift, quasi-finite type is equivalent to the following condition. When two points agree on a sufficiently large fixed centered window, a third point agrees with the entire past tail of the first and the entire future tail of the second outside a fixed central interval. Both sides use the original time coordinate.

For the forward implication, use exact-length replacement on every pair of finite exterior contexts. The sets of points matching those contexts are closed, nonempty and nested. Their intersection gives one point for the infinite tails. Conversely, align the common bridge of two legal words so it contains the fixed central interval and the required agreement window. The point tracing the tails preserves the exterior contexts at their original positions. Its intervening coordinates give a replacement of the prescribed length.

**Theorem 1.2 (Shadowing both tails at the original times).**

Lean statement: `D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_twoTailShadowing`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_twoTailShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate criterion is equivalent to uniform two-tail shadowing for every compatible metric. Choose the input tolerance and cutoff for the requested accuracy before choosing the nearby points. A single orbit traces both infinite tails at the original times. The interval omitted from tracing has a uniformly bounded length.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_exactTailSplicing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_twoTailShadowing`
- Dependency: [D5/S1/Dynamics/Shadowing/LanguageCharacterization](LanguageCharacterization.md)
