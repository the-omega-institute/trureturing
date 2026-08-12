# Finite Binary Kraft Inequality

## Abstract

Every finite uniquely decodable binary code has Kraft sum at most one.

**Theorem 1.1 (Finite binary Kraft inequality).**

$$\forall S, uniquelyDecodable(S) \Rightarrow kraftSum(S) \le 1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/KraftInequality.finite_binary_kraft_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the finite-code partial closure of the source's fixed-input prefix-free coding fact. Pinned mathlib's InformationTheory.kraft_mcmillan_inequality supplies the counting argument, so the Lean declaration is a thin wrapper and does not reprove Kraft-McMillan.

The source also discusses an infinite halting set and the bridge from prefix freedom to unique decodability. Those stronger steps are outside this deposited partial closure.

## References

- Truth anchor: `D5/S0/Computability/KraftInequality.finite_binary_kraft_inequality`
