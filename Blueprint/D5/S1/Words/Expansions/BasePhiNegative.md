# Negative Base-Phi Prefix Interfaces

## Abstract

Negative base-phi prefixes have canonical local constraints and Lucas-gap sequence interfaces.

**Theorem 1.1 (Positive gap letters make each trident component strictly increasing).**

$$a>0 \land b>0 \Rightarrow \operatorname{StrictMono}(V_X(a,b,r))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegative.gap_sequence_strict_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three sequence families accumulate one of two integer gaps at every step. When both gaps are positive, each next value is larger, independently of the chosen Sturmian family.

The module also proves that Lucas parameters are positive, that adjacent negative digits cannot both be true, and hence that any prefix containing 11 is not admissible. The one-digit prefix occurrence sets form a disjoint cover of expansions reaching negative depth one.

These interface theorems do not prove the conjectural Lucas formulas for the one-digit prefixes. That step still requires a formal bridge from canonical Zeckendorf digits to the two-sided base-phi expansion.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegative.gap_sequence_strict_mono`
- Dependency: [D5/S0/Carrier/Units](../../../S0/Carrier/Units.md)
- Dependency: [D5/S0/Conventions/WDigits](../../../S0/Conventions/WDigits.md)
