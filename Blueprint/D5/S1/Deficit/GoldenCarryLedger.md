# The Two-Face Golden Carry Ledger

## Abstract

The adjacency and doubling carries preserve value on both golden faces.

**Theorem 1.1 (The golden carry rewrites preserve both faces).**

$$\forall k\in\mathbb{N},\quad\forall x\in\{\varphi, \psi\},\quad(x^{k+1}+x^{k+2}=x^{k+3} \land 2x^{k+2}=x^{k+3}+x^k)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/GoldenCarryLedger.carry_rewrite_face_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural index k, the adjacency carry x^{k+1}+x^{k+2}=x^{k+3} and the doubling carry 2x^{k+2}=x^{k+3}+x^k preserve value when x is either the expanding golden face φ=goldenRatio or the conjugate golden face ψ=goldenConj. Thus each internal rewrite has zero deficit on both faces simultaneously.

The proof first establishes both carry identities for an arbitrary real root of x²=x+1. It then instantiates those parametric identities with the two library equations goldenRatio_sq and goldenConj_sq, producing the paired two-face ledger statement.

## References

- Truth anchor: `D5/S1/Deficit/GoldenCarryLedger.carry_rewrite_face_invariant`
