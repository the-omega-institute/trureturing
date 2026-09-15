# Ordowski's Immediate-Successor Weak Pseudoprime Conjecture

## Abstract

Ordowski's immediate-successor weak-pseudoprime condition holds exactly at odd composite successors.

**Theorem 1.1 (Odd composite successors are exactly the qualifying successors).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((((1 < n + 1) \land ((\neg Prime\left(n + 1\right)) \land (n^{n + 1} \bmod \left(n + 1\right) = n \bmod \left(n + 1\right)))) \Leftrightarrow ((\neg Prime\left(n + 1\right)) \land ((Odd\left(n + 1\right)) \land (1 < n + 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a239293-ordowski-immediate-successor-weak-pseudoprime` (proved) by `D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a239293-ordowski-immediate-successor-weak-pseudoprime","declaration_gid":"D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert Ferreol; Thomas Ordowski (2018). *OEIS A239293, Smallest composite c > n such that n^c == n (mod c)*. URL: <https://oeis.org/A239293>.

*Commentary.*

For every natural n at least one, the composite successor n+1 satisfies the weak-pseudoprime congruence exactly when n+1 is odd. Since n+1 is the immediate successor of n, qualification at this modulus is already least among qualifying composites greater than n. Modulo n+1, the residue of n is minus one, so its power is classified by the parity of n+1. An even qualifying successor would make minus one equal to one; compositeness excludes the only boundary modulus two. The underlying casts, parity powers, and residue facts are pinned Mathlib material.

## References

- Truth anchor: `D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime.result`
