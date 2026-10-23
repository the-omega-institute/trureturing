# DiophantineExponentCriterion

## Abstract

Episturmian words: DiophantineExponentCriterion.

**Theorem 1.1 (result).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (Lang\left(t\right) = Lang\left((cDelta\left(Delta\right))\right)) \Rightarrow ((\neg (\exists N \in (Nat),\; \exists p \in (Nat),\; (0 < p) \land (\forall n \in (Nat),\; (N \le n) \Rightarrow (t\left((n+p)\right) = t\left(n\right))))) \Rightarrow (((dio\left(t\right) < \infty) \Leftrightarrow (BoundedPQ\left(Delta\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DiophantineExponentCriterion.result` (`✓ std3`). ∎

*Resolves.* `Problems/peltomaki-2024-episturmian-diophantine-exponent` (proved) by `D5/S1/Words/Episturmian/DiophantineExponentCriterion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"peltomaki-2024-episturmian-diophantine-exponent","declaration_gid":"D5/S1/Words/Episturmian/DiophantineExponentCriterion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Let $\mathbf{t}$ be an aperiodic episturmian word. Then $dio\left(\mathbf{t}\right) < \infty$ if and only if $\mathbf{t}$ has bounded partial quotients.

Peltomäki, Conjecture 8.4, Section 8.

The alphabet is Fin d, letters are indexed from zero, and equality of Lang expresses equality of factor sets.

## References

- Truth anchor: `D5/S1/Words/Episturmian/DiophantineExponentCriterion.result`
- Dependency: [D5/S1/Words/Episturmian/BoundedPowers](BoundedPowers.md)
