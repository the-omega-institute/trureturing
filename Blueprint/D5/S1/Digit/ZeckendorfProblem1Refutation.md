# Moradi--Rampersad--Shallit Problem 1: exact partial MSD model

## Abstract

Literal refutation of the complete Fibonacci-DFAO Problem 1 statement.

**Definition 1.1 (Problem 1 as full eventual uniform linear bounds).**

Lean statement: `D5/S1/Digit/ZeckendorfProblem1Refutation.Problem1`

*Formalization.* `D5/S1/Digit/ZeckendorfProblem1Refutation.Problem1` (`✓ std3`).

*Citation.* Delaram Moradi; Narad Rampersad; Jeffrey Shallit (2026). *Complexity of Linear Subsequences of Fibonacci-Automatic Sequences*. DOI: [10.48550/arXiv.2603.21645](https://doi.org/10.48550/arXiv.2603.21645). URL: <https://arxiv.org/abs/2603.21645v1>.

*Commentary.*

The exact Lean definition is `Problem1 : Prop := ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c → a * c ≤ minimumStates c ∧ (minimumStates c : ℝ) ≤ b * c`. Here minimumStates c is the attained minimum over reachable finite partial MSD Fibonacci machines for shift c. A machine is correct for every valid padded no-adjacent-ones word, starts at a counted zero-loop state, omits a sink, and is undefined on invalid words. The empty word and every all-zero word output t(c), where t(n) is the parity of the occupied canonical Fibonacci digits.

**Theorem 1.2 (Literal negation of Problem 1).**

Lean statement: `D5/S1/Digit/ZeckendorfProblem1Refutation.problem1_refuted`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfProblem1Refutation.problem1_refuted` (`✓ std3`). ∎

*Resolves.* `Problems/moradi-rampersad-shallit-2026-fibonacci-shift-linear-refutation` (refuted) by `D5/S1/Digit/ZeckendorfProblem1Refutation.problem1_refuted`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"moradi-rampersad-shallit-2026-fibonacci-shift-linear-refutation","declaration_gid":"D5/S1/Digit/ZeckendorfProblem1Refutation.problem1_refuted","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Delaram Moradi; Narad Rampersad; Jeffrey Shallit (2026). *Complexity of Linear Subsequences of Fibonacci-Automatic Sequences*. DOI: [10.48550/arXiv.2603.21645](https://doi.org/10.48550/arXiv.2603.21645). URL: <https://arxiv.org/abs/2603.21645v1>.

*Commentary.*

The complete theorem statement is `theorem problem1_refuted : ¬ Problem1`, namely ¬ (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c → a * c ≤ minimumStates c ∧ (minimumStates c : ℝ) ≤ b * c). It uses the full source machine class and all-word Option semantics. Finite residual realization supplies an ordinary reachable partial machine with the counted initial zero-loop; contextual replacement and normalized state covers give an unbounded Fibonacci family with a sublinear state-count upper bound. For H ≥ 14, put φ = (1 + √5)/2, δ = 1 − φ^(−14), and C = 128(2φ + 1). The proof bounds minimumStates(F_H) / F_H by C δ^floor(H/14), with 0 ≤ δ < 1. The positive shifts F_H are unbounded. The ratio tends to zero along this family, which refutes the original positive uniform lower bound for all sufficiently large c.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfProblem1Refutation.Problem1`
- Truth anchor: `D5/S1/Digit/ZeckendorfProblem1Refutation.problem1_refuted`
- Dependency: [D5/S1/Digit/ZeckendorfAvoidanceCount](ZeckendorfAvoidanceCount.md)
- Dependency: [D5/S1/Digit/ZeckendorfCarryBarrier](ZeckendorfCarryBarrier.md)
- Dependency: [D5/S1/Digit/ZeckendorfContextualReplacement](ZeckendorfContextualReplacement.md)
- Dependency: [D5/S1/Digit/ZeckendorfRawWindow](ZeckendorfRawWindow.md)
- Dependency: [D5/S1/Digit/ZeckendorfResidualCover](ZeckendorfResidualCover.md)
- Dependency: [D5/S1/Digit/ZeckendorfResidualMachine](ZeckendorfResidualMachine.md)
- Dependency: [D5/S1/Digit/ZeckendorfResidualNormalForm](ZeckendorfResidualNormalForm.md)
