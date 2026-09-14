# Zumkeller's Binary Gaussian Evaluation

## Abstract

A vanishing binary digit polynomial at the Gaussian unit has an argument divisible by five.

**Definition 1.1 (The binary Gaussian evaluation).**

$$z\left(0\right) = 0 \land (\forall b \in Bool,\; \forall n \in Nat,\; z\left(bit\left(b, n\right)\right) = if\left(b, 1, 0\right) + \langle0, 1\rangle \cdot z\left(n\right))$$

*Formalization.* `D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.z` (`✓ std3`).

*Citation.* Reinhard Zumkeller (2007). *OEIS A131853, Numbers m such that z(m)=(0,0) with z as defined in A131851*. URL: <https://oeis.org/A131853>.

*Commentary.*

The definition is Nat.binaryRec 0 (fun b _ w => (if b then 1 else 0) + ⟨0, 1⟩ * w). Here bit b n = 2n + (if b then 1 else 0), so the equations are exactly the OEIS A131851 recursion for the binary digit polynomial evaluated at the Gaussian imaginary unit.

**Theorem 1.2 (Zumkeller's divisibility conjecture).**

$$\forall m \in Nat,\; z\left(m\right) = 0 \Rightarrow 5 \mid m$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.zumkeller_a131853` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a131853-binary-gaussian-evaluation-zero-multiple-of-five` (proved) by `D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.zumkeller_a131853`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a131853-binary-gaussian-evaluation-zero-multiple-of-five","declaration_gid":"D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.zumkeller_a131853","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Binary induction proves m ≡ Re z(m) + 2·Im z(m) (mod 5). The identity uses the fact that the Gaussian unit behaves as 2 modulo 5 because 2 squared is congruent to minus one. Therefore z(m) = 0 forces m to be divisible by five, including the case m = 0.

## References

- Truth anchor: `D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.z`
- Truth anchor: `D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.zumkeller_a131853`
