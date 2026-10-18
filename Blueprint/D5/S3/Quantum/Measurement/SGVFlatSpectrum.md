# Flat-spectrum probe probabilities

## Abstract

Explicit positive probabilities solve the flat-spectrum system for every copy number.

**Definition 1.1 (The coherent Clebsch–Gordan sum).**

$$\forall tj \in \mathbb{N},\; \forall J \in \mathbb{N},\; \operatorname{S}\left(tj, J\right) = (\operatorname{let} (fz: \mathbb{Z} \to \mathbb{R}):= \operatorname{fun} (x: \mathbb{Z}) \mapsto (\operatorname{Nat.factorial}\left(\operatorname{Int.toNat}\left(x\right)\right): \mathbb{R}); (\operatorname{let} (clebschGordan: \mathbb{N} \to \left(\mathbb{N} \to \left(\mathbb{N} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{R}\right)\right)\right)\right)\right)):= \operatorname{fun} (a: \mathbb{N}) \mapsto \operatorname{fun} (b: \mathbb{N}) \mapsto \operatorname{fun} (c: \mathbb{N}) \mapsto \operatorname{fun} (x: \mathbb{Z}) \mapsto \operatorname{fun} (y: \mathbb{Z}) \mapsto \operatorname{fun} (z: \mathbb{Z}) \mapsto (\operatorname{if} ((z = x + y) \land (((c: \mathbb{Z}) \le (a: \mathbb{Z}) + (b: \mathbb{Z})) \land (((a: \mathbb{Z}) \le (b: \mathbb{Z}) + (c: \mathbb{Z})) \land (((b: \mathbb{Z}) \le (a: \mathbb{Z}) + (c: \mathbb{Z})) \land ((\operatorname{Even}\left((a: \mathbb{Z}) + (b: \mathbb{Z}) + (c: \mathbb{Z})\right)) \land ((\left|x\right| \le (a: \mathbb{Z})) \land ((\left|y\right| \le (b: \mathbb{Z})) \land ((\left|z\right| \le (c: \mathbb{Z})) \land ((\operatorname{Even}\left((a: \mathbb{Z}) + x\right)) \land ((\operatorname{Even}\left((b: \mathbb{Z}) + y\right)) \land (\operatorname{Even}\left((c: \mathbb{Z}) + z\right)))))))))))) \operatorname{then} \sqrt{\frac{\left((c: \mathbb{R}) + 1\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((c: \mathbb{Z}) + (a: \mathbb{Z}) - (b: \mathbb{Z}), 2\right)\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((c: \mathbb{Z}) - (a: \mathbb{Z}) + (b: \mathbb{Z}), 2\right)\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((a: \mathbb{Z}) + (b: \mathbb{Z}) - (c: \mathbb{Z}), 2\right)\right)}{\operatorname{fz}\left(\operatorname{Int.ediv}\left((a: \mathbb{Z}) + (b: \mathbb{Z}) + (c: \mathbb{Z}), 2\right) + 1\right)}} \cdot \sqrt{\operatorname{fz}\left(\operatorname{Int.ediv}\left((c: \mathbb{Z}) + z, 2\right)\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((c: \mathbb{Z}) - z, 2\right)\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((a: \mathbb{Z}) - x, 2\right)\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((a: \mathbb{Z}) + x, 2\right)\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((b: \mathbb{Z}) - y, 2\right)\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((b: \mathbb{Z}) + y, 2\right)\right)} \cdot \sum_{k \in \operatorname{Finset.range}\left(a + b + c + 1\right)} ((\operatorname{if} ((0 \le \operatorname{Int.ediv}\left((a: \mathbb{Z}) + (b: \mathbb{Z}) - (c: \mathbb{Z}), 2\right) - (k: \mathbb{Z})) \land ((0 \le \operatorname{Int.ediv}\left((a: \mathbb{Z}) - x, 2\right) - (k: \mathbb{Z})) \land ((0 \le \operatorname{Int.ediv}\left((b: \mathbb{Z}) + y, 2\right) - (k: \mathbb{Z})) \land ((0 \le \operatorname{Int.ediv}\left((c: \mathbb{Z}) - (b: \mathbb{Z}) + x, 2\right) + (k: \mathbb{Z})) \land (0 \le \operatorname{Int.ediv}\left((c: \mathbb{Z}) - (a: \mathbb{Z}) - y, 2\right) + (k: \mathbb{Z})))))) \operatorname{then} \frac{(-1)^{k}}{\operatorname{fz}\left((k: \mathbb{Z})\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((a: \mathbb{Z}) + (b: \mathbb{Z}) - (c: \mathbb{Z}), 2\right) - (k: \mathbb{Z})\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((a: \mathbb{Z}) - x, 2\right) - (k: \mathbb{Z})\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((b: \mathbb{Z}) + y, 2\right) - (k: \mathbb{Z})\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((c: \mathbb{Z}) - (b: \mathbb{Z}) + x, 2\right) + (k: \mathbb{Z})\right) \cdot \operatorname{fz}\left(\operatorname{Int.ediv}\left((c: \mathbb{Z}) - (a: \mathbb{Z}) - y, 2\right) + (k: \mathbb{Z})\right)} \operatorname{else} 0)) \operatorname{else} 0); \sum_{i \in \operatorname{Finset.range}\left(tj + 1\right)} (\operatorname{clebschGordan}\left(tj, tj, 2 \cdot J, (tj: \mathbb{Z}) - 2 \cdot (i: \mathbb{Z}), 2 \cdot (i: \mathbb{Z}) - (tj: \mathbb{Z}), 0\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/SGVFlatSpectrum.S` (`✓ std3`).

*Citation.* Eddie Schoute, Dmitry Grinko, Yiğit Subaşı, Tyler Volkoff (2024). *Quantum Programmable Reflections*. DOI: [10.48550/arXiv.2411.03648](https://doi.org/10.48550/arXiv.2411.03648). URL: <https://arxiv.org/abs/2411.03648v2>.

*Commentary.*

Equation (183), Section 4.2.1, p. 36, uses the coherent sum of the real Condon–Shortley coefficients. Here tj = 2j and i enumerates m = j − i. The displayed function clebschGordan is Racah's source expression; the Lean owner is D5.S3.Quantum.Decoherence.DampedSpinKernelPositivityRefutation.CG. Equality on J ≤ tj and i ≤ tj is established inside equal_spin_coefficient, including the square-root product and the zero terms outside the owner's shorter sum. In the displayed expression, a = 2j₁, b = 2j₂, c = 2J, x = 2m₁, y = 2m₂ and z = 2M. Its first three arguments are natural numbers; every factorial argument and each division inside fz is an integer. Int.ediv denotes Euclidean integer division; Nat.div denotes natural division. The two square roots and all selection rules are retained. The displayed function fz uses Int.toNat before Nat.factorial, so negative integer arguments map to zero before taking the factorial.

**Definition 1.2 (Conjecture 4.6 as its linear system).**

$$(claim: Prop) = \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{N} \to \mathbb{R},\; (\forall k \in \mathbb{N},\; k \le \operatorname{Nat.div}\left(n, 2\right) \Rightarrow 0 \le \operatorname{q}\left(k\right)) \land ((\sum_{k \in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(n, 2\right) + 1\right)} (\operatorname{q}\left(k\right)) = 1) \land (\forall J \in \mathbb{N},\; J \le n \Rightarrow \left(\operatorname{Nat.mod}\left(J, 2\right) = \operatorname{Nat.mod}\left(n, 2\right) \Rightarrow \frac{2 \cdot (J: \mathbb{R}) + 1}{(\operatorname{Nat.choose}\left(n + 2, 2\right): \mathbb{R})} = \sum_{k \in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(n, 2\right) + 1\right)} ((\operatorname{if} (J \le n - 2 \cdot k) \operatorname{then} \frac{\operatorname{q}\left(k\right)}{((n - 2 \cdot k: \mathbb{N}): \mathbb{R}) + 1} \cdot \operatorname{S}\left(n - 2 \cdot k, J\right)^{2} \operatorname{else} 0))\right)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/SGVFlatSpectrum.claim` (`✓ std3`).

*Citation.* Eddie Schoute, Dmitry Grinko, Yiğit Subaşı, Tyler Volkoff (2024). *Quantum Programmable Reflections*. DOI: [10.48550/arXiv.2411.03648](https://doi.org/10.48550/arXiv.2411.03648). URL: <https://arxiv.org/abs/2411.03648v2>.

*Commentary.*

Section 4.2.1, p. 36: “Conjecture 4.6. The probabilities q_j for j ∈ {(n mod 2)/2, …, n/2} in Eq. (181), which define the probe state Φ_n, could be chosen such that ‖|v_J⟩‖² = 1/binom(n+2, 2) (182) for every J ∈ {(n mod 2), …, n − 2, n}.” The displayed predicate is equation (183). Its k corresponds to j = n/2 − k, and the finite range has Nat.div n 2 + 1 elements. Probabilities are nonnegative and sum to one. Nat.mod selects the allowed parity. Nat subtraction is truncated at zero; the conditional excludes terms with 2j < J. The real coefficient is squared. Equation (181) identifies this system with equation (182) after division by 2J + 1.

**Definition 1.3 (The explicit probabilities).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{explicitQ}\left(n, k\right) = \frac{((n - 2 \cdot k + 1: \mathbb{N}): \mathbb{R})^{2} \cdot (\operatorname{Nat.choose}\left(2 \cdot n - 2 \cdot k + 1, n - k\right): \mathbb{R}) \cdot (\operatorname{Nat.choose}\left(2 \cdot k, k\right): \mathbb{R})}{(4: \mathbb{R})^{n} \cdot (\operatorname{Nat.choose}\left(n + 2, 2\right): \mathbb{R})}$$

*Formalization.* `D5/S3/Quantum/Measurement/SGVFlatSpectrum.explicitQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eddie Schoute, Dmitry Grinko, Yiğit Subaşı, Tyler Volkoff (2024). *Quantum Programmable Reflections*. DOI: [10.48550/arXiv.2411.03648](https://doi.org/10.48550/arXiv.2411.03648). URL: <https://arxiv.org/abs/2411.03648v2>.

*Commentary.*

For k ≤ Nat.div n 2 this expression is strictly positive. Every subtraction in a Nat.choose argument and in the first squared factor is natural subtraction. The quotient and the square are real operations. These probabilities sum to one and solve the coherent system for every n ≥ 1.

**Theorem 1.4 (Existence for every copy number).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{N} \to \mathbb{R},\; (\forall k \in \mathbb{N},\; k \le \operatorname{Nat.div}\left(n, 2\right) \Rightarrow 0 \le \operatorname{q}\left(k\right)) \land ((\sum_{k \in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(n, 2\right) + 1\right)} (\operatorname{q}\left(k\right)) = 1) \land (\forall J \in \mathbb{N},\; J \le n \Rightarrow \left(\operatorname{Nat.mod}\left(J, 2\right) = \operatorname{Nat.mod}\left(n, 2\right) \Rightarrow \frac{2 \cdot (J: \mathbb{R}) + 1}{(\operatorname{Nat.choose}\left(n + 2, 2\right): \mathbb{R})} = \sum_{k \in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(n, 2\right) + 1\right)} ((\operatorname{if} (J \le n - 2 \cdot k) \operatorname{then} \frac{\operatorname{q}\left(k\right)}{((n - 2 \cdot k: \mathbb{N}): \mathbb{R}) + 1} \cdot \operatorname{S}\left(n - 2 \cdot k, J\right)^{2} \operatorname{else} 0))\right)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/SGVFlatSpectrum.result` (`✓ std3`). ∎

*Resolves.* `Problems/schoute-grinko-subasi-volkoff-2024-flat-spectrum` (proved) by `D5/S3/Quantum/Measurement/SGVFlatSpectrum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"schoute-grinko-subasi-volkoff-2024-flat-spectrum","declaration_gid":"D5/S3/Quantum/Measurement/SGVFlatSpectrum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eddie Schoute, Dmitry Grinko, Yiğit Subaşı, Tyler Volkoff (2024). *Quantum Programmable Reflections*. DOI: [10.48550/arXiv.2411.03648](https://doi.org/10.48550/arXiv.2411.03648). URL: <https://arxiv.org/abs/2411.03648v2>.

*Commentary.*

The probabilities explicitQ n give the required distribution. Extracting the common square root from Racah's formula reduces the coherent sum to a rational binomial convolution. Its generating series evaluates the kernel. Two factorial sum identities, proved by telescoping and induction, give normalization and every equation of the system. The proof uses the original coherent sums directly and does not require a polynomial connection identity. Uniqueness is not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/SGVFlatSpectrum.S`
- Truth anchor: `D5/S3/Quantum/Measurement/SGVFlatSpectrum.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/SGVFlatSpectrum.explicitQ`
- Truth anchor: `D5/S3/Quantum/Measurement/SGVFlatSpectrum.result`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah](../Algebra/ZeitlinSixJ/Racah.md)
- Dependency: [D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation](../Decoherence/DampedSpinKernelPositivityRefutation.md)
- Dependency: [D5/S3/Zeros/Convolution/AlternatingFactorialSum](../../Zeros/Convolution/AlternatingFactorialSum.md)
