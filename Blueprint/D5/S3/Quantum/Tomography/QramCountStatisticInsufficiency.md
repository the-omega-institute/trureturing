# Insufficiency of the plus-count statistic

## Abstract

Two queries to a fixed four-address memory contain discrimination information beyond the plus count.

**Definition 1.1 (The weight of a Boolean memory).**

$$\forall (n: \mathbb{N}), (\forall (f: (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \to (\operatorname{Bool})), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.weight}\left(f\right): \mathbb{N}) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (x: \operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \mapsto (f\left(x\right) = \operatorname{Bool.true}), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right))\right))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.weight` (`✓ std3`).

*Citation.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

The weight of f is the number of addresses at which f is true. This is the Hamming weight in bias_class_discrimination.tex, lines 244–250. Addresses are indexed by Fin (2^n), and the definition includes n = 0.

**Definition 1.2 (An exact-weight class).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.weightClass}\left(n, m\right): \operatorname{Finset}\left(((\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \to (\operatorname{Bool}))\right)) = \operatorname{Finset.filter}\left(\lambda (f: (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \to (\operatorname{Bool})) \mapsto (\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.weight}\left(f\right) = m), (\operatorname{Finset.univ}: \operatorname{Finset}\left(((\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \to (\operatorname{Bool}))\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.weightClass` (`✓ std3`).

*Citation.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

The class consists of all Boolean memories on 2^n addresses with weight m, as in bias_class_discrimination.tex, lines 244–250. The finite set is empty when m exceeds 2^n.

**Definition 1.3 (The phase address state).**

$$\forall (n: \mathbb{N}), (\forall (f: (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \to (\operatorname{Bool})), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.addressState}\left(n, f\right): (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \to (\mathbb{C})) = \lambda (x: \operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \mapsto (\frac{(-1: \mathbb{C})^{\operatorname{Bool.toNat}\left(f\left(x\right)\right)}}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left((2: \mathbb{R})^{n}\right)\right)})))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.addressState` (`✓ std3`).

*Citation.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

The coordinate at x is the sign determined by f(x), divided by the square root of the number of addresses. This is the address state in bias_class_discrimination.tex, lines 169–174. Bool.toNat converts false and true to zero and one. The power 2^n inside Real.sqrt is real; Complex.ofReal includes that real square root into the complex scalars.

**Definition 1.4 (The all-plus address state).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.plusState}\left(n\right): (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)) \to (\mathbb{C})) = \operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.addressState}\left(n, \operatorname{Function.const}\left(\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right), \operatorname{Bool.false}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.plusState` (`✓ std3`).

*Citation.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

The identically false memory gives the uniform all-plus vector. The source defines this vector in bias_class_discrimination.tex, line 165, and relates it to the address state in line 174. Function.const specifies the constant Boolean memory.

**Definition 1.5 (Several copies of one sampled memory).**

$$\forall (n: \mathbb{N}), (\forall (t: \mathbb{N}), (\forall (m: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.copyState}\left(n, t, m\right): \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right)) = (\frac{(1: \mathbb{C})}{(\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.weightClass}\left(n, m\right)\right)\right): \mathbb{C})}) \cdot (\sum_{f \in \operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.weightClass}\left(n, m\right)} (\operatorname{Matrix.of}\left(\lambda (x: (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right))) \mapsto (\lambda (y: (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right))) \mapsto (\prod_{i: \operatorname{Fin}\left((t)\right)} ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.addressState}\left(n, f, x\left(i\right)\right)) \cdot (\operatorname{star}\left(\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.addressState}\left(n, f, y\left(i\right)\right)\right)))))\right))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.copyState` (`✓ std3`).

*Citation.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

Average the t-fold product of the address-state projectors over the uniform exact-weight class. The same f occurs in every register: the memory is sampled once and held fixed, as in bias_class_discrimination.tex, lines 255–256 and 395–400. A row or column is a function from Fin t to Fin (2^n). The natural class cardinality is cast to a complex scalar before division. The formula is defined for all natural n, t and m; an empty class gives the zero matrix.

**Definition 1.6 (The single-register plus projector).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.plusProj}\left(n\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right), \operatorname{Fin}\left(((2: \mathbb{N})^{n})\right), \mathbb{C}\right)) = \operatorname{Matrix.vecMulVec}\left(\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.plusState}\left(n\right), \operatorname{star}\left(\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.plusState}\left(n\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.plusProj` (`✓ std3`).

*Citation.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

The outer product of the all-plus vector with its conjugate is the plus projector. It is the first effect of the two-outcome measurement in bias_class_discrimination.tex, line 405. The star on a vector acts coordinatewise.

**Definition 1.7 (The projector for an exact plus count).**

$$\forall (n: \mathbb{N}), (\forall (t: \mathbb{N}), (\forall (k: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.countProj}\left(n, t, k\right): \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right)) = \sum_{s \in \operatorname{Finset.powersetCard}\left(k, (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left((t)\right))\right))\right)} (\operatorname{Matrix.of}\left(\lambda (x: (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right))) \mapsto (\lambda (y: (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right))) \mapsto (\prod_{i: \operatorname{Fin}\left((t)\right)} ((\operatorname{ite}\left(i \in s, \operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.plusProj}\left(n\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right), \operatorname{Fin}\left(((2: \mathbb{N})^{n})\right), \mathbb{C}\right)) - \operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.plusProj}\left(n\right)\right))\left(x\left(i\right), y\left(i\right)\right))))\right)))))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.countProj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

For each k-element subset s of the registers, use the plus projector at sites in s and its complementary projector at the remaining sites, then sum these tensor-product effects. This constructs the exact-count effect for the measurement of bias_class_discrimination.tex, lines 404–415. The matrix entries are products over the registers. For k greater than t the sum is empty.

**Definition 1.8 (Equal-prior success of a binary test).**

$$\forall (n: \mathbb{N}), (\forall (t: \mathbb{N}), (\forall (m_{0}: \mathbb{N}), (\forall (m_{1}: \mathbb{N}), (\forall (e: \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.successProb}\left(n, t, m_{0}, m_{1}, e\right): \mathbb{R}) = ((\frac{1}{2}: \mathbb{R})) \cdot (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.copyState}\left(n, t, m_{0}\right)) \cdot (e)\right)\right)) + ((\frac{1}{2}: \mathbb{R})) \cdot (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.copyState}\left(n, t, m_{1}\right)) \cdot ((1: \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right)) - e)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.successProb` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

The effect e accepts weight m₀ and the complementary effect accepts weight m₁. Their Born readouts, each weighted by one half, give the equal-prior success probability. The equal-prior discrimination setting is that of bias_class_discrimination.tex, lines 327–345; this formula applies it to the t-copy states. Taking real parts makes the expression a real number for arbitrary e; its probability interpretation requires e and 1 − e to be positive semidefinite and both weights to lie between zero and 2^n.

**Definition 1.9 (A deterministic count decision).**

$$\forall (n: \mathbb{N}), (\forall (t: \mathbb{N}), (\forall (g: (\operatorname{Fin}\left((t + 1)\right)) \to (\operatorname{Bool})), ((\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.countTest}\left(n, t, g\right): \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right)) = \sum_{k: \operatorname{Fin}\left((t + 1)\right)} (\operatorname{ite}\left(g\left(k\right) = \operatorname{Bool.true}, \operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.countProj}\left(n, t, (\operatorname{Fin.val}\left(k\right): \mathbb{N})\right), (0: \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.countTest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

A Boolean rule g accepts the first weight exactly for those counts at which it is true. Sum the corresponding exact-count projectors over k : Fin (t + 1). Fin.val explicitly converts this finite index to the natural argument of countProj.

**Definition 1.10 (Sufficiency for every equal-prior test).**

$$(\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.claim}: \operatorname{Prop}) = (\forall (n: \mathbb{N}), ((1 \le n) \to (\forall (t: \mathbb{N}), ((1 \le t) \to (\forall (m_{0}: \mathbb{N}), (\forall (m_{1}: \mathbb{N}), ((m_{0} \le (2: \mathbb{N})^{n}) \to ((m_{1} \le (2: \mathbb{N})^{n}) \to (\forall (e: \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(e\right)) \to ((\operatorname{Matrix.PosSemidef}\left((1: \operatorname{Matrix}\left((\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), (\operatorname{Fin}\left((t)\right)) \to (\operatorname{Fin}\left(((2: \mathbb{N})^{n})\right)), \mathbb{C}\right)) - e\right)) \to (\exists (g: (\operatorname{Fin}\left((t + 1)\right)) \to (\operatorname{Bool})), (\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.successProb}\left(n, t, m_{0}, m_{1}, e\right) \le \operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.successProb}\left(n, t, m_{0}, m_{1}, \operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.countTest}\left(n, t, g\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

For every positive n and t, every pair of admissible weights and every effect e with both e and 1 − e positive semidefinite, ask whether a deterministic count rule achieves at least the success of e. This is an equal-prior reading of the count-sufficiency question in bias_class_discrimination.tex, lines 454–457.

**Theorem 1.11 (Four addresses and two copies suffice for a strict gap).**

$$\neg (\operatorname{D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.result` (`✓ std3`). ∎

*Resolves.* `Problems/bohac-2025-qram-count-statistic-insufficiency` (refuted) by `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bohac-2025-qram-count-statistic-insufficiency","declaration_gid":"D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Leonardo Bohac (2025). *Bias-Class Discrimination of Universal QRAM Boolean Memories*. DOI: [10.48550/arXiv.2512.17503](https://doi.org/10.48550/arXiv.2512.17503). URL: <https://arxiv.org/abs/2512.17503v1>.

*Commentary.*

Take n = 2, t = 2, m₀ = 1 and m₁ = 2. In coordinate order 0, 1, 2, 3, let h₀ = (1,1,1,1)/2, h₁ = (1,−1,1,−1)/2, h₂ = (1,1,−1,−1)/2 and h₃ = (1,−1,−1,1)/2. Their inner products are one for equal indices and zero otherwise, and h₀ is plusState 2. Put vᵧ𝓏(x) = hᵧ(x(0))h𝓏(x(1)), R = Σᵧ₌₁³ vᵧᵧvᵧᵧ† and E = 1 − R. Thus E accepts weight one unless the two Walsh outcomes are equal and nonzero.

The weight-one class consists of the four memories with one true entry; the weight-two class consists of the six memories with two true entries. Inner products of product vectors factor into products of single-register inner products. For vectors u and v, trace((uu†)(vv†)) = (u†v)(v†u). Each weight-one address state has squared overlap 1/4 with every hᵧ. Factoring the two-register overlaps and averaging over the four memories therefore gives trace(copyState 2 2 1 · vᵧ𝓏vᵧ𝓏†) = 1/16 for every y and z.

For weight two, the supports {0,1}, {0,2}, {0,3}, {1,2}, {1,3} and {2,3} give address states −h₂, −h₁, −h₃, h₃, h₁ and h₂, respectively. The signs cancel in the two-copy projectors, giving copyState 2 2 2 = R/3. The product vectors vᵧ𝓏 are orthonormal, so R† = R and R² = R. Consequently E†E = E and R†R = R; each is a Gram matrix and hence positive semidefinite. Thus both E and 1 − E are positive semidefinite.

Every four-address phase state has norm one. Factoring the tensor inner products and averaging gives trace(copyState 2 2 1) = 1. The three orthonormal summands of R give trace(R) = 3, so trace(copyState 2 2 2) = 1 as well. The flat weight-one outcome law gives trace(copyState 2 2 1 · R) = 3/16, whereas copyState 2 2 2 = R/3 and R² = R give trace(copyState 2 2 2 · R) = 1. Substituting E = 1 − R into successProb yields (1/2)(1 − 3/16) + (1/2) = 29/32.

The weight-two Walsh outcome law is 1/3 for y = z ≠ 0 and zero otherwise. Since 1 − plusProj 2 is the sum of the three nonzero Walsh projectors, countProj 2 2 k is the sum of the projectors vᵧ𝓏vᵧ𝓏† whose pair of labels contains exactly k zeros. Summing the two outcome laws gives count probabilities (9/16, 3/8, 1/16) for weight one and (1, 0, 0) for weight two, in count order 0, 1, 2. Expanding successProb for countTest and evaluating the eight choices of g(0), g(1), g(2) bounds every deterministic count rule by 23/32.

If claim held, its specialization to these parameters and the valid effect E would supply a count rule g with 29/32 ≤ successProb 2 2 1 2 (countTest 2 2 g). The bound 23/32 contradicts this inequality. Hence claim is false. This strict gap establishes insufficiency of the plus count; it does not determine the optimal collective success or the error exponent asked for in the same remark.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.addressState`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.claim`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.copyState`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.countProj`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.countTest`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.plusProj`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.plusState`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.result`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.successProb`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.weight`
- Truth anchor: `D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.weightClass`
- Dependency: [D5/S3/Observer/BornReduction](../../Observer/BornReduction.md)
- Dependency: [D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation](../Thermal/MetrotropyHalfErgotropyRefutation.md)
