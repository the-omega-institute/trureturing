# Unambiguous discrimination without repeated labels

## Abstract

Independent local measurements attain the global unambiguous optimum for sequences of distinct equal-overlap states.

**Definition 1.1 (Sequences of distinct labels).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (\operatorname{Label}\left(N, k\right) = \{(x: (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right))) // \operatorname{Function.Injective}\left(x\right)\}))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.Label` (`✓ std3`).

*Citation.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

Label N k is the type of injective functions from the k positions to the N labels. An element x consists of its function x.val and a proof of injectivity. These are the ordered sequences in revised_02.tex, lines 828–835.

**Definition 1.2 (Normalized states with equal real overlap).**

$$\forall (N: \mathbb{N}), (\forall (\psi: (\operatorname{Fin}\left(N\right)) \to ((\operatorname{Fin}\left(N\right)) \to (\mathbb{C}))), (\forall (s: \mathbb{R}), ((\operatorname{IsEquiangular}\left(\psi, s\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(N\right)), (\operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(i\right)\right), \psi\left(i\right)\right) = (1: \mathbb{C}))) \land (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), ((i \ne j) \Rightarrow (\operatorname{dotProduct}\left(\operatorname{star}\left(\psi\left(i\right)\right), \psi\left(j\right)\right) = (\operatorname{Complex.ofReal}\left(s\right): \mathbb{C})))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.IsEquiangular` (`✓ std3`).

*Citation.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

Each vector ψ i has squared norm one, and every inner product between different vectors equals the real number s included in the complex numbers. The predicate itself places no restriction on s; the theorem assumes 0 < s < 1. This is the equal-overlap family in revised_02.tex, lines 822–826.

**Definition 1.3 (Product-state coordinates).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (\psi: (\operatorname{Fin}\left(N\right)) \to ((\operatorname{Fin}\left(N\right)) \to (\mathbb{C}))), (\forall (x: \operatorname{Label}\left(N, k\right)), (\forall (a: (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right))), (\operatorname{productState}\left(\psi, x, a\right) = \prod_{j: \operatorname{Fin}\left(k\right)} (\psi\left(\operatorname{Subtype.val}\left(x\right)\left(j\right), a\left(j\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.productState` (`✓ std3`).

*Citation.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

The coordinate a of the product state labelled by x is the product, over positions j, of the coordinate a j of ψ (x.val j). Subtype.val explicitly extracts the function from the injective label. This expresses the tensor products in revised_02.tex, lines 828–832, in the coordinate basis.

**Definition 1.4 (Measurements with no erroneous output).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (\varphi: (\operatorname{Label}\left(N, k\right)) \to (((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right))) \to (\mathbb{C}))), (\forall (E: (\operatorname{Label}\left(N, k\right)) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))), (\forall (E_{0}: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right)), ((\operatorname{IsUnambiguousMeasurement}\left(\varphi, E, E_{0}\right)) \Leftrightarrow ((\forall (x: \operatorname{Label}\left(N, k\right)), (\operatorname{Matrix.PosSemidef}\left(E\left(x\right)\right))) \land ((\operatorname{Matrix.PosSemidef}\left(E_{0}\right)) \land (((\sum_{x: \operatorname{Label}\left(N, k\right)} (E\left(x\right))) + (E_{0}) = (1: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))) \land (\forall (x: \operatorname{Label}\left(N, k\right)), (\forall (y: \operatorname{Label}\left(N, k\right)), ((y \ne x) \Rightarrow (\operatorname{dotProduct}\left(\operatorname{star}\left(\varphi\left(y\right)\right), \operatorname{Matrix.mulVec}\left(E\left(x\right), \varphi\left(y\right)\right)\right) = (0: \mathbb{C})))))))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.IsUnambiguousMeasurement` (`✓ std3`).

*Citation.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

Every conclusive effect E x and the inconclusive effect E₀ is positive semidefinite. Their sum is the identity, and the effect for x has zero probability on every different input y. The success probabilities may depend on the input. This is the unambiguous condition of revised_02.tex, lines 652–672.

**Definition 1.5 (Uniform average success).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (\varphi: (\operatorname{Label}\left(N, k\right)) \to (((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right))) \to (\mathbb{C}))), (\forall (E: (\operatorname{Label}\left(N, k\right)) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))), (\operatorname{averageSuccess}\left(\varphi, E\right) = \frac{\sum_{x: \operatorname{Label}\left(N, k\right)} (\operatorname{Complex.re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\varphi\left(x\right)\right), \operatorname{Matrix.mulVec}\left(E\left(x\right), \varphi\left(x\right)\right)\right)\right))}{(\operatorname{Nat.cast}\left(\operatorname{Fintype.card}\left(\operatorname{Label}\left(N, k\right)\right)\right): \mathbb{R})}))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.averageSuccess` (`✓ std3`).

*Citation.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

The finite expectation averages the real readout of E x on φ x over all injective labels x, as in the uniform ensemble of revised_02.tex, lines 834–840. The displayed quotient expands that expectation and readout. Nat.cast explicitly includes the natural cardinality in the reals. If there are no labels the finite expectation is zero; k ≤ N ensures that labels exist in the theorem.

**Definition 1.6 (Effects after classical processing).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (F: (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right))), (\forall (d: ((\operatorname{Fin}\left(k\right)) \to (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right))) \to (\operatorname{Option}\left(\operatorname{Label}\left(N, k\right)\right))), (\forall (z: \operatorname{Option}\left(\operatorname{Label}\left(N, k\right)\right)), (\operatorname{inducedEffect}\left(F, d, z\right) = \sum_{o: (\operatorname{Fin}\left(k\right)) \to (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right))} (\operatorname{ite}\left(d\left(o\right) = z, \operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(N\right)\right), \lambda (j: \operatorname{Fin}\left(k\right)) \mapsto (F\left(o\left(j\right)\right))\right), (0: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))\right)))))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.inducedEffect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

For each output z, sum the tensor-product effects of exactly those outcome tuples o for which d o = z. Option.none denotes an inconclusive output, while Option.some carries a label. The single-system effects are the same at every position.

**Definition 1.7 (Independent measurements and a decision rule).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (F: (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right))), (\forall (d: ((\operatorname{Fin}\left(k\right)) \to (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right))) \to (\operatorname{Option}\left(\operatorname{Label}\left(N, k\right)\right))), (\forall (E: (\operatorname{Label}\left(N, k\right)) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))), (\forall (E_{0}: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right)), ((\operatorname{IsProductProtocol}\left(F, d, E, E_{0}\right)) \Leftrightarrow ((\forall (o: \operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right)), (\operatorname{Matrix.PosSemidef}\left(F\left(o\right)\right))) \land ((\sum_{o: \operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right)} (F\left(o\right)) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right))) \land ((\forall (x: \operatorname{Label}\left(N, k\right)), (E\left(x\right) = \operatorname{inducedEffect}\left(F, d, \operatorname{Option.some}\left(x\right)\right))) \land (E_{0} = \operatorname{inducedEffect}\left(F, d, (\operatorname{Option.none}: \operatorname{Option}\left(\operatorname{Label}\left(N, k\right)\right))\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.IsProductProtocol` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

The family F is one positive operator-valued measurement with outcomes Option (Fin N). Each position uses F independently, and d assigns an output to every tuple of local outcomes. The conclusive and inconclusive effects are precisely the effects induced by d. This predicate specifies the measurement and its processing; the separate unambiguous predicate imposes the no-error condition.

**Definition 1.8 (The two branches of the optimum).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (s: \mathbb{R}), (\operatorname{value}\left(N, k, s\right) = \operatorname{ite}\left(k < N, (((1: \mathbb{R})) - (s))^{(k)}, ((((1: \mathbb{R})) - (s))^{(((N) - ((1: \mathbb{N})): \mathbb{N}))}) \cdot (((1: \mathbb{R})) + (((\operatorname{Nat.cast}\left(((N) - ((1: \mathbb{N})): \mathbb{N})\right): \mathbb{R})) \cdot (s)))\right))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.value` (`✓ std3`).

*Citation.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

The first branch is (1 − s) to the power k. The other branch is (1 − s) to the power N − 1 times 1 + (N − 1)s. In the latter coefficient, N − 1 is first computed in the natural numbers and then cast to a real number. The formula agrees with revised_02.tex, lines 976–982, on k ≤ N; its second branch also defines a value when k > N.

**Definition 1.9 (The global bound and product attainment).**

$$\operatorname{claim} = (\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (((3: \mathbb{N}) \le N) \Rightarrow (((2: \mathbb{N}) \le k) \Rightarrow ((k \le N) \Rightarrow (\forall (s: \mathbb{R}), (((0: \mathbb{R}) < s) \Rightarrow ((s < (1: \mathbb{R})) \Rightarrow (\forall (\psi: (\operatorname{Fin}\left(N\right)) \to ((\operatorname{Fin}\left(N\right)) \to (\mathbb{C}))), ((\operatorname{IsEquiangular}\left(\psi, s\right)) \Rightarrow ((\forall (E: (\operatorname{Label}\left(N, k\right)) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))), (\forall (E_{0}: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right)), ((\operatorname{IsUnambiguousMeasurement}\left(\operatorname{productState}\left(\psi\right), E, E_{0}\right)) \Rightarrow (\operatorname{averageSuccess}\left(\operatorname{productState}\left(\psi\right), E\right) \le \operatorname{value}\left(N, k, s\right))))) \land (\exists (F: (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right))), (\exists (d: ((\operatorname{Fin}\left(k\right)) \to (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right))) \to (\operatorname{Option}\left(\operatorname{Label}\left(N, k\right)\right))), (\exists (E: (\operatorname{Label}\left(N, k\right)) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))), (\exists (E_{0}: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right)), ((\operatorname{IsProductProtocol}\left(F, d, E, E_{0}\right)) \land ((\operatorname{IsUnambiguousMeasurement}\left(\operatorname{productState}\left(\psi\right), E, E_{0}\right)) \land (\operatorname{averageSuccess}\left(\operatorname{productState}\left(\psi\right), E\right) = \operatorname{value}\left(N, k, s\right)))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

For every N ≥ 3, 2 ≤ k ≤ N, real 0 < s < 1 and normalized equal-overlap family ψ, every unambiguous measurement has average success at most value N k s, and one independent product protocol is unambiguous and attains that value. This expresses the unambiguous clauses of the conjecture in revised_02.tex, lines 970–984. The minimum-error clause is not claimed.

For k < N this also answers the no-repetition question in the 2024 paper, source.tex, lines 883–903: collective measurements give no improvement under these hypotheses. See `D5/L/QuantumContext/guptamurshidbandyopadhyay2024sequences`.

**Theorem 1.10 (Optimal unambiguous discrimination by local product measurements).**

$$\forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (((3: \mathbb{N}) \le N) \Rightarrow (((2: \mathbb{N}) \le k) \Rightarrow ((k \le N) \Rightarrow (\forall (s: \mathbb{R}), (((0: \mathbb{R}) < s) \Rightarrow ((s < (1: \mathbb{R})) \Rightarrow (\forall (\psi: (\operatorname{Fin}\left(N\right)) \to ((\operatorname{Fin}\left(N\right)) \to (\mathbb{C}))), ((\operatorname{IsEquiangular}\left(\psi, s\right)) \Rightarrow ((\forall (E: (\operatorname{Label}\left(N, k\right)) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))), (\forall (E_{0}: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right)), ((\operatorname{IsUnambiguousMeasurement}\left(\operatorname{productState}\left(\psi\right), E, E_{0}\right)) \Rightarrow (\operatorname{averageSuccess}\left(\operatorname{productState}\left(\psi\right), E\right) \le \operatorname{value}\left(N, k, s\right))))) \land (\exists (F: (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right))), (\exists (d: ((\operatorname{Fin}\left(k\right)) \to (\operatorname{Option}\left(\operatorname{Fin}\left(N\right)\right))) \to (\operatorname{Option}\left(\operatorname{Label}\left(N, k\right)\right))), (\exists (E: (\operatorname{Label}\left(N, k\right)) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right))), (\exists (E_{0}: \operatorname{Matrix}\left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), (\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(N\right)), \mathbb{C}\right)), ((\operatorname{IsProductProtocol}\left(F, d, E, E_{0}\right)) \land ((\operatorname{IsUnambiguousMeasurement}\left(\operatorname{productState}\left(\psi\right), E, E_{0}\right)) \land (\operatorname{averageSuccess}\left(\operatorname{productState}\left(\psi\right), E\right) = \operatorname{value}\left(N, k, s\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.result` (`✓ std3`). ∎

*Resolves.* `Problems/murshid-gupta-russo-bandyopadhyay-2026-no-repetition-unambiguous-discrimination` (proved) by `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"murshid-gupta-russo-bandyopadhyay-2026-no-repetition-unambiguous-discrimination","declaration_gid":"D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shayeef Murshid; Tathagata Gupta; Vincent Russo; Somshubhro Bandyopadhyay (2026). *Quantum nonlocality without entanglement and state discrimination measures*. DOI: [10.22331/q-2026-07-23-2174](https://doi.org/10.22331/q-2026-07-23-2174). URL: <https://arxiv.org/abs/2506.20560v3>.

*Commentary.*

First form the Gram matrix K of the product states φ x = productState ψ x. Its (x,y) entry is the product over positions of 1 when x.val j = y.val j and s otherwise. For an unambiguous measurement put q x = Re⟨φ x, E x φ x⟩. Positivity and zero erroneous probability imply E x φ y = 0 whenever y ≠ x. Writing A for the matrix whose columns are φ x, compression of the conclusive effects therefore gives A* (Σx E x) A = diag(q). The inconclusive effect is positive, so K − diag(q) is positive semidefinite.

Permutations of the N labels preserve K and act transitively on the injective labels: any bijection between the images of two injections extends to a permutation. Average the permuted positive matrices K − diag(q). Transitivity makes every averaged diagonal entry equal to the uniform mean of q. After division by the positive number of permutations, K − averageSuccess φ E times the identity is positive semidefinite.

To find an eigenvalue of K, let G = (1 − s)I + sJ, where J has every entry one. If u i are eigenvectors of G with eigenvalues ev i, expand the determinant det(u i (y j)) by multilinearity in its rows. Summing over all tuples y shows that the tensor power of G multiplies this determinant by the product of the ev i. The determinant vanishes whenever y repeats a label, because two rows coincide. Thus the same eigenvector equation restricts to the injective labels and K.

When k < N, use the k difference vectors eᵢ − eₖ for i in Fin k, with Fin k embedded in Fin N. Each has eigenvalue 1 − s. On the injection listing the first k labels, their evaluation matrix is the identity, so the determinant vector is nonzero. Its eigenvalue is (1 − s)^k. When k = N, write N = n + 1 and use the n differences eᵢ − eₙ together with the constant-one vector. The latter has eigenvalue 1 + ns. The evaluation matrix is invertible: summing coordinates in a vector in its nullspace first forces the coefficient of the constant column to vanish, and the other coordinates then force every remaining coefficient to vanish. Its nonzero determinant supplies an eigenvector with eigenvalue (1 − s)^(N − 1)(1 + (N − 1)s).

Apply the positive matrix K − averageSuccess φ E times the identity to the nonzero determinant vector w. Its quadratic form is (value N k s − averageSuccess φ E) times the strictly positive squared norm of w. Nonnegativity proves the required upper bound for every unambiguous measurement.

For attainment, let A now be the square matrix whose columns are the single-system vectors ψ i. Its Gram matrix is G. Since 1 − s > 0 and sJ is positive semidefinite, G is positive definite, so A is invertible. Put B = A⁻¹. On the label-coordinate space take H none = sJ and H (some i) = (1 − s)eᵢeᵢ*. These positive effects sum to G. The effects F o = B* H o B are positive and sum to the identity. The identity A* F o A = H o shows that on ψ j the outcome some j has probability 1 − s, none has probability s, and every other conclusive outcome has probability zero.

A product effect is positive: each coordinate effect pulled back to the tuple indices is positive, and successive Hadamard products preserve positivity. Distributing the finite sums shows that all product effects sum to the identity. Distributing the coordinate sums in the quadratic form shows that each outcome probability is the product of its single-system probabilities. Summing product effects over the fibers of any decision rule preserves positivity and completeness. An injective map from pairs (x,r) to accepted outcome patterns defines a rule that returns x on these patterns and none elsewhere; the effect for x is then the sum over its patterns r. If its probability on y is p for x = y and zero otherwise, these effects form an unambiguous measurement with uniform average p.

For full sequences, two injective maps Fin N → Fin N agreeing away from one position also agree at that position, since both use every label. Consequently the patterns obtained from x by retaining all outcomes, or replacing exactly one position by none, identify both x and the erased position uniquely. For k < N accept only the fully conclusive pattern listing x. Its probability is (1 − s)^k on x and zero on every other sequence. For k = N accept the fully conclusive pattern and all N patterns with exactly one inconclusive position. Their probabilities on x are (1 − s)^N and s(1 − s)^(N − 1) respectively. On a different sequence every accepted pattern contains a mismatched conclusive label, so its probability is zero. The total correct probability is (1 − s)^N + Ns(1 − s)^(N − 1) = (1 − s)^(N − 1)(1 + (N − 1)s). The two cases provide the required attaining protocol.

Together the global upper bound and this attained value prove the unambiguous clauses of the conjecture. Independent local measurements followed by classical processing form an LOCC protocol. Thus the local and global unambiguous optima defined in revised_02.tex, lines 213–221, both equal value N k s. The same conclusion answers the 2024 no-repetition question for k < N under the stated hypotheses. The minimum-error clause is not claimed.

## References

- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.IsEquiangular`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.IsProductProtocol`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.IsUnambiguousMeasurement`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.Label`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.averageSuccess`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.claim`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.inducedEffect`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.productState`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.result`
- Truth anchor: `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.value`
- Dependency: [D5/S3/Quantum/Measurement/OverlapLowRankDistance](../Measurement/OverlapLowRankDistance.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
