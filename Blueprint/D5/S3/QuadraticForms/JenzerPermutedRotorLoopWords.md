# JenzerPermutedRotorLoopWords

## Abstract

Balanced exterior words cancel odd full-support coefficients.

**Theorem 1.1 (Subset expansion of the chain).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \operatorname{chain}\left(B, theta\right) = (\sum_{S \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))).\operatorname{powerset}} ((\operatorname{a}\left(theta, S\right)) \cdot (\operatorname{subsetProduct}\left(B, S\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.chain_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Distributing the ordered rotor product gives one increasing product for each subset, weighted by a. This expansion needs no anticommutation assumption.

**Theorem 1.2 (Square of an increasing subset product).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), (\operatorname{AnticommutingUnitFamily}\left(q, k, B\right)) \Rightarrow (\forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), (\operatorname{subsetProduct}\left(B, S\right)) \cdot (\operatorname{subsetProduct}\left(B, S\right)) = ((((-(1) : \mathbb{R}))^{\operatorname{Nat}.\operatorname{div}\left(((S).\operatorname{card}) \cdot (((S).\operatorname{card}) + (1)), 2\right)}) \cdot ((1 : \operatorname{CliffordAlgebra}\left(q\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.subsetProduct_square` (`✓ std3`). ∎

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

The square depends only on the subset size. Nat.div is natural-number division. This is the Square of a Subset Product identity in Jenzer, Lemma 3.2.

**Theorem 1.3 (Complementary subset coefficients).**

$$\forall (k : \mathbb{N}), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), (\operatorname{a}\left(theta, S\right)) \cdot (\operatorname{a}\left(theta, ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)\right)) = (\prod_{i \in (\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))} ((\operatorname{s}\left(theta, i\right)) \cdot (\operatorname{c}\left(theta, i\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.coefficient_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Multiplying coefficients for complementary subsets selects one sine and one cosine at every index, including when one of them is zero.

**Theorem 1.4 (Subset expansion of the return product).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), (\operatorname{AnticommutingUnitFamily}\left(q, k, B\right)) \Rightarrow (\forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (tau : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{returnProduct}\left(B, theta, tau\right) = (\sum_{S \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))).\operatorname{powerset}} ((((((-(1) : \mathbb{R}))^{(S).\operatorname{card}}) \cdot (((-(1) : \mathbb{R}))^{\operatorname{inversionCount}\left(tau, S\right)})) \cdot (\operatorname{a}\left(theta, S\right))) \cdot (\operatorname{subsetProduct}\left(B, S\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.return_expansion` (`✓ std3`). ∎

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Reversion contributes one minus sign per selected bivector. Sorting the return order contributes the inversion parity on that subset. Every factor is retained in the coefficient; this is the return-product subset expansion and inversion-sign identity in the proof of Jenzer Theorem 5.5, before the star condition is used.

**Theorem 1.5 (Complementary scalar pairs and exterior coefficients).**

$$\forall (A : Type*), [\operatorname{Ring}\left(A\right)] [\operatorname{Algebra}\left(\mathbb{R}, A\right)] \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to A)), (\forall (i : \operatorname{Fin}\left(k\right)), \forall (j : \operatorname{Fin}\left(k\right)), (i \ne (j)) \Rightarrow ((B\left(i\right)) \cdot (B\left(j\right)) = (-((B\left(j\right)) \cdot (B\left(i\right)))))) \Rightarrow (\forall (t : \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right)), \forall (b : \operatorname{Module}.\operatorname{Basis}\left(\operatorname{Fin}\left(k\right), \mathbb{R}, (\operatorname{Fin}\left(k\right) \to \mathbb{R})\right)), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), t\left(((((S).\operatorname{sort}\left((\operatorname{fun} u \mapsto (\operatorname{fun} v \mapsto u \le (v)))\right)).\operatorname{map}\left(B\right)).\operatorname{prod}) \cdot ((((((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)).\operatorname{sort}\left((\operatorname{fun} u \mapsto (\operatorname{fun} v \mapsto u \le (v)))\right)).\operatorname{map}\left(B\right)).\operatorname{prod})\right) = ((((b).\operatorname{ExteriorAlgebra}).\operatorname{repr}\left(((b).\operatorname{ExteriorAlgebra}\left(S\right)) \cdot ((b).\operatorname{ExteriorAlgebra}\left(((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)\right))\right)\left((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))\right)) \cdot (t\left(((((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))).\operatorname{sort}\left((\operatorname{fun} u \mapsto (\operatorname{fun} v \mapsto u \le (v)))\right)).\operatorname{map}\left(B\right)).\operatorname{prod}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.canonical_complementary_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

For complementary supports, the Clifford sign is the top exterior coefficient of the corresponding pair. No cyclicity of the linear functional is required here.

**Theorem 1.6 (Top exterior coefficients require complementary supports).**

$$\forall (k : \mathbb{N}), \forall (b : \operatorname{Module}.\operatorname{Basis}\left(\operatorname{Fin}\left(k\right), \mathbb{R}, (\operatorname{Fin}\left(k\right) \to \mathbb{R})\right)), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), \forall (T : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), (T \ne (((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S))) \Rightarrow (((b).\operatorname{ExteriorAlgebra}).\operatorname{repr}\left(((b).\operatorname{ExteriorAlgebra}\left(S\right)) \cdot ((b).\operatorname{ExteriorAlgebra}\left(T\right))\right)\left((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))\right) = (0))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.canonical_exterior_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Repeated generators annihilate an exterior word, while a support missing an index cannot have the top coefficient. Thus only complementary supports contribute.

**Theorem 1.7 (A nonempty index set has no self-complementary subset).**

$$\forall (k : \mathbb{N}), (1 \le (k)) \Rightarrow (\forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), S \ne (((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.complement_ne_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

At any chosen index, membership in a subset is the negation of membership in its complement.

**Theorem 1.8 (Cancellation of the odd full-support coefficient).**

$$\forall (k : \mathbb{N}), \forall (b : \operatorname{Module}.\operatorname{Basis}\left(\operatorname{Fin}\left(k\right), \mathbb{R}, (\operatorname{Fin}\left(k\right) \to \mathbb{R})\right)), \forall (tau : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), (\operatorname{Odd}\left(k\right)) \Rightarrow (\sum_{S \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))).\operatorname{powerset}} (\sum_{T \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))).\operatorname{powerset}} (((((-(1) : \mathbb{R}))^{(T).\operatorname{card}}) \cdot (((-(1) : \mathbb{R}))^{\operatorname{inversionCount}\left(tau, T\right)})) \cdot (((b).\operatorname{ExteriorAlgebra}).\operatorname{repr}\left(((b).\operatorname{ExteriorAlgebra}\left(S\right)) \cdot ((b).\operatorname{ExteriorAlgebra}\left(T\right))\right)\left((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))\right)))) = (0))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.signed_top_sum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

The balanced exterior word has even parity for every permutation. Its odd top coefficient vanishes; expansion identifies that coefficient with the displayed double sum.

## References

- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.canonical_complementary_trace`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.canonical_exterior_top`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.chain_expansion`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.coefficient_complement`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.complement_ne_self`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.return_expansion`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.signed_top_sum_zero`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.subsetProduct_square`
- Dependency: [D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra](JenzerPermutedRotorLoopAlgebra.md)
