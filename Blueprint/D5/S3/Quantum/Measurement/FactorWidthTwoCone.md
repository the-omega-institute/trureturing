# FactorWidthTwoCone

## Abstract

Finite support cones and factor-width-two trace duality.

**Definition 1.1 (IsKSparse).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{k} : \mathbb{N}) , \forall (\operatorname{v} : \operatorname{Fin} \operatorname{n} \to \mathbb{C}) , \operatorname{IsKSparse} \operatorname{k} \operatorname{v} = ((\operatorname{Finset}.\operatorname{filter} (\operatorname{fun} (\operatorname{i} : \operatorname{Fin} \operatorname{n}) \mapsto \operatorname{v} \operatorname{i} \neq 0) \operatorname{Finset}.\operatorname{univ}).\operatorname{card} \leq \operatorname{k})$$

*Formalization.* `D5/S3/Quantum/Measurement/FactorWidthTwoCone.IsKSparse` (`✓ std3`).

*Citation.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Section 2.1, page 3: “In the special case when each vⱼ can be chosen to have at most k non-zero entries (where 1 ≤ k ≤ n), ρ is called k-incoherent”. The finite support counts the nonzero coordinates of v.

**Definition 1.2 (IsKIncoherentSum).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{k} : \mathbb{N}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , \operatorname{IsKIncoherentSum} \operatorname{k} \operatorname{X} = (\exists (\operatorname{m} : \mathbb{N}) , \exists (\operatorname{v} : \operatorname{Fin} \operatorname{m} \to \operatorname{Fin} \operatorname{n} \to \mathbb{C}) , (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{m}) , \operatorname{IsKSparse} \operatorname{k} (\operatorname{v} \operatorname{j})) \land (\operatorname{X} = \sum_{(\operatorname{j} : \operatorname{Fin} \operatorname{m})} \operatorname{Matrix}.\operatorname{vecMulVec} (\operatorname{v} \operatorname{j}) (\operatorname{star} (\operatorname{v} \operatorname{j}))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FactorWidthTwoCone.IsKIncoherentSum` (`✓ std3`).

*Citation.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Section 2.1, page 3: “every mixed state ρ ∈ Mₙ⁺ can be written in the form ρ = Σⱼ vⱼvⱼ* for some {vⱼ} ⊆ ℂⁿ. In the special case when each vⱼ can be chosen to have at most k non-zero entries (where 1 ≤ k ≤ n), ρ is called k-incoherent”. Here j ranges over Fin m, and no normalization is imposed on the individual vectors.

**Definition 1.3 (IsLocally2).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{Y} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , \operatorname{IsLocally2} (\operatorname{Y}) = (((\operatorname{Y}).\operatorname{IsHermitian}) \land (\forall (\operatorname{s} : \operatorname{Subtype} (\operatorname{fun} (\operatorname{s} : \operatorname{Finset} (\operatorname{Fin} \operatorname{n})) \mapsto (\operatorname{s}).\operatorname{card} \leq 2)) , \forall (\operatorname{x} : \operatorname{Fin} \operatorname{n} \to \mathbb{C}) , (\forall (\operatorname{j} : \operatorname{Fin} \operatorname{n}) , (\neg (\operatorname{j} \in (\operatorname{s}).\operatorname{val})) \to \operatorname{x} \operatorname{j} = 0) \to 0 \leq \operatorname{RHLinalg}.\operatorname{hermForm} \operatorname{Y} \operatorname{x}))$$

*Formalization.* `D5/S3/Quantum/Measurement/FactorWidthTwoCone.IsLocally2` (`✓ std3`).

*Citation.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Definition 1(b), page 4: “⟨v|X|v⟩ ≥ 0 for all |v⟩ ∈ ℂⁿ with at most k non-zero entries; or”. Here k = 2; s ranges over coordinate subsets with cardinality at most two, and x vanishes outside s.

**Theorem 1.4 (fw2 duality).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{X} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , ((\operatorname{X}).\operatorname{IsHermitian}) \to (\forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsLocally2} (\operatorname{A})) \to 0 \leq \operatorname{RHLinalg}.\operatorname{rtrace} (\operatorname{X} \cdot \operatorname{A})) \to \operatorname{IsKIncoherentSum} 2 \operatorname{X}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidthTwoCone.fw2_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Nonnegative trace pairing against all locally positive matrices implies a finite sum of outer products of two-sparse vectors. Closedness of the finite family of support cones gives the separating Hermitian matrix.

**Theorem 1.5 (local2 diagonal).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsLocally2} (\operatorname{A})) \to \forall (\operatorname{i} : \operatorname{Fin} \operatorname{n}) , 0 \leq (\operatorname{A} \operatorname{i} \operatorname{i}).\operatorname{re}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Every diagonal entry of a locally positive matrix is nonnegative.

**Theorem 1.6 (local2 minor).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsLocally2} (\operatorname{A})) \to \forall (\operatorname{i} : \operatorname{Fin} \operatorname{n}) , \forall (\operatorname{j} : \operatorname{Fin} \operatorname{n}) , \operatorname{Complex}.\operatorname{normSq} (\operatorname{A} \operatorname{i} \operatorname{j}) \leq (\operatorname{A} \operatorname{i} \operatorname{i}).\operatorname{re} \cdot (\operatorname{A} \operatorname{j} \operatorname{j}).\operatorname{re}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Each two-coordinate principal submatrix is positive semidefinite, so its determinant bounds its off-diagonal entry.

**Theorem 1.7 (local2 smul).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsLocally2} (\operatorname{A})) \to \forall (\operatorname{c} : \mathbb{R}) , (0 \leq \operatorname{c}) \to \operatorname{IsLocally2} (\operatorname{HSMul}.\operatorname{hSMul} \operatorname{c} \operatorname{A})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

Multiplication by a nonnegative real scalar preserves local positivity.

**Theorem 1.8 (local2 trace nonneg).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsLocally2} (\operatorname{A})) \to 0 \leq \operatorname{RHLinalg}.\operatorname{rtrace} (\operatorname{A})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_trace_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

The real trace of a locally positive matrix is nonnegative.

**Theorem 1.9 (local2 trace zero).**

$$\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{A} : \operatorname{Matrix} (\operatorname{Fin} \operatorname{n}) (\operatorname{Fin} \operatorname{n}) \mathbb{C}) , (\operatorname{IsLocally2} (\operatorname{A})) \to (\operatorname{RHLinalg}.\operatorname{rtrace} (\operatorname{A}) = 0) \to \operatorname{A} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston; Shirin Moein; Rajesh Pereira; Sarah Plosker (2022). *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*. DOI: [10.1103/PhysRevA.106.052417](https://doi.org/10.1103/PhysRevA.106.052417). URL: <https://arxiv.org/abs/2205.05110v2>.

*Commentary.*

A locally positive matrix with zero real trace vanishes.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.IsKIncoherentSum`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.IsKSparse`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.IsLocally2`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.fw2_duality`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_diagonal`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_minor`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_smul`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_trace_nonneg`
- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidthTwoCone.local2_trace_zero`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/IncoherentCone](IncoherentCone.md)
