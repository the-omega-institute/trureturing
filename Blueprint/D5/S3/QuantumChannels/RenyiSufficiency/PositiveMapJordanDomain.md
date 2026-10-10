# PositiveMapJordanDomain

## Abstract

Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.

**Theorem 1.1 (positive map hermitian).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (Phi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}), (\forall X , X.\operatorname{PosSemidef} \to (Phi X) .\operatorname{PosSemidef}) \Rightarrow \forall (H: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (H.\operatorname{IsHermitian}) \Rightarrow (Phi H) .\operatorname{IsHermitian}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_map_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.2 (kadison finite weights).**

$$\forall (m: \mathbb{N}), \forall (k: \operatorname{Type}), [\operatorname{Fintype} k], \forall (A: k \to \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}), \forall (lambda: k \to \mathbb{R}), (\forall i , (A i) .\operatorname{PosSemidef}) \Rightarrow (\sum i , A i = 1) \Rightarrow (\sum i , (lambda i : \mathbb{C}) \cdot A i) \times (\sum i , (lambda i : \mathbb{C}) \cdot A i) \leq \sum i , ((lambda i : \mathbb{C})^{2}) \cdot A i$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.kadison_finite_weights` (`✓ std3`). ∎

*Citation.* Richard V. Kadison (1952). *A Generalized Schwarz Inequality and Algebraic Invariants for Operator Algebras*. DOI: [10.2307/1969657](https://doi.org/10.2307/1969657). URL: <https://doi.org/10.2307/1969657>.

*Commentary.*

A sum of the positive matrices (lambda(i)I−K) A(i) (lambda(i)I−K), where K is the weighted sum, proves the finite-weight Kadison inequality.

**Theorem 1.3 (kadison hermitian).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (Phi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}), (\forall X , X.\operatorname{PosSemidef} \to (Phi X) .\operatorname{PosSemidef}) \Rightarrow (Phi 1 = 1) \Rightarrow \forall (H: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (H.\operatorname{IsHermitian}) \Rightarrow Phi H \times Phi H \leq Phi (H \times H)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.kadison_hermitian` (`✓ std3`). ∎

*Citation.* Richard V. Kadison (1952). *A Generalized Schwarz Inequality and Algebraic Invariants for Operator Algebras*. DOI: [10.2307/1969657](https://doi.org/10.2307/1969657). URL: <https://doi.org/10.2307/1969657>.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Definition 1.4 (jordan).**

$$\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (B: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \operatorname{jordan} A B = (A \times B + B \times A)$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.jordan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.5 (hermitian jordan domain).**

$$\forall (n: \mathbb{N}), \forall (E: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\operatorname{IsPositive} E) \Rightarrow (E 1 = 1) \Rightarrow \forall (H: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (Y: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (H.\operatorname{IsHermitian}) \Rightarrow (Y.\operatorname{IsHermitian}) \Rightarrow (E (H \times H) = E H \times E H) \Rightarrow E (\operatorname{jordan} H Y) = \operatorname{jordan} (E H) (E Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.hermitian_jordan_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kadison equality for H makes the linear coefficient of the quadratic positivity inequality vanish, giving the Jordan identity with every Hermitian Y.

**Theorem 1.6 (jordan smul right).**

$$\forall (n: \mathbb{N}), \forall (c: \mathbb{C}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (B: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \operatorname{jordan} A (c \cdot B) = c \cdot \operatorname{jordan} A B$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.jordan_smul_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.7 (jordan smul left).**

$$\forall (n: \mathbb{N}), \forall (c: \mathbb{C}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (B: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \operatorname{jordan} (c \cdot A) B = c \cdot \operatorname{jordan} A B$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.jordan_smul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Definition 1.8 (JordanMD).**

$$\forall (n: \mathbb{N}), \forall (E: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \operatorname{JordanMD} E A = (\forall (B : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , E (\operatorname{jordan} A B) = \operatorname{jordan} (E A) (E B))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.JordanMD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.9 (positive map star).**

$$\forall (n: \mathbb{N}), \forall (E: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\operatorname{IsPositive} E) \Rightarrow \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), E (\operatorname{conjTranspose}\left(A\right)) = \operatorname{conjTranspose}\left((E A)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_map_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.10 (fixed jordan domain).**

$$\forall (n: \mathbb{N}), \forall (E: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\operatorname{IsPositive} E) \Rightarrow (E 1 = 1) \Rightarrow \forall (S: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (S.\operatorname{PosDef}) \Rightarrow (\forall Y , (S \times E Y) .\operatorname{trace} = (S \times Y) .\operatorname{trace}) \Rightarrow (E A = A) \Rightarrow \operatorname{JordanMD} E A$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.fixed_jordan_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.11 (fixed jordan).**

$$\forall (n: \mathbb{N}), \forall (E: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\operatorname{IsPositive} E) \Rightarrow (E 1 = 1) \Rightarrow \forall (S: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (B: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (S.\operatorname{PosDef}) \Rightarrow (\forall Y , (S \times E Y) .\operatorname{trace} = (S \times Y) .\operatorname{trace}) \Rightarrow (E A = A) \Rightarrow (E B = B) \Rightarrow E (\operatorname{jordan} A B) = \operatorname{jordan} A B$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.fixed_jordan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.12 (arbitrary square extension).**

$$\forall (n: \mathbb{N}), \forall (E: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (D: \operatorname{Submodule} \mathbb{C} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})), (\forall A \in D , \operatorname{conjTranspose}\left(A\right) \in D) \Rightarrow (\forall A \in D , A.\operatorname{IsHermitian} \to E (A \times A) = E A \times E A) \Rightarrow \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (A \in D) \Rightarrow E (A \times A) = E A \times E A$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.arbitrary_square_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.13 (positive inverse square preserving).**

$$\forall (n: \mathbb{N}), \forall (Phi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (Psi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\operatorname{IsPositive} Phi) \Rightarrow (\operatorname{IsPositive} Psi) \Rightarrow (Phi 1 = 1) \Rightarrow (Psi 1 = 1) \Rightarrow (Psi.\operatorname{comp} Phi = \operatorname{LinearMap}.\operatorname{id}) \Rightarrow \forall (H: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (H.\operatorname{IsHermitian}) \Rightarrow Phi (H \times H) = Phi H \times Phi H$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_inverse_square_preserving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kadison applied to each member of the positive inverse pair gives opposing inequalities, and their equality preserves Hermitian squares.

**Theorem 1.14 (positive inverse complex jordan).**

$$\forall (n: \mathbb{N}), \forall (Phi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (Psi: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \to_{l}[\mathbb{C}] \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), (\operatorname{IsPositive} Phi) \Rightarrow (\operatorname{IsPositive} Psi) \Rightarrow (Phi 1 = 1) \Rightarrow (Psi 1 = 1) \Rightarrow (Psi.\operatorname{comp} Phi = \operatorname{LinearMap}.\operatorname{id}) \Rightarrow \forall (A: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), \forall (B: \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}), Phi (\operatorname{jordan} A B) = \operatorname{jordan} (Phi A) (Phi B)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_inverse_complex_jordan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

## References

- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.JordanMD`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.arbitrary_square_extension`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.fixed_jordan`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.fixed_jordan_domain`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.hermitian_jordan_domain`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.jordan`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.jordan_smul_left`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.jordan_smul_right`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.kadison_finite_weights`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.kadison_hermitian`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_inverse_complex_jordan`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_inverse_square_preserving`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_map_hermitian`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain.positive_map_star`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../../Quantum/Foundation/FiniteKrausChannel.md)
