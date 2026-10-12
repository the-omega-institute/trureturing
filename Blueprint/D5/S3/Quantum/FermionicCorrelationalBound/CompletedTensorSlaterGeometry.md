# CompletedTensorSlaterGeometry

## Abstract

Completed fermionic operators and their correlational estimate.

All types range over arbitrary universes. Underscores in declaration names appear as typographical subscripts and retain the full Lean spelling. Juxtaposition and the displayed binders use Lean function-application syntax; sums and products use Lean's typed binder syntax. Bracketed typeclass requirements are anonymous instances. Real and complex casts retain their target-type annotation. Submodules and lp spaces in type position carry the ordinary CoeSort coercion. Nat subtraction is truncated, Nat division is Euclidean division, and field division is written with a slash. Named constants retain their actual Lean spelling. The three-dot marker suppresses only proof fields and proof arguments, which are proof-irrelevant; it never suppresses mathematical data. The additional h and g binders in construction equations stand for proofs of the displayed propositions; proof irrelevance makes the equation independent of their choice. Completed tensors are UniformSpace.Completion of the Mathlib Hilbert tensor product.

**Definition 1.1 (CanonicalFamily).**

$$\operatorname{CanonicalFamily}. \operatorname{mk} : \{\iota : \operatorname{Type}\}\to (\operatorname{coeff} : \iota \to \mathbb{R})\to (\forall (i : \iota), 0 \leq \operatorname{coeff} i)\to (\operatorname{Summable} \operatorname{fun} (i : \iota)\mapsto( \operatorname{coeff} i)^{2})\to \sum ' (i : \iota),( \operatorname{coeff} i)^{2}= 1 \to \operatorname{CanonicalFamily} \iota$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.CanonicalFamily` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.2 (HilbertObject).**

$$\operatorname{HilbertObject}. \operatorname{mk} : (\operatorname{carrier} : \operatorname{Type})\to \operatorname{NormedAddCommGroup} \operatorname{carrier} \to \operatorname{InnerProductSpace} \mathbb{C} \operatorname{carrier} \to \operatorname{CompleteSpace} \operatorname{carrier} \to \operatorname{HilbertObject}$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.3 (IsAntisymmetric).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2)), (\operatorname{IsAntisymmetric} (N)(\psi): \operatorname{Prop})= (\forall (t : \operatorname{Fin} N \to \mathbb{N})(\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} N)), (\psi : (i : \operatorname{Fin} N \to \mathbb{N})\to (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})i)(t \circ (\sigma : \operatorname{Fin} N \to \operatorname{Fin} N))= \operatorname{permutationPhase} N \sigma * (\psi : (i : \operatorname{Fin} N \to \mathbb{N})\to (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})i)t)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.IsAntisymmetric` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.4 (TensorTowerIndex).**

$$\forall (\iota : \operatorname{Type}), \operatorname{TensorTowerIndex} \iota 0 = \iota \land (\forall (n : \mathbb{N}), \operatorname{TensorTowerIndex} \iota (n + 1)= \iota \times \operatorname{TensorTowerIndex} \iota n)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.TensorTowerIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.5 (antisymmetricComplete).**

$$\forall (N : \mathbb{N}), \operatorname{CompleteSpace} (\operatorname{antisymmetricSubmodule} N)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetricComplete` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.6 (antisymmetricSubmodule).**

$$\forall (N : \mathbb{N}), (\operatorname{antisymmetricSubmodule} (N): \operatorname{Submodule} \mathbb{C} (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2))= (\{\operatorname{carrier} := \{\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2)| \operatorname{IsAntisymmetric} N \psi\}, \operatorname{add}_{\operatorname{mem'}} :=..., \operatorname{zero}_{\operatorname{mem'}} :=..., \operatorname{smul}_{\operatorname{mem'}} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetricSubmodule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.7 (antisymmetricSubmodule_closed).**

$$\forall (N : \mathbb{N}), \operatorname{IsClosed} ((\operatorname{antisymmetricSubmodule} N): \operatorname{Set} (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetricSubmodule_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.8 (antisymmetric_orthogonal_slaters_zero).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2)), \operatorname{IsAntisymmetric} N \psi \to (\forall (S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}), \operatorname{inner} \mathbb{C} (\operatorname{slaterVector} N S)\psi = 0)\to \psi = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetric_orthogonal_slaters_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.9 (antisymmetric_repeated_zero).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2)), \operatorname{IsAntisymmetric} N \psi \to \forall (t : \operatorname{Fin} N \to \mathbb{N}), \neg \operatorname{Function}. \operatorname{Injective} t \to (\psi : (i : \operatorname{Fin} N \to \mathbb{N})\to (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})i)t = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetric_repeated_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.10 (coordinateEquiv).**

$$\forall (A : \operatorname{Type})(B : \operatorname{Type})(e : A \equiv B), (\operatorname{coordinateEquiv} (e): (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)\equiv_{li} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : B)\mapsto \mathbb{C})2))= (\operatorname{LinearIsometryEquiv}. \operatorname{ofSurjective} (\operatorname{coordinateRename} e. \operatorname{toEmbedding})...)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.11 (extendedCoeff_moment).**

$$\forall \{\iota : \operatorname{Type}\}(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(c : \operatorname{CanonicalFamily} \iota)(k : \mathbb{N}), 0 < k \to \sum ' (j : \mathbb{N}),( \operatorname{Function}. \operatorname{extend} (e : \iota \to \mathbb{N})c. \operatorname{coeff} (\operatorname{fun} (_ : \mathbb{N})\mapsto 0)j)^{k}= \sum ' (i : \iota),( c. \operatorname{coeff} i)^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.extendedCoeff_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.12 (familyCoefficients).**

$$\forall (\iota : \operatorname{Type})(c : \operatorname{CanonicalFamily} \iota), (\operatorname{familyCoefficients} (c): (\operatorname{lp} (\operatorname{fun} (_ : \iota)\mapsto \mathbb{C})2))= (\langle \operatorname{fun} (i : \iota)\mapsto ((c. \operatorname{coeff} i): \mathbb{C}),...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.familyCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.13 (familySequence).**

$$\forall (\iota : \operatorname{Type})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(c : \operatorname{CanonicalFamily} \iota), (\operatorname{familySequence} (e)(c): \operatorname{CanonicalSequence})= (\{\operatorname{coeff} := \operatorname{Function}. \operatorname{extend} (e : \iota \to \mathbb{N})c. \operatorname{coeff} \operatorname{fun} (_ : \mathbb{N})\mapsto 0, \operatorname{nonneg} :=..., \operatorname{summable}_{\operatorname{sq}} :=..., \operatorname{mass} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.familySequence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.14 (familySequence_cap).**

$$\forall \{\iota : \operatorname{Type}\}(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(c : \operatorname{CanonicalFamily} \iota)(\alpha : \mathbb{R}), 0 \leq \alpha \to (\forall (i : \iota),( c. \operatorname{coeff} i)^{2}\leq \alpha)\to \forall (j : \mathbb{N}),( (\operatorname{familySequence} e c). \operatorname{coeff} j)^{2}\leq \alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.familySequence_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.15 (occupationTuple).**

$$\forall (N : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})(\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} N))(\operatorname{aAnon} : \operatorname{Fin} N), (\operatorname{occupationTuple} (N)(S)(\sigma)(\operatorname{aAnon}): \mathbb{N})= (((S : \operatorname{Finset} \mathbb{N}). \operatorname{orderEmbOfFin}... : \operatorname{Fin} N \to \mathbb{N})((\sigma : \operatorname{Fin} N \to \operatorname{Fin} N)\operatorname{aAnon}))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.occupationTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.16 (permutationPhase).**

$$\forall (N : \mathbb{N})(\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} N)), (\operatorname{permutationPhase} (N)(\sigma): \mathbb{C})= (((((\operatorname{Equiv}. \operatorname{Perm}. \operatorname{sign} : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} N)\to \operatorname{Units} \mathbb{Z})\sigma): \mathbb{Z}): \mathbb{C}))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.permutationPhase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.17 (slaterAntiVector).**

$$\forall (N : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}), (\operatorname{slaterAntiVector} (N)(S): (\operatorname{antisymmetricSubmodule} N))= (\langle \operatorname{slaterVector} N S,...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterAntiVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.18 (slaterAntiVector_dense).**

$$\forall (N : \mathbb{N}), (\operatorname{Submodule}. \operatorname{span} \mathbb{C} (\operatorname{Set}. \operatorname{range} (\operatorname{slaterAntiVector} N)))\perp = \operatorname{bot}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterAntiVector_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.19 (slaterAntiVector_orthonormal).**

$$\forall (N : \mathbb{N}), \operatorname{Orthonormal} \mathbb{C} (\operatorname{slaterAntiVector} N)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterAntiVector_orthonormal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.20 (slaterHilbertBasis).**

$$\forall (N : \mathbb{N})(h : \operatorname{Orthonormal} \mathbb{C} (\operatorname{slaterAntiVector} N))(g : (\operatorname{Submodule}. \operatorname{span} \mathbb{C} (\operatorname{Set}. \operatorname{range} (\operatorname{slaterAntiVector} N)))\perp = \operatorname{bot}), (\operatorname{slaterHilbertBasis} (N): \operatorname{HilbertBasis} \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}\mathbb{C} (\operatorname{antisymmetricSubmodule} N))= (\operatorname{HilbertBasis}. \operatorname{mkOfOrthogonalEqBot} h g)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterHilbertBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.21 (slaterVector).**

$$\forall (N : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}), (\operatorname{slaterVector} (N)(S): (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2))= (\langle (((\operatorname{Real}. \operatorname{sqrt} (N. \operatorname{factorial} : \mathbb{R}): \mathbb{C}))^{- 1})\cdot \operatorname{MultilinearMap}. \operatorname{alternatization} (\operatorname{MultilinearMap}. \operatorname{piFamily} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \operatorname{MultilinearMap}. \operatorname{mkPiAlgebra} \mathbb{C} (\operatorname{Fin} N)\mathbb{C}))(\operatorname{fun} (i : \operatorname{Fin} N)\mapsto \operatorname{Pi}. \operatorname{single} (S. \operatorname{val}. \operatorname{orderEmbOfFin} S. \operatorname{property} i)(1 : \mathbb{C})),...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.22 (slater_inner_antisymmetric).**

$$\forall (N : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2)), \operatorname{IsAntisymmetric} N \psi \to \operatorname{inner} \mathbb{C} (\operatorname{slaterVector} N S)\psi = (\operatorname{Real}. \operatorname{sqrt} (N. \operatorname{factorial} : \mathbb{R}): \mathbb{C})* (\psi : (i : \operatorname{Fin} N \to \mathbb{N})\to (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})i)(\operatorname{occupationTuple} N S 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slater_inner_antisymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.23 (sourceCanonicalFamily).**

$$\forall (\iota : \operatorname{Type})(E : \operatorname{Type})[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{CompleteSpace} E][\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} E](e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(v : \iota \times \operatorname{Fin} 2 \to E)(\operatorname{hv} : \operatorname{Orthonormal} \mathbb{C} v)(c : \operatorname{CanonicalFamily} \iota)(h : \operatorname{Orthonormal} \mathbb{C} (\operatorname{sourcePairWedge} v)), (\operatorname{sourceCanonicalFamily} (e)(v)(\operatorname{hv})(c): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E E))= (h. \operatorname{orthogonalFamily}. \operatorname{linearIsometry} (\operatorname{familyCoefficients} c))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceCanonicalFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.24 (sourceCanonicalFamily_coordinates).**

$$\forall \{\iota : \operatorname{Type}\}\{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{CompleteSpace} E][\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} E]\{\kappa : \operatorname{Type}\}(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(v : \iota \times \operatorname{Fin} 2 \to E)(\operatorname{hv} : \operatorname{Orthonormal} \mathbb{C} v)(c : \operatorname{CanonicalFamily} \iota)(b : \operatorname{HilbertBasis} \kappa \mathbb{C} E)(\operatorname{label} : \operatorname{Function}. \operatorname{Embedding} \kappa \mathbb{N})(r : \iota \times \operatorname{Fin} 2 \to \kappa), (\forall (p : \iota \times \operatorname{Fin} 2), (b : \kappa \to E)(r p)= v p)\to (\forall (i : \iota), (\operatorname{label} : \kappa \to \mathbb{N})(r (i, 0))= 4 * (e : \iota \to \mathbb{N})i)\to (\forall (i : \iota), (\operatorname{label} : \kappa \to \mathbb{N})(r (i, 1))= 4 * (e : \iota \to \mathbb{N})i + 1)\to (\operatorname{tensorCoordinateEmbedding} b \operatorname{label} : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E E)\to (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))(\operatorname{sourceCanonicalFamily} e v \operatorname{hv} c)= \operatorname{canonicalTensor} (\operatorname{padCanonicalSequence} (\operatorname{familySequence} e c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.25 (sourceCanonicalFamily_series).**

$$\forall \{\iota : \operatorname{Type}\}\{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{CompleteSpace} E][\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} E](e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(v : \iota \times \operatorname{Fin} 2 \to E)(\operatorname{hv} : \operatorname{Orthonormal} \mathbb{C} v)(c : \operatorname{CanonicalFamily} \iota), \operatorname{sourceCanonicalFamily} e v \operatorname{hv} c = \sum ' (i : \iota), ((c. \operatorname{coeff} i): \mathbb{C})\cdot \operatorname{sourcePairWedge} v i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceCanonicalFamily_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.26 (sourceExterior).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(x_{e} : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N}), (\operatorname{sourceExterior} (X)(b)(x_{e})(n): \operatorname{Submodule} \mathbb{C} (\operatorname{tensorTower} X n). \operatorname{carrier})= (\{\operatorname{carrier} := \{\psi | \forall (\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} (n + 1))), \operatorname{tensorPermutation} X b n \sigma \psi = \operatorname{permutationPhase} (n + 1)\sigma \cdot \psi\},...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceExterior` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The exterior sector is the physical permutation-antisymmetric part of the actual completed tensor power: each permutation acts by its sign. The coordinate characterization is private and is used by the physical contraction proof.

**Definition 1.27 (sourceHilbertObject).**

$$\forall (E : \operatorname{Type})[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{CompleteSpace} E], (\operatorname{sourceHilbertObject} (E): \operatorname{HilbertObject})= (\{\operatorname{carrier} := E, \operatorname{normed} := \operatorname{inferInstance}, \operatorname{innerProduct} := \operatorname{inferInstance}, \operatorname{complete} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceHilbertObject` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.28 (sourceTensorCoordinates).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N}), (\operatorname{sourceTensorCoordinates} (X)(b)(e)(n): (\operatorname{tensorTower} X n). \operatorname{carrier} \to_{li} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2))= ((\operatorname{coordinateRename} e. \operatorname{arrowCongrRight}). \operatorname{comp} (\operatorname{tensorTowerTupleBasis} X b n). \operatorname{repr}. \operatorname{toLinearIsometry})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceTensorCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.29 (sourceTensorCoordinates_antisymmetric).**

$$\forall \{\iota : \operatorname{Type}\}(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(\psi : (\operatorname{tensorTower} X n). \operatorname{carrier}), \operatorname{IsAntisymmetric} (n + 1)((\operatorname{sourceTensorCoordinates} X b e n : (\operatorname{tensorTower} X n). \operatorname{carrier} \to (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2))\psi)\iff \psi \in \operatorname{sourceExterior} X b e n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceTensorCoordinates_antisymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.30 (tensorHead).**

$$\forall (E : \operatorname{Type})(F : \operatorname{Type})[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{NormedAddCommGroup} F][\operatorname{InnerProductSpace} \mathbb{C} F][\operatorname{CompleteSpace} F](f : E), (\operatorname{tensorHead} (f): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F)\to_{L} [\mathbb{C}]F)= (((((\operatorname{TensorProduct}. \operatorname{lidIsometry} \mathbb{C} F): \operatorname{TensorProduct} \mathbb{C} \mathbb{C} F \equiv_{L} [\mathbb{C}]F): \operatorname{TensorProduct} \mathbb{C} \mathbb{C} F \to_{L} [\mathbb{C}]F)\circ_{\operatorname{SL}} \operatorname{ContinuousLinearMap}. \operatorname{rTensor} F ((\operatorname{innerSL} \mathbb{C} : E \to E \to_{L} [\mathbb{C}]\mathbb{C})f)). \operatorname{extend} \operatorname{UniformSpace}. \operatorname{Completion}. \operatorname{toComplL})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHead` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.31 (tensorHead_adjoint).**

$$\forall \{E : \operatorname{Type}\}\{F : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{NormedAddCommGroup} F][\operatorname{InnerProductSpace} \mathbb{C} F][\operatorname{CompleteSpace} F]\{\iota : \operatorname{Type}\}\{\kappa : \operatorname{Type}\}(_ : \operatorname{HilbertBasis} \iota \mathbb{C} E)(_ : \operatorname{HilbertBasis} \kappa \mathbb{C} F)(f : E), \operatorname{tensorHead} f = (\operatorname{ContinuousLinearMap}. \operatorname{adjoint} : (F \to_{L} [\mathbb{C}]\operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F))\to \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F)\to_{L} [\mathbb{C}]F)(\operatorname{UniformSpace}. \operatorname{Completion}. \operatorname{toComplL} \circ_{\operatorname{SL}} (\operatorname{TensorProduct}. \operatorname{mkL} \mathbb{C} E F : E \to F \to_{L} [\mathbb{C}]\operatorname{TensorProduct} \mathbb{C} E F)f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHead_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.32 (tensorHead_basis_coordinates).**

$$\forall \{E : \operatorname{Type}\}\{F : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{NormedAddCommGroup} F][\operatorname{InnerProductSpace} \mathbb{C} F][\operatorname{CompleteSpace} F]\{\iota : \operatorname{Type}\}\{\kappa : \operatorname{Type}\}(b : \operatorname{HilbertBasis} \iota \mathbb{C} E)(c : \operatorname{HilbertBasis} \kappa \mathbb{C} F)(i : \iota)(\psi : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F))(j : \kappa), (((c. \operatorname{repr} : F \to (\operatorname{lp} (\operatorname{fun} (_ : \kappa)\mapsto \mathbb{C})2))((\operatorname{tensorHead} ((b : \iota \to E)i): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F)\to F)\psi)): (i : \kappa)\to (\operatorname{fun} (_ : \kappa)\mapsto \mathbb{C})i)j = ((((\operatorname{tensorHilbertBasis} b c). \operatorname{repr} : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F)\to (\operatorname{lp} (\operatorname{fun} (_ : \iota \times \kappa)\mapsto \mathbb{C})2))\psi): (i : \iota \times \kappa)\to (\operatorname{fun} (_ : \iota \times \kappa)\mapsto \mathbb{C})i)(i, j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHead_basis_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.33 (tensorHilbertObject).**

$$\forall (X : \operatorname{HilbertObject})(Y : \operatorname{HilbertObject}), (\operatorname{tensorHilbertObject} (X)(Y): \operatorname{HilbertObject})= (\{\operatorname{carrier} := \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} Y. \operatorname{carrier}), \operatorname{normed} := \operatorname{inferInstance}, \operatorname{innerProduct} := \operatorname{inferInstance}, \operatorname{complete} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHilbertObject` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.34 (tensorPermutation).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(n : \mathbb{N})(\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} (n + 1))), (\operatorname{tensorPermutation} (X)(b)(n)(\sigma): (\operatorname{tensorTower} X n). \operatorname{carrier} \equiv_{li} [\mathbb{C}](\operatorname{tensorTower} X n). \operatorname{carrier})= ((\operatorname{tensorTowerTupleBasis} X b n). \operatorname{repr}. \operatorname{trans} ((\operatorname{coordinateEquiv} (\operatorname{Equiv}. \operatorname{arrowCongr} \sigma (\operatorname{Equiv}. \operatorname{refl} \iota))). \operatorname{trans} (\operatorname{tensorTowerTupleBasis} X b n). \operatorname{repr}. \operatorname{symm}))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.35 (tensorPermutation_product).**

$$\forall \{\iota : \operatorname{Type}\}(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(n : \mathbb{N})(\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} (n + 1)))(x : \operatorname{Fin} (n + 1)\to X. \operatorname{carrier}), (\operatorname{tensorPermutation} X b n \sigma : (\operatorname{tensorTower} X n). \operatorname{carrier} \to (\operatorname{tensorTower} X n). \operatorname{carrier})(\operatorname{tensorPure} X n x)= \operatorname{tensorPure} X n (x \circ ((\operatorname{Equiv}. \operatorname{symm} \sigma): \operatorname{Fin} (n + 1)\to \operatorname{Fin} (n + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorPermutation_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The bounded tensor permutation acts on an actual pure completed tensor by permuting its physical one-particle factors. This identifies the coordinate construction with physical tensor antisymmetry.

**Definition 1.36 (tensorPure).**

$$\forall (X : \operatorname{HilbertObject}), (\forall (x : \operatorname{Fin} 1 \to X. \operatorname{carrier}), \operatorname{tensorPure} X 0 x = x 0)\land (\forall (n : \mathbb{N})(x : \operatorname{Fin} (n + 2)\to X. \operatorname{carrier}), \operatorname{tensorPure} X (n + 1)x = (\operatorname{TensorProduct}. \operatorname{tmul} \mathbb{C} (x 0)(\operatorname{tensorPure} X n (\operatorname{Fin}. \operatorname{tail} x)): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} (\operatorname{tensorTower} X n). \operatorname{carrier})))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorPure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.37 (tensorTower).**

$$\forall (X : \operatorname{HilbertObject}), \operatorname{tensorTower} X 0 = X \land (\forall (n : \mathbb{N}), \operatorname{tensorTower} X (n + 1)= \operatorname{tensorHilbertObject} X (\operatorname{tensorTower} X n))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.38 (tensorTowerBasis).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier}), \operatorname{tensorTowerBasis} X b 0 = b \land (\forall (n : \mathbb{N}), \operatorname{tensorTowerBasis} X b (n + 1)= \operatorname{tensorHilbertBasis} b (\operatorname{tensorTowerBasis} X b n))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTowerBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.39 (tensorTowerTupleBasis).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(n : \mathbb{N}), (\operatorname{tensorTowerTupleBasis} (X)(b)(n): \operatorname{HilbertBasis} (\operatorname{Fin} (n + 1)\to \iota)\mathbb{C} (\operatorname{tensorTower} X n). \operatorname{carrier})= (\{\operatorname{repr} := (\operatorname{tensorTowerBasis} X b n). \operatorname{repr}. \operatorname{trans} (\operatorname{coordinateEquiv} (\operatorname{tensorTowerTupleEquiv} \iota n))\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTowerTupleBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.40 (tensorTowerTupleEquiv).**

$$\forall (\iota : \operatorname{Type}), \operatorname{tensorTowerTupleEquiv} \iota 0 = (\operatorname{Equiv}. \operatorname{funUnique} (\operatorname{Fin} 1)\iota). \operatorname{symm} \land (\forall (n : \mathbb{N}), \operatorname{tensorTowerTupleEquiv} \iota (n + 1)= (\operatorname{Equiv}. \operatorname{prodCongr} (\operatorname{Equiv}. \operatorname{refl} \iota)(\operatorname{tensorTowerTupleEquiv} \iota n)). \operatorname{trans} (\operatorname{Fin}. \operatorname{consEquiv} (\operatorname{fun} _ : \operatorname{Fin} (n + 2)\mapsto \iota)))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTowerTupleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.41 (tupleBasis_repr).**

$$\forall \{\iota : \operatorname{Type}\}(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(n : \mathbb{N})(\psi : (\operatorname{tensorTower} X n). \operatorname{carrier})(t : \operatorname{Fin} (n + 1)\to \iota), ((((\operatorname{tensorTowerTupleBasis} X b n). \operatorname{repr} : (\operatorname{tensorTower} X n). \operatorname{carrier} \to (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \iota)\mapsto \mathbb{C})2))\psi): (i : \operatorname{Fin} (n + 1)\to \iota)\to (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \iota)\mapsto \mathbb{C})i)t = ((((\operatorname{tensorTowerBasis} X b n). \operatorname{repr} : (\operatorname{tensorTower} X n). \operatorname{carrier} \to (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{TensorTowerIndex} \iota n)\mapsto \mathbb{C})2))\psi): (i : \operatorname{TensorTowerIndex} \iota n)\to (\operatorname{fun} (_ : \operatorname{TensorTowerIndex} \iota n)\mapsto \mathbb{C})i)(((\operatorname{tensorTowerTupleEquiv} \iota n). \operatorname{symm} : (\operatorname{Fin} (n + 1)\to \iota)\to \operatorname{TensorTowerIndex} \iota n)t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tupleBasis_repr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.CanonicalFamily`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.HilbertObject`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.IsAntisymmetric`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.TensorTowerIndex`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetricComplete`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetricSubmodule`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetricSubmodule_closed`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetric_orthogonal_slaters_zero`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.antisymmetric_repeated_zero`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.coordinateEquiv`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.extendedCoeff_moment`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.familyCoefficients`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.familySequence`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.familySequence_cap`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.occupationTuple`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.permutationPhase`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterAntiVector`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterAntiVector_dense`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterAntiVector_orthonormal`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterHilbertBasis`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slaterVector`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.slater_inner_antisymmetric`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceCanonicalFamily`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceCanonicalFamily_series`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceExterior`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceHilbertObject`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceTensorCoordinates`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.sourceTensorCoordinates_antisymmetric`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHead`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHead_adjoint`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHead_basis_coordinates`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorHilbertObject`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorPermutation`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorPermutation_product`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorPure`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTower`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTowerBasis`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTowerTupleBasis`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tensorTowerTupleEquiv`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry.tupleBasis_repr`
- Dependency: [D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding](CanonicalRdmAndPadding.md)
