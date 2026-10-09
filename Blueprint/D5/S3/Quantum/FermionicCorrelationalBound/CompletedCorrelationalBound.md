# CompletedCorrelationalBound

## Abstract

Completed fermionic operators and their correlational estimate.

All types range over arbitrary universes. Underscores in declaration names appear as typographical subscripts and retain the full Lean spelling. Juxtaposition and the displayed binders use Lean function-application syntax; sums and products use Lean's typed binder syntax. Bracketed typeclass requirements are anonymous instances. Real and complex casts retain their target-type annotation. Submodules and lp spaces in type position carry the ordinary CoeSort coercion. Nat subtraction is truncated, Nat division is Euclidean division, and field division is written with a slash. Named constants retain their actual Lean spelling. The three-dot marker suppresses only proof fields and proof arguments, which are proof-irrelevant; it never suppresses mathematical data. The additional h and g binders in construction equations stand for proofs of the displayed propositions; proof irrelevance makes the equation independent of their choice. Completed tensors are UniformSpace.Completion of the Mathlib Hilbert tensor product.

**Theorem 1.1 (standardK_real).**

$$\forall \{L s : \mathbb{N}\}(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R})(x y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), ((\operatorname{standardB} \operatorname{coeff}). \operatorname{conjTranspose} * \operatorname{standardB} \operatorname{coeff})x y = ((\operatorname{realK} \operatorname{coeff} x y): \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.standardK_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.2 (standardB_sector_support).**

$$\forall \{L s N : \mathbb{N}\}(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R})(\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s_{\operatorname{1}} : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s_{\operatorname{1}} = N\})(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} x \neq N - 2 \to (((\operatorname{Matrix}. \operatorname{toEuclideanLin} : \operatorname{Matrix} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\mathbb{C} \to \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\to_{l} [\mathbb{C}]\operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool}))(\operatorname{standardB} \operatorname{coeff}): \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\to \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool}))(\operatorname{lift} \psi)). \operatorname{ofLp} x = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.standardB_sector_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.3 (realK_symm).**

$$\forall \{L s : \mathbb{N}\}(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R})(x y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), \operatorname{realK} \operatorname{coeff} x y = \operatorname{realK} \operatorname{coeff} y x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.4 (realK_row).**

$$\forall \{L s : \mathbb{N}\}(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R})(f : (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\to \mathbb{R})(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), \sum y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}, \operatorname{realK} \operatorname{coeff} x y * f y = \sum i : \operatorname{Fin} L, \operatorname{if} \operatorname{pairFull} i x \operatorname{then} \operatorname{coeff} i * \sum j : \operatorname{Fin} L, \operatorname{if} \operatorname{pairEmpty} j (\operatorname{removePair} i x)\operatorname{then} \operatorname{coeff} j * f (\operatorname{addPair} j (\operatorname{removePair} i x))\operatorname{else} 0 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.5 (realK_nonneg).**

$$\forall \{L s : \mathbb{N}\}(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R}), (\forall (i : \operatorname{Fin} L), 0 \leq \operatorname{coeff} i)\to \forall (x y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), 0 \leq \operatorname{realK} \operatorname{coeff} x y$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.6 (realK).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R})(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{realK} (\operatorname{coeff})(x)(y): \mathbb{R})= (\operatorname{dotProduct} (\operatorname{fun} (z : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\mapsto \operatorname{realB} \operatorname{coeff} z x)(\operatorname{fun} (z : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\mapsto \operatorname{realB} \operatorname{coeff} z y))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.7 (realB).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R})(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{realB} (\operatorname{coeff})(x)(y): \mathbb{R})= (\sum i : \operatorname{Fin} L, \operatorname{if} \operatorname{pairTransition} i x y \operatorname{then} \operatorname{coeff} i \operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.8 (occupiedModes).**

$$\forall (d : \mathbb{N})(x : \operatorname{Fin} d \to \operatorname{Bool}), (\operatorname{occupiedModes} (x): \operatorname{Finset} (\operatorname{Fin} d))= (\{i : \operatorname{Fin} d | x i = \operatorname{true}\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.occupiedModes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.9 (doublePairs_sector).**

$$\forall \{L s m : \mathbb{N}\}(x : \{s_{\operatorname{1}} : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s_{\operatorname{1}} = 2 * m\}), (\operatorname{doublePairs} (x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})). \operatorname{card} \leq m$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.doublePairs_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.10 (actual_sector_bound).**

$$\forall \{L s : \mathbb{N}\}(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R}), (\forall (i : \operatorname{Fin} L), 0 \leq \operatorname{coeff} i)\to \forall (m : \mathbb{N}), 1 \leq m \to \forall (\alpha : \mathbb{R}), 0 \leq \alpha \to (\forall (i : \operatorname{Fin} L),( \operatorname{coeff} i)^{2}\leq \alpha)\to (\sum i : \operatorname{Fin} L,( \operatorname{coeff} i)^{2})\leq 1 \to 2 * (m : \mathbb{R})* \alpha \leq 1 \to \forall (\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s_{\operatorname{1}} : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s_{\operatorname{1}} = 2 * m\}),( \left\lVert ((\operatorname{Matrix}. \operatorname{toEuclideanLin} : \operatorname{Matrix} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\mathbb{C} \to \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\to_{l} [\mathbb{C}]\operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool}))(\operatorname{standardB} \operatorname{coeff}): \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\to \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool}))(\operatorname{lift} \psi) \right\rVert)^{2}\leq ((m : \mathbb{R})- (m : \mathbb{R})* ((m : \mathbb{R})- 1)* (\sum i : \operatorname{Fin} L,( \operatorname{coeff} i)^{4})+ 5 / 2 *( (m : \mathbb{R}))^{3}*( \alpha)^{2})*( \left\lVert \operatorname{lift} \psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.actual_sector_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.11 (completedClaim).**

$$(\operatorname{completedClaim} : \operatorname{Prop})= (\forall (m : \mathbb{N}), 1 \leq m \to \forall (c : \operatorname{CanonicalSequence})(\alpha : \mathbb{R}), (\forall (i : \mathbb{N}),( c. \operatorname{coeff} i)^{2}\leq \alpha)\to 2 * (m : \mathbb{R})* \alpha \leq 1 \to \forall (\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), \left\lVert \psi  \right\rVert= 1 \to \operatorname{completedRayleigh} (2 * m)\psi (\operatorname{canonicalTensor} c)\leq 2 * (m : \mathbb{R})* (1 - ((m : \mathbb{R})- 1)* (\sum ' (i : \mathbb{N}),( c. \operatorname{coeff} i)^{4})+ 5 / 8 *( (2 * (m : \mathbb{R})* \alpha))^{2}))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.completedClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.12 (completed_result).**

$$\operatorname{completedClaim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.completed_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.13 (countableBLinear).**

$$\forall (\operatorname{coeff} : \mathbb{N} \to \mathbb{R})(\operatorname{hq} : \operatorname{Summable} \operatorname{fun} (i : \mathbb{N})\mapsto( \operatorname{coeff} i)^{2})(m : \mathbb{N}), (\operatorname{countableBLinear} (\operatorname{coeff})(\operatorname{hq})(m): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)\to_{l} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))= (\{\operatorname{toFun} := \operatorname{countableB} \operatorname{coeff} m, \operatorname{map}_{\operatorname{add'}} :=..., \operatorname{map}_{\operatorname{smul'}} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.countableBLinear` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.14 (countable_finite_corrected_bound).**

$$\forall (m : \mathbb{N}), 1 \leq m \to \forall (c : \operatorname{CanonicalSequence})(\alpha : \mathbb{R}), (\forall (i : \mathbb{N}),( c. \operatorname{coeff} i)^{2}\leq \alpha)\to 2 * (m : \mathbb{R})* \alpha \leq 1 \to \forall (\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2))(L : \mathbb{N}),( \left\lVert \operatorname{countableBL} c. \operatorname{coeff} m L \psi  \right\rVert)^{2}\leq ((m : \mathbb{R})- (m : \mathbb{R})* ((m : \mathbb{R})- 1)* (\sum i \in \operatorname{Finset}. \operatorname{range} L,( c. \operatorname{coeff} i)^{4})+ 5 / 2 *( (m : \mathbb{R}))^{3}*( \alpha)^{2})*( \left\lVert \psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.countable_finite_corrected_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.15 (finiteEmbed).**

$$\forall (d : \mathbb{N})(N : \mathbb{N})(\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\}), (\operatorname{finiteEmbed} (\psi): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))= ((\operatorname{coordinateRename} \{\operatorname{toFun} := \operatorname{finiteOccupation}, \operatorname{inj'} :=...\}: (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(((\operatorname{lpPiLp}_{li} (\operatorname{fun} (_ : \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})\mapsto \mathbb{C})\mathbb{C}). \operatorname{symm} : (\operatorname{PiLp} 2 \operatorname{fun} (_ : \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})\mapsto \mathbb{C})\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})\mapsto \mathbb{C})2))\psi))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.16 (finiteEmbed_apply).**

$$\forall \{d N : \mathbb{N}\}(\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})(x : \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\}), ((\operatorname{finiteEmbed} \psi): (i : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\to (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})i)(\operatorname{finiteOccupation} x)= \psi. \operatorname{ofLp} x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.17 (finiteEmbed_norm).**

$$\forall \{d N : \mathbb{N}\}(\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\}), \left\lVert \operatorname{finiteEmbed} \psi  \right\rVert= \left\lVert \psi  \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.18 (finiteEmbed_outside).**

$$\forall \{d N : \mathbb{N}\}(\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}), \neg \operatorname{modesBelow} d S \to ((\operatorname{finiteEmbed} \psi): (i : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\to (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})i)S = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.19 (finiteEmbedding_dense).**

$$\forall (N : \mathbb{N})(\psi : \operatorname{lp} (\operatorname{fun} _ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}\mapsto \mathbb{C})2), \operatorname{Filter}. \operatorname{Tendsto} (\operatorname{fun} (d : \mathbb{N})\mapsto \operatorname{finiteEmbed} (d := d)(N := N)(\operatorname{finiteRestrict} (d := d)(N := N)\psi))\operatorname{Filter}. \operatorname{atTop} (\operatorname{nhds} \psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbedding_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.20 (finiteOccupation).**

$$\forall (d : \mathbb{N})(N : \mathbb{N})(x : \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\}), (\operatorname{finiteOccupation} (x): \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})= (\langle \operatorname{occupationSet} (x : \operatorname{Fin} d \to \operatorname{Bool}),...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.21 (finiteOccupation_sectorOfCountable).**

$$\forall (d N : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})(\operatorname{hS} : \operatorname{modesBelow} d S), \operatorname{finiteOccupation} (\operatorname{sectorOfCountable} d N S \operatorname{hS})= S$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteOccupation_sectorOfCountable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.22 (finiteRestrict).**

$$\forall (d : \mathbb{N})(N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), (\operatorname{finiteRestrict} (\psi): \operatorname{EuclideanSpace} \mathbb{C} \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})= (\operatorname{WithLp}. \operatorname{toLp} 2 \operatorname{fun} (x : \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})\mapsto (\psi : (i : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\to (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})i)(\operatorname{finiteOccupation} x))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteRestrict` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.23 (finite_pair_coordinate).**

$$\forall \{L s N : \mathbb{N}\}(i : \operatorname{Fin} L)(\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s_{\operatorname{1}} : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s_{\operatorname{1}} = N\})(x : \{s_{\operatorname{1}} : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s_{\operatorname{1}} = N - 2\}), \operatorname{pairCoordinate} (\operatorname{finiteEmbed} \psi)(2 * (i : \mathbb{N}))(2 * (i : \mathbb{N})+ 1)((\operatorname{finiteOccupation} x): \operatorname{Finset} \mathbb{N})= (((\operatorname{Matrix}. \operatorname{toEuclideanLin} : \operatorname{Matrix} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\mathbb{C} \to \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\to_{l} [\mathbb{C}]\operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool}))(\operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{downMode} i)* \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{upMode} i)): \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\to \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool}))(\operatorname{lift} \psi)). \operatorname{ofLp} (x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finite_pair_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.24 (modesBelow).**

$$\forall (N : \mathbb{N})(d : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}), (\operatorname{modesBelow} (d)(S): \operatorname{Prop})= (\forall n \in (S : \operatorname{Finset} \mathbb{N}), n < d)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.modesBelow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.25 (occupationOfSet).**

$$\forall (d : \mathbb{N})(S : \operatorname{Finset} \mathbb{N})(\operatorname{aAnon} : \operatorname{Fin} d), (\operatorname{occupationOfSet} (d)(S)(\operatorname{aAnon}): \operatorname{Bool})= (\operatorname{decide} ((\operatorname{aAnon} : \mathbb{N})\in S))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.occupationOfSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.26 (occupationSet).**

$$\forall (d : \mathbb{N})(x : \operatorname{Fin} d \to \operatorname{Bool}), (\operatorname{occupationSet} (x): \operatorname{Finset} \mathbb{N})= (\operatorname{Finset}. \operatorname{map} \{\operatorname{toFun} := \operatorname{Fin}. \operatorname{val}, \operatorname{inj'} :=...\}(\operatorname{occupiedModes} x))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.occupationSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.27 (sectorOfCountable).**

$$\forall (d : \mathbb{N})(N : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})(\operatorname{hS} : \operatorname{modesBelow} d S), (\operatorname{sectorOfCountable} (d)(N)(S)(\operatorname{hS}): \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\})= (\langle \operatorname{occupationOfSet} d (S : \operatorname{Finset} \mathbb{N}),...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.sectorOfCountable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

## References

- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.actual_sector_bound`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.completedClaim`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.completed_result`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.countableBLinear`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.countable_finite_corrected_bound`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.doublePairs_sector`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed_apply`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed_norm`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbed_outside`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteEmbedding_dense`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteOccupation`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteOccupation_sectorOfCountable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finiteRestrict`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.finite_pair_coordinate`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.modesBelow`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.occupationOfSet`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.occupationSet`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.occupiedModes`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realB`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK_nonneg`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK_row`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.realK_symm`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.sectorOfCountable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.standardB_sector_support`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound.standardK_real`
- Dependency: [D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding](CanonicalRdmAndPadding.md)
