# PhysicalContractionRdmBridge

## Abstract

Completed fermionic operators and their correlational estimate.

All types range over arbitrary universes. Underscores in declaration names appear as typographical subscripts and retain the full Lean spelling. Juxtaposition and the displayed binders use Lean function-application syntax; sums and products use Lean's typed binder syntax. Bracketed typeclass requirements are anonymous instances. Real and complex casts retain their target-type annotation. Submodules and lp spaces in type position carry the ordinary CoeSort coercion. Nat subtraction is truncated, Nat division is Euclidean division, and field division is written with a slash. Named constants retain their actual Lean spelling. The three-dot marker suppresses only proof fields and proof arguments, which are proof-irrelevant; it never suppresses mathematical data. The additional h and g binders in construction equations stand for proofs of the displayed propositions; proof irrelevance makes the equation independent of their choice. Completed tensors are UniformSpace.Completion of the Mathlib Hilbert tensor product.

**Definition 1.1 (AdaptedChart).**

$$\operatorname{AdaptedChart}. \operatorname{mk} : \{H : \operatorname{Type}\}\to [\operatorname{NormedAddCommGroup} H]\to [\operatorname{InnerProductSpace} \mathbb{C} H]\to \{\iota : \operatorname{Type}\}\to \{e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N}\}\to \{v : \iota \times \operatorname{Fin} 2 \to H\}\to (\operatorname{index} : \operatorname{Set} H)\to (\operatorname{basis} : \operatorname{HilbertBasis} (\operatorname{index} : \operatorname{Type})\mathbb{C} H)\to (\operatorname{label} : \operatorname{Function}. \operatorname{Embedding} (\operatorname{index} : \operatorname{Type})\mathbb{N})\to (\operatorname{pairs} : \iota \times \operatorname{Fin} 2 \to (\operatorname{index} : \operatorname{Type}))\to (\forall (p : \iota \times \operatorname{Fin} 2), (\operatorname{basis} : (\operatorname{index} : \operatorname{Type})\to H)(\operatorname{pairs} p)= v p)\to (\forall (i : \iota), (\operatorname{label} : (\operatorname{index} : \operatorname{Type})\to \mathbb{N})(\operatorname{pairs} (i, 0))= 4 * (e : \iota \to \mathbb{N})i)\to (\forall (i : \iota), (\operatorname{label} : (\operatorname{index} : \operatorname{Type})\to \mathbb{N})(\operatorname{pairs} (i, 1))= 4 * (e : \iota \to \mathbb{N})i + 1)\to \operatorname{AdaptedChart} e v$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.AdaptedChart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.2 (single_pair_composition).**

$$\forall (n i j : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 2\})\mapsto \mathbb{C})2)), (\operatorname{countableAnnihilate} n j : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto \mathbb{C})2))((\operatorname{countableAnnihilate} (n + 1)i : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1 + 1\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\})\mapsto \mathbb{C})2))\psi)= (\operatorname{pairContract} (n + 2)i j : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 2\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 2 - 2\})\mapsto \mathbb{C})2))\psi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.single_pair_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.3 (countableAnnihilate).**

$$\forall (n : \mathbb{N})(i : \mathbb{N}), (\operatorname{countableAnnihilate} (n)(i): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto \mathbb{C})2))= (\operatorname{partialPullCLM} (\operatorname{fun} (R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto \neg (i \in R. \operatorname{val}))(\operatorname{fun} (R : \{R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\}/ / \neg (i \in R. \operatorname{val})\})\mapsto (\langle \operatorname{insert} i R. \operatorname{val}. \operatorname{val},...\rangle: \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\}))... (\operatorname{fun} (R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto( (- 1 : \mathbb{C}))^{R. \operatorname{val}. \operatorname{filter} (\operatorname{fun} (k : \mathbb{N})\mapsto k < i).\operatorname{card}})...)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.countableAnnihilate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.4 (tensorSlice_apply).**

$$\forall (n i : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2))(t : \operatorname{Fin} n \to \mathbb{N}), (((\operatorname{tensorSlice} n i : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} n \to \mathbb{N})\mapsto \mathbb{C})2))\psi): (i : \operatorname{Fin} n \to \mathbb{N})\to (\operatorname{fun} (_ : \operatorname{Fin} n \to \mathbb{N})\mapsto \mathbb{C})i)t = (\psi : (i : \operatorname{Fin} (n + 1)\to \mathbb{N})\to (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})i)(\operatorname{Fin}. \operatorname{cons} i t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.tensorSlice_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.5 (tensorSlice_antisymmetric).**

$$\forall (n i : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2)), \operatorname{IsAntisymmetric} (n + 1)\psi \to \operatorname{IsAntisymmetric} n ((\operatorname{tensorSlice} n i : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} n \to \mathbb{N})\mapsto \mathbb{C})2))\psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.tensorSlice_antisymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.6 (tensorSlice).**

$$\forall (n : \mathbb{N})(i : \mathbb{N}), (\operatorname{tensorSlice} (n)(i): (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} n \to \mathbb{N})\mapsto \mathbb{C})2))= (\operatorname{partialPullCLM} (\operatorname{fun} (_ : \operatorname{Fin} n \to \mathbb{N})\mapsto \operatorname{True})(\operatorname{fun} (t : \{_ : \operatorname{Fin} n \to \mathbb{N} / / \operatorname{True}\})\mapsto \operatorname{Fin}. \operatorname{cons} i (t : \operatorname{Fin} n \to \mathbb{N}))... (\operatorname{fun} (_ : \operatorname{Fin} n \to \mathbb{N})\mapsto 1)...)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.tensorSlice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.7 (slaterBasis_apply).**

$$\forall (n : \mathbb{N})(S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\}), (\operatorname{slaterHilbertBasis} n : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\}\to (\operatorname{antisymmetricSubmodule} n))S = \operatorname{slaterAntiVector} n S$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.slaterBasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.8 (antiHead_intertwining).**

$$\forall (n i : \mathbb{N})(\psi : (\operatorname{antisymmetricSubmodule} (n + 1))), ((\operatorname{slaterHilbertBasis} n). \operatorname{repr} : (\operatorname{antisymmetricSubmodule} n)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto \mathbb{C})2))((\operatorname{antiHead} n i : (\operatorname{antisymmetricSubmodule} (n + 1))\to (\operatorname{antisymmetricSubmodule} n))\psi)= (\operatorname{countableAnnihilate} n i : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto \mathbb{C})2))(((\operatorname{slaterHilbertBasis} (n + 1)). \operatorname{repr} : (\operatorname{antisymmetricSubmodule} (n + 1))\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\})\mapsto \mathbb{C})2))\psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.antiHead_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.9 (antiHead).**

$$\forall (n : \mathbb{N})(i : \mathbb{N}), (\operatorname{antiHead} (n)(i): (\operatorname{antisymmetricSubmodule} (n + 1))\to_{L} [\mathbb{C}](\operatorname{antisymmetricSubmodule} n))= (\operatorname{let} x_{x_{\operatorname{LinearMap}}} := \{\operatorname{toFun} := \operatorname{fun} (\psi : (\operatorname{antisymmetricSubmodule} (n + 1)))\mapsto \langle (\operatorname{Real}. \operatorname{sqrt} ((n : \mathbb{R})+ 1): \mathbb{C})\cdot (\operatorname{tensorSlice} n i : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} n \to \mathbb{N})\mapsto \mathbb{C})2))(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} (n + 1)\to \mathbb{N})\mapsto \mathbb{C})2)),...\rangle, \operatorname{map}_{\operatorname{add'}} :=..., \operatorname{map}_{\operatorname{smul'}} :=...\}; \{\operatorname{toLinearMap} := x_{x_{\operatorname{LinearMap}}}, \operatorname{cont} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.antiHead` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.10 (adaptedChart).**

$$\forall (H : \operatorname{Type})[\operatorname{NormedAddCommGroup} H][\operatorname{InnerProductSpace} \mathbb{C} H][\operatorname{CompleteSpace} H][\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} H](\iota : \operatorname{Type})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(v : \iota \times \operatorname{Fin} 2 \to H)(\operatorname{hv} : \operatorname{Orthonormal} \mathbb{C} v)(h : \operatorname{Nonempty} (\operatorname{AdaptedChart} e v)), (\operatorname{adaptedChart} (e)(v)(\operatorname{hv}): \operatorname{AdaptedChart} e v)= (\operatorname{Classical}. \operatorname{choice} h)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.adaptedChart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.11 (canonicalPair_countable).**

$$\forall \{H : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} H][\operatorname{InnerProductSpace} \mathbb{C} H][\operatorname{CompleteSpace} H][\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} H]\{\iota : \operatorname{Type}\}(v : \iota \times \operatorname{Fin} 2 \to H), \operatorname{Orthonormal} \mathbb{C} v \to \operatorname{Countable} \iota$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.canonicalPair_countable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.12 (particleAntiEmbedding).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(N : \mathbb{N}), (\operatorname{particleAntiEmbedding} (X)(b)(e)(N): (\operatorname{particleExterior} X b e N)\to_{li} [\mathbb{C}](\operatorname{antisymmetricSubmodule} N))= (\{\operatorname{toFun} := \operatorname{fun} (\psi : (\operatorname{particleExterior} X b e N))\mapsto \langle (\operatorname{particleCoordinates} X b e N : (\operatorname{particleObject} X N). \operatorname{carrier} \to (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} N \to \mathbb{N})\mapsto \mathbb{C})2))(\psi : (\operatorname{particleObject} X N). \operatorname{carrier}),...\rangle, \operatorname{map}_{\operatorname{add'}} :=..., \operatorname{map}_{\operatorname{smul'}} :=..., \operatorname{norm}_{\operatorname{map'}} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleAntiEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.13 (particleBasis).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier}), \operatorname{particleBasis} X b 0 = \operatorname{HilbertBasis}. \operatorname{ofRepr} (\operatorname{coordinateEquiv} (\operatorname{Equiv}. \operatorname{ofUnique} (\operatorname{Fin} 0 \to X. \operatorname{carrier})(\operatorname{Fin} 0 \to \iota)))\land (\forall (n : \mathbb{N}), \operatorname{particleBasis} X b (n + 1)= \operatorname{tensorTowerTupleBasis} X b n)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.14 (particleCoordinates).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N}), \operatorname{particleCoordinates} X b e 0 = (\operatorname{coordinateRename} (\operatorname{Function}. \operatorname{Embedding}. \operatorname{arrowCongrRight} (\gamma := \operatorname{Fin} 0)e)). \operatorname{comp} (\operatorname{particleBasis} X b 0). \operatorname{repr}. \operatorname{toLinearIsometry} \land (\forall (n : \mathbb{N}), \operatorname{particleCoordinates} X b e (n + 1)= \operatorname{sourceTensorCoordinates} X b e n)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The zero branch gives vacuum coordinates; the positive branch uses sourceTensorCoordinates.

**Definition 1.15 (particleExterior).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N}), \operatorname{particleExterior} X b e 0 = \operatorname{top} \land (\forall (n : \mathbb{N}), \operatorname{particleExterior} X b e (n + 1)= \operatorname{sourceExterior} X b e n)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleExterior` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The zero-particle sector is the scalar vacuum. Every positive-particle sector uses the literal physical exterior definition sourceExterior.

**Definition 1.16 (particleHead).**

$$\forall (X : \operatorname{HilbertObject})(f : X. \operatorname{carrier})(n : \mathbb{N}), (\operatorname{particleHead} (X)(f)(n): (\operatorname{particleObject} X (n + 1)). \operatorname{carrier} \to_{L} [\mathbb{C}](\operatorname{particleObject} X n). \operatorname{carrier})= (\operatorname{match} n \operatorname{with} | 0 \mapsto (\operatorname{lp}. \operatorname{singleContinuousLinearMap} \mathbb{C} (\operatorname{fun} (_ : \operatorname{Fin} 0 \to X. \operatorname{carrier})\mapsto \mathbb{C})2 \operatorname{fun} (k : \operatorname{Fin} 0)\mapsto k. \operatorname{elim0})\circ_{\operatorname{SL}} (\operatorname{innerSL} \mathbb{C} : (\operatorname{particleObject} X (0 + 1)). \operatorname{carrier} \to (\operatorname{particleObject} X (0 + 1)). \operatorname{carrier} \to_{L} [\mathbb{C}]\mathbb{C})f | n. \operatorname{succ} \mapsto \operatorname{tensorHead} f)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleHead` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.17 (particleObject).**

$$\forall (X : \operatorname{HilbertObject}), \operatorname{particleObject} X 0 = \operatorname{vacuumObject} X \land (\forall (n : \mathbb{N}), \operatorname{particleObject} X (n + 1)= \operatorname{tensorTower} X n)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleObject` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.18 (particleOccupation).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(N : \mathbb{N}), (\operatorname{particleOccupation} (X)(b)(e)(N): (\operatorname{particleExterior} X b e N)\to_{li} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))= ((\operatorname{slaterHilbertBasis} N). \operatorname{repr}. \operatorname{toLinearIsometry}. \operatorname{comp} (\operatorname{particleAntiEmbedding} X b e N))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.19 (sourceAnnihilate).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(f : X. \operatorname{carrier}), (\operatorname{sourceAnnihilate} (X)(b)(e)(n)(f): (\operatorname{particleExterior} X b e (n + 1))\to_{L} [\mathbb{C}](\operatorname{particleExterior} X b e n))= (\operatorname{let} x_{x_{\operatorname{LinearMap}}} := \{\operatorname{toFun} := \operatorname{fun} (\psi : (\operatorname{particleExterior} X b e (n + 1)))\mapsto \langle (\operatorname{Real}. \operatorname{sqrt} ((n : \mathbb{R})+ 1): \mathbb{C})\cdot (\operatorname{particleHead} X f n : (\operatorname{particleObject} X (n + 1)). \operatorname{carrier} \to (\operatorname{particleObject} X n). \operatorname{carrier})(\psi : (\operatorname{particleObject} X (n + 1)). \operatorname{carrier}),...\rangle, \operatorname{map}_{\operatorname{add'}} :=..., \operatorname{map}_{\operatorname{smul'}} :=...\}; \{\operatorname{toLinearMap} := x_{x_{\operatorname{LinearMap}}}, \operatorname{cont} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceAnnihilate` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The fermionic annihilator at an arbitrary one-particle vector f contracts the first tensor factor against f, with the physical square-root particle-number normalization.

**Definition 1.20 (sourceCreate).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(f : X. \operatorname{carrier}), (\operatorname{sourceCreate} (X)(b)(e)(n)(f): (\operatorname{particleExterior} X b e n)\to_{L} [\mathbb{C}](\operatorname{particleExterior} X b e (n + 1)))= ((\operatorname{ContinuousLinearMap}. \operatorname{adjoint} : ((\operatorname{particleExterior} X b e (n + 1))\to_{L} [\mathbb{C}](\operatorname{particleExterior} X b e n))\to (\operatorname{particleExterior} X b e n)\to_{L} [\mathbb{C}](\operatorname{particleExterior} X b e (n + 1)))(\operatorname{sourceAnnihilate} X b e n f))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceCreate` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The fermionic creation operator at f is the Hilbert adjoint of sourceAnnihilate at f.

**Definition 1.21 (sourceGamma).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(\psi : (\operatorname{particleExterior} X b e (n + 2)))(h : \exists \Gamma : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})\to_{L} [\mathbb{C}]\operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}), \forall (f_{1} f_{2} g_{1} g_{2} : X. \operatorname{carrier}), \operatorname{inner} \mathbb{C} ((\operatorname{TensorProduct}. \operatorname{tmul} \mathbb{C} f_{1} f_{2} : \operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}))(\Gamma ((\operatorname{TensorProduct}. \operatorname{tmul} \mathbb{C} g_{1} g_{2} : \operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})))= \operatorname{inner} \mathbb{C} \psi (\operatorname{sourceCreate} X b e (n + 1)g_{1} (\operatorname{sourceCreate} X b e n g_{2} (\operatorname{sourceAnnihilate} X b e n f_{2} (\operatorname{sourceAnnihilate} X b e (n + 1)f_{1} \psi))))), (\operatorname{sourceGamma} (X)(b)(e)(n)(\psi): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})\to_{L} [\mathbb{C}]\operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}))= (\operatorname{Classical}. \operatorname{choose} h)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceGamma` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

Christiansen, Section 1, p. 1, equation (1.1): “Given a normalized state Ψ ∈ ⋀ᴺ𝔥 we define the 2-body operator associated to Ψ, γ₂^Ψ : 𝔥 ⊗ 𝔥 → 𝔥 ⊗ 𝔥, by ⟨φ₁ ⊗ φ₂, γ₂^Ψ(ψ₁ ⊗ ψ₂)⟩ = ⟨Ψ, c*(ψ₁)c*(ψ₂)c(φ₂)c(φ₁)Ψ⟩ for any φ₁, φ₂, ψ₁, ψ₂ ∈ 𝔥, where c*(·) and c(·) denote the fermionic creation and annihilation operators.” The bounded operator is selected from the operators satisfying this arbitrary-vector kernel equation. The private Gram construction proves existence and uniqueness and transports this operator on the result’s live Rayleigh path. Annihilation is defined at every one-particle vector; creation is its Hilbert adjoint. Source tensor and particle carriers are actual completed Hilbert tensor powers, and the basis trace normalization is proved in sourceGamma_trace.

**Theorem 1.22 (sourceGamma_trace).**

$$\forall \{\iota : \operatorname{Type}\}(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(\psi : (\operatorname{particleExterior} X b e (n + 2))), \sum ' (p : \iota \times \iota), (\operatorname{inner} \mathbb{C} ((\operatorname{tensorHilbertBasis} b b : \iota \times \iota \to \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}))p)((\operatorname{sourceGamma} X b e n \psi : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})\to \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}))((\operatorname{tensorHilbertBasis} b b : \iota \times \iota \to \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}))p))). \operatorname{re} = (((n + 2)* (n + 1)): \mathbb{R})*( \left\lVert \psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceGamma_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The physical two-body Gram operator has trace N(N−1) for a unit vector, with N = n+2. The displayed basis trace is an absolutely summable series, rather than a formal finite-dimensional trace.

**Definition 1.23 (sourceRayleigh).**

$$\forall (\iota : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(\psi : (\operatorname{particleExterior} X b e (n + 2)))(\varphi : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})), (\operatorname{sourceRayleigh} (X)(b)(e)(n)(\psi)(\varphi): \mathbb{R})= ((\operatorname{inner} \mathbb{C} \varphi ((\operatorname{sourceGamma} X b e n \psi : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})\to \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier}))\varphi)). \operatorname{re})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceRayleigh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.24 (sourceRayleigh_transport).**

$$\forall \{\iota : \operatorname{Type}\}(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(\psi : (\operatorname{particleExterior} X b e (n + 2)))(\varphi : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})), \operatorname{sourceRayleigh} X b e n \psi \varphi = \operatorname{completedRayleigh} (n + 2)((\operatorname{particleOccupation} X b e (n + 2): (\operatorname{particleExterior} X b e (n + 2))\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 2\})\mapsto \mathbb{C})2))\psi)((\operatorname{tensorCoordinateEmbedding} b e : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} X. \operatorname{carrier} X. \operatorname{carrier})\to (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))\varphi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceRayleigh_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.25 (source_single_intertwining).**

$$\forall \{\iota : \operatorname{Type}\}(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \iota \mathbb{C} X. \operatorname{carrier})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(n : \mathbb{N})(i : \iota)(\psi : (\operatorname{particleExterior} X b e (n + 1))), (\operatorname{particleOccupation} X b e n : (\operatorname{particleExterior} X b e n)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto \mathbb{C})2))((\operatorname{sourceAnnihilate} X b e n ((b : \iota \to X. \operatorname{carrier})i): (\operatorname{particleExterior} X b e (n + 1))\to (\operatorname{particleExterior} X b e n))\psi)= (\operatorname{countableAnnihilate} n ((e : \iota \to \mathbb{N})i): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n\})\mapsto \mathbb{C})2))((\operatorname{particleOccupation} X b e (n + 1): (\operatorname{particleExterior} X b e (n + 1))\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = n + 1\})\mapsto \mathbb{C})2))\psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.source_single_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.26 (vacuumObject).**

$$\forall (X : \operatorname{HilbertObject}), (\operatorname{vacuumObject} (X): \operatorname{HilbertObject})= (\{\operatorname{carrier} := (\operatorname{lp} (\operatorname{fun} (_ : \operatorname{Fin} 0 \to X. \operatorname{carrier})\mapsto \mathbb{C})2), \operatorname{normed} := \operatorname{inferInstance}, \operatorname{innerProduct} := \operatorname{inferInstance}, \operatorname{complete} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.vacuumObject` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

## References

- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.AdaptedChart`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.adaptedChart`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.antiHead`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.antiHead_intertwining`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.canonicalPair_countable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.countableAnnihilate`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleAntiEmbedding`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleBasis`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleCoordinates`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleExterior`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleHead`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleObject`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.particleOccupation`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.single_pair_composition`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.slaterBasis_apply`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceAnnihilate`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceCreate`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceGamma`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceGamma_trace`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceRayleigh`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.sourceRayleigh_transport`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.source_single_intertwining`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.tensorSlice`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.tensorSlice_antisymmetric`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.tensorSlice_apply`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge.vacuumObject`
- Dependency: [D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry](CompletedTensorSlaterGeometry.md)
