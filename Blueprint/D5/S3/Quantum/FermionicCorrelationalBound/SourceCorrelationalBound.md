# SourceCorrelationalBound

## Abstract

Completed fermionic operators and their correlational estimate.

All types range over arbitrary universes. Underscores in declaration names appear as typographical subscripts and retain the full Lean spelling. Juxtaposition and the displayed binders use Lean function-application syntax; sums and products use Lean's typed binder syntax. Bracketed typeclass requirements are anonymous instances. Real and complex casts retain their target-type annotation. Submodules and lp spaces in type position carry the ordinary CoeSort coercion. Nat subtraction is truncated, Nat division is Euclidean division, and field division is written with a slash. Named constants retain their actual Lean spelling. The three-dot marker suppresses only proof fields and proof arguments, which are proof-irrelevant; it never suppresses mathematical data. The additional h and g binders in construction equations stand for proofs of the displayed propositions; proof irrelevance makes the equation independent of their choice. Completed tensors are UniformSpace.Completion of the Mathlib Hilbert tensor product.

**Definition 1.1 (canonicalIndex).**

$$\forall (H : \operatorname{Type})[\operatorname{NormedAddCommGroup} H][\operatorname{InnerProductSpace} \mathbb{C} H][\operatorname{CompleteSpace} H][\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} H](\iota : \operatorname{Type})(v : \iota \times \operatorname{Fin} 2 \to H)(\operatorname{hv} : \operatorname{Orthonormal} \mathbb{C} v)(h : \exists f : \iota \to \mathbb{N}, \operatorname{Function}. \operatorname{Injective} f), (\operatorname{canonicalIndex} (v)(\operatorname{hv}): \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})= (\{\operatorname{toFun} := \operatorname{Classical}. \operatorname{choose} h, \operatorname{inj'} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.canonicalIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.2 (claim).**

$$(\operatorname{claim} : \operatorname{Prop})= (\forall (H : \operatorname{Type})[\operatorname{NormedAddCommGroup} H][\operatorname{InnerProductSpace} \mathbb{C} H][\operatorname{CompleteSpace} H][\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} H](\iota : \operatorname{Type})(v : \iota \times \operatorname{Fin} 2 \to H)(\operatorname{hv} : \operatorname{Orthonormal} \mathbb{C} v)(c : \operatorname{CanonicalFamily} \iota)(\phi : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} H H)), \operatorname{HasSum} (\operatorname{fun} (i : \iota)\mapsto ((c. \operatorname{coeff} i): \mathbb{C})\cdot \operatorname{sourcePairWedge} v i)\phi \to \forall (m : \mathbb{N}), (2 * (m : \mathbb{R})+ 2)*( \operatorname{lambdaMax} c)^{2}\leq 1 \to \operatorname{have} d := \operatorname{adaptedChart} (\operatorname{canonicalIndex} v \operatorname{hv})v \operatorname{hv} ; \forall (\psi : (\operatorname{tensorTower} (\operatorname{sourceHilbertObject} H)(2 * m + 1)). \operatorname{carrier})(\operatorname{hanti} : \forall (\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} (2 * m + 2))), (\operatorname{tensorPermutation} (\operatorname{sourceHilbertObject} H)d. \operatorname{basis} (2 * m + 1)\sigma : (\operatorname{tensorTower} (\operatorname{sourceHilbertObject} H)(2 * m + 1)). \operatorname{carrier} \to (\operatorname{tensorTower} (\operatorname{sourceHilbertObject} H)(2 * m + 1)). \operatorname{carrier})\psi = \operatorname{permutationPhase} (2 * m + 2)\sigma \cdot \psi), \left\lVert \psi  \right\rVert= 1 \to \operatorname{sourceRayleigh} (\operatorname{sourceHilbertObject} H)d. \operatorname{basis} d. \operatorname{label} (2 * m)(\operatorname{physicalParticle} (\operatorname{sourceHilbertObject} H)d. \operatorname{basis} d. \operatorname{label} (2 * m + 1)\psi \operatorname{hanti})\phi \leq (2 * (m : \mathbb{R})+ 2)* (1 - (m : \mathbb{R})* (\sum ' (i : \iota),( c. \operatorname{coeff} i)^{4})+ 5 / 8 *( ((2 * (m : \mathbb{R})+ 2)*( \operatorname{lambdaMax} c)^{2}))^{2}))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

Christiansen, Section 1.1, p. 4, Conjecture 3, verbatim: “Let Φ ∈ 𝔥 ∧ 𝔥 be normalized with canonical form Φ = ∑_{k=1}^{∞} λ_k u_k ∧ v_k. Then there exists a constant C > 0, independent of Φ, such that for every N ∈ 2ℕ with N λ_max² ≤ 1 sup_{Ψ ∈ ⋀ᴺ𝔥, ‖Ψ‖=1} ⟨Φ, γ₂^Ψ Φ⟩ ≤ N(1 − (N−2)/2 ∑_{k=1}^{∞} λ_k⁴ + C(N λ_max²)²).”. The displayed claim fixes C = 5/8. H is an arbitrary separable complex Hilbert space; Φ has the supplied normalized canonical form, v(i,0) and v(i,1) are mutually orthonormal, and m parametrizes N = 2m + 2. The physical tensor permutation action defines fermionic antisymmetry. sourceRayleigh uses the literal creation/annihilation-kernel RDM, with trace N(N−1). lambdaMax is the attained maximum. The source supremum is encoded by quantifying every normalized ψ.

**Definition 1.3 (lambdaMax).**

$$\forall (\iota : \operatorname{Type})(c : \operatorname{CanonicalFamily} \iota)(h : \exists a : \mathbb{R}, \operatorname{IsGreatest} (\operatorname{Set}. \operatorname{range} c. \operatorname{coeff})a), (\operatorname{lambdaMax} (c): \mathbb{R})= (\operatorname{Classical}. \operatorname{choose} h)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.lambdaMax` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.4 (physicalParticle).**

$$\forall (\kappa : \operatorname{Type})(X : \operatorname{HilbertObject})(b : \operatorname{HilbertBasis} \kappa \mathbb{C} X. \operatorname{carrier})(\operatorname{label} : \operatorname{Function}. \operatorname{Embedding} \kappa \mathbb{N})(n : \mathbb{N})(\psi : (\operatorname{tensorTower} X n). \operatorname{carrier})(\operatorname{h\psi} : \forall (\sigma : \operatorname{Equiv}. \operatorname{Perm} (\operatorname{Fin} (n + 1))), (\operatorname{tensorPermutation} X b n \sigma : (\operatorname{tensorTower} X n). \operatorname{carrier} \to (\operatorname{tensorTower} X n). \operatorname{carrier})\psi = \operatorname{permutationPhase} (n + 1)\sigma \cdot \psi), (\operatorname{physicalParticle} (X)(b)(\operatorname{label})(n)(\psi)(\operatorname{h\psi}): (\operatorname{particleExterior} X b \operatorname{label} (n + 1)))= (\langle \psi,...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.physicalParticle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.5 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The claim holds with C = 5/8. The weighted occupation-row estimate retains the fourth moment, spectator modes, weight one at zero coefficient, and the original unrenormalized cutoffs.

## References

- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.canonicalIndex`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.claim`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.lambdaMax`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.physicalParticle`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.result`
- Dependency: [D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound](CompletedCorrelationalBound.md)
- Dependency: [D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge](PhysicalContractionRdmBridge.md)
