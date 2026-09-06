/- GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/FiniteMoorePenroseInverse
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.SingularValues]
   utility: none
   digest: The finite Moore-Penrose inverse satisfies all four Penrose identities and is unique. -/

import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Authors: Jon Crall, GPT-5.6 Thinking; singular-basis prerequisites:
Jon Crall, GPT-5.6 High, Claude Fable 5.

A17.2 source port from AIQ-Kitware/aiq-dkps-formalization,
commit 20461e477e1ae464d6abac1dade3188c29109b8c,
ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean and
ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean.
Modified: repository header and namespace, minimal direct Mathlib import,
selected only the inverse construction, its laws and uniqueness.
Renamed upstream ite_eq_left/right to pinned if_pos/if_neg.
The upstream license is retained verbatim below. Upstream vendor/lean/NOTICE.md
exists; its applicable notices and the proof-source attribution chain follow.
No claim of an original local proof is made.
Consumer: FiniteSynthesisGramDistance.finite_synthesis_gram_distance.
Retirement: replace this port by direct imports when this repository's pinned
Mathlib contains equivalent declarations, following frozen-change governance.

Proof-source chain: System.lean credits the Apache-2.0 matrix-Euclidean
development in vendor/lean/lean-stat-learning-theory/SingularSystemGram.excerpt.lean
by Yuanhe Zhang, Jason D. Lee and Fanghui Liu. Its Proof sources paragraph says
the construction was restated intrinsically for linear maps, using the excerpt
as a route map with no code copied verbatim. This attribution applies to the
three selected prerequisites: rightSingularBasis,
adjointCompSelf_apply_rightSingularBasis, and
apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero.
The excerpt and upstream vendor/lean/manifest.toml identify the original as
https://github.com/YuanheZ/lean-stat-learning-theory,
SLT/MatrixInfra/Basic.lean at commit
216e578c9576bab6b0abc3ba6c65762536768e96,
blob 8c7dd1aaeaedd6c702c28fee2845d9f66cecf219.
Additional notices from that original source and its LICENSE:
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Copyright 2026 lean-stat-learning-theory contributors

Retained text from vendor/lean/NOTICE.md at the Kitware commit above:

The files under `vendor/lean/` are source references, not linked build dependencies.

## Lean community / Mathlib

Selected excerpts from Mathlib at the project-pinned revision.
Copyright is retained by the named upstream authors and Mathlib contributors.
Licensed under the Apache License, Version 2.0.
See `LICENSES/Apache-2.0.txt` and `manifest.toml`.

## Yuanhe Zhang, Jason D. Lee, Fanghui Liu / lean-stat-learning-theory

Copyright (c) 2026 Yuanhe Zhang.
Licensed under the Apache License, Version 2.0.
See `LICENSES/Apache-2.0.txt` and `manifest.toml`.

The paths in that retained text are relative to upstream vendor/lean/ at the
Kitware commit above. Its LICENSES/Apache-2.0.txt is byte-identical to the full
license retained below. The Mathlib notice is retained for the spectral route;
this port imports this repository's pinned Mathlib directly, not vendor excerpts.
Omitted NOTICE entries: Jacob Barr / jbarrcfl mathlib4 fork and Dronmong /
drifting-identifiability. The upstream manifest associates them with
TopSingularValue.excerpt.lean and FiniteFrameBound.excerpt.lean respectively;
neither excerpt nor its top-singular-value norm or finite-frame-bound results
is part of the selected inverse construction and three-prerequisite closure.
No unrelated vendor source code is imported by this port.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The right singular basis, chosen as the sorted orthonormal eigenbasis of `A†A`. -/
noncomputable def rightSingularBasis (A : E →ₗ[𝕜] F) :
    OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- The right singular basis diagonalizes `A†A`. -/
theorem adjointCompSelf_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    (A.adjoint.comp A) (rightSingularBasis A i) =
      (((A.singularValues i : ℝ) ^ 2 : ℝ) : 𝕜) • rightSingularBasis A i := by
  have h := A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [← A.sq_singularValues_fin rfl i] at h
  exact h

/-- A right singular vector with zero singular value lies in the kernel of `A`. -/
theorem apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
    (A : E →ₗ[𝕜] F) {i : Fin (finrank 𝕜 E)}
    (hi : A.singularValues i = 0) :
    A (rightSingularBasis A i) = 0 := by
  have hker : rightSingularBasis A i ∈ (A.adjoint ∘ₗ A).ker := by
    rw [LinearMap.mem_ker, adjointCompSelf_apply_rightSingularBasis A i, hi]
    simp
  rw [LinearMap.ker_adjoint_comp_self] at hker
  exact LinearMap.mem_ker.mp hker

/-- **Penrose's four conditions**, as a `Prop`-valued structure with named accessors rather
than four anonymous hypotheses.

The four conditions *are* Penrose's definition of a pseudoinverse, so packaging them is what
lets the uniqueness theorem below read as *the Moore--Penrose inverse is unique*, and gives
the relation somewhere to carry its own theory. -/
structure IsMoorePenroseInverse (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) : Prop where
  /-- `B` is a generalized inverse of `A`. -/
  comp_comp_self : A ∘ₗ B ∘ₗ A = A
  /-- `A` is a generalized inverse of `B`. -/
  comp_comp_self' : B ∘ₗ A ∘ₗ B = B
  /-- The idempotent `A B` onto the range of `A` is self-adjoint. -/
  isSymmetric_comp : (A ∘ₗ B).IsSymmetric
  /-- The idempotent `B A` onto the range of `B` is self-adjoint. -/
  isSymmetric_comp' : (B ∘ₗ A).IsSymmetric

/-- The finite-dimensional Moore--Penrose inverse, reconstructed from the
right singular basis and the Gram eigenvalues. -/
noncomputable def moorePenroseInverse (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E),
    (((((A.singularValues i) ^ 2 : ℝ) : 𝕜))⁻¹) •
      (InnerProductSpace.rankOne 𝕜
        (rightSingularBasis A i)
        (A (rightSingularBasis A i))).toLinearMap

/-- Gram orthogonality of the images of the right singular basis. -/
theorem inner_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i j : Fin (finrank 𝕜 E)) :
    inner 𝕜 (A (rightSingularBasis A i))
        (A (rightSingularBasis A j)) =
      (((A.singularValues j) ^ 2 : ℝ) : 𝕜) *
        inner 𝕜 (rightSingularBasis A i)
          (rightSingularBasis A j) := by
  rw [← LinearMap.adjoint_inner_right,
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    show A.adjoint (A (rightSingularBasis A j)) =
      (A.adjoint.comp A) (rightSingularBasis A j) from rfl,
    adjointCompSelf_apply_rightSingularBasis,
    inner_smul_right]

/-- The pseudoinverse followed by the original map fixes each right singular
vector with nonzero singular value. -/
theorem moorePenroseInverse_apply_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) {k : Fin (finrank 𝕜 E)}
    (hk : A.singularValues k ≠ 0) :
    moorePenroseInverse A (A (rightSingularBasis A k)) =
      rightSingularBasis A k := by
  classical
  unfold moorePenroseInverse
  rw [LinearMap.sum_apply]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro i _ hik
    rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply,
      inner_apply_rightSingularBasis]
    have hinner : inner 𝕜 (rightSingularBasis A i)
        (rightSingularBasis A k) = 0 := by
      simp [orthonormal_iff_ite.mp
        (rightSingularBasis A).orthonormal i k, if_neg hik]
    rw [hinner, mul_zero, zero_smul, smul_zero]
  · intro hkmem
    exact absurd (Finset.mem_univ k) hkmem
  · rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply,
      inner_apply_rightSingularBasis]
    have hinner : inner 𝕜 (rightSingularBasis A k)
        (rightSingularBasis A k) = 1 := by
      simp
    rw [hinner, mul_one, smul_smul]
    have hσ : ((((A.singularValues k) ^ 2 : ℝ) : 𝕜)) ≠ 0 := by
      exact RCLike.ofReal_ne_zero.mpr (pow_ne_zero 2 hk)
    rw [inv_mul_cancel₀ hσ, one_smul]

/-- The first Penrose identity `A A⁺ A = A`. -/
theorem comp_moorePenroseInverse_comp (A : E →ₗ[𝕜] F) :
    A ∘ₗ moorePenroseInverse A ∘ₗ A = A := by
  apply (rightSingularBasis A).toBasis.ext
  intro i
  by_cases hi : A.singularValues i = 0
  · -- on a zero singular direction both sides vanish; the composite has to be
    -- unfolded before the vanishing rewrite reaches the inner occurrence
    rw [OrthonormalBasis.coe_toBasis]
    simp [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi]
  · rw [OrthonormalBasis.coe_toBasis]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (moorePenroseInverse A (A (rightSingularBasis A i))) =
      A (rightSingularBasis A i)
    rw [moorePenroseInverse_apply_apply_rightSingularBasis A hi]

/-- The initial projection `A⁺A` is diagonal in the right singular basis, with
entry `1` on the directions of nonzero singular value and `0` on the rest.  Every
Penrose identity below is read off this one fact. -/
theorem moorePenroseInverse_comp_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    (moorePenroseInverse A ∘ₗ A) (rightSingularBasis A i) =
      if A.singularValues i = 0 then 0 else rightSingularBasis A i := by
  by_cases hi : A.singularValues i = 0
  · rw [if_pos hi, LinearMap.comp_apply,
      apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi,
      map_zero]
  · rw [if_neg hi, LinearMap.comp_apply,
      moorePenroseInverse_apply_apply_rightSingularBasis A hi]

/-- **The fourth Penrose identity: `A⁺A` is self-adjoint.**

`A⁺A` is diagonal in the right singular basis with entries `0` and `1`
(`moorePenroseInverse_comp_apply_rightSingularBasis`), so it is the orthogonal
projection onto the span of the directions with nonzero singular value. -/
theorem isSymmetric_moorePenroseInverse_comp (A : E →ₗ[𝕜] F) :
    (moorePenroseInverse A ∘ₗ A).IsSymmetric := by
  classical
  set v := rightSingularBasis A with hv
  set P := moorePenroseInverse A ∘ₗ A with hP
  -- On the basis, `⟪P (v j), v i⟫ = ⟪v j, P (v i)⟫`: both sides are `1` when
  -- `i = j` and `σᵢ ≠ 0`, and `0` otherwise.
  have horth : ∀ j i, ⟪v j, v i⟫_𝕜 = if j = i then 1 else 0 :=
    fun j i => orthonormal_iff_ite.mp v.orthonormal j i
  have hbasis : ∀ i j, ⟪P (v j), v i⟫_𝕜 = ⟪v j, P (v i)⟫_𝕜 := by
    intro i j
    rw [hP, moorePenroseInverse_comp_apply_rightSingularBasis,
      moorePenroseInverse_comp_apply_rightSingularBasis]
    by_cases hi : A.singularValues i = 0
    · by_cases hj : A.singularValues j = 0
      · rw [if_pos hi, if_pos hj, inner_zero_left, inner_zero_right]
      · have hne : j ≠ i := fun h => hj (h ▸ hi)
        rw [if_pos hi, if_neg hj, inner_zero_right, horth, if_neg hne]
    · by_cases hj : A.singularValues j = 0
      · have hne : j ≠ i := fun h => hi (h ▸ hj)
        rw [if_neg hi, if_pos hj, inner_zero_left, horth, if_neg hne]
      · rw [if_neg hi, if_neg hj]
  intro x y
  rw [← v.sum_repr x, ← v.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, hbasis]

/-- The pseudoinverse, evaluated.  Directions of zero singular value drop out
because the field inverse of `0` is `0`. -/
@[simp]
theorem moorePenroseInverse_apply (A : E →ₗ[𝕜] F) (y : F) :
    moorePenroseInverse A y =
      ∑ i : Fin (finrank 𝕜 E), (((A.singularValues i ^ 2 : ℝ) : 𝕜))⁻¹ •
        (⟪A (rightSingularBasis A i), y⟫_𝕜 •
          rightSingularBasis A i) := by
  simp [moorePenroseInverse, LinearMap.sum_apply,
    InnerProductSpace.rankOne_apply]

/-- **The second Penrose identity: `A⁺ A A⁺ = A⁺`.**

`A⁺` lands in the span of the right singular directions with nonzero singular
value, and `A⁺A` is the identity there. -/
theorem moorePenroseInverse_comp_comp (A : E →ₗ[𝕜] F) :
    moorePenroseInverse A ∘ₗ A ∘ₗ moorePenroseInverse A =
      moorePenroseInverse A := by
  classical
  ext y
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change (moorePenroseInverse A ∘ₗ A) (moorePenroseInverse A y) =
    moorePenroseInverse A y
  rw [moorePenroseInverse_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, moorePenroseInverse_comp_apply_rightSingularBasis]
  by_cases hi : A.singularValues i = 0
  · rw [if_pos hi]
    simp [hi]
  · rw [if_neg hi]

/-- **The third Penrose identity: `A A⁺` is self-adjoint.**

Unlike its companion this needs no orthogonality: `A A⁺` is visibly
`∑ᵢ (σᵢ²)⁻¹ • rankOne (A vᵢ) (A vᵢ)`, a real-coefficient combination of
rank-one projections onto the images of the right singular vectors. -/
theorem isSymmetric_comp_moorePenroseInverse (A : E →ₗ[𝕜] F) :
    (A ∘ₗ moorePenroseInverse A).IsSymmetric := by
  have happ : ∀ w : F, (A ∘ₗ moorePenroseInverse A) w =
      ∑ i : Fin (finrank 𝕜 E), (((A.singularValues i ^ 2 : ℝ) : 𝕜))⁻¹ •
        (⟪A (rightSingularBasis A i), w⟫_𝕜 •
          A (rightSingularBasis A i)) := by
    intro w
    rw [LinearMap.comp_apply, moorePenroseInverse_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul]
  intro y z
  rw [happ y, happ z]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    map_inv₀, RCLike.conj_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_conj_symm]
  ring

/-- **Uniqueness: the four Penrose identities determine the inverse.**

Any `B` satisfying all four *is* `A⁺`, so together with the identities above the
name is earned rather than asserted: `moorePenroseInverse` is the Moore--Penrose
inverse, not merely some generalized inverse.

The proof is the classical one.  Both `B` and `A⁺` are shown equal to the same
composite `B ∘ₗ A ∘ₗ A⁺`, each by pushing an adjoint through the factorization
of `A` supplied by the *other* map's first identity. -/
theorem eq_moorePenroseInverse_of_isMoorePenroseInverse {A : E →ₗ[𝕜] F} {B : F →ₗ[𝕜] E}
    (h : IsMoorePenroseInverse A B) : B = moorePenroseInverse A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  set G := moorePenroseInverse A with hGdef
  have hG1 : A ∘ₗ G ∘ₗ A = A := comp_moorePenroseInverse_comp A
  have hG2 : G ∘ₗ A ∘ₗ G = G := moorePenroseInverse_comp_comp A
  have hG3 : (A ∘ₗ G).IsSymmetric := isSymmetric_comp_moorePenroseInverse A
  have hG4 : (G ∘ₗ A).IsSymmetric := isSymmetric_moorePenroseInverse_comp A
  -- `A⋆ = A⋆ (A A⁺)`, from `A = (A A⁺) A` and self-adjointness of `A A⁺`.
  have hAr : LinearMap.adjoint A = LinearMap.adjoint A ∘ₗ (A ∘ₗ G) := by
    conv_lhs => rw [← hG1, ← LinearMap.comp_assoc]
    rw [LinearMap.adjoint_comp, hG3.adjoint_eq]
  -- `A⋆ = (B A) A⋆`, from `A = A (B A)` and self-adjointness of `B A`.
  have hAl : LinearMap.adjoint A = (B ∘ₗ A) ∘ₗ LinearMap.adjoint A := by
    conv_lhs => rw [← h1]
    rw [LinearMap.adjoint_comp, h4.adjoint_eq]
  have hB : B = B ∘ₗ A ∘ₗ G := by
    calc B = B ∘ₗ A ∘ₗ B := h2.symm
      _ = B ∘ₗ LinearMap.adjoint (A ∘ₗ B) := by rw [h3.adjoint_eq]
      _ = B ∘ₗ LinearMap.adjoint B ∘ₗ LinearMap.adjoint A := by
          rw [LinearMap.adjoint_comp]
      _ = B ∘ₗ LinearMap.adjoint B ∘ₗ LinearMap.adjoint A ∘ₗ (A ∘ₗ G) := by
          conv_lhs => rw [hAr]
      _ = (B ∘ₗ LinearMap.adjoint (A ∘ₗ B)) ∘ₗ (A ∘ₗ G) := by
          rw [LinearMap.adjoint_comp]
          simp only [LinearMap.comp_assoc]
      _ = (B ∘ₗ A ∘ₗ B) ∘ₗ (A ∘ₗ G) := by rw [h3.adjoint_eq]
      _ = B ∘ₗ A ∘ₗ G := by rw [h2]
  have hG : G = B ∘ₗ A ∘ₗ G := by
    calc G = G ∘ₗ A ∘ₗ G := hG2.symm
      _ = (G ∘ₗ A) ∘ₗ G := by rw [LinearMap.comp_assoc]
      _ = LinearMap.adjoint (G ∘ₗ A) ∘ₗ G := by rw [hG4.adjoint_eq]
      _ = (LinearMap.adjoint A ∘ₗ LinearMap.adjoint G) ∘ₗ G := by
          rw [LinearMap.adjoint_comp]
      _ = ((B ∘ₗ A) ∘ₗ LinearMap.adjoint A ∘ₗ LinearMap.adjoint G) ∘ₗ G := by
          conv_lhs => rw [hAl]
          simp only [LinearMap.comp_assoc]
      _ = (B ∘ₗ A) ∘ₗ (LinearMap.adjoint (G ∘ₗ A) ∘ₗ G) := by
          rw [LinearMap.adjoint_comp]
          simp only [LinearMap.comp_assoc]
      _ = (B ∘ₗ A) ∘ₗ ((G ∘ₗ A) ∘ₗ G) := by rw [hG4.adjoint_eq]
      _ = B ∘ₗ A ∘ₗ G := by simp only [LinearMap.comp_assoc, hG2]
  rw [hB, ← hG]

/-- The construction satisfies the four conditions, so a Moore--Penrose inverse exists. -/
theorem isMoorePenroseInverse_moorePenroseInverse (A : E →ₗ[𝕜] F) :
    IsMoorePenroseInverse A (moorePenroseInverse A) where
  comp_comp_self := comp_moorePenroseInverse_comp A
  comp_comp_self' := moorePenroseInverse_comp_comp A
  isSymmetric_comp := isSymmetric_comp_moorePenroseInverse A
  isSymmetric_comp' := isSymmetric_moorePenroseInverse_comp A

#print axioms isMoorePenroseInverse_moorePenroseInverse
#print axioms eq_moorePenroseInverse_of_isMoorePenroseInverse

end D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2026 "Kitware Inc"

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
