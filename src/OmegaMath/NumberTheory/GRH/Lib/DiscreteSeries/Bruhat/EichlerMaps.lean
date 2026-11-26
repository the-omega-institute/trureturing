import OmegaMath.NumberTheory.GRH.Lib.Adelic.Witt.FrameAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar measure
(known result; see Lib.DiscreteSeries.Bruhat.ComplexPlace).

Part of: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa decomposition
(known result; see Lib.SiegelWeil.SingularForms.AdaptedHom).

This file: Hermitian form, Eichler transformations are isometries; leading minors invariant under
unitriangular groups. -/

open Fin Fintype Matrix

variable {A} [CommRing A] [StarRing A] {n} [Fintype n] (J : Matrix n n A) (x u : n → A) (ς : A)

/-- The matrix of the Eichler map v ↦ v + h(u, v)x − h(x, v)(u + ςx), where h is the form of J. -/
noncomputable def eichlerMap := 1 + vecMulVec x (star u ᵥ* J) - vecMulVec (u + ς • x) (star x ᵥ* J)

attribute [local simp] dotProduct_mulVec ext_iff_mulVec mulVec_sub star_vecMul vecMulVec_mulVec
  frameGram eichlerMap funext_iff

variable {J : Matrix n n A} {x u : n → A} {ς : A} {𝔰} {T : Shape.Form 𝔰 A} {γ : T.G}

lemma eichlerMap_mulVec v :
  eichlerMap J x u ς *ᵥ v = v + (star u ⬝ᵥ J *ᵥ v) • x - (star x ⬝ᵥ J *ᵥ v) • (u + ς • x) := by simp

lemma exists_unitary_eq_eichlerMap : Jᴴ = J → star x ⬝ᵥ J *ᵥ x = 0 → star u ⬝ᵥ J *ᵥ x = 0 →
  ς + star ς = star u ⬝ᵥ J *ᵥ u → ∃ e : U J, e =
  eichlerMap J x u ς := by intros; use! eichlerMap J x u ς, eichlerMap J x (-u) (star ς) <;>
  simp [U, ← mulVec_mulVec, ← dotProduct_mulVec] <;> grind [star_form]

lemma Filling.leadingMinor_frameGram_besselU_mul {u u'} (hu : u ∈ besselU) (hu' : u' ∈ besselU) l :
    leadingMinor (T.frameGram (u⁻¹ * γ * u').1) l = leadingMinor (T.frameGram γ) l := by
  have {u} (h : u ∈ T.besselU) Z : leadingMinor (Z * frameMatrix u) l =
    star (leadingMinor Zᴴ l) := by
    have := frameMatrix_unitriangular h
    refine (det_eq_of_eq_mul_det_one _ (det_eq_one_of_unitriangular (lev := id) ?_) (ext fun _ _ ↦
      .symm (sum_of_injective _ (castLE_injective l.is_le) _ _ ?_ (by aesop)))).trans
      (det_conjTranspose _) <;> simp_all; grind
  simp [*, ↓frameGram_inv_mul_mul]

lemma Filling.frameGram_eq_frameImage γ : T.frameGram γ =
  (@frameImage A 𝔰 1)ᴴ * (T.splitGram * frameImage γ) := by simp [entrywise]

@[simp] lemma Filling.frameGram_inv [h : IsHermUnit T.splitGram] : T.frameGram ↑γ⁻¹ =
  (T.frameGram γ)ᴴ := by simp [h.1, ← U.form_mul_inv_eq]

omit [StarRing A] in
lemma exists_mulVec_eq_single_det Z : ∃ y, Z *ᵥ y = Pi.single 𝔰.top (Z.det : A) ∧ y 𝔰.top =
  leadingMinor Z 𝔰.top.castSucc := ⟨_, congr(col $Z.mul_adjugate 𝔰.top).trans (by simp), by
  simp [adjugate_fin_succ_eq_det_submatrix']; rfl⟩
