/- GID: D5/S3/Zeros/GRH/New/Filling/StableCells
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/StableCells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.StableCells. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/StableCells.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.CrudeBoundDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Invariance of link, level and discriminant under unipotent groups; link is Lagrangian
(`link`: classes of the pairs (y, γ⁻¹y), y orthogonal to X and γX, X spanned by e₁, …, e_ϱ). -/

open Matrix Fin Fintype Sum Function
attribute [local simp] fromBlocks_mulVec neg_mulVec comp_def


variable {F} [CommRing F] [StarRing F] {𝔰} {T : Shape.Form 𝔰 F} {j} {γ u u' : T.G}

omit [StarRing F] in
lemma splitGram_mulVec v : T.splitGram *ᵥ v =
  (v <| eStar ·) ⊕ᵥ (T *ᵥ (v <| inr <| inl ·) ⊕ᵥ (v <| inl ·)) := funext (by simp [splitGram])

@[simp ↓] lemma linkMatrix_mulVec t : linkMatrix γ *ᵥ t = (t <| inr <| inl ·) ⊕ᵥ
    (γ⁻¹.1.1 *ᵥ t <| inr <| inl ·) := funext (by simp [mulVec_eq_sum, linkMatrix])

@[simp ↓] lemma isotropicFramePair_mulVec_eq_zero_iff {t} :
  t ∈ ((isotropicFramePair γ)ᴴ * T.splitGram).mulVecLin.ker ↔ (∀ a, t (eStar a) = 0) ∧
  ∀ a, (γ⁻¹.1.1 *ᵥ t) (eStar a) = 0 := have := congr($(U.form_mul_inv_eq γ) *ᵥ t); by
  simp_all [← mulVec_mulVec, splitGram_mulVec, mulVec_apply_eq_sum, funext_iff]

attribute [local simp ↓] SetLike.mem_coe

lemma mem_link {p} : p ∈ link γ ↔ ∃ a, (γ.1.1 *ᵥ (a ⊕ᵥ (p ∘ inr ⊕ᵥ 0))) ∘ inr = p ∘ inl ⊕ᵥ 0 :=
  (mulVec_surjective_of_invertible γ).exists.trans (by
    simp [funext_iff, @exists_sum (Fin _), @exists_sum 𝔰.MiddleIndex,
      @Sum.forall 𝔰.MiddleIndex, -Sum.forall]
    simp [← funext_iff]; tauto)

lemma IsNormalForm.inv : IsNormalForm j γ → IsNormalForm j γ⁻¹ := .imp' star fun c h ↦
  h.imp (by simp [mul_comm]) (forall₂_imp fun _ _ ⟨x, y, _⟩ ↦ ⟨star c • y, star c • x, by
    simp_all [↓frameImage_mulVec (Units.val _), mul_comm]⟩)

lemma Filling.exists_frameImage_eq_of_isNormalForm {j : Fin (𝔰.ϱ + 2)} (h : IsNormalForm j γ) (y :
  _ → F) : ∃ x y', (∀ a, ↑j ≤ a.1 → y' a = y a) ∧ frameImage 1 *ᵥ x = frameImage γ.1.1 *ᵥ y' := by
  choose! _ _ X Y _ using h
  induction' j using reverseInduction with j i
  use 0, 0, by grind, by simp
  choose x z _ using i (by grind)
  use x + (y - z) j • X j, z + (y - z) j • Y j; simp; grind

lemma IsNormalForm.besselU_mul (h : u ∈ besselU) : IsNormalForm j γ → IsNormalForm j (u * γ) :=
  .imp fun _ ↦ .imp_right (forall₂_imp fun a _ ⟨x, y, _⟩ ↦ ⟨frameMatrix u *ᵥ x,
  y, by simp_all [← submatrix_mul_besselFrame, frameImage_mulVec u.1.1]; rfl, by
    grind [mulVec_apply_eq_sum, sum_eq_single a, Matrix.one_apply, frameMatrix_unitriangular]⟩)

lemma Filling.link_besselU_mul (a : u ∈ besselU) (b : u' ∈ besselU) : link (u⁻¹ * γ * u') = link
  γ := have l {u w γ} : u ∈ _ → w ∈ _ → link γ ≤ link (u * γ * w⁻¹) := fun _ _ _ ↦
    .imp' (u *ᵥ ·) (by simp_all [apply_inr_of_mem_besselU, ← mulVec_mulVec, inv_mulVec_eq_vec rfl,
    mulVec_apply_eq_sum (Units.val _)])
  (l (inv_mem a) (inv_mem b)).antisymm' ((l a b).trans_eq (by group))

lemma Filling.frameDisc_frameGram_besselU_mul (a : u ∈ besselU) (b : u' ∈ besselU) N :
  frameDisc N (T.frameGram (u⁻¹ * γ * u').1.1) = frameDisc
  N (T.frameGram γ) := by erw [frameDisc, leadingMinor_frameGram_besselU_mul,
  @id (det _ = _) (leadingMinor_frameGram_besselU_mul a b ⊤)] <;> tauto

variable {E} [Field E] [CMType E] {S : Filling E 𝔰}

lemma Filling.isStable_hasLevel j : S.IsStable {γ | S.HasLevel j γ} := fun _ a _ b _ ↦ .and ⟨(by
  simpa [mul_assoc] using ·.besselU_mul a |>.inv.besselU_mul b |>.inv),
  (·.besselU_mul (inv_mem a) |>.inv.besselU_mul (inv_mem b)
  |>.inv)⟩ (by simp [leadingMinor_frameGram_besselU_mul, frameDisc_frameGram_besselU_mul, *])

/-- The link of a rational γ in the unitary group of the filling data is Lagrangian: with T =
diag(1, …, 1, −N), p lies in it iff p is orthogonal for T ⊕ (−T) to every q in the link. -/
lemma mem_link_iff_orthogonal {γ : S.G E} {p} : p ∈ link γ ↔ ∀ q ∈ link γ,
  star q ⬝ᵥ S.linkForm *ᵥ p = 0 := ⟨by
  rintro ⟨t, _, rfl⟩ _ ⟨s, _, rfl⟩; have := U.form_mulVec_mulVec γ⁻¹ s t
  simp_all [↓splitGram_mulVec, dotProduct], fun h ↦
  (exists_mulVec_eq_of_annihilator 1 γ (.range inl) (.range inl) (0 ⊕ᵥ (p ∘ inl ⊕ᵥ 0))
  (0 ⊕ᵥ (p ∘ inr ⊕ᵥ 0)) ((Surjective.forall (exists_star_vecMul_eq S.ratGram)).2 fun t a b ↦ by
  erw [vecMul_vecMul _ _ γ.1.1, U.form_mul_inv_eq γ⁻¹, ← vecMul_vecMul, ← star_mulVec] at *
  simpa [↓← dotProduct_mulVec, splitGram_mulVec, dotProduct, add_eq_zero_iff_eq_neg] using h _
    ⟨t, by aesop, rfl⟩)).imp (by aesop)⟩

variable {A : Type} [Field A] [StarRing A] {T : 𝔰.Form A} {σ τ :
  T.G} {p q : ℕ → Aˣ}

/-- For σ in the unitary group of the middle space, t = h(z, σz) and d the product of the first
ϱ units of p, `frameDisc` N of Z(w_p σ) is d d̄ (t t̄ − N²); Z = `Shape.Form.frameGram`,
w_p = `weylElem` ϱ p. -/
lemma Filling.frameDisc_weylElem_mul (hσ : σ ∈ GT 𝔰.ϱ) N :
    let t := T.frameGram σ 𝔰.top 𝔰.top; let d := ∏ a : Fin 𝔰.ϱ, (p a).1
      frameDisc N (T.frameGram (weylElem 𝔰.ϱ p * σ).1.1) =
        d * star d * (t * star t - N ^ 2) := by simp [field, ↓frameGram_weylElem_mul hσ, frameDisc,
  leadingMinor, submatrix_diagonal, castLE_injective, prod_univ_castSucc, snoc]

/-- Over a field with involution, let σ, τ fix all e_a, e*_a,
and let w_p, w_q be Weyl elements of length ϱ. Then w_pσ and w_qτ have the same link if and
only if σ = τ. -/
lemma Filling.link_big_cell_eq_iff (hσ : σ ∈ GT 𝔰.ϱ) (hτ : τ ∈ GT 𝔰.ϱ) :
    link (weylElem 𝔰.ϱ p * σ) = link (weylElem 𝔰.ϱ q * τ) ↔ σ = τ := by
  rw [SetLike.ext_iff, forall_sum, forall_comm, ← mul_right_inj (weylElem 𝔰.ϱ p), Subtype.ext_iff]
  simp [*, ↓Units.ext_iff, mem_link, ↓coe_weylElem_mul, elim_eq_iff, ← elim_add_add,
    ← ext_iff_mulVec, (⟨_, mulVec_zero _⟩ : ∃ x, _ = _)]
