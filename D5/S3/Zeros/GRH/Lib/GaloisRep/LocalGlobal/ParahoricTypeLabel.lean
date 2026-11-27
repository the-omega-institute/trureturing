/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/ParahoricTypeLabel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/ParahoricTypeLabel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.LocalGlobal.ParahoricTypeLabel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/LocalGlobal/ParahoricTypeLabel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.BlockMatrices
import D5.S3.Zeros.GRH.Lib.LocalGL.Shintani.ShintaniLifting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Local-global compatibility at tame level, away from and at l (known result; see
Lib.GaloisRep.LocalGlobal.LabelCompatibility).

This file: Parahoric types and depth-zero labels; type implies label by Frobenius reciprocity. -/


open NumberField Matrix Polynomial Fintype Function Fint Fin Set MulChar Finset
variable {E n M K ρ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {w :
  FinPlace E} [Field K] [Algebra (ResField w) K] [Fintype ρ] {s V} [AddCommGroup V] [Module ℂ V]
  {σ : Representation ℂ (GL ρ (ResField w)) V}

/-- Parahoric type: block 0 of b is the image of e; each k in GL_n(O_w), block triangular mod w
with block 0 equal to x, sends f to ∏χ_l(det k_{l+1})·ψ(det x)·F(x), k_j its block j mod w. -/
def HasParahoricType f hw (e : ρ ↪ n) b (ψ : MulChar (ResField w) ℂ) (χ : Fin s →
  MulChar (ResField w) ℂ) (F : GL ρ (ResField w) → _) := (∀ i, b i = 0 ↔ i ∈ range e) ∧ ∀ k x h,
  submatrix (reduceGL k) e e = x.1 → rightRegular ℂ _ (M → ℂ)
  (atSplit hw k.1) f = (∏ l, χ l (blockHom b l.succ ⟨reduceGL k, h⟩).det.1) • ψ x.det • F x

/-- c is monic squarefree of degree d, c(0) ≠ 0, c∏(X − x_{χ_l}) is separable, d + Σt_l = n, and
f has label Ξ_c * ∏(χ_l∘det on GL_{t_l}) at w. -/
def HasProductLabel (f : Gf E n → M → ℂ) hw T [IsFaithfulMulChar K T] d (c : (ResField w)[X])
  (χ : _ → _) (t : Fin s → ℕ) := IsLabel d c ∧ Separable (c * ∏ l, (X - C (charName T (χ l)).1)) ∧
  d + ∑ l, t l = card n ∧ HasLabel f hw (labelChar T c * ∏ l, (detChar (χ l)).rankPart (t l)).evalGL

/-- Type implies label (Frobenius reciprocity): let c be a label of degree |ρ|, c' its roots
scaled by x_ψ, the χ_l distinct, c'(x_{χ_l}) ≠ 0, and Σ conj(Ξ_c(x))F(x) ≠ 0. Then
`HasParahoricType` gives `HasProductLabel` for c', the χ_l and the block sizes. -/
lemma HasParahoricType.hasProductLabel {f hw e y b c ψ} {χ : Fin s → _} (L : V →ₗ[ℂ] Gf E n →
  M → ℂ) (hL : Injective L) (h₂ : σ.asAlgebraHom (labelIdem ρ c) y ≠ 0) (h :
  HasParahoricType f hw e b ψ χ (L <| σ · y)) (hχ : Injective χ) : let T := faithfulChar (ResField
    w); let a := c.scaleRoots (charName T ψ); (∀ l, ¬a.IsRoot
      (charName T (χ l)).1) → HasProductLabel f hw T (card ρ) a χ (card {i // b i = ·.succ}) := by
  intro T a hψ; simp [labelIdem, asAlgebraHom_eq_sum, apply_ite, ite_apply] at h₂; exact
  let ε := (Equiv.subtypeEquivRight h.1).trans e.toEquivRange.symm
  have h₁ k g := h.2 k (reindexGL ε (blockHom b 0 ⟨_, g⟩)) g rfl
  have hK k _ := .symm (by simpa [*] using h₁ 1)
  have H g x y := by simpa using hK (y⁻¹ * g * x)
  have d := h₂.1.scaleRoots _
  ⟨d, (PerfectField.separable_iff_squarefree.2 d.2.1).mul (by simpa [Units.val_inj, Injective,
    separable_prod_X_sub_C_iff]) (.symm (.prod_left (by simpa [dvd_iff_isRoot,
    (prime_X_sub_C _).coprime_iff_not_dvd]))), by simp [sum_univ_succ, card_congr ε, ← card_congr
    (.sigmaFiberEquiv b)], hK, fun z ↦ h₂.2 (hL (by
  ext; have := congrFun₂ ((sum_evalGL_prod_eq_zero_iff b (F :=
    cons _ (detChar ∘ χ)) (cases (lift_labelChar_self T d) fun _ ↦ lift_detChar T rfl) _ fun _ _ ↦
    H _ _ (surjInv reduceGL_surjective _) (by simp [surjInv_eq])).1
    (by simpa [prod_univ_succ, card_congr ε, rankPart_labelChar, d] using z) 1) ‹_› ‹_›
  simp [prod_univ_succ, mul_assoc, h₁, ← mul_sum, star_apply', ↓isUnits_det_units, surjInv_eq,
    inv_apply_eq_inv', prod_ne_zero_iff, apply_eq_zero_iff, ← labelChar_mul_det h₂.1] at *
  simp_rw [Hall.evalGL, ← simClassOf_submatrix ε.symm, ← finsum_eq_sum_of_fintype] at *
  exact .inr
    ((mul_eq_zero_iff_right (by simp)).1 ((finMean_comp_surjective ((reindexGL ε).toMonoidHom.comp
    (blockHom b 0)).toAdditive (⟨⟨extendGL e ·, fun _ ↦ by grind [one_apply_ne, extendGL_spec]⟩,
    Units.ext (extendGL_spec ..).1⟩) _).symm.trans (mul_eq_zero_of_left this _)))))⟩
