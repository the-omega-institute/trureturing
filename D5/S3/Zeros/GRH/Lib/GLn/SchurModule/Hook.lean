/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Hook
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/Hook
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.Hook. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/Hook.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.RationalRep
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Weights majorised by λ, extremal weights have multiplicity one, symmetric power case.
Positivity and crude bound for Fischer norms of products of minors. -/

variable {Φ R} [CommRing R] [Fintype Φ] {n n' : Φ → _} {κ} [∀ τ, Fintype (n τ)]
  [∀ τ, Fintype (n' τ)] (e : ∀ τ, n τ ≃ Fin (rankAt n τ)) (i : WeylIndexFam n κ)

open MvPolynomial Finset Matrix PolyRep Equiv Fintype

attribute [local simp] tableauWeight rowSubst permArray weylEval minor tableauPoly
  Finsupp.single_apply ite_and RingHom.map_det highestPoly
  AlgHom.map_det Matrix.map diagramWeight sum_card_fiberwise_eq_card_filter Fin.val_inj weylKernel

lemma tableau_col_injective τ h j : ((i τ).1 h j).Injective := fun _ _ _ ↦
  by_contra ((@linearIndependent_nablaBasis _ ℤ).ne_zero i <| by simpa [nablaBasis,
  prod_eq_zero_iff] using ⟨τ, h, j, det_zero_of_row_eq · (by aesop)⟩)

omit [Fintype Φ] in
/-- For a family i of chosen standard fillings and a place τ, the total number of entries of
i_τ, summed over all rows a, equals Σ_{h<|n_τ|} h·κ_τ(h). -/
lemma sum_tableauWeight τ : ∑ a, tableauWeight i τ a = ∑ h ∈ range (rankAt n τ), h * κ τ h := by
  simp [sum_comm, sum_range, mul_comm]

/-- For a set A of rows at τ, the number of entries of i_τ lying in A is at most Σ_{j<|A|}
λ(τ,j), where λ(τ,j) = Σ_{j<h<|n_τ|} κ_τ(h); if equality holds, all entries of columns of
height at most |A| lie in A. -/
lemma sum_tableauWeight_le τ A : A.sum (tableauWeight i τ ·) ≤ (range #A).sum
  (diagramWeight (rankAt n) κ ⟨τ, ·⟩) ∧ (∑ x ∈ range #A, (diagramWeight (rankAt n) κ) (τ, x) ≤
  A.sum (tableauWeight i τ ·) → ∀ h j s, h.1 ≤ #A → (i τ).1 h j s ∈ A) := by
  have c (p : Σ h, Fin (κ ..)) := le_min (card_le_card_of_injOn (t := A) _
    (mem_filter_univ · |>.1) (tableau_col_injective i τ _ p.2).injOn) (card_le_univ _)
  simpa [-mem_range, mul_comm, Fintype.sum_sigma, sum_range (n := rankAt ..), sum_comm] using
    And.intro (sum_mono c) fun e h j s _ ↦ card_filter_eq_iff.1
    (congr($((Pi.le_def.2 c).eq_of_not_lt ((sum_strictMono ·).mt e)) ⟨h, j⟩).trans (by simpa)) s

omit [Fintype Φ] [∀ τ, Fintype (n' τ)] in
lemma PolyRep.eval_rowSubst z y f : eval y (@rowSubst Φ R _ n n' _ z f) = eval (fun x ↦ ∑ a,
    z _ x.1.2 a * y (⟨_, a⟩, x.2)) f := (aeval_bind₁ ..).trans (by simp)

/-- If the sizes fit κ (`FitsRanks`), then ∏_τ det(y_τ)^{d_τ} · S_κ(z) ev_y = ev_{zy}, where ev
is the evaluation vector, y_τ the first |n_τ| columns of block τ, and d_τ is given by
`schurDetExp`. -/
lemma schur_mulVec_weylEval (h : FitsRanks n n' κ) z y :
  (detPow R n (schurDetExp n n' κ)).eval y • schur κ z *ᵥ weylEval n κ y = weylEval n' κ fun x ↦
  ∑ a, z _ x.1.2 a * y (⟨_, a⟩, x.2) := funext (by simpa [↓PolyRep.eval_rowSubst,
  mulVec_apply_eq_sum, mul_sum, mul_rotate'] using congr(eval y $(sum_schur_smul_nablaBasis h _ ·)))

lemma schur_mulVec_weylEval_of_detExp_zero (h : FitsRanks n n' κ) (d :
  schurDetExp n n' κ = 0) z (y : _ → R) : schur κ z *ᵥ weylEval n κ y = weylEval n'
  κ fun x ↦ ∑ a, z _ x.1.2 a * y (⟨_, a⟩, x.2) := by simp [← schur_mulVec_weylEval, *]

lemma weylKernel_mem_nablaFam y : weylKernel n κ y ∈ nablaFam R n κ :=
  rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla

lemma PolyRep.eval_weylKernel_permArray : (weylKernel n κ (permArray e)).eval (permArray e) =
  (1 : R) := by simp [reindex_equiv (e _).symm, ← diagonal.eq_1]

/-- Let w be the permutation matrix of the row numbering e, φ a linear form, b_i a basis
product. If φ(b_i) ≠ 0 forces b_i to have degree ≥ λ_τ(e a) in every row (τ,a), then φ(b_i)
= φ(f_λ(wᵀx))·b_i(w), f_λ = `highestPoly`. -/
lemma map_nablaBasis_eq_mul_weylEval (φ : _ →ₗ[R] R) (h : φ (nablaBasis R n κ i) ≠ 0 → ∀ τ a,
  diagramWeight (rankAt n) κ (τ, e τ a) ≤ tableauWeight i τ a) : φ (nablaBasis R n κ i) =
  φ (weylKernel n κ (permArray e)) * weylEval n κ (permArray e) i := by
  by_cases! p : ∀ τ h j s, e τ ((i τ).1 h j s) < h; rw [mul_comm, ← smul_eq_mul, ← map_smul]
  simp [nablaBasis, ← C_mul', ← prod_mul_distrib, ← det_mul, -prod_const]; congr!; ext
  rw [mul_apply, sum_eq_ite ⟨_, p ..⟩] <;> aesop
  choose τ k j s p using p; convert (mul_zero _).symm; by_contra
  simpa [p.not_gt] using (sum_tableauWeight_le i τ ((Iio k).map (e τ).symm)).2 (by
    grw [← h ‹_›]; simp [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio]) _ j s
  simp [nablaBasis]; repeat apply prod_eq_zero (mem_univ ‹_›)
  grind only [det_eq_zero_of_row_eq_zero s, of_apply]

/-- One place, |m| > 1, a columns of height 1, none of heights 2, …, |m|−1: up to a bijection φ
of basis indices with degree a monomials, c^a·S(z) is the transpose of the symmetric power
`symPowMatrix` a of c·zᵀ, for complex c, z. -/
lemma schur_one_row_eq_symPowMatrix {a m σ} [Fintype m] [Fintype σ] {k} (q : σ ≃ m) (h : 1 < card m)
  (hκ : ∀ i > 0, i < card m → k i = ite (i = 1) a 0) : ∃ φ : _ ≃ _, ∀ (c : ℂ) z i j, c ^ a * schur
  (fun () ↦ k) (fun _ ↦ z) i j = symPowMatrix a (c • zᵀ.submatrix q q) (φ j) (φ i) := by
  have s : ∑ h ∈ range (card m), h * k h = a := by grind [sum_eq_ite 1]
  choose φ B using fun i ↦ (⟨⟨∑ h, ∑ j, ∑ s, .single (q.symm ((i ()).1 h j s)) 1, by
    simp [@sum_comm _ _ σ, ← s, sum_range, mul_comm]⟩, by
    simp [nablaBasis, monomial_sum_one, ← X.eq_1]; congr! with ⟨_ | _ | _⟩ <;> simp [univ_eq_empty]
    grind [Fin]⟩ : ∃ d : Monomials σ a, nablaBasis ℂ m (fun () ↦ k) i =
    bind₁ (X ⟨⟨(), q ·⟩, 0⟩) (monomial d 1))
  have e : φ.Bijective := ⟨fun i j c ↦ (@linearIndependent_nablaBasis _ ℂ).injective (by grind),
    fun ⟨d, _⟩ ↦ Function.mtr (by simp_all [coeff_sum, Subtype.ext_iff, rename_bind₁])
      congr((rename (q.symm ·.1.2) $(sum_coords_nablaBasis
    (show bind₁ (X ⟨⟨(), q ·⟩, 0⟩) (monomial d 1) ∈ nablaFam ℂ m fun () ↦ k by
      simp_all [mem_nabla, monomial_eq, borelMul, mul_pow, prod_pow_eq_pow_sum]
      rw [sum_eq_ite 1] <;> simp_all <;> grind))).coeff d)⟩
  use .ofBijective φ e, fun c z ↦ congrFun₂ (.trans (funext₂ (by simp [schur_smul, s]))
    (schur_eq_of_expansion (z := fun () ↦
    c • z) (by simpa [*, monomial_eq, reindex_equiv q, ↓← e.sum_comp, symPowMatrix, linSubst]
    using congr(bind₁ _ $(sum_monomials_eq_of_isHomogeneous <| φ · |>.isHomogeneous_linSubst _)))))

open Finsupp Nat RingHom
variable {Φ : _} [Fintype Φ] {κ : Φ → ℕ → ℕ} {N L}

/-- The hook number ⟨f,f⟩ = f(∂)f(0) is positive, where f is the product over τ and h < N_τ of
the leading principal h×h minors raised to κ_τ(h). -/
@[simp] lemma hookNumber_pos : 0 < hookNumber κ N := (fockPairing_star_self_pos
  (ne_of_apply_ne (eval (permArray fun _ ↦ (↑))) (by simp [highestPoly, tableauPoly, minor, map_det,
  Matrix.map, permArray, Fin.val_inj, ← diagonal.eq_1]))).trans_eq (congr (by simp) rfl)

@[simp] lemma hookNumber_ne_zero : hookNumber κ N ≠ 0 := hookNumber_pos.ne'

/-- If Σ_τ Σ_{h<N_τ} h·κ_τ(h) ≤ L, then the hook number attached to κ and N is at most L^{3L}. -/
lemma hookNumber_le (h : ∑ τ, ∑ h ∈ range (N τ), h * κ τ h ≤ L) : hookNumber κ N ≤ (L ^ L) ^ 3 := by
  have k := (le_of_dvd (by grind) <| @prod_factorial_dvd_factorial_sum · · ·)
  simp_rw [hookNumber, highestPoly, tableauPoly, minor, det_apply, prod_univ_sum, prod_smul,
    of_apply, X, ← monomial_sum_one, LinearMap.map_sum₂, map_sum, smul_monomial,
    fockPairing_monomial, coeff_monomial, prod, mul_ite_zero]
  grw [ite_le_sup, le_abs_self (_ • _ * _), k]; simp [↓← degree_apply, -prod_const, -cast_prod,
    Fintype.card_perm, Units.smul_def, abs_prod]; repeat grw [k]
  grw [← cast_pow, ← factorial_le_pow, ← h]; simp [sum_range, pow_succ, mul_comm]
