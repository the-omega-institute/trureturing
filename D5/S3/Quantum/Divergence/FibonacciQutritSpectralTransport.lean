/- GID: D5/S3/Quantum/Divergence/FibonacciQutritSpectralTransport
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/FibonacciQutritSpectralTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral transport of strict Fibonacci qutrit rank reduction. -/

import D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination

/-! A bounded null-reference loss forces a small eigenvalue and gives a
strict improvement by compressing onto its orthogonal complement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport

private abbrev M₃ := Matrix (Fin 3) (Fin 3) ℂ
private abbrev Block := Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) ℂ
private abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
private abbrev Ray := Matrix Unit Unit ℂ

private def divergence {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) : ℝ := (X * (CFC.log X - CFC.log Y)).trace.re

private def coordinates (U : unitaryGroup (Fin 3) ℂ) (f : Fin 3 ≃ Fin 2 ⊕ Unit) :
    M₃ ≃ₐ[ℝ] Block :=
  (Unitary.conjStarAlgAut ℝ M₃ U).toAlgEquiv.trans (Matrix.reindexAlgEquiv ℝ ℂ f)

private lemma coordinates_posSemidef (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X : M₃) :
    (coordinates U f X).PosSemidef ↔ X.PosSemidef := by
  change ((U.val * X * (star U : M₃)).submatrix f.symm f.symm).PosSemidef ↔ X.PosSemidef
  have hU : IsUnit (U : M₃) := Unitary.isUnit_coe
  rw [← Matrix.IsUnit.posSemidef_star_right_conjugate_iff (x := X) hU]
  constructor
  · intro h
    have hback := h.submatrix f
    have heq : (((U : M₃) * X * (star U : M₃)).submatrix f.symm f.symm).submatrix f f =
        (U : M₃) * X * (star U : M₃) := by
      ext i j
      simp [Matrix.submatrix_apply]
    rwa [heq] at hback
  · exact fun h => h.submatrix f.symm

private lemma coordinates_le (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X Y : M₃) :
    coordinates U f X ≤ coordinates U f Y ↔ X ≤ Y := by
  rw [Matrix.le_iff, Matrix.le_iff, ← map_sub, coordinates_posSemidef]

private lemma coordinates_trace (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X : M₃) : (coordinates U f X).trace = X.trace := by
  change (Matrix.reindex f f (U.val * X * (star U : M₃))).trace = X.trace
  rw [ConditionalHockeyStickOrthogonalReduction.trace_reindex,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

private lemma coordinates_log (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X : M₃) :
    CFC.log (coordinates U f X) = coordinates U f (CFC.log X) := by
  change cfc Real.log (Matrix.reindex f f (U.val * X * (star U : M₃))) =
    Matrix.reindex f f (U.val * cfc Real.log X * (star U : M₃))
  rw [Matrix.cfc_reindex]
  congr 1
  exact Matrix.cfc_conj_unitary Real.log U

private lemma coordinates_divergence (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X Y : M₃) :
    divergence (coordinates U f X) (coordinates U f Y) = divergence X Y := by
  simp only [divergence, coordinates_log, ← map_sub, ← map_mul, coordinates_trace]

private lemma not_floor (A C ρ : M₃) (e : ℝ) (he : C.trace.re / 3 ≤ e)
    (hc : 11 / 19 ≤ C.trace.re) (hlo : (4 / 3 : ℝ) • C ≤ A)
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hloss : (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re ≤ 1 / 114) :
    ¬ (1 / 500 : ℝ) • (1 : M₃) ≤ C := by
  intro hfloor
  have h := UmegakiNullReferencePenalty.log_increment_ge A C ρ (4 / 3) (1 / 500) e
    (by norm_num) (by norm_num) (by linarith) hlo hfloor hρ hρtr
  have h64 : (64 : ℝ) < 1 + e / (1 / 500) := by linarith
  have hlog := Real.log_lt_log (by norm_num : 0 < (64 : ℝ)) h64
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow] at hlog
  have htwo : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  linarith

private lemma trace_blocks (X : Block) :
    X.trace = X.toBlocks₁₁.trace + X (Sum.inr ()) (Sum.inr ()) := by
  simp [Matrix.trace, Fintype.sum_sum_type, Matrix.toBlocks₁₁]

private lemma ray_from_real {X : Block} (hX : X.IsHermitian) :
    X.toBlocks₂₂ = (X (Sum.inr ()) (Sum.inr ())).re • (1 : Ray) := by
  ext ⟨⟩ ⟨⟩
  have h := congrFun (congrFun hX.eq (Sum.inr ())) (Sum.inr ())
  simp only [Matrix.conjTranspose_apply] at h
  change star (X (Sum.inr ()) (Sum.inr ())) = _ at h
  simpa [Matrix.toBlocks₂₂, Complex.real_smul] using (Complex.conj_eq_iff_re.mp h).symm

private lemma embed_posSemidef {X : Qubit} (hX : X.PosSemidef) :
    (fromBlocks X 0 0 (0 : Ray)).PosSemidef := by
  let J : Matrix (Fin 2) (Fin 2 ⊕ Unit) ℂ :=
    fromCols (1 : Qubit) (0 : Matrix (Fin 2) Unit ℂ)
  have hJ : Jᴴ * X * J = fromBlocks X 0 0 (0 : Ray) := by
    dsimp only [J]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    simp
  rw [← hJ]
  exact hX.conjTranspose_mul_mul_same J

private lemma embed_rank (X : Qubit) : (fromBlocks X 0 0 (0 : Ray)).rank ≤ 2 := by
  let s : Finset (Fin 2 ⊕ Unit) := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩
  have h := (fromBlocks X 0 0 (0 : Ray)).rank_le_card_of_support_subset s (by
    intro i hi
    cases i with
    | inl i => simp [s]
    | inr i => exact False.elim (hi (by ext j; cases j <;> rfl)))
  simpa [s] using h

private def compress (τ : Qubit) : Block →ₗ[ℝ] Block where
  toFun X := fromBlocks (X.toBlocks₁₁ + (X (Sum.inr ()) (Sum.inr ())).re • τ) 0 0 (0 : Ray)
  map_add' X Y := by
    ext (i | i) (j | j) <;>
      simp [Matrix.toBlocks₁₁, add_smul, add_add_add_comm]
  map_smul' r X := by
    ext (i | i) (j | j) <;>
      simp [Matrix.toBlocks₁₁, smul_add, mul_assoc]

private def nullRay : Block := fromBlocks (0 : Qubit) 0 0 (1 : Ray)

private lemma compress_posSemidef {τ : Qubit} (hτ : τ.PosSemidef)
    {X : Block} (hX : X.PosSemidef) : (compress τ X).PosSemidef := by
  exact embed_posSemidef ((hX.submatrix Sum.inl).add
    (hτ.smul (Complex.nonneg_iff.mp (hX.diag_nonneg (i := Sum.inr ()))).1))

private lemma compress_trace {τ : Qubit} (hτ : τ.trace = 1) {X : Block}
    (hX : X.PosSemidef) : (compress τ X).trace = X.trace := by
  rw [trace_blocks (compress τ X), trace_blocks X]
  change (X.toBlocks₁₁ + (X (Sum.inr ()) (Sum.inr ())).re • τ).trace + 0 =
    X.toBlocks₁₁.trace + X (Sum.inr ()) (Sum.inr ())
  have h := congrFun (congrFun (ray_from_real hX.isHermitian) ()) ()
  rw [Matrix.trace_add, Matrix.trace_smul, hτ, add_zero]
  congr 1
  exact h.symm

private lemma nullRay_trace : nullRay.trace = 1 := by
  rw [trace_blocks]
  simp [nullRay]

private lemma nullRay_posSemidef : nullRay.PosSemidef := by
  have h : nullRay = diagonal (Sum.elim (fun _ : Fin 2 => 0) (fun _ : Unit => 1)) := by
    ext (i | ⟨⟩) (j | ⟨⟩) <;> simp [nullRay, Matrix.diagonal_apply]
  rw [h, Matrix.posSemidef_diagonal_iff]
  intro i
  cases i <;> simp

set_option maxHeartbeats 1000000 in
/-- A full-rank Fibonacci comparison with small null-reference loss admits
strict improvement on the qubit complementary to a smallest eigendirection. -/
theorem strict_spectral_transport (A C ρ : M₃) (e : ℝ) (hC : C.PosDef)
    (hlo : (4 / 3 : ℝ) • C ≤ A) (hhi : A ≤ (7 / 3 : ℝ) • C)
    (hA : A.trace = 1) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hc : 11 / 19 ≤ C.trace.re) (he : C.trace.re / 3 ≤ e)
    (hloss : (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re ≤ 1 / 114) :
    ∃ (U : unitaryGroup (Fin 3) ℂ) (f : Fin 3 ≃ Fin 2 ⊕ Unit) (lam : ℝ),
      let E := coordinates U f
      let Cₚ := (E C).toBlocks₁₁
      let τ := (Cₚ.trace.re)⁻¹ • Cₚ
      let T := (compress τ).comp E.toLinearMap
      let A' := T A
      let C' := T C
      0 < lam ∧ lam < 1 / 500 ∧ lam • (1 : M₃) ≤ C ∧
        E C = fromBlocks Cₚ 0 0 (lam • (1 : Ray)) ∧
        τ.PosDef ∧ τ.trace = 1 ∧ A'.PosSemidef ∧ A'.trace = 1 ∧
        C'.PosSemidef ∧ C'.trace = C.trace ∧ A'.rank ≤ 2 ∧ C'.rank ≤ 2 ∧
        nullRay.PosSemidef ∧ nullRay.trace = 1 ∧ (C' + e • nullRay).PosDef ∧
        (∀ X, X.PosSemidef → (T X).PosSemidef ∧ (T X).trace = X.trace ∧ (T X).rank ≤ 2) ∧
        (∀ (ι : Type) [Fintype ι] (X : ι → M₃) (p γ : ι → ℝ),
          A = ∑ i, p i • X i → C = ∑ i, γ i • X i →
          A' = ∑ i, p i • T (X i) ∧ C' + e • nullRay = (∑ i, γ i • T (X i)) + e • nullRay) ∧
        divergence A (C + e • ρ) < divergence A' (C' + e • nullRay) := by
  classical
  let h := hC.isHermitian
  obtain ⟨i, -, hmin⟩ := Finset.exists_min_image Finset.univ h.eigenvalues Finset.univ_nonempty
  let lam := h.eigenvalues i
  have hlam : 0 < lam := hC.eigenvalues_pos i
  let g : Fin 2 ⊕ Unit ≃ Fin 3 := Fintype.equivFinOfCardEq (by decide)
  let f : Fin 3 ≃ Fin 2 ⊕ Unit := (g.trans (Equiv.swap (g (Sum.inr ())) i)).symm
  have hfi : f.symm (Sum.inr ()) = i := Equiv.swap_apply_left _ _
  let U := star h.eigenvectorUnitary
  let E := coordinates U f
  let d (j : Fin 2 ⊕ Unit) := h.eigenvalues (f.symm j)
  have hdiag : E C = diagonal (fun j => (d j : ℂ)) := by
    change Matrix.reindex f f (Unitary.conjStarAlgAut ℂ M₃ U C) = _
    rw [h.conjStarAlgAut_star_eigenvectorUnitary]
    rw [Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
    rfl
  have hfloor : lam • (1 : M₃) ≤ C := by
    apply (coordinates_le U f _ _).mp
    change E (lam • (1 : M₃)) ≤ E C
    rw [map_smul, map_one, hdiag, Matrix.le_iff, ← diagonal_one,
      ← diagonal_smul]
    have hconst : lam • (fun _ : Fin 2 ⊕ Unit => (1 : ℂ)) = fun _ => (lam : ℂ) := by
      funext j
      simp [Complex.real_smul]
    rw [hconst]
    rw [diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro j
    have hm : lam ≤ d j := hmin _ (Finset.mem_univ _)
    exact Complex.nonneg_iff.mpr ⟨by simpa using sub_nonneg.mpr hm, by simp⟩
  have hsmall : lam < 1 / 500 := by
    by_contra! hlarge
    exact not_floor A C ρ e he hc hlo hρ hρtr hloss
      ((smul_le_smul_of_nonneg_right hlarge zero_le_one).trans hfloor)
  let Cₚ := (E C).toBlocks₁₁
  have hCₚ : Cₚ.PosDef := by
    change (E C).toBlocks₁₁.PosDef
    rw [hdiag, Matrix.toBlocks₁₁_diagonal, Matrix.posDef_diagonal_iff]
    exact fun j => Complex.pos_iff.mpr ⟨hC.eigenvalues_pos _, rfl⟩
  have hCblocks : E C = fromBlocks Cₚ 0 0 (lam • (1 : Ray)) := by
    have hlast : d (Sum.inr ()) = lam := by simp [d, hfi, lam]
    nth_rewrite 1 [← Matrix.fromBlocks_toBlocks (E C)]
    apply Matrix.fromBlocks_inj.mpr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hdiag, Matrix.toBlocks₁₂_diagonal]
    · rw [hdiag, Matrix.toBlocks₂₁_diagonal]
    · rw [hdiag, Matrix.toBlocks₂₂_diagonal]
      ext ⟨⟩ ⟨⟩
      simp [hlast, Complex.real_smul]
  have hCtrace : Cₚ.trace.re + lam = C.trace.re := by
    have htr := congrArg Complex.re ((trace_blocks (E C)).symm.trans (coordinates_trace U f C))
    have hd : E C (Sum.inr ()) (Sum.inr ()) = (lam : ℂ) := by
      simp [hdiag, d, hfi, lam]
    simpa [Cₚ, hd] using htr
  have hApos : A.PosSemidef :=
    ((hC.smul (by norm_num : (0 : ℝ) < 4 / 3)).isStrictlyPositive.of_le hlo).posDef.posSemidef
  have hEApos : (E A).PosSemidef := (coordinates_posSemidef U f A).mpr hApos
  have hECpos : (E C).PosSemidef := (coordinates_posSemidef U f C).mpr hC.posSemidef
  let F := (E A).toBlocks₁₁
  let H := (E A).toBlocks₁₂
  let a := (E A (Sum.inr ()) (Sum.inr ())).re
  have hAblocks : E A = fromBlocks F H Hᴴ (a • (1 : Ray)) := by
    have h21 : (E A).toBlocks₂₁ = Hᴴ := by
      ext j k
      exact (congrFun (congrFun hEApos.isHermitian.eq (Sum.inr j)) (Sum.inl k)).symm
    nth_rewrite 1 [← Matrix.fromBlocks_toBlocks (E A)]
    rw [h21, ray_from_real hEApos.isHermitian]
  have hAtrace : F.trace.re + a = 1 := by
    simpa [F, a] using congrArg Complex.re
      ((trace_blocks (E A)).symm.trans ((coordinates_trace U f A).trans hA))
  have hCₚfloor : lam • (1 : Qubit) ≤ Cₚ := by
    have hE := (coordinates_le U f _ _).mpr hfloor
    change E (lam • (1 : M₃)) ≤ E C at hE
    rw [map_smul, map_one] at hE
    apply Matrix.le_iff.mpr
    have hh := (Matrix.le_iff.mp hE).submatrix (Sum.inl : Fin 2 → Fin 2 ⊕ Unit)
    rw [Matrix.submatrix_sub, Matrix.submatrix_smul] at hh
    change (Cₚ - lam • (1 : Block).submatrix Sum.inl Sum.inl).PosSemidef at hh
    rwa [Matrix.submatrix_one _ Sum.inl_injective] at hh
  have hlo' : (4 / 3 : ℝ) • E C ≤ E A := by
    simpa only [map_smul] using (coordinates_le U f _ _).mpr hlo
  have hhi' : E A ≤ (7 / 3 : ℝ) • E C := by
    simpa only [map_smul] using (coordinates_le U f _ _).mpr hhi
  have hblock := FibonacciQutritBlockDomination.strict_block_domination Cₚ F H (E ρ) a lam e
    hCₚ hlam hsmall ((coordinates_posSemidef U f ρ).mpr hρ)
    ((coordinates_trace U f ρ).trans hρtr) (hCtrace ▸ hc) (hCtrace ▸ he) hCₚfloor hAtrace
    (by rwa [← hCblocks, ← hAblocks]) (by rwa [← hCblocks, ← hAblocks])
  have hbetter := lt_of_lt_of_le hblock.1 hblock.2
  let b := Cₚ.trace.re
  let τ := b⁻¹ • Cₚ
  have hb : 0 < b := (Complex.pos_iff.mp hCₚ.trace_pos).1
  have hτ : τ.PosDef := hCₚ.smul (inv_pos.mpr hb)
  have hτtrace : τ.trace = 1 := by
    have hreal : (b : ℂ) = Cₚ.trace := by
      apply Complex.conj_eq_iff_re.mp
      change star Cₚ.trace = Cₚ.trace
      rw [← Matrix.trace_conjTranspose, hCₚ.isHermitian.eq]
    change (b⁻¹ • Cₚ).trace = 1
    rw [Matrix.trace_smul, ← hreal, Complex.real_smul, Complex.ofReal_inv,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne')]
  have hcompressC : compress τ (E C) =
      fromBlocks ((Cₚ.trace.re + lam) • τ) 0 0 (0 : Ray) := by
    have hbτ : b • τ = Cₚ := by rw [show τ = b⁻¹ • Cₚ from rfl, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
    have hd : (E C (Sum.inr ()) (Sum.inr ())).re = lam := by
      simp [hdiag, d, hfi, lam]
    change fromBlocks (Cₚ + (E C (Sum.inr ()) (Sum.inr ())).re • τ) 0 0 (0 : Ray) = _
    rw [hd, add_smul]
    change fromBlocks (Cₚ + lam • τ) 0 0 (0 : Ray) = fromBlocks (b • τ + lam • τ) 0 0 0
    rw [hbτ]
  have hB' : compress τ (E C) + e • nullRay =
      fromBlocks ((Cₚ.trace.re + lam) • τ) 0 0 (e • (1 : Ray)) := by
    rw [hcompressC]
    simp [nullRay, fromBlocks_smul, fromBlocks_add]
  refine ⟨U, f, lam, hlam, hsmall, hfloor, hCblocks, hτ, hτtrace,
    compress_posSemidef hτ.posSemidef hEApos, (compress_trace hτtrace hEApos).trans
      ((coordinates_trace U f A).trans hA),
    compress_posSemidef hτ.posSemidef hECpos, (compress_trace hτtrace hECpos).trans
      (coordinates_trace U f C), embed_rank _, embed_rank _, nullRay_posSemidef,
    nullRay_trace, ?_, ?_, ?_, ?_⟩
  · change (compress τ (E C) + e • nullRay).PosDef
    rw [hB']
    exact UmegakiRareFlagBKM.block_diag_posDef _ 1 (hτ.smul (by rw [hCtrace]; linarith))
      Matrix.PosDef.one (by linarith)
  · intro X hX
    have hEX := (coordinates_posSemidef U f X).mpr hX
    exact ⟨compress_posSemidef hτ.posSemidef hEX,
      (compress_trace hτtrace hEX).trans (coordinates_trace U f X), embed_rank _⟩
  · intro ι _ X p γ hAp hCγ
    let T := (compress τ).comp E.toLinearMap
    change T A = (∑ i, p i • T (X i)) ∧
      T C + e • nullRay = (∑ i, γ i • T (X i)) + e • nullRay
    constructor
    · rw [hAp, map_sum]
      simp only [map_smul]
    · rw [hCγ, map_sum]
      simp only [map_smul]
  · apply lt_of_sub_pos
    change 0 < divergence (compress τ (E A)) (compress τ (E C) + e • nullRay) -
      divergence A (C + e • ρ)
    have hcompressA : compress τ (E A) = fromBlocks (F + a • τ) 0 0 (0 : Ray) := rfl
    rw [hB', ← coordinates_divergence U f A (C + e • ρ), map_add, map_smul, hCblocks]
    rw [hcompressA, hAblocks]
    exact hbetter

#print axioms strict_spectral_transport

end D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport
