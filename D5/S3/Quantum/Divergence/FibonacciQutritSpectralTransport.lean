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
  rw [← (Unitary.isUnit_coe U).posSemidef_star_right_conjugate_iff (x := X)]
  constructor
  · intro h
    simpa [Matrix.submatrix_submatrix, Function.comp_def] using h.submatrix f
  · exact fun h => h.submatrix f.symm

private lemma coordinates_le (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X Y : M₃) :
    coordinates U f X ≤ coordinates U f Y ↔ X ≤ Y := by
  rw [Matrix.le_iff, Matrix.le_iff, ← map_sub, coordinates_posSemidef]

private lemma coordinates_trace (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X : M₃) : (coordinates U f X).trace = X.trace := by
  change (Matrix.reindex f f (U.val * X * (star U : M₃))).trace = X.trace
  rw [ConditionalHockeyStickOrthogonalReduction.trace_reindex,
    Matrix.trace_mul_cycle, ← Matrix.mul_assoc, ← Unitary.coe_star, Unitary.coe_star_mul_self,
    Matrix.one_mul]

private lemma coordinates_log (U : unitaryGroup (Fin 3) ℂ)
    (f : Fin 3 ≃ Fin 2 ⊕ Unit) (X : M₃) :
    CFC.log (coordinates U f X) = coordinates U f (CFC.log X) := by
  change cfc Real.log (Matrix.reindex f f (U.val * X * (star U : M₃))) =
    Matrix.reindex f f (U.val * cfc Real.log X * (star U : M₃))
  rw [Matrix.cfc_reindex, ← Unitary.star_eq_inv, Matrix.cfc_conj_unitary]

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
  have him := congrArg Complex.im h
  have hz : (X (Sum.inr ()) (Sum.inr ())).im = 0 := by
    simp only [Complex.conj_im] at him
    linarith
  apply Complex.ext <;> simp [Matrix.toBlocks₂₂, Complex.real_smul, hz]

private lemma embed_posSemidef {X : Qubit} (hX : X.PosSemidef) :
    (fromBlocks X 0 0 (0 : Ray)).PosSemidef := by
  let J : Matrix (Fin 2) (Fin 2 ⊕ Unit) ℂ :=
    fromRows (1 : Qubit) (0 : Matrix (Fin 2) Unit ℂ)
  have hJ : Jᴴ * X * J = fromBlocks X 0 0 (0 : Ray) := by
    simp [J, Matrix.fromRows, Matrix.fromCols, ← fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.mul_apply, Fintype.sum_sum_type]
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

private def compress (τ : Qubit) (X : Block) : Block :=
  fromBlocks (X.toBlocks₁₁ + (X (Sum.inr ()) (Sum.inr ())).re • τ) 0 0 (0 : Ray)

private def nullRay : Block := fromBlocks (0 : Qubit) 0 0 (1 : Ray)

private lemma compress_posSemidef {τ : Qubit} (hτ : τ.PosSemidef)
    {X : Block} (hX : X.PosSemidef) : (compress τ X).PosSemidef := by
  exact embed_posSemidef ((hX.submatrix Sum.inl).add
    (hτ.smul (Complex.nonneg_iff.mp (hX.diag_nonneg (i := Sum.inr ()))).1))

private lemma compress_trace {τ : Qubit} (hτ : τ.trace = 1) {X : Block}
    (hX : X.PosSemidef) : (compress τ X).trace = X.trace := by
  rw [trace_blocks (compress τ X), trace_blocks X]
  have h := congrFun (congrFun (ray_from_real hX.isHermitian) ()) ()
  change X (Sum.inr ()) (Sum.inr ()) = _ at h
  simp [compress, Matrix.trace_add, Matrix.trace_smul, hτ, h, Complex.real_smul]

private lemma nullRay_trace : nullRay.trace = 1 := by
  rw [trace_blocks]
  simp [nullRay]

private lemma nullRay_posSemidef : nullRay.PosSemidef := by
  have h : nullRay = diagonal (Sum.elim (fun _ : Fin 2 => 0) (fun _ : Unit => 1)) := by
    ext (i | ⟨⟩) (j | ⟨⟩) <;> simp [nullRay]
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
      let A' := compress τ (E A)
      let C' := compress τ (E C)
      0 < lam ∧ lam < 1 / 500 ∧ lam • (1 : M₃) ≤ C ∧
        E C = fromBlocks Cₚ 0 0 (lam • (1 : Ray)) ∧
        τ.PosDef ∧ τ.trace = 1 ∧ A'.PosSemidef ∧ A'.trace = 1 ∧
        C'.PosSemidef ∧ C'.trace = C.trace ∧ A'.rank ≤ 2 ∧ C'.rank ≤ 2 ∧
        (C' + e • nullRay).PosDef ∧
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
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [d, RCLike.ofReal_apply, Matrix.reindex_apply]
    · have hf : f.symm j ≠ f.symm k := fun e => hjk (f.symm.injective e)
      simp [d, Matrix.reindex_apply, Matrix.diagonal_apply_ne hjk, Matrix.diagonal_apply_ne hf]
  have hfloor : lam • (1 : M₃) ≤ C := by
    apply (coordinates_le U f _ _).mp
    change E (lam • (1 : M₃)) ≤ E C
    rw [map_smul, map_one, hdiag, Matrix.le_iff, ← diagonal_one,
      ← diagonal_smul, ← diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro j
    have hm : lam ≤ d j := hmin _ (Finset.mem_univ _)
    simpa [Pi.sub_apply, Complex.real_smul, ← Complex.ofReal_sub] using
      (Complex.ofReal_nonneg.mpr (sub_nonneg.mpr hm))
  have hsmall : lam < 1 / 500 := by
    by_contra! hlarge
    exact not_floor A C ρ e he hc hlo hρ hρtr hloss
      ((smul_le_smul_of_nonneg_right hlarge zero_le_one).trans hfloor)
  let Cₚ := (E C).toBlocks₁₁
  have hCₚ : Cₚ.PosDef := by
    change (E C).toBlocks₁₁.PosDef
    rw [hdiag, Matrix.toBlocks₁₁_diagonal, Matrix.posDef_diagonal_iff]
    exact fun j => Complex.ofReal_pos.mpr (hC.eigenvalues_pos _)
  have hCblocks : E C = fromBlocks Cₚ 0 0 (lam • (1 : Ray)) := by
    have hlast : d (Sum.inr ()) = lam := by simp [d, hfi, lam]
    rw [← Matrix.fromBlocks_toBlocks (E C)]
    conv_lhs => rw [hdiag, Matrix.toBlocks₁₂_diagonal, Matrix.toBlocks₂₁_diagonal,
      Matrix.toBlocks₂₂_diagonal]
    congr 1
    · exact congrArg Matrix.toBlocks₁₁ hdiag.symm
    · ext ⟨⟩ ⟨⟩
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
    exact Matrix.le_iff.mpr ((Matrix.le_iff.mp hE).submatrix
      (Sum.inl : Fin 2 → Fin 2 ⊕ Unit))
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
      exact Complex.conj_eq_iff_re.mp (by
        rw [← Matrix.trace_conjTranspose, hCₚ.isHermitian.eq])
    change (b⁻¹ • Cₚ).trace = 1
    rw [Matrix.trace_smul, ← hreal, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne')]
  have hcompressC : compress τ (E C) =
      fromBlocks ((Cₚ.trace.re + lam) • τ) 0 0 (0 : Ray) := by
    have hbτ : b • τ = Cₚ := by rw [show τ = b⁻¹ • Cₚ from rfl, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
    have hd : (E C (Sum.inr ()) (Sum.inr ())).re = lam := by
      simp [hdiag, d, hfi, lam]
    simp only [compress, hd, ← show b = Cₚ.trace.re from rfl, add_smul]
    change fromBlocks (Cₚ + lam • τ) 0 0 (0 : Ray) = _
    rw [hbτ]
  have hB' : compress τ (E C) + e • nullRay =
      fromBlocks ((Cₚ.trace.re + lam) • τ) 0 0 (e • (1 : Ray)) := by
    rw [hcompressC]
    simp [nullRay, fromBlocks_smul, fromBlocks_add]
  refine ⟨U, f, lam, hlam, hsmall, hfloor, hCblocks, hτ, hτtrace,
    compress_posSemidef hτ.posSemidef hEApos, (compress_trace hτtrace hEApos).trans
      ((coordinates_trace U f A).trans hA),
    compress_posSemidef hτ.posSemidef hECpos, (compress_trace hτtrace hECpos).trans
      (coordinates_trace U f C), embed_rank _, embed_rank _, ?_, ?_⟩
  · rw [hB']
    exact UmegakiRareFlagBKM.block_diag_posDef _ 1 (hτ.smul (by rw [hCtrace]; linarith))
      Matrix.PosDef.one (by linarith)
  · apply lt_of_sub_pos
    rw [hB', ← coordinates_divergence U f A (C + e • ρ), map_add, map_smul, hCblocks]
    rw [hAblocks]
    exact hbetter

#print axioms strict_spectral_transport

end D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport
