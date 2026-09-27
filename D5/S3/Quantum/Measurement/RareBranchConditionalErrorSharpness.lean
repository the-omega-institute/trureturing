/- GID: D5/S3/Quantum/Measurement/RareBranchConditionalErrorSharpness
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/RareBranchConditionalErrorSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rare branch can attain maximal conditional error from an arbitrarily small initial error. -/

import D5.S3.Quantum.Measurement.BranchConditionedTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness

open BigOperators Matrix
open Filter
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped ComplexOrder MatrixOrder Topology

theorem rare_branch_conditional_error_sharpness :
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      let C : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
        if i = 0 then 1 else 0)
      let E0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
        if i = 1 then 1 else 0)
      let E1 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
        if i = 2 then 1 else 0)
      let rhoM : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
        if i = 0 then (1 - ε : ℂ) else if i = 1 then (ε : ℂ) else 0)
      let sigmaM : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
        if i = 0 then (1 - ε : ℂ) else if i = 2 then (ε : ℂ) else 0)
      let P : Matrix (Fin 3) (Fin 3) ℂ := E0 + E1
      ∃ ρ σ : DensityState (Fin 3), ∃ Pm K : Matrix (Fin 3) (Fin 3) ℂ,
        CStarMatrix.ofMatrix.symm ρ.val = rhoM ∧
        CStarMatrix.ofMatrix.symm σ.val = sigmaM ∧
        Pm = P ∧ K = C ∧
        Pmᴴ * Pm + Kᴴ * K = 1 ∧
        Pmᴴ * Pm ≤ 1 ∧
        traceDistance ρ σ = ε ∧
        (CStarMatrix.ofMatrix.symm ρ.val *
            Pmᴴ * Pm).trace.re = ε ∧
        (CStarMatrix.ofMatrix.symm σ.val *
            Pmᴴ * Pm).trace.re = ε ∧
        (1 / ε : ℝ) •
            (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) = E0 ∧
        (1 / ε : ℝ) •
            (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ) = E1 ∧
        traceNorm (E0 - E1) / 2 = 1 ∧
        Pm = E0 + E1 ∧
        max ε ε * (traceNorm (
          (1 / ε : ℝ) • (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) -
          (1 / ε : ℝ) • (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ)) / 2) =
          traceDistance ρ σ) ∧
    ¬ ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ ρ σ : DensityState (Fin 3),
        ∀ Pm : Matrix (Fin 3) (Fin 3) ℂ,
          Pmᴴ * Pm ≤ 1 →
          0 < (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re →
          0 < (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re →
          traceNorm (
            (1 / (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re : ℝ) •
              (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) -
            (1 / (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re : ℝ) •
              (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ)) / 2 ≤
            f (traceDistance ρ σ) := by
  classical
  have hdiagNorm (t : ℝ) (ht : 0 ≤ t) :
      traceNorm (Matrix.diagonal (fun i : Fin 3 =>
        if i = 0 then (0 : ℂ) else if i = 1 then (t : ℂ) else (-t : ℂ))) = 2 * t := by
    let A : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i : Fin 3 =>
      if i = 0 then (0 : ℂ) else if i = 1 then (t : ℂ) else (-t : ℂ))
    have hupper : traceNorm A ≤ 2 * t := by
      let E₁ : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
        if i = 1 then (t : ℂ) else 0)
      let E₂ : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
        if i = 2 then (t : ℂ) else 0)
      have hE₁ : E₁.PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro i
        fin_cases i <;> simp [E₁, ht]
      have hE₂ : E₂.PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro i
        fin_cases i <;> simp [E₂, ht]
      have hdecomp : A = E₁ + -(E₂) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [A, E₁, E₂]
      calc
        traceNorm A = traceNorm (E₁ + -(E₂)) := by rw [hdecomp]
        _ ≤ traceNorm E₁ + traceNorm (-(E₂)) := traceNorm_add_le _ _
        _ = traceNorm E₁ + traceNorm E₂ := by rw [traceNorm_neg]
        _ = 2 * t := by
          have ht₁ := congrArg Complex.re (traceNorm_of_posSemidef hE₁)
          have ht₂ := congrArg Complex.re (traceNorm_of_posSemidef hE₂)
          norm_num at ht₁ ht₂
          rw [ht₁, ht₂]
          simp [E₁, E₂, Matrix.trace_diagonal, Fin.sum_univ_three]
          ring
    have hU : Matrix.diagonal (fun i : Fin 3 =>
        if i = 2 then (-1 : ℂ) else 1) ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.diagonal, Matrix.mul_apply, Matrix.star_apply, RCLike.star_def]
    have hlower : 2 * t ≤ traceNorm A := by
      have h := (traceNorm_eq_max_re_tr_U A).2
        ⟨⟨Matrix.diagonal (fun i : Fin 3 => if i = 2 then (-1 : ℂ) else 1), hU⟩, rfl⟩
      have htrace : ((Matrix.diagonal (fun i : Fin 3 =>
          if i = 2 then (-1 : ℂ) else 1) * A).trace).re = 2 * t := by
        simp [A, Matrix.trace_diagonal, Matrix.diagonal_mul_diagonal, Fin.sum_univ_three]
        ring
      rw [htrace] at h
      exact h
    dsimp [A] at hupper hlower ⊢
    exact le_antisymm hupper hlower
  constructor
  · intro ε hε0 hε1
    dsimp only
    let C : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 0 then 1 else 0)
    let E0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 1 then 1 else 0)
    let E1 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 2 then 1 else 0)
    let rhoM : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 0 then (1 - ε : ℂ) else if i = 1 then (ε : ℂ) else 0)
    let sigmaM : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 0 then (1 - ε : ℂ) else if i = 2 then (ε : ℂ) else 0)
    let P : Matrix (Fin 3) (Fin 3) ℂ := E0 + E1
    have hρpsd : rhoM.PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i
      · simp [rhoM]
        exact_mod_cast hε1.le
      · simp [rhoM]
        positivity
      · simp [rhoM]
    have hσpsd : sigmaM.PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i
      · simp [sigmaM]
        exact_mod_cast hε1.le
      · simp [sigmaM]
      · simp [sigmaM]
        positivity
    have hρtrace : rhoM.trace = 1 := by
      simp [rhoM, Matrix.trace_diagonal, Fin.sum_univ_three]
    have hσtrace : sigmaM.trace = 1 := by
      simp [sigmaM, Matrix.trace_diagonal, Fin.sum_univ_three]
    let ρ : DensityState (Fin 3) :=
      ⟨CStarMatrix.ofMatrix rhoM,
        map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
          (Matrix.nonneg_iff_posSemidef.mpr hρpsd),
        hρtrace⟩
    let σ : DensityState (Fin 3) :=
      ⟨CStarMatrix.ofMatrix sigmaM,
        map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
          (Matrix.nonneg_iff_posSemidef.mpr hσpsd),
        hσtrace⟩
    have hinst : Pᴴ * P + Cᴴ * C = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, C, E0, E1, Matrix.diagonal, Matrix.mul_apply,
          Matrix.star_apply, RCLike.star_def]
    have hPproj : Pᴴ * P = P := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, E0, E1, Matrix.diagonal, Matrix.mul_apply,
          Matrix.star_apply, RCLike.star_def]
    have hCpsd : C.PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> simp [C]
    have hPbound : Pᴴ * P ≤ 1 := by
      rw [Matrix.le_iff, hPproj]
      have hcomp : 1 - P = C := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [P, C, E0, E1, Matrix.diagonal]
      rw [hcomp]
      exact hCpsd
    have hdiff : rhoM - sigmaM = Matrix.diagonal (fun i : Fin 3 =>
        if i = 0 then (0 : ℂ) else if i = 1 then (ε : ℂ) else (-ε : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rhoM, sigmaM, Matrix.diagonal]
    have hD : traceDistance ρ σ = ε := by
      unfold traceDistance
      change traceNorm (rhoM - sigmaM) / 2 = ε
      rw [hdiff, hdiagNorm ε hε0.le]
      ring
    have hp : (rhoM * Pᴴ * P).trace.re = ε := by
      rw [Matrix.mul_assoc, hPproj]
      simp [rhoM, P, E0, E1, Matrix.trace, Matrix.mul_apply,
        Matrix.diagonal, Fin.sum_univ_three, Matrix.star_apply,
        RCLike.star_def]
    have hq : (sigmaM * Pᴴ * P).trace.re = ε := by
      rw [Matrix.mul_assoc, hPproj]
      simp [sigmaM, P, E0, E1, Matrix.trace, Matrix.mul_apply,
        Matrix.diagonal, Fin.sum_univ_three, Matrix.star_apply,
        RCLike.star_def]
    have hcondρ : (1 / ε : ℝ) • (P * rhoM * Pᴴ) = E0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, rhoM, E0, E1, Matrix.diagonal, Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal, Matrix.mul_apply, Matrix.star_apply,
          RCLike.star_def, hε0.ne']
      all_goals field_simp [hε0.ne']
    have hcondσ : (1 / ε : ℝ) • (P * sigmaM * Pᴴ) = E1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, sigmaM, E0, E1, Matrix.diagonal, Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal, Matrix.mul_apply, Matrix.star_apply,
          RCLike.star_def, hε0.ne']
      all_goals field_simp [hε0.ne']
    have hcondNorm : traceNorm (E0 - E1) / 2 = 1 := by
      have he : E0 - E1 = Matrix.diagonal (fun i : Fin 3 =>
          if i = 0 then (0 : ℂ) else if i = 1 then (1 : ℂ) else (-1 : ℂ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [E0, E1, Matrix.diagonal]
      rw [he]
      have hnorm : traceNorm (Matrix.diagonal (fun i : Fin 3 =>
          if i = 0 then (0 : ℂ) else if i = 1 then (1 : ℂ) else (-1 : ℂ))) = 2 := by
        simpa using hdiagNorm (1 : ℝ) (by norm_num)
      rw [hnorm]
      norm_num
    have hw : max ε ε * (traceNorm (
        (1 / ε : ℝ) • (P * rhoM * Pᴴ) -
        (1 / ε : ℝ) • (P * sigmaM * Pᴴ)) / 2) = traceDistance ρ σ := by
      rw [hcondρ, hcondσ, hcondNorm, max_self, hD]
      ring
    refine ⟨ρ, σ, P, C, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, hinst, hPbound, hD, ?_, ?_, ?_, ?_,
      hcondNorm, ?_, ?_⟩
    · simp [ρ, rhoM]
    · simp [σ, sigmaM]
    · rfl
    · rfl
    · simpa [ρ, rhoM, P] using hp
    · simpa [σ, sigmaM, P] using hq
    · simpa [ρ, rhoM, P, E0] using hcondρ
    · simpa [σ, sigmaM, P, E1] using hcondσ
    · rfl
    · simpa [ρ, σ, rhoM, sigmaM, P] using hw
  · rintro ⟨f, hlim, hall⟩
    have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, f t < 1 :=
      (tendsto_order.1 hlim).2 1 zero_lt_one
    have hev' := hev.and (nhdsGT_basis 0 |>.mem_of_mem zero_lt_one)
    obtain ⟨t, ht⟩ := hev'.exists
    have ht0 : 0 < t := ht.2.1
    have ht1 : t < 1 := ht.2.2
    let C : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 0 then 1 else 0)
    let E0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 1 then 1 else 0)
    let E1 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 2 then 1 else 0)
    let rhoM : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 0 then (1 - t : ℂ) else if i = 1 then (t : ℂ) else 0)
    let sigmaM : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i =>
      if i = 0 then (1 - t : ℂ) else if i = 2 then (t : ℂ) else 0)
    let P : Matrix (Fin 3) (Fin 3) ℂ := E0 + E1
    have hρpsd : rhoM.PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i
      · simp [rhoM]
        exact_mod_cast ht1.le
      · simp [rhoM]
        positivity
      · simp [rhoM]
    have hσpsd : sigmaM.PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i
      · simp [sigmaM]
        exact_mod_cast ht1.le
      · simp [sigmaM]
      · simp [sigmaM]
        positivity
    have hρtrace : rhoM.trace = 1 := by
      simp [rhoM, Matrix.trace_diagonal, Fin.sum_univ_three]
    have hσtrace : sigmaM.trace = 1 := by
      simp [sigmaM, Matrix.trace_diagonal, Fin.sum_univ_three]
    let ρ : DensityState (Fin 3) :=
      ⟨CStarMatrix.ofMatrix rhoM,
        map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
          (Matrix.nonneg_iff_posSemidef.mpr hρpsd), hρtrace⟩
    let σ : DensityState (Fin 3) :=
      ⟨CStarMatrix.ofMatrix sigmaM,
        map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
          (Matrix.nonneg_iff_posSemidef.mpr hσpsd), hσtrace⟩
    have hPproj : Pᴴ * P = P := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, E0, E1, Matrix.diagonal, Matrix.mul_apply,
          Matrix.star_apply, RCLike.star_def]
    have hCpsd : C.PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> simp [C]
    have hPbound : Pᴴ * P ≤ 1 := by
      rw [Matrix.le_iff, hPproj]
      have hcomp : 1 - P = C := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [P, C, E0, E1, Matrix.diagonal]
      rw [hcomp]
      exact hCpsd
    have hp : (rhoM * Pᴴ * P).trace.re = t := by
      rw [Matrix.mul_assoc, hPproj]
      simp [rhoM, P, E0, E1, Matrix.trace, Matrix.mul_apply,
        Matrix.diagonal, Fin.sum_univ_three, Matrix.star_apply,
        RCLike.star_def]
    have hq : (sigmaM * Pᴴ * P).trace.re = t := by
      rw [Matrix.mul_assoc, hPproj]
      simp [sigmaM, P, E0, E1, Matrix.trace, Matrix.mul_apply,
        Matrix.diagonal, Fin.sum_univ_three, Matrix.star_apply,
        RCLike.star_def]
    have hcondρ : (1 / t : ℝ) • (P * rhoM * Pᴴ) = E0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, rhoM, E0, E1, Matrix.diagonal, Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal, Matrix.mul_apply, Matrix.star_apply,
          RCLike.star_def, ht0.ne']
      all_goals field_simp [ht0.ne']
    have hcondσ : (1 / t : ℝ) • (P * sigmaM * Pᴴ) = E1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, sigmaM, E0, E1, Matrix.diagonal, Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal, Matrix.mul_apply, Matrix.star_apply,
          RCLike.star_def, ht0.ne']
      all_goals field_simp [ht0.ne']
    have hD : traceDistance ρ σ = t := by
      have hdiff : rhoM - sigmaM = Matrix.diagonal (fun i : Fin 3 =>
          if i = 0 then (0 : ℂ) else if i = 1 then (t : ℂ) else (-t : ℂ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [rhoM, sigmaM, Matrix.diagonal]
      unfold traceDistance
      change traceNorm (rhoM - sigmaM) / 2 = t
      rw [hdiff, hdiagNorm t ht0.le]
      ring
    have hρpos : 0 < (CStarMatrix.ofMatrix.symm ρ.val * Pᴴ * P).trace.re := by
      change 0 < (rhoM * Pᴴ * P).trace.re
      rw [hp]
      exact ht0
    have hσpos : 0 < (CStarMatrix.ofMatrix.symm σ.val * Pᴴ * P).trace.re := by
      change 0 < (sigmaM * Pᴴ * P).trace.re
      rw [hq]
      exact ht0
    have hineq := hall ρ σ P hPbound hρpos hσpos
    simp only [ρ, σ, CStarMatrix.ofMatrix_symm_apply] at hineq
    rw [hD] at hineq
    change traceNorm (
      (1 / (rhoM * Pᴴ * P).trace.re : ℝ) • (P * rhoM * Pᴴ) -
      (1 / (sigmaM * Pᴴ * P).trace.re : ℝ) • (P * sigmaM * Pᴴ)) / 2 ≤ f t at hineq
    rw [hp, hq, hcondρ, hcondσ] at hineq
    have hunit : traceNorm (E0 - E1) / 2 = 1 := by
      have he : E0 - E1 = Matrix.diagonal (fun i : Fin 3 =>
          if i = 0 then (0 : ℂ) else if i = 1 then (1 : ℂ) else (-1 : ℂ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [E0, E1, Matrix.diagonal]
      rw [he]
      have hnorm : traceNorm (Matrix.diagonal (fun i : Fin 3 =>
          if i = 0 then (0 : ℂ) else if i = 1 then (1 : ℂ) else (-1 : ℂ))) = 2 := by
        simpa using hdiagNorm (1 : ℝ) (by norm_num)
      rw [hnorm]
      norm_num
    rw [hunit] at hineq
    exact (not_lt_of_ge hineq) ht.1

#print axioms rare_branch_conditional_error_sharpness

end D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness
