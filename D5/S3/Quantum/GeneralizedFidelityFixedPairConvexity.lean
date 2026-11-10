/- GID: D5/S3/Quantum/GeneralizedFidelityFixedPairConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/GeneralizedFidelityFixedPairConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-pair convexity iff Hermitian coefficient positivity. -/

import D5.S3.Quantum.GeneralizedFidelity
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! # Fixed-pair qubit convexity on the full density-state domain -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

local notation "M2" => D5.S3.Quantum.FiniteDimensional.QubitMatrix

/-- The raw matrices of the canonical positive trace-one density states. -/
def densitySet : Set M2 := {P | P.PosSemidef ∧ Matrix.trace P = 1}

/-- The actual Hermitian coefficient of the square-root trace functional. -/
def coefficient (R Q : M2) : M2 :=
  (1 / 2 : ℝ) • (R⁻¹ * CFC.sqrt (CFC.sqrt R * Q * CFC.sqrt R) +
    CFC.sqrt (CFC.sqrt R * Q * CFC.sqrt R) * R⁻¹)

private theorem root_hermitian (A : M2) : (CFC.sqrt A).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian

private theorem coefficient_hermitian (R Q : M2) (hR : R.PosDef) :
    (coefficient R Q).IsHermitian := by
  have hI := hR.inv.isHermitian
  have hD := root_hermitian (CFC.sqrt R * Q * CFC.sqrt R)
  change (coefficient R Q)ᴴ = coefficient R Q
  simp only [coefficient, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hI.eq, hD.eq, star_trivial]
  rw [add_comm]

private theorem fidelity_trace_root (R P Q : M2) (hR : R.PosDef) :
    (GeneralizedFidelity.fidelity R P Q).re =
      (Matrix.trace (coefficient R Q * CFC.sqrt (CFC.sqrt R * P * CFC.sqrt R))).re := by
  let H := CFC.sqrt (CFC.sqrt R * P * CFC.sqrt R)
  let D := CFC.sqrt (CFC.sqrt R * Q * CFC.sqrt R)
  have hH : Hᴴ = H := (root_hermitian _).eq
  have hD : Dᴴ = D := (root_hermitian _).eq
  have hI : (R⁻¹)ᴴ = R⁻¹ := hR.inv.isHermitian.eq
  have hconj : (Matrix.trace (D * R⁻¹ * H)).re =
      (Matrix.trace (H * R⁻¹ * D)).re := by
    calc
      _ = (star (Matrix.trace (H * R⁻¹ * D))).re := by
        rw [← Matrix.trace_conjTranspose]
        simp only [Matrix.conjTranspose_mul, hH, hD, hI, Matrix.mul_assoc]
      _ = _ := Complex.conj_re _
  have hcycle : Matrix.trace (R⁻¹ * D * H) = Matrix.trace (H * R⁻¹ * D) := by
    rw [Matrix.trace_mul_cycle]
  change (Matrix.trace (H * R⁻¹ * D)).re = _
  change _ = (Matrix.trace ((1 / 2 : ℝ) • (R⁻¹ * D + D * R⁻¹) * H)).re
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add]
  simp only [Complex.smul_re, smul_eq_mul, Complex.add_re, hcycle, hconj]
  ring

private theorem density_convex : Convex ℝ densitySet := by
  intro P hP T hT a b ha hb hab
  refine ⟨(hP.1.smul ha).add (hT.1.smul hb), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hP.2, hT.2]
  rw [← add_smul, hab, one_smul]

private theorem bures_trace_one (R Q P : M2) (hQ : Matrix.trace Q = 1)
    (hP : P ∈ densitySet) :
    GeneralizedFidelity.bures R P Q = 2 - 2 * (GeneralizedFidelity.fidelity R P Q).re := by
  norm_num [GeneralizedFidelity.bures, Matrix.trace_add, hP.2, hQ]

private theorem bures_convex_iff_fidelity_concave (Q R : M2) (hQ : Matrix.trace Q = 1) :
    ConvexOn ℝ densitySet (fun P => GeneralizedFidelity.bures R P Q) ↔
      ConcaveOn ℝ densitySet (fun P => (GeneralizedFidelity.fidelity R P Q).re) := by
  constructor
  · intro h
    refine ⟨density_convex, ?_⟩
    intro P hP T hT a b ha hb hab
    have hm := h.2 hP hT ha hb hab
    dsimp only at hm ⊢
    rw [bures_trace_one R Q P hQ hP, bures_trace_one R Q T hQ hT,
      bures_trace_one R Q _ hQ (density_convex hP hT ha hb hab)] at hm
    simp only [smul_eq_mul] at *
    nlinarith
  · intro h
    refine ⟨density_convex, ?_⟩
    intro P hP T hT a b ha hb hab
    have hm := h.2 hP hT ha hb hab
    dsimp only at hm ⊢
    rw [bures_trace_one R Q P hQ hP, bures_trace_one R Q T hQ hT,
      bures_trace_one R Q _ hQ (density_convex hP hT ha hb hab)]
    simp only [smul_eq_mul] at *
    nlinarith

private theorem fidelity_concave_of_coefficient (Q R : M2) (hR : R.PosDef)
    (hC : (coefficient R Q).PosSemidef) :
    ConcaveOn ℝ densitySet (fun P => (GeneralizedFidelity.fidelity R P Q).re) := by
  refine ⟨density_convex, ?_⟩
  intro P hP T hT a b ha hb hab
  have hS := root_hermitian R
  have hA : 0 ≤ CFC.sqrt R * P * CFC.sqrt R := by
    simpa only [hS.eq] using (hP.1.conjTranspose_mul_mul_same (CFC.sqrt R)).nonneg
  have hB : 0 ≤ CFC.sqrt R * T * CFC.sqrt R := by
    simpa only [hS.eq] using (hT.1.conjTranspose_mul_mul_same (CFC.sqrt R)).nonneg
  have hm := (CFC.concaveOn_sqrt (A := M2)).2 hA hB ha hb hab
  have ht := RHLinalg.trace_mul_nonneg_of_posSemidef hC (Matrix.le_iff.mp hm)
  have hsand : CFC.sqrt R * (a • P + b • T) * CFC.sqrt R =
      a • (CFC.sqrt R * P * CFC.sqrt R) + b • (CFC.sqrt R * T * CFC.sqrt R) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  dsimp only
  rw [fidelity_trace_root R P Q hR, fidelity_trace_root R T Q hR,
    fidelity_trace_root R _ Q hR, hsand]
  simpa only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, RCLike.re_to_complex,
    Complex.sub_re, Complex.add_re, Complex.smul_re, smul_eq_mul, sub_nonneg] using ht

private theorem unitary_diagonal_sqrt (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (d : Fin 2 → ℝ) (hd : ∀ i, 0 ≤ d i) :
    CFC.sqrt ((U : M2) * Matrix.diagonal (fun i => (d i : ℂ)) * star (U : M2)) =
      (U : M2) * Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)) * star (U : M2) := by
  let φ := Unitary.conjStarAlgAut ℂ M2 U
  have hsquare : Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)) *
      Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)) =
      Matrix.diagonal (fun i => (d i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (hd i)
  apply CFC.sqrt_unique
  · change φ (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ))) *
      φ (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ))) =
      φ (Matrix.diagonal (fun i => (d i : ℂ)))
    rw [← map_mul, hsquare]
  · exact (Matrix.PosSemidef.diagonal (by
      intro i
      change (0 : ℂ) ≤ (Real.sqrt (d i) : ℂ)
      exact_mod_cast Real.sqrt_nonneg (d i))).mul_mul_conjTranspose_same (U : M2) |>.nonneg

private theorem trace_unitary_diagonal (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (d : Fin 2 → ℂ) :
    Matrix.trace ((U : M2) * Matrix.diagonal d * star (U : M2)) = ∑ i, d i := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]

private theorem trace_spectral_pair (C : M2) (hC : C.IsHermitian)
    (d : Fin 2 → ℝ) :
    (Matrix.trace (C * ((hC.eigenvectorUnitary : M2) *
      Matrix.diagonal (fun i => (d i : ℂ)) * star (hC.eigenvectorUnitary : M2)))).re =
      ∑ i, hC.eigenvalues i * d i := by
  let φ := Unitary.conjStarAlgAut ℂ M2 hC.eigenvectorUnitary
  have heq : C * ((hC.eigenvectorUnitary : M2) *
      Matrix.diagonal (fun i => (d i : ℂ)) * star (hC.eigenvectorUnitary : M2)) =
      φ (Matrix.diagonal (fun i => ((hC.eigenvalues i * d i : ℝ) : ℂ))) := by
    conv_lhs => lhs; rw [hC.spectral_theorem]
    change φ (Matrix.diagonal (fun i => (hC.eigenvalues i : ℂ))) *
      φ (Matrix.diagonal (fun i => (d i : ℂ))) = _
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    simp
  rw [heq]
  change (Matrix.trace ((hC.eigenvectorUnitary : M2) * _ *
    star (hC.eigenvectorUnitary : M2))).re = _
  rw [trace_unitary_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

private theorem sqrt_chord_forces_nonneg (a b : ℝ)
    (hchord : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 - t) * b + t * a ≤ a * Real.sqrt t + b * Real.sqrt (1 - t)) :
    0 ≤ a := by
  have hevent : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ a + (|a| + |b|) * x := by
    have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with x hx hx1
    have hx0 : 0 < x := hx
    have ht : x ^ 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨sq_nonneg x, by nlinarith⟩
    have hu0 : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
    have hu2 := Real.sq_sqrt (show 0 ≤ 1 - x ^ 2 by linarith [ht.2])
    have hu1 : Real.sqrt (1 - x ^ 2) ≤ 1 := by nlinarith [sq_nonneg x]
    have hulow : 1 - x ^ 2 ≤ Real.sqrt (1 - x ^ 2) := by nlinarith
    have hbnd : -|b| * x ^ 2 ≤ b * (1 - x ^ 2 - Real.sqrt (1 - x ^ 2)) := by
      by_cases hb : 0 ≤ b
      · rw [abs_of_nonneg hb]
        nlinarith [mul_nonneg hb (sub_nonneg.mpr hu1)]
      · have hb' : b ≤ 0 := le_of_not_ge hb
        have hp := mul_nonneg_of_nonpos_of_nonpos hb'
          (show 1 - x ^ 2 - Real.sqrt (1 - x ^ 2) ≤ 0 by linarith)
        nlinarith [mul_nonneg (abs_nonneg b) (sq_nonneg x)]
    have habnd := mul_le_mul_of_nonneg_right (neg_abs_le a) (sq_nonneg x)
    have h := hchord (x ^ 2) ht
    rw [Real.sqrt_sq hx0.le] at h
    have hp : 0 ≤ x * (a + (|a| + |b|) * x) := by nlinarith
    exact nonneg_of_mul_nonneg_right hp hx0
  have hlim : Filter.Tendsto (fun x : ℝ => a + (|a| + |b|) * x)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hc : ContinuousAt (fun x : ℝ => a + (|a| + |b|) * x) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim hevent

private theorem coefficient_posSemidef_of_concave (Q R : M2) (hR : R.PosDef)
    (hc : ConcaveOn ℝ densitySet (fun P => (GeneralizedFidelity.fidelity R P Q).re)) :
    (coefficient R Q).PosSemidef := by
  classical
  let C := coefficient R Q
  have hC : C.IsHermitian := coefficient_hermitian R Q hR
  let U := hC.eigenvectorUnitary
  let S := CFC.sqrt R
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff R hR.posSemidef.nonneg).2 hR.isUnit
  have hSstar : Sᴴ = S := (root_hermitian R).eq
  let V : M2 := S⁻¹ * (U : M2)
  have hVunit : IsUnit V := (Matrix.isUnit_nonsing_inv_iff.2 hSunit).mul
    (Unitary.isUnit_coe (U := U))
  have hH : (Vᴴ * V).PosDef := by
    have h := hVunit.posDef_star_left_conjugate_iff (x := (1 : M2))
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_one] using h.mpr Matrix.PosDef.one
  let α : ℝ := (Vᴴ * V) 0 0 |>.re
  let β : ℝ := (Vᴴ * V) 1 1 |>.re
  have hα : 0 < α := (Complex.pos_iff.mp (hH.diag_pos (i := 0))).1
  have hβ : 0 < β := (Complex.pos_iff.mp (hH.diag_pos (i := 1))).1
  have hαC : (Vᴴ * V) 0 0 = (α : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.pos_iff.mp (hH.diag_pos (i := 0))).2.symm
  have hβC : (Vᴴ * V) 1 1 = (β : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.pos_iff.mp (hH.diag_pos (i := 1))).2.symm
  let d (t : ℝ) : Fin 2 → ℝ := ![(1 - t) / α, t / β]
  let P (t : ℝ) : M2 := V * Matrix.diagonal (fun i => (d t i : ℂ)) * Vᴴ
  have hP (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : P t ∈ densitySet := by
    refine ⟨?_, ?_⟩
    · apply Matrix.PosSemidef.mul_mul_conjTranspose_same
      apply Matrix.PosSemidef.diagonal
      intro i
      fin_cases i
      · change (0 : ℂ) ≤ (((1 - t) / α : ℝ) : ℂ)
        exact_mod_cast div_nonneg (sub_nonneg.mpr ht.2) hα.le
      · change (0 : ℂ) ≤ ((t / β : ℝ) : ℂ)
        exact_mod_cast div_nonneg ht.1 hβ.le
    · change Matrix.trace (V * _ * Vᴴ) = 1
      rw [Matrix.trace_mul_cycle]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fin.sum_univ_two,
        hαC, hβC, d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      push_cast
      field_simp [ne_of_gt hα, ne_of_gt hβ]
      ring
  have hPaff (t : ℝ) : P t = (1 - t) • P 0 + t • P 1 := by
    have hd : Matrix.diagonal (fun i => (d t i : ℂ)) =
        (1 - t) • Matrix.diagonal (fun i => (d 0 i : ℂ)) +
          t • Matrix.diagonal (fun i => (d 1 i : ℂ)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply]
      fin_cases i <;> fin_cases j <;>
        simp [d, Matrix.diagonal, Complex.real_smul] <;> ring
    dsimp only [P]
    rw [hd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hSV : S * V = (U : M2) := by
    dsimp [V]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSunit),
      Matrix.one_mul]
  have hA (t : ℝ) : S * P t * S =
      (U : M2) * Matrix.diagonal (fun i => (d t i : ℂ)) * star (U : M2) := by
    change S * (V * _ * Vᴴ) * S = _
    calc
      _ = (S * V) * Matrix.diagonal (fun i => (d t i : ℂ)) * (S * V)ᴴ := by
        simp only [Matrix.conjTranspose_mul, hSstar, Matrix.mul_assoc]
      _ = _ := by rw [hSV]; rfl
  have hF (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (GeneralizedFidelity.fidelity R (P t) Q).re =
        (hC.eigenvalues 0 / Real.sqrt α) * Real.sqrt (1 - t) +
        (hC.eigenvalues 1 / Real.sqrt β) * Real.sqrt t := by
    rw [fidelity_trace_root R (P t) Q hR]
    change (Matrix.trace (C * CFC.sqrt (S * P t * S))).re = _
    rw [hA, unitary_diagonal_sqrt U (d t)]
    · rw [trace_spectral_pair C hC]
      simp only [Fin.sum_univ_two, d, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Real.sqrt_div' _ hα.le, Real.sqrt_div' _ hβ.le]
      ring
    · intro i
      fin_cases i
      · exact div_nonneg (sub_nonneg.mpr ht.2) hα.le
      · exact div_nonneg ht.1 hβ.le
  let a := hC.eigenvalues 1 / Real.sqrt β
  let b := hC.eigenvalues 0 / Real.sqrt α
  have hchord (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (1 - t) * b + t * a ≤ a * Real.sqrt t + b * Real.sqrt (1 - t) := by
    have hm := hc.2 (hP 0 (by norm_num)) (hP 1 (by norm_num))
      (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    dsimp only at hm
    rw [← hPaff, hF t ht, hF 0 (by norm_num), hF 1 (by norm_num)] at hm
    have hm' : (1 - t) * b + t * a ≤ b * Real.sqrt (1 - t) + a * Real.sqrt t := by
      simpa only [Real.sqrt_zero, Real.sqrt_one, sub_zero, sub_self,
        mul_zero, mul_one, add_zero, zero_add, smul_eq_mul] using hm
    calc
      _ ≤ b * Real.sqrt (1 - t) + a * Real.sqrt t := hm'
      _ = _ := add_comm _ _
  have ha : 0 ≤ a := sqrt_chord_forces_nonneg a b hchord
  have hb : 0 ≤ b := sqrt_chord_forces_nonneg b a (by
    intro t ht
    have h := hchord (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [sub_sub_cancel] at h
    calc
      (1 - t) * a + t * b = t * b + (1 - t) * a := add_comm _ _
      _ ≤ a * Real.sqrt (1 - t) + b * Real.sqrt t := h
      _ = _ := add_comm _ _)
  apply hC.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  fin_cases i
  · exact nonneg_of_mul_nonneg_left
      (show 0 ≤ hC.eigenvalues 0 * (Real.sqrt α)⁻¹ by simpa [b, div_eq_mul_inv] using hb)
      (inv_pos.mpr (Real.sqrt_pos.mpr hα))
  · exact nonneg_of_mul_nonneg_left
      (show 0 ≤ hC.eigenvalues 1 * (Real.sqrt β)⁻¹ by simpa [a, div_eq_mul_inv] using ha)
      (inv_pos.mpr (Real.sqrt_pos.mpr hβ))

/-- The all-density fixed-pair criterion. Trace normalization of the reference
and positivity of the second input are unnecessary for this stronger statement;
the original source domain is its direct specialization. -/
theorem fixed_pair_convexity_iff (Q R : M2) (hQtr : Matrix.trace Q = 1)
    (hR : R.PosDef) :
    ConvexOn ℝ densitySet (fun P => GeneralizedFidelity.bures R P Q) ↔
      (coefficient R Q).PosSemidef := by
  rw [bures_convex_iff_fidelity_concave Q R hQtr]
  exact ⟨coefficient_posSemidef_of_concave Q R hR,
    fidelity_concave_of_coefficient Q R hR⟩

end D5.S3.Quantum.GeneralizedFidelityFixedPairConvexity
