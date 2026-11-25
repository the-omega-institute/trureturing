/- GID: D5/S3/Quantum/Recovery/PetzPhysicalQubitRoot
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/PetzPhysicalQubitRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact normalized square root and first variation of a physical Petz flag. -/

import D5.S3.Quantum.CommutingMidpoint.Fidelity
import D5.S3.Quantum.Matrix.SpectralPower
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The normalized square root of a real qubit flag in the retained basis. -/

noncomputable section

open Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.CommutingMidpoint (sqrt_times_trace_two sqrt_trace_square_two)

namespace D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

/-- A qubit matrix in the physical retained basis, with real entries. -/
def qubit (a b c d : ℝ) : Qubit := !![(a : ℂ), (b : ℂ); (c : ℂ), (d : ℂ)]

/-- The determinant of the flag correlation block before the reference scaling. -/
def detFactor (x c : ℝ) : ℝ := (1 - x) * (1 + x) - (2 * x * c) ^ 2

/-- The reference block after removing the common scalar. -/
def unscaledBlock (x η c : ℝ) : Qubit :=
  qubit (η ^ 2 * (1 - x)) (η * (2 * x * c)) (η * (2 * x * c)) (1 + x)

/-- The half-power with the marginal inverse half-power on the right.
The common scalar in the reference and its marginal cancels. -/
def normalizedRoot (x η c : ℝ) : Qubit :=
  mpow (unscaledBlock x η c) (1 / 2) * qubit η⁻¹ 0 0 1

private theorem symmetric_posDef {a v d : ℝ} (ha : 0 < a) (hdet : 0 < a * d - v ^ 2) :
    (qubit a v v d).PosDef := by
  let L := qubit (Real.sqrt a) 0 (v / Real.sqrt a) (Real.sqrt (d - v ^ 2 / a))
  have hs := Real.sq_sqrt ha.le
  have hr : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hres : 0 ≤ d - v ^ 2 / a := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ ha).mpr (by linarith)
  have ha' : Real.sqrt a * Real.sqrt a = a := by simpa [pow_two] using hs
  have hd' : Real.sqrt (d - v ^ 2 / a) * Real.sqrt (d - v ^ 2 / a) =
      d - v ^ 2 / a := Real.mul_self_sqrt hres
  have hf : qubit a v v d = L * Lᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [L, qubit, Matrix.mul_apply, Fin.sum_univ_two, ha', hd']
    · field_simp
    · field_simp
    · rw [← sq, div_pow, hs]
      ring
  apply (hf ▸ Matrix.posSemidef_self_mul_conjTranspose L).posDef_iff_det_ne_zero.mpr
  have hv : (qubit a v v d).det.re = a * d - v ^ 2 := by
    simp [qubit, Matrix.det_fin_two, pow_two]
  intro hz
  rw [hz, Complex.zero_re] at hv
  linarith

theorem unscaledBlock_posDef {x η c : ℝ} (hη : 0 < η) (hb : 0 < 1 - x)
    (hδ : 0 < detFactor x c) : (unscaledBlock x η c).PosDef := by
  apply symmetric_posDef (by positivity)
  convert mul_pos (sq_pos_of_pos hη) hδ using 1
  unfold detFactor
  ring

/-- The exact denominator in the normalized qubit square root. -/
def rootDen (x η c : ℝ) : ℝ :=
  Real.sqrt (η ^ 2 * (1 - x) + (1 + x) + 2 * η * Real.sqrt (detFactor x c))

theorem normalizedRoot_formula {x η c : ℝ} (hη : 0 < η) (hb : 0 < 1 - x)
    (hd : 0 < 1 + x) (hδ : 0 < detFactor x c) :
    normalizedRoot x η c =
      qubit ((η * (1 - x) + Real.sqrt (detFactor x c)) / rootDen x η c)
        (η * (2 * x * c) / rootDen x η c)
        (2 * x * c / rootDen x η c)
        (((1 + x) + η * Real.sqrt (detFactor x c)) / rootDen x η c) := by
  let M := unscaledBlock x η c
  have hM := (unscaledBlock_posDef hη hb hδ).posSemidef
  have hsqrt : mpow M (1 / 2) = CFC.sqrt M := by
    rw [mpow, ← CFC.rpow_eq_cfc_real hM.nonneg, ← CFC.sqrt_eq_rpow]
  have hdet : M.det.re = η ^ 2 * detFactor x c := by
    simp [M, unscaledBlock, qubit, detFactor, Matrix.det_fin_two, pow_two]
    ring
  have htrace : M.trace.re = η ^ 2 * (1 - x) + (1 + x) := by
    simp [M, unscaledBlock, qubit, Matrix.trace_fin_two, pow_two]
  have hr : Real.sqrt M.det.re = η * Real.sqrt (detFactor x c) := by
    rw [hdet, Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le]
  have hD : 0 < rootDen x η c := by unfold rootDen; positivity
  have htr : (CFC.sqrt M).trace.re = rootDen x η c := by
    symm
    unfold rootDen
    rw [Real.sqrt_eq_iff_eq_sq (by positivity)
      (Complex.nonneg_iff.mp (CFC.sqrt_nonneg M).posSemidef.trace_nonneg).1,
      sqrt_trace_square_two M hM, htrace, hr]
    ring
  have he (i j : Fin 2) :
      (CFC.sqrt M) i j =
        (M i j + (η * Real.sqrt (detFactor x c) : ℝ) • (1 : Qubit) i j) /
          (rootDen x η c : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hD.ne')).2
    simpa [hr, htr, mul_comm] using
      congrArg (fun A : Qubit => A i j) (sqrt_times_trace_two M hM)
  rw [normalizedRoot, show unscaledBlock x η c = M from rfl, hsqrt]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, he]
  fin_cases i <;> fin_cases j <;>
    simp [qubit, Matrix.one_apply, M, unscaledBlock] <;>
    field_simp [hη.ne', hD.ne']

private theorem root_data {x η : ℝ} (hη : 0 < η) (hb : 0 < 1 - x) (hd : 0 < 1 + x) :
    rootDen x η 0 = η * Real.sqrt (1 - x) + Real.sqrt (1 + x) ∧
    HasDerivAt (fun c => Real.sqrt (detFactor x c)) 0 0 ∧
    HasDerivAt (rootDen x η) 0 0 := by
  have hδ : detFactor x 0 = (1 - x) * (1 + x) := by simp [detFactor]
  have hδpos : 0 < detFactor x 0 := hδ ▸ mul_pos hb hd
  have hδ' : HasDerivAt (detFactor x) 0 0 := by
    unfold detFactor
    convert (hasDerivAt_const (0 : ℝ) ((1 - x) * (1 + x))).sub
      (((hasDerivAt_id (0 : ℝ)).const_mul (2 * x)).pow 2) using 1
    · rfl
    · simp
  have hd' := hδ'.sqrt hδpos.ne'
  have hval : rootDen x η 0 = η * Real.sqrt (1 - x) + Real.sqrt (1 + x) := by
    unfold rootDen
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), hδ, Real.sqrt_mul hb.le]
    nlinarith only [Real.sq_sqrt hb.le, Real.sq_sqrt hd.le,
      congrArg (fun r : ℝ => η ^ 2 * r) (Real.sq_sqrt hb.le)]
  refine ⟨hval, by simpa using hd', ?_⟩
  have hinner := (hasDerivAt_const (0 : ℝ) (η ^ 2 * (1 - x) + (1 + x))).add
    ((show HasDerivAt (fun c => Real.sqrt (detFactor x c)) 0 0 by simpa using hd').const_mul
      (2 * η))
  have hpos : 0 < η ^ 2 * (1 - x) + (1 + x) + 2 * η * Real.sqrt (detFactor x 0) :=
    by positivity
  exact (show HasDerivAt (fun c => Real.sqrt
      (η ^ 2 * (1 - x) + (1 + x) + 2 * η * Real.sqrt (detFactor x c))) 0 0 by
    simpa using hinner.sqrt hpos.ne')

theorem normalizedRoot_firstVariation {x η : ℝ} (hη : 0 < η) (hb : 0 < 1 - x)
    (hd : 0 < 1 + x) :
    let denom := η * Real.sqrt (1 - x) + Real.sqrt (1 + x)
    normalizedRoot x η 0 = qubit (Real.sqrt (1 - x)) 0 0 (Real.sqrt (1 + x)) ∧
      HasDerivAt (normalizedRoot x η) (qubit 0 (2 * x * η / denom) (2 * x / denom) 0) 0 := by
  dsimp
  obtain ⟨hval, hs, hden⟩ := root_data hη hb hd
  have hD : 0 < rootDen x η 0 := by rw [hval]; positivity
  have hδ : 0 < detFactor x 0 := by simpa [detFactor] using mul_pos hb hd
  refine ⟨?_, ?_⟩
  · rw [normalizedRoot_formula hη hb hd hδ, hval]
    have hD' : 0 < η * Real.sqrt (1 - x) + Real.sqrt (1 + x) := by positivity
    have h00 : (η * (1 - x) + Real.sqrt (detFactor x 0)) /
        (η * Real.sqrt (1 - x) + Real.sqrt (1 + x)) = Real.sqrt (1 - x) := by
      rw [div_eq_iff hD'.ne']
      simp [detFactor, Real.sqrt_mul hb.le]
      nlinarith only [congrArg (fun r : ℝ => η * r) (Real.sq_sqrt hb.le)]
    have h11 : (1 + x + η * Real.sqrt (detFactor x 0)) /
        (η * Real.sqrt (1 - x) + Real.sqrt (1 + x)) = Real.sqrt (1 + x) := by
      rw [div_eq_iff hD'.ne']
      simp [detFactor, Real.sqrt_mul hb.le]
      nlinarith only [Real.sq_sqrt hd.le]
    simp [h00, h11]
  · have hnear : ∀ᶠ c in 𝓝 (0 : ℝ), 0 < detFactor x c := by
      have hc : Continuous (detFactor x) := by unfold detFactor; fun_prop
      exact hc.continuousAt.eventually (lt_mem_nhds hδ)
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have h00 := ((hasDerivAt_const (0 : ℝ) (η * (1 - x))).add hs).div hden hD.ne'
    have h11 := ((hasDerivAt_const (0 : ℝ) (1 + x)).add (hs.const_mul η)).div hden hD.ne'
    have h01 : HasDerivAt (fun c => η * (2 * x * c) / rootDen x η c)
        (2 * x * η / (η * Real.sqrt (1 - x) + Real.sqrt (1 + x))) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).const_mul (2 * x)).const_mul η).div hden hD.ne'
        using 1
      · rfl
      · rw [← hval]
        simp only [id_eq, mul_one, mul_zero, sub_zero]
        field_simp [hD.ne']
    have h10 : HasDerivAt (fun c => 2 * x * c / rootDen x η c)
        (2 * x / (η * Real.sqrt (1 - x) + Real.sqrt (1 + x))) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).const_mul (2 * x)).div hden hD.ne' using 1
      · rfl
      · rw [← hval]
        simp only [id_eq, mul_one, mul_zero, sub_zero]
        field_simp [hD.ne']
    fin_cases i <;> fin_cases j
    · have h := h00.ofReal_comp
      simp only [zero_add, zero_mul, mul_zero, sub_zero, zero_div, Complex.ofReal_zero] at h
      exact h.congr_of_eventuallyEq (by
        filter_upwards [hnear] with c hc
        rw [normalizedRoot_formula hη hb hd hc] <;> rfl)
    · exact h01.ofReal_comp.congr_of_eventuallyEq (by
        filter_upwards [hnear] with c hc
        rw [normalizedRoot_formula hη hb hd hc] <;> rfl)
    · exact h10.ofReal_comp.congr_of_eventuallyEq (by
        filter_upwards [hnear] with c hc
        rw [normalizedRoot_formula hη hb hd hc] <;> rfl)
    · have h := h11.ofReal_comp
      simp only [zero_add, zero_mul, mul_zero, sub_zero, zero_div, Complex.ofReal_zero] at h
      exact h.congr_of_eventuallyEq (by
        filter_upwards [hnear] with c hc
        rw [normalizedRoot_formula hη hb hd hc] <;> rfl)

end D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
