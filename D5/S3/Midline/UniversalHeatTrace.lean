/- GID: D5/S3/Midline/UniversalHeatTrace
   generality: G
   mirror-B: D5/B/S3/Midline/UniversalHeatTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive the universal heat-trace midline from its abscissa and half-density weight. -/

import Mathlib.Analysis.InnerProductSpace.l2Space

namespace D5.S3.Midline.UniversalHeatTrace

open scoped ComplexConjugate

variable {A : Type*} [Countable A] [Zero A]

/-- The complex heat trace associated with a nonnegative length function. -/
noncomputable def heatTrace (M : A → ℝ) (s : ℂ) : ℂ :=
  ∑' a, Complex.exp (-s * (M a : ℂ))

/-- The labeled heat coefficient before imposing square summability. -/
noncomputable def heatCoefficient (M : A → ℝ) (s : ℂ) (a : A) : ℂ :=
  Complex.exp (-s * (M a : ℂ))

/-- The Hilbert space of square-summable labeled heat coefficients. -/
noncomputable abbrev HeatHilbertSpace := lp (fun _ : A => ℂ) 2

/-- The source convention is linear in the first displayed entry. -/
noncomputable def sourcePairing (x y : HeatHilbertSpace (A := A)) : ℂ :=
  inner ℂ y x

omit [Countable A] [Zero A] in theorem source_pairing_eq_tsum
    (x y : HeatHilbertSpace (A := A)) :
    sourcePairing x y = ∑' a, x a * conj (y a) := by
  rw [sourcePairing, lp.inner_eq_tsum]
  congr 1

omit [Countable A] [Zero A] in
@[simp]
theorem heatCoefficient_norm
    (M : A → ℝ) (s : ℂ) (a : A) :
    ‖heatCoefficient M s a‖ = Real.exp (-s.re * M a) := by
  rw [heatCoefficient, Complex.norm_exp]
  congr 1
  simp

/--
`α` is assumed to be the abscissa through `hAbscissa`; this module does not
construct the abscissa. The zero, nonnegativity, and nontriviality hypotheses
record the intended heat-length setting and are used by the half-density law.
-/
theorem heat_coefficient_mem_iff
    (M : A → ℝ) (α : ℝ)
    (_hM0 : M 0 = 0) (_hMnn : ∀ a, 0 ≤ M a) (_hMne : ∃ a, M a ≠ 0)
    (hAbscissa : ∀ σ : ℝ,
      Summable (fun a => Real.exp (-σ * M a)) ↔ α < σ)
    (s : ℂ) :
    Memℓp (heatCoefficient M s) 2 ↔ α / 2 < s.re := by
  rw [memℓp_gen_iff (by norm_num)]
  change (Summable fun a => ‖heatCoefficient M s a‖ ^ ENNReal.toReal 2) ↔ _
  rw [show ENNReal.toReal 2 = 2 by norm_num]
  simp_rw [heatCoefficient_norm]
  calc
    (Summable fun a => Real.exp (-s.re * M a) ^ (2 : ℝ)) ↔
        Summable (fun a => Real.exp (-(2 * s.re) * M a)) :=
      summable_congr fun a => by
        rw [Real.rpow_two, pow_two, ← Real.exp_add]
        congr 1
        ring
    _ ↔ α < 2 * s.re := hAbscissa (2 * s.re)
    _ ↔ α / 2 < s.re := by constructor <;> intro h <;> linarith

/-- The actual labeled heat vector in its square-summable half-plane. -/
noncomputable def heatVector
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (hAbscissa : ∀ σ : ℝ,
      Summable (fun a => Real.exp (-σ * M a)) ↔ α < σ)
    (s : ℂ) (hs : α / 2 < s.re) : HeatHilbertSpace (A := A) :=
  ⟨heatCoefficient M s,
    (heat_coefficient_mem_iff M α hM0 hMnn hMne hAbscissa s).2 hs⟩

@[simp]
theorem heatVector_apply
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (hAbscissa : ∀ σ : ℝ,
      Summable (fun a => Real.exp (-σ * M a)) ↔ α < σ)
    (s : ℂ) (hs : α / 2 < s.re) (a : A) :
    heatVector M α hM0 hMnn hMne hAbscissa s hs a = heatCoefficient M s a :=
  rfl

/-- The squared norm is the heat trace at twice the real part, hence is vertical-invariant. -/
theorem heat_vector_norm_sq
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (hAbscissa : ∀ σ : ℝ,
      Summable (fun a => Real.exp (-σ * M a)) ↔ α < σ)
    (σ t : ℝ) (hσ : α / 2 < σ) :
    ((‖heatVector M α hM0 hMnn hMne hAbscissa
      ((σ : ℂ) + Complex.I * (t : ℂ)) (by simpa using hσ)‖ ^ 2 : ℝ) : ℂ) =
      heatTrace M ((2 * σ : ℝ) : ℂ) := by
  let x := heatVector M α hM0 hMnn hMne hAbscissa
      ((σ : ℂ) + Complex.I * (t : ℂ)) (by simpa using hσ)
  have hlp : ‖x‖ ^ (2 : ℝ) =
      ∑' a : A, ‖x a‖ ^ (2 : ℝ) := by
    exact lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) x
  have hsum : Summable (fun a => Real.exp (-(2 * σ) * M a)) :=
    (hAbscissa (2 * σ)).2 (by linarith)
  have hcoord (a : A) : ‖x a‖ ^ (2 : ℝ) =
      Real.exp (-(2 * σ) * M a) := by
    change ‖heatCoefficient M ((σ : ℂ) + Complex.I * (t : ℂ)) a‖ ^ (2 : ℝ) = _
    rw [heatCoefficient_norm, Real.rpow_two, pow_two, ← Real.exp_add]
    congr 1
    simp
    ring
  have hnorm : ‖x‖ ^ 2 = ∑' a : A, Real.exp (-(2 * σ) * M a) := by
    calc
      ‖x‖ ^ 2 = ‖x‖ ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ = ∑' a : A, ‖x a‖ ^ (2 : ℝ) := hlp
      _ = ∑' a : A, Real.exp (-(2 * σ) * M a) := tsum_congr hcoord
  change ((‖x‖ ^ 2 : ℝ) : ℂ) = _
  rw [hnorm, heatTrace]
  change Complex.ofRealCLM (∑' a : A, Real.exp (-(2 * σ) * M a)) = _
  rw [Complex.ofRealCLM.map_tsum hsum]
  apply tsum_congr
  intro a
  change ((Real.exp (-(2 * σ) * M a) : ℝ) : ℂ) = _
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

omit [Countable A] [Zero A] in
/-- The raw source-ordered pairing is the heat-trace reproducing kernel. -/
theorem heat_kernel
    (M : A → ℝ) (α : ℝ)
    (_hAbscissa : ∀ σ : ℝ,
      Summable (fun a => Real.exp (-σ * M a)) ↔ α < σ)
    (s w : ℂ) (_h : α < (s + conj w).re) :
    (∑' a, heatCoefficient M s a * conj (heatCoefficient M w a)) =
      heatTrace M (s + conj w) := by
  rw [heatTrace]
  apply tsum_congr
  intro a
  rw [heatCoefficient, heatCoefficient, ← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  simp
  ring

/-- In the l2 domain, the source-ordered inner product is the heat-trace kernel. -/
theorem heat_vector_inner
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (hAbscissa : ∀ σ : ℝ,
      Summable (fun a => Real.exp (-σ * M a)) ↔ α < σ)
    (s w : ℂ) (hs : α / 2 < s.re) (hw : α / 2 < w.re) :
    sourcePairing
      (heatVector M α hM0 hMnn hMne hAbscissa s hs)
      (heatVector M α hM0 hMnn hMne hAbscissa w hw) =
      heatTrace M (s + conj w) := by
  rw [source_pairing_eq_tsum]
  simp_rw [heatVector_apply]
  apply heat_kernel M α hAbscissa s w
  simp
  linarith

/-- Kernel resonance is the affine pole-locus equation determined by the abscissa. -/
def KernelResonant (α : ℝ) (s w : ℂ) : Prop :=
  s + conj w = (α : ℂ)

/-- Resonance has the unique involutive partner and self-resonates exactly on the midline. -/
theorem resonance_partner_spec (α : ℝ) (s w : ℂ) :
    (KernelResonant α s w ↔ w = (α : ℂ) - conj s) ∧
    (KernelResonant α s s ↔ s.re = α / 2) ∧
    ((α : ℂ) - conj ((α : ℂ) - conj s) = s) := by
  constructor
  · constructor
    · intro h
      have hc := congrArg conj h
      simp at hc
      linear_combination hc
    · intro h
      simp [KernelResonant, h]
  · constructor
    · constructor
      · intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      · intro h
        apply Complex.ext
        · simp
          linarith
        · simp
    · simp

/-- The half-density normalization of a labeled heat coefficient. -/
noncomputable def halfDensityCoefficient (M : A → ℝ) (α : ℝ)
    (s : ℂ) (a : A) : ℂ :=
  Complex.exp (((α / 2 : ℝ) : ℂ) * (M a : ℂ)) * heatCoefficient M s a

omit [Countable A] [Zero A] in
/-- Half-density coefficients have coordinatewise unit modulus exactly on the midline. -/
theorem half_density_unit_modulus_iff
    (M : A → ℝ) (α : ℝ) (_hMnn : ∀ a, 0 ≤ M a)
    (hMne : ∃ a, M a ≠ 0) (s : ℂ) :
    (∀ a, ‖halfDensityCoefficient M α s a‖ = 1) ↔ s.re = α / 2 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := hMne
    have he := h a
    simp only [halfDensityCoefficient, norm_mul, Complex.norm_exp,
      heatCoefficient_norm] at he
    rw [← Real.exp_add] at he
    have hz : α / 2 * M a + -s.re * M a = 0 := by
      apply Real.exp_injective
      simpa using he
    have hprod : (α / 2 - s.re) * M a = 0 := by
      nlinarith
    have hzero := (mul_eq_zero.mp hprod).resolve_right ha
    linarith
  · intro hs a
    simp only [halfDensityCoefficient, norm_mul, Complex.norm_exp,
      heatCoefficient_norm]
    rw [← Real.exp_add]
    rw [← Real.exp_zero]
    congr 1
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.mul_re,
      Complex.div_ofNat_re, Complex.ofReal_re, Complex.div_ofNat_im,
      Complex.ofReal_im, zero_div, mul_zero, sub_zero, neg_mul]
    rw [hs]
    ring

/--
The universal heat-trace midline theorem. The abscissa is characterized by
`hAbscissa`, not constructed here. The three conclusions respectively encode
the l2 boundary, kernel self-resonance, and half-density unitarity; no functional
equation is assumed.
-/
theorem universal_heat_trace_midline
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (_hα : 0 < α)
    (hAbscissa : ∀ σ : ℝ,
      Summable (fun a => Real.exp (-σ * M a)) ↔ α < σ) :
    (∀ s : ℂ, Memℓp (heatCoefficient M s) 2 ↔ α / 2 < s.re) ∧
    (∀ s : ℂ, KernelResonant α s s ↔ s.re = α / 2) ∧
    (∀ s : ℂ, (∀ a, ‖halfDensityCoefficient M α s a‖ = 1) ↔
      s.re = α / 2) := by
  exact ⟨fun s => heat_coefficient_mem_iff M α hM0 hMnn hMne hAbscissa s,
    fun s => (resonance_partner_spec α s s).2.1,
    fun s => half_density_unit_modulus_iff M α hMnn hMne s⟩

/-- A reflection `s ↦ c - conjugate s` has the universal midline exactly when `c = α`. -/
theorem reflection_center_eq_abscissa_iff (α c : ℝ) :
    (∀ s : ℂ, s = (c : ℂ) - conj s ↔ s.re = α / 2) ↔ c = α := by
  constructor
  · intro h
    let s0 : ℂ := ⟨c / 2, 0⟩
    have hfixed : s0 = (c : ℂ) - conj s0 := by
      apply Complex.ext
      · simp [s0]
        ring
      · simp [s0]
    have hc := (h s0).mp hfixed
    change c / 2 = α / 2 at hc
    linarith
  · intro hc s
    subst c
    constructor
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    · intro h
      apply Complex.ext
      · simp
        linarith
      · simp

end D5.S3.Midline.UniversalHeatTrace
