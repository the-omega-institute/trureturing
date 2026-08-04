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

/-- A genuine convergence abscissa: convergence and divergence are prescribed only
on the two strict sides. No behavior at the boundary is implied. -/
def IsHeatAbscissa (M : A → ℝ) (α : ℝ) : Prop :=
  (∀ σ, α < σ → Summable (fun a => Real.exp (-σ * M a))) ∧
  (∀ σ, σ < α → ¬Summable (fun a => Real.exp (-σ * M a)))

/-- A heat abscissa whose boundary series also diverges. The flat iff used by
the original atom (i) implicitly adopts exactly this stronger convention. -/
def BoundaryDivergentAbscissa (M : A → ℝ) (α : ℝ) : Prop :=
  IsHeatAbscissa M α ∧ ¬Summable (fun a => Real.exp (-α * M a))

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

omit [Countable A] [Zero A] in
/-- Square summability is exactly summability of the heat series at twice the
real parameter. This statement makes no boundary convention. -/
theorem heat_coefficient_mem_iff
    (M : A → ℝ) (_α : ℝ)
    (s : ℂ) :
    Memℓp (heatCoefficient M s) 2 ↔
      Summable (fun a => Real.exp (-(2 * s.re) * M a)) := by
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
    _ ↔ Summable (fun a => Real.exp (-(2 * s.re) * M a)) := Iff.rfl

omit [Countable A] [Zero A] in
/-- Strictly right of half the abscissa, the heat coefficients are square-summable. -/
theorem heat_coefficient_mem_of_abscissa
    (M : A → ℝ) (α : ℝ)
    (hAbscissa : IsHeatAbscissa M α) (s : ℂ) (hs : α / 2 < s.re) :
    Memℓp (heatCoefficient M s) 2 :=
  (heat_coefficient_mem_iff M α s).2
    (hAbscissa.1 (2 * s.re) (by linarith))

omit [Countable A] [Zero A] in
/-- Strictly left of half the abscissa, the heat coefficients are not square-summable. -/
theorem not_heat_coefficient_mem_of_abscissa
    (M : A → ℝ) (α : ℝ)
    (hAbscissa : IsHeatAbscissa M α) (s : ℂ) (hs : s.re < α / 2) :
    ¬Memℓp (heatCoefficient M s) 2 := by
  rw [heat_coefficient_mem_iff M α s]
  exact hAbscissa.2 (2 * s.re) (by linarith)

omit [Countable A] [Zero A] in
/-- Under explicit boundary divergence, square summability has the flat strict iff. -/
theorem heat_coefficient_mem_iff_of_boundary_divergent
    (M : A → ℝ) (α : ℝ)
    (hAbscissa : BoundaryDivergentAbscissa M α) (s : ℂ) :
    Memℓp (heatCoefficient M s) 2 ↔ α / 2 < s.re := by
  rw [heat_coefficient_mem_iff M α s]
  constructor
  · intro h
    rcases lt_trichotomy s.re (α / 2) with hlt | heq | hgt
    · exact False.elim ((hAbscissa.1.2 (2 * s.re) (by linarith)) h)
    · exfalso
      apply hAbscissa.2
      have htwo : 2 * s.re = α := by linarith
      convert h using 1
      ext a
      rw [htwo]
    · exact hgt
  · intro hs
    exact hAbscissa.1.1 (2 * s.re) (by linarith)

/-- The actual labeled heat vector in its square-summable half-plane. -/
noncomputable def heatVector
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (hAbscissa : IsHeatAbscissa M α)
    (s : ℂ) (hs : α / 2 < s.re) : HeatHilbertSpace (A := A) :=
  ⟨heatCoefficient M s,
    heat_coefficient_mem_of_abscissa M α hAbscissa s hs⟩

@[simp]
theorem heatVector_apply
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (hAbscissa : IsHeatAbscissa M α)
    (s : ℂ) (hs : α / 2 < s.re) (a : A) :
    heatVector M α hM0 hMnn hMne hAbscissa s hs a = heatCoefficient M s a :=
  rfl

/-- The squared norm is the heat trace at twice the real part, hence is vertical-invariant. -/
theorem heat_vector_norm_sq
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (hAbscissa : IsHeatAbscissa M α)
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
    hAbscissa.1 (2 * σ) (by linarith)
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
    (_hAbscissa : IsHeatAbscissa M α)
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
    (hAbscissa : IsHeatAbscissa M α)
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
The honest universal heat-trace theorem. A genuine abscissa leaves boundary
behavior unspecified. Atom (i) therefore consists of the exact summability
criterion plus the two strict-side implications. The resonance and half-density
conclusions do not depend on boundary behavior; no functional equation is assumed.
-/
theorem universal_heat_trace_midline
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (_hα : 0 < α)
    (hAbscissa : IsHeatAbscissa M α) :
    (∀ s : ℂ, Memℓp (heatCoefficient M s) 2 ↔
      Summable (fun a => Real.exp (-(2 * s.re) * M a))) ∧
    (∀ s : ℂ, α / 2 < s.re → Memℓp (heatCoefficient M s) 2) ∧
    (∀ s : ℂ, s.re < α / 2 → ¬Memℓp (heatCoefficient M s) 2) ∧
    (∀ s : ℂ, KernelResonant α s s ↔ s.re = α / 2) ∧
    (∀ s : ℂ, (∀ a, ‖halfDensityCoefficient M α s a‖ = 1) ↔
      s.re = α / 2) := by
  exact ⟨fun s => heat_coefficient_mem_iff M α s,
    fun s => heat_coefficient_mem_of_abscissa M α hAbscissa s,
    fun s => not_heat_coefficient_mem_of_abscissa M α hAbscissa s,
    fun s => (resonance_partner_spec α s s).2.1,
    fun s => half_density_unit_modulus_iff M α hMnn hMne s⟩

/-- The original flat iff is valid for the explicitly stronger boundary-divergent class. -/
theorem universal_heat_trace_midline_of_boundary_divergent
    (M : A → ℝ) (α : ℝ)
    (hM0 : M 0 = 0) (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (_hα : 0 < α) (hAbscissa : BoundaryDivergentAbscissa M α) :
    (∀ s : ℂ, Memℓp (heatCoefficient M s) 2 ↔ α / 2 < s.re) ∧
    (∀ s : ℂ, KernelResonant α s s ↔ s.re = α / 2) ∧
    (∀ s : ℂ, (∀ a, ‖halfDensityCoefficient M α s a‖ = 1) ↔
      s.re = α / 2) := by
  exact ⟨fun s => heat_coefficient_mem_iff_of_boundary_divergent M α hAbscissa s,
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
