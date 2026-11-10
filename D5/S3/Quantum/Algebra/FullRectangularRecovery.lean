/- GID: D5/S3/Quantum/Algebra/FullRectangularRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FullRectangularRecovery
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension, D5/S3/QuantumStates/GNSCompatibleStateExtension]
   utility: none
   digest: All-state square bounds on an actual left corner force rectangular norm recovery through an internally constructed signed norm-attaining state. -/

import D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension
import D5.S3.QuantumStates.GNSCompatibleStateExtension
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open scoped ComplexOrder

namespace D5.S3.Quantum.Algebra.FullRectangularRecovery

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual ambient corner, with its inherited complex vector space, order and norm. -/
def cornerSpace (e : A) : Submodule ℂ A where
  carrier := {x | e * x = x ∧ x * e = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨by simp [mul_add, hx.1, hy.1], by simp [add_mul, hx.2, hy.2]⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by simp [mul_smul_comm, hx.1], by simp [smul_mul_assoc, hx.2]⟩

theorem corner_mem_iff (e : A) (he : IsStarProjection e) (x : A) :
    x ∈ cornerSpace e ↔ x = e * x * e := by
  change (e * x = x ∧ x * e = x) ↔ _
  have hee : e * e = e := he.isIdempotentElem
  constructor
  · intro hx
    rw [hx.1, hx.2]
  · intro hx
    constructor
    · calc
        e * x = e * (e * x * e) := congrArg (e * ·) hx
        _ = e * x * e := by simp only [← mul_assoc, hee]
        _ = x := hx.symm
    · calc
        x * e = (e * x * e) * e := congrArg (· * e) hx
        _ = e * x * e := by simp only [mul_assoc, hee]
        _ = x := hx.symm

/-- A state of eAe: a continuous positive complex functional normalized at its actual unit e.
No ambient extension or state-norming supplier is included in this definition. -/
structure CornerState (e : A) (he : IsStarProjection e) where
  functional : cornerSpace e →P[ℂ] ℂ
  normalized : functional ⟨e, he.isIdempotentElem, he.isIdempotentElem⟩ = 1

theorem positive_real (f : A →P[ℂ] ℂ) (a : A) (ha : IsSelfAdjoint a) :
    f a = ((f a).re : ℂ) := by
  have hi : (f a).im = 0 := Complex.conj_eq_iff_im.mp (by
    simpa only [Complex.star_def] using (ha.map' f).star_eq)
  apply Complex.ext <;> simp [hi]

theorem positive_re_bounds (f : A →P[ℂ] ℂ) (a : A) (ha : IsSelfAdjoint a) :
    -‖a‖ * (f 1).re ≤ (f a).re ∧ (f a).re ≤ ‖a‖ * (f 1).re := by
  have hu := (Complex.le_def.mp (f.monotone' (ha.le_algebraMap_norm_self))).1
  have hl := (Complex.le_def.mp (f.monotone' (ha.neg_algebraMap_norm_le_self))).1
  constructor
  · simpa [Algebra.algebraMap_eq_smul_one] using hl
  · simpa [Algebra.algebraMap_eq_smul_one] using hu

/-- Hahn--Banach and the existing norm-additive positive extension supply an exact
norm-attaining state, including either spectral sign, with no supplied norming premise. -/
theorem exists_norming_state (a : A) (ha : IsSelfAdjoint a) (ha0 : a ≠ 0) :
    ∃ (φ : A →P[ℂ] ℂ) (s : ℝ),
      φ 1 = 1 ∧ φ a = (s : ℂ) ∧ s ^ 2 = ‖a‖ ^ 2 := by
  let X := selfAdjoint.submodule ℝ A
  let x : X := ⟨a, ha⟩
  have hx : ‖x‖ ≠ 0 := by simpa [x] using (norm_ne_zero_iff.mpr ha0)
  obtain ⟨g, hgn, hgx⟩ := exists_dual_vector ℝ x hx
  obtain ⟨p, q, hpq, hmass⟩ :=
    D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive
      X (fun y => y.2) g
  have hd : ‖a‖ = (p a).re - (q a).re := by simpa [x] using (hgx.symm.trans (hpq x))
  have hm : (p 1).re + (q 1).re = 1 := by simpa [hgn] using hmass
  have hp0 : 0 ≤ (p 1).re := (Complex.nonneg_iff.mp (p.map_nonneg zero_le_one)).1
  have hq0 : 0 ≤ (q 1).re := (Complex.nonneg_iff.mp (q.map_nonneg zero_le_one)).1
  have hpb := positive_re_bounds p a ha
  have hqb := positive_re_bounds q a ha
  have hpa : (p a).re = ‖a‖ * (p 1).re := by nlinarith
  have hqa : (q a).re = -‖a‖ * (q 1).re := by nlinarith
  have choose_normalized (f : A →P[ℂ] ℂ) (s : ℝ) (hf : 0 < (f 1).re)
      (hfa : (f a).re = s * (f 1).re) (hs : s ^ 2 = ‖a‖ ^ 2) :
      ∃ (φ : A →P[ℂ] ℂ) (s : ℝ),
        φ 1 = 1 ∧ φ a = (s : ℂ) ∧ s ^ 2 = ‖a‖ ^ 2 := by
    let φ : A →P[ℂ] ℂ := PositiveContinuousLinearMap.mk₀
      ((f 1).re⁻¹ • f.toContinuousLinearMap)
      (fun y hy => smul_nonneg (inv_nonneg.mpr hf.le) (f.map_nonneg hy))
    have hφ (y : A) : φ y = (f 1).re⁻¹ • f y := rfl
    refine ⟨φ, s, ?_, ?_, hs⟩
    · rw [hφ, positive_real f 1 (IsSelfAdjoint.one A)]
      apply Complex.ext <;> simp [hf.ne']
    · rw [hφ, positive_real f a ha, hfa]
      apply Complex.ext <;> simp [hf.ne', mul_comm, mul_left_comm, mul_assoc]
  by_cases hp : 0 < (p 1).re
  · exact choose_normalized p ‖a‖ hp hpa rfl
  · have hq : 0 < (q 1).re := by linarith
    exact choose_normalized q (-‖a‖) hq hqa (by ring)

/-- Zero variance in a norm-attaining state forces both multiplication identities.
The Cauchy--Schwarz argument keeps the same state and the same arbitrary middle element. -/
theorem norming_state_multiplication (φ : A →P[ℂ] ℂ) (hφ : φ 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (s : ℝ)
    (has : φ a = (s : ℂ)) (hs : s ^ 2 = ‖a‖ ^ 2) :
    ∀ x : A, φ (a * x) = (s : ℂ) * φ x ∧ φ (x * a) = (s : ℂ) * φ x := by
  let r := a - s • (1 : A)
  have hr : IsSelfAdjoint r := ha.sub ((IsSelfAdjoint.all s).smul (IsSelfAdjoint.one A))
  have hpos : 0 ≤ φ (r * r) := φ.map_nonneg (by simpa [hr.star_eq] using star_mul_self_nonneg r)
  have hbound : (φ (a * a)).re ≤ ‖a‖ ^ 2 := by
    calc
      (φ (a * a)).re ≤ ‖φ (a * a)‖ := Complex.re_le_norm _
      _ ≤ ‖a * a‖ := D5.S3.QuantumStates.GNSCompatibleStateExtension.state_bound
        φ.toPositiveLinearMap hφ _
      _ = ‖a‖ ^ 2 := by
        simpa [ha.star_eq, pow_two] using (CStarRing.norm_star_mul_self (x := a))
  have hexpand : (φ (r * r)).re = (φ (a * a)).re - 2 * s ^ 2 + s ^ 2 := by
    simp [r, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      map_sub, hφ, has]
    <;> ring
  have hzero : φ (r * r) = 0 := by
    apply Complex.ext
    · have hh := (Complex.nonneg_iff.mp hpos).1
      simp only [Complex.zero_re]
      nlinarith
    · exact (Complex.nonneg_iff.mp hpos).2.symm
  have hleft (x : A) : φ (r * x) = 0 := by
    have h := PositiveLinearMap.norm_map_star_mul_sq_le φ r x
    rw [hr.star_eq, hzero, norm_zero, zero_mul] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (φ (r * x))])
  have hright (x : A) : φ (x * r) = 0 := by
    have h := PositiveLinearMap.norm_map_mul_star_sq_le φ x r
    rw [hr.star_eq, hzero, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (φ (x * r))])
  intro x
  constructor
  · have h := hleft x
    simpa [r, sub_mul, smul_mul_assoc, sub_eq_zero, ← Complex.coe_smul, smul_eq_mul] using h
  · have h := hright x
    simpa [r, mul_sub, mul_smul_comm, sub_eq_zero, ← Complex.coe_smul, smul_eq_mul] using h

/-- The same norm-attaining state evaluates every sandwich exactly. -/
theorem norming_state_sandwich (φ : A →P[ℂ] ℂ) (hφ : φ 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (s : ℝ)
    (has : φ a = (s : ℂ)) (hs : s ^ 2 = ‖a‖ ^ 2) (C : A) :
    φ (a * C * a) = ((‖a‖ ^ 2 : ℝ) : ℂ) * φ C := by
  have h := norming_state_multiplication φ hφ a ha s has hs
  rw [(h (a * C)).2, (h C).1]
  rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, hs]

theorem rowGram_mem (e U : A) (he : IsStarProjection e) (hU : e * U = U) :
    U * star U ∈ cornerSpace e := by
  change e * (U * star U) = U * star U ∧ (U * star U) * e = U * star U
  constructor
  · rw [← mul_assoc, hU]
  · have hu : star U * e = star U := by
      simpa [star_mul, he.isSelfAdjoint.star_eq] using congrArg star hU
    rw [mul_assoc, hu]

/-- Rectangular recovery for arbitrary unital complex C*-algebras and actual corners.
The right projection and channel may be zero, unequal, infinite, or noninvertible. -/
theorem full_rectangular_recovery
    (e f a U : A) (he : IsStarProjection e) (hf : IsStarProjection f)
    (ha : IsSelfAdjoint a) (hae : a = e * a * e) (hU : U = e * U * f)
    (κ : ℝ) (hκ : 0 < κ)
    (hsquare : ∀ ω : CornerState e he,
      ‖ω.functional ⟨a, (corner_mem_iff e he a).2 hae⟩‖ ^ 2 ≤ κ *
        (ω.functional ⟨U * star U, rowGram_mem e U he (by
          have hee : e * e = e := he.isIdempotentElem
          calc
            e * U = e * (e * U * f) := congrArg (e * ·) hU
            _ = e * U * f := by simp only [← mul_assoc, hee]
            _ = U := hU.symm)⟩).re) :
    ‖a‖ ^ 2 / Real.sqrt κ ≤ ‖a * U‖ := by
  by_cases ha0 : a = 0
  · simp [ha0]
  obtain ⟨φ, s, hφ, has, hs⟩ := exists_norming_state a ha ha0
  have haec := (corner_mem_iff e he a).2 hae
  have hm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; nlinarith
  have heφ : φ e = 1 := by
    have h := (norming_state_multiplication φ hφ a ha s has hs e).2
    rw [haec.1, has] at h
    apply mul_left_cancel₀ (show (s : ℂ) ≠ 0 by exact_mod_cast hs0)
    simpa using h.symm
  let ω : CornerState e he :=
    { functional := PositiveContinuousLinearMap.mk₀
        (φ.toContinuousLinearMap.comp (cornerSpace e).subtypeL)
        (fun x hx => φ.map_nonneg hx)
      normalized := heφ }
  have hineq : ‖φ a‖ ^ 2 ≤ κ * (φ (U * star U)).re := hsquare ω
  have hnorma : ‖φ a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [has, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs]
  rw [hnorma] at hineq
  have hmiddle := norming_state_sandwich φ hφ a ha s has hs (U * star U)
  have hmiddle_re : (φ (a * (U * star U) * a)).re =
      ‖a‖ ^ 2 * (φ (U * star U)).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using congrArg Complex.re hmiddle
  have hnorm : ‖a‖ ^ 2 * (φ (U * star U)).re ≤ ‖a * U‖ ^ 2 := by
    rw [← hmiddle_re]
    calc
      (φ (a * (U * star U) * a)).re ≤ ‖φ (a * (U * star U) * a)‖ := Complex.re_le_norm _
      _ ≤ ‖a * (U * star U) * a‖ := D5.S3.QuantumStates.GNSCompatibleStateExtension.state_bound
        φ.toPositiveLinearMap hφ _
      _ = ‖a * U‖ ^ 2 := by
        calc
          _ = ‖(a * U) * star (a * U)‖ := by
            congr 1
            simp only [star_mul, ha.star_eq, mul_assoc]
          _ = _ := by simpa [pow_two] using (CStarRing.norm_self_mul_star (x := a * U))
  have hsq : ‖a‖ ^ 4 ≤ κ * ‖a * U‖ ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hineq (sq_nonneg ‖a‖)
    have hscaled' := mul_le_mul_of_nonneg_left hnorm hκ.le
    nlinarith
  apply (div_le_iff₀ (Real.sqrt_pos.2 hκ)).2
  have hsqrt := Real.sq_sqrt hκ.le
  have hn := norm_nonneg (a * U)
  have hroot := Real.sqrt_nonneg κ
  apply (sq_le_sq₀ (sq_nonneg ‖a‖) (mul_nonneg hn hroot)).mp
  calc
    (‖a‖ ^ 2) ^ 2 = ‖a‖ ^ 4 := by ring
    _ ≤ κ * ‖a * U‖ ^ 2 := hsq
    _ = (‖a * U‖ * Real.sqrt κ) ^ 2 := by rw [mul_pow, hsqrt]; ring

end D5.S3.Quantum.Algebra.FullRectangularRecovery
