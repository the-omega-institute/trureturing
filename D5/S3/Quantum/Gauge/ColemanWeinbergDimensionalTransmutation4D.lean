/- GID: D5/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/ColemanWeinbergDimensionalTransmutation4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Renormalization, vacuum curvature, and scale invariance of the one-loop potential. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import D5.S3.Quantum.Gauge.ElectroweakHiggsMechanism4D
import D5.S3.Quantum.Gauge.GaugeUnificationRG4D

/-! Scalar electrodynamics at one loop with the logarithmic coefficient held fixed. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D

def cwCoeff (e : ℝ) : ℝ := 3 * e ^ 4 / (64 * Real.pi ^ 2)

def cwPotential (lam B M φ : ℝ) : ℝ :=
  (lam / 24) * φ ^ 4 + B * φ ^ 4 * (Real.log (φ ^ 2 / M ^ 2) - 25 / 6)

def cwUniversal (B v φ : ℝ) : ℝ :=
  B * φ ^ 4 * (Real.log (φ ^ 2 / v ^ 2) - 1 / 2)

def cwVev (lam B M : ℝ) : ℝ :=
  M * Real.exp (11 / 6 - lam / (48 * B))

def cwRunningLam (lam₀ B M₀ M : ℝ) : ℝ :=
  lam₀ + 48 * B * Real.log (M / M₀)

def cwEffCoeff (e y_t Nc : ℝ) : ℝ :=
  (3 * e ^ 4 - 4 * Nc * y_t ^ 4) / (64 * Real.pi ^ 2)

private theorem hasDerivAt_log_sq_div {M x : ℝ} (hM : M ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun y => Real.log (y ^ 2 / M ^ 2)) (2 / x) x := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / M ^ 2) (2 * x / M ^ 2) x := by
    simpa [id] using ((hasDerivAt_id x).pow 2).div_const (M ^ 2)
  have hlog := (Real.hasDerivAt_log (div_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hM))).comp x hsq
  apply hlog.congr_deriv
  field_simp [hx, hM]

private theorem hasDerivAt_pow_log {M x : ℝ} (hM : M ≠ 0) (hx : x ≠ 0) (n : ℕ) (a B : ℝ) :
    HasDerivAt (fun y => y ^ (n + 1) * (a + B * Real.log (y ^ 2 / M ^ 2)))
      (x ^ n * ((n + 1 : ℕ) * a + 2 * B + (n + 1 : ℕ) * B * Real.log (x ^ 2 / M ^ 2))) x := by
  have hp : HasDerivAt (fun y : ℝ => y ^ (n + 1)) ((n + 1 : ℕ) * x ^ n) x := by
    have hpow := (hasDerivAt_id x).pow (n + 1)
    change HasDerivAt (fun y : ℝ => y ^ (n + 1)) (↑(n + 1) * x ^ (n + 1 - 1) * 1) x at hpow
    simpa only [Nat.add_sub_cancel, mul_one] using hpow
  have h := hp.mul ((hasDerivAt_const x a).add ((hasDerivAt_log_sq_div hM hx).const_mul B))
  apply h.congr_deriv
  simp only [Pi.add_apply, zero_add, pow_succ]
  field_simp [hx]
  ring

private theorem eventually_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, y ≠ 0 :=
  isOpen_ne.mem_nhds hx

private theorem quartic_log_fourth_at_scale {M : ℝ} (hM : M ≠ 0) (a B : ℝ) :
    iteratedDeriv 4 (fun x => x ^ 4 * (a + B * Real.log (x ^ 2 / M ^ 2))) M =
      24 * a + 100 * B := by
  let f : ℝ → ℝ := fun x => x ^ 4 * (a + B * Real.log (x ^ 2 / M ^ 2))
  let a₁ := 4 * a + 2 * B
  let B₁ := 4 * B
  let a₂ := 3 * a₁ + 2 * B₁
  let B₂ := 3 * B₁
  let a₃ := 2 * a₂ + 2 * B₂
  let B₃ := 2 * B₂
  have h₁ (x : ℝ) (hx : x ≠ 0) :
      iteratedDeriv 1 f x = x ^ 3 * (a₁ + B₁ * Real.log (x ^ 2 / M ^ 2)) := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_zero]
    simpa [f, a₁, B₁] using (hasDerivAt_pow_log hM hx 3 a B).deriv
  have h₂ (x : ℝ) (hx : x ≠ 0) :
      iteratedDeriv 2 f x = x ^ 2 * (a₂ + B₂ * Real.log (x ^ 2 / M ^ 2)) := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ]
    simpa [a₂, B₂] using ((hasDerivAt_pow_log hM hx 2 a₁ B₁).congr_of_eventuallyEq
      ((eventually_ne_zero hx).mono (fun y hy => h₁ y hy))).deriv
  have h₃ (x : ℝ) (hx : x ≠ 0) :
      iteratedDeriv 3 f x = x * (a₃ + B₃ * Real.log (x ^ 2 / M ^ 2)) := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ]
    simpa [a₃, B₃] using ((hasDerivAt_pow_log hM hx 1 a₂ B₂).congr_of_eventuallyEq
      ((eventually_ne_zero hx).mono (fun y hy => h₂ y hy))).deriv
  have h₄ : iteratedDeriv 4 f M = a₃ + 2 * B₃ + B₃ * Real.log (M ^ 2 / M ^ 2) := by
    rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ]
    simpa using ((hasDerivAt_pow_log hM hM 0 a₃ B₃).congr_of_eventuallyEq
      ((eventually_ne_zero hM).mono (fun y hy => by
        simpa only [Nat.zero_add, pow_one] using h₃ y hy))).deriv
  rw [Real.log_div_self, mul_zero, add_zero] at h₄
  change iteratedDeriv 4 f M = _
  rw [h₄]
  dsimp [a₃, a₂, a₁, B₃, B₂, B₁]
  ring

private theorem quartic_subtraction_fourth_at_scale {M : ℝ} (hM : M ≠ 0) (lam B c : ℝ) :
    iteratedDeriv 4 (fun φ => lam / 24 * φ ^ 4 +
      B * φ ^ 4 * (Real.log (φ ^ 2 / M ^ 2) - c)) M = lam + B * (100 - 24 * c) := by
  have hfun : (fun x : ℝ => lam / 24 * x ^ 4 + B * x ^ 4 * (Real.log (x ^ 2 / M ^ 2) - c)) =
      (fun x : ℝ => x ^ 4 * (lam / 24 - B * c + B * Real.log (x ^ 2 / M ^ 2))) := by
    funext x
    ring
  rw [hfun, quartic_log_fourth_at_scale hM]
  ring

/-- A nonzero logarithmic coefficient fixes the finite subtraction by the fourth derivative. -/
theorem cw_fourth_derivative_renormalization_condition {M : ℝ} (hM : 0 < M) (lam B : ℝ) :
    iteratedDeriv 4 (fun φ => φ ^ 4 * Real.log (φ ^ 2 / M ^ 2)) M = 100 ∧
    iteratedDeriv 4 (fun φ => φ ^ 4 * (Real.log (φ ^ 2 / M ^ 2) - 25 / 6)) M = 0 ∧
    iteratedDeriv 4 (cwPotential lam B M) M = lam ∧
    (B ≠ 0 → ∀ c : ℝ, iteratedDeriv 4 (fun φ => lam / 24 * φ ^ 4 +
      B * φ ^ 4 * (Real.log (φ ^ 2 / M ^ 2) - c)) M = lam ↔ c = 25 / 6) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using quartic_log_fourth_at_scale hM.ne' 0 1
  · have h := quartic_subtraction_fourth_at_scale hM.ne' 0 1 (25 / 6)
    norm_num at h
    exact h
  · unfold cwPotential
    rw [quartic_subtraction_fourth_at_scale hM.ne']
    ring
  · intro hB c
    rw [quartic_subtraction_fourth_at_scale hM.ne']
    constructor
    · intro h
      have hzero : B * (100 - 24 * c) = 0 := by linarith
      rcases mul_eq_zero.mp hzero with hBzero | hc
      · exact (hB hBzero).elim
      · linarith
    · intro hc
      rw [hc]
      ring

private theorem cwUniversal_hasDerivAt (B : ℝ) {v : ℝ} (hv : v ≠ 0) (φ : ℝ) :
    HasDerivAt (cwUniversal B v) (4 * B * φ ^ 3 * Real.log (φ ^ 2 / v ^ 2)) φ := by
  by_cases hφ : φ = 0
  · subst φ
    simp only [zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, zero_mul]
    rw [hasDerivAt_iff_tendsto_slope]
    have hs : Continuous (fun x : ℝ => x ^ 2 / v ^ 2) := by fun_prop
    have hc := Real.continuous_mul_log.comp hs
    have h₀cont : Continuous (fun x : ℝ => x ^ 3 * Real.log (x ^ 2 / v ^ 2)) := by
      have heq :
          (fun x : ℝ => x ^ 3 * Real.log (x ^ 2 / v ^ 2)) =
            (fun x : ℝ => v ^ 2 * x * ((x ^ 2 / v ^ 2) * Real.log (x ^ 2 / v ^ 2))) := by
        funext x
        field_simp [hv]
      rw [heq]
      exact (continuous_id.const_mul (v ^ 2)).mul hc
    have hlim : Tendsto (fun x : ℝ => B * (x ^ 3 * (Real.log (x ^ 2 / v ^ 2) - 1 / 2)))
        (𝓝 (0 : ℝ)) (𝓝 0) := by
      have h : Continuous (fun x : ℝ => B * (x ^ 3 * (Real.log (x ^ 2 / v ^ 2) - 1 / 2))) := by
        have hpow : Continuous (fun x : ℝ => x ^ 3 * (1 / 2 : ℝ)) := by fun_prop
        have hdiff : Continuous (fun x : ℝ =>
            x ^ 3 * (Real.log (x ^ 2 / v ^ 2) - 1 / 2)) := by
          simp_rw [mul_sub]
          exact h₀cont.sub hpow
        exact hdiff.const_mul B
      simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, sub_zero, mul_zero] using
        h.continuousAt (x := (0 : ℝ)).tendsto
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x ≠ 0 := hx
    simp only [slope, cwUniversal, sub_zero, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero,
      zero_mul, smul_eq_mul, vsub_eq_sub]
    field_simp [hne]
  · have hfun : cwUniversal B v =
        fun x => x ^ 4 * (-B / 2 + B * Real.log (x ^ 2 / v ^ 2)) := by
      funext x
      unfold cwUniversal
      ring
    rw [hfun]
    apply (hasDerivAt_pow_log hv hφ 3 (-B / 2) B).congr_deriv
    norm_num
    ring

private theorem cwVev_pos (lam B : ℝ) {M : ℝ} (hM : 0 < M) : 0 < cwVev lam B M :=
  mul_pos hM (Real.exp_pos _)

private theorem cwPotential_eq_universal (lam : ℝ) {B M : ℝ} (hB : B ≠ 0) (hM : 0 < M) (φ : ℝ) :
    cwPotential lam B M φ = cwUniversal B (cwVev lam B M) φ := by
  by_cases hφ : φ = 0
  · simp [hφ, cwPotential, cwUniversal]
  have hv := cwVev_pos lam B hM
  have hlogv : Real.log (cwVev lam B M) = Real.log M + (11 / 6 - lam / (48 * B)) := by
    unfold cwVev
    rw [Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp]
  unfold cwPotential cwUniversal
  rw [Real.log_div (pow_ne_zero 2 hφ) (pow_ne_zero 2 hM.ne'),
    Real.log_div (pow_ne_zero 2 hφ) (pow_ne_zero 2 hv.ne')]
  simp only [Real.log_pow, Nat.cast_ofNat, hlogv]
  field_simp [hB]
  ring

theorem cw_dimensional_transmutation_and_coupling_lock {B M : ℝ}
    (hB : 0 < B) (hM : 0 < M) (lam e : ℝ) :
    0 < cwVev lam B M ∧
    (∀ φ : ℝ, cwPotential lam B M φ = cwUniversal B (cwVev lam B M) φ) ∧
    ContinuousAt (cwPotential lam B M) 0 ∧
    (M = cwVev lam B M ↔ lam = 88 * B) ∧
    (B = cwCoeff e → (M = cwVev lam B M ↔ lam = 33 * e ^ 4 / (8 * Real.pi ^ 2))) := by
  have hv := cwVev_pos lam B hM
  have hpot := cwPotential_eq_universal lam hB.ne' hM
  have hcont : ContinuousAt (cwPotential lam B M) 0 := by
    rw [funext hpot]
    exact (cwUniversal_hasDerivAt B hv.ne' 0).continuousAt
  have hlock : M = cwVev lam B M ↔ lam = 88 * B := by
    have hcancel : M = cwVev lam B M ↔ Real.exp (11 / 6 - lam / (48 * B)) = 1 := by
      unfold cwVev
      constructor
      · intro h
        exact mul_left_cancel₀ hM.ne' (by simpa using h.symm)
      · intro h
        rw [h, mul_one]
    rw [hcancel, Real.exp_eq_one_iff]
    constructor
    · intro h
      field_simp [hB.ne'] at h
      linarith
    · intro h
      rw [h]
      field_simp [hB.ne']
      ring
  refine ⟨hv, hpot, hcont, hlock, fun hc => ?_⟩
  have hcoeff : 88 * B = 33 * e ^ 4 / (8 * Real.pi ^ 2) := by
    rw [hc, cwCoeff]
    ring
  rw [hlock, hcoeff]

private theorem cwUniversal_even (B v x : ℝ) : cwUniversal B v (-x) = cwUniversal B v x := by
  simp only [cwUniversal, neg_pow, even_two.neg_one_pow, Even.neg_pow (by decide : Even 4), one_mul]

private theorem cwUniversal_minimum_value (B v : ℝ) :
    cwUniversal B v v = -(1 / 2) * B * v ^ 4 := by
  unfold cwUniversal
  rw [Real.log_div_self]
  ring

private theorem cwUniversal_strict_at_positive {B v x : ℝ}
    (hB : 0 < B) (hv : 0 < v) (hx : 0 ≤ x) (hxv : x ≠ v) :
    cwUniversal B v v < cwUniversal B v x := by
  have hc : Continuous (cwUniversal B v) :=
    continuous_iff_continuousAt.mpr (fun y => (cwUniversal_hasDerivAt B hv.ne' y).continuousAt)
  cases lt_or_gt_of_ne hxv with
  | inl hlt =>
    have hanti : StrictAntiOn (cwUniversal B v) (Icc 0 v) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hc.continuousOn ?_
      intro y hy
      rw [interior_Icc] at hy
      rw [(cwUniversal_hasDerivAt B hv.ne' y).deriv]
      have hy₀ : 0 < y := hy.1
      have hyv : y < v := hy.2
      have hlog : Real.log (y ^ 2 / v ^ 2) < 0 := by
        apply Real.log_neg (by positivity)
        rw [div_lt_one (by positivity : 0 < v ^ 2)]
        gcongr
      exact mul_neg_of_pos_of_neg (by positivity) hlog
    exact hanti ⟨hx, hlt.le⟩ ⟨hv.le, le_rfl⟩ hlt
  | inr hgt =>
    have hmono : StrictMonoOn (cwUniversal B v) (Ici v) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici _) hc.continuousOn ?_
      intro y hy
      rw [interior_Ici] at hy
      have hyv : v < y := hy
      have hy₀ := hv.trans hyv
      rw [(cwUniversal_hasDerivAt B hv.ne' y).deriv]
      have hlog : 0 < Real.log (y ^ 2 / v ^ 2) := by
        apply Real.log_pos
        rw [one_lt_div (by positivity : 0 < v ^ 2)]
        gcongr
      exact mul_pos (by positivity) hlog
    exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hgt.le) hgt

theorem cw_radiative_global_minimum_and_symmetry_breaking {B v : ℝ} (hB : 0 < B) (hv : 0 < v) :
    (∀ φ : ℝ, HasDerivAt (cwUniversal B v) (4 * B * φ ^ 3 * Real.log (φ ^ 2 / v ^ 2)) φ) ∧
    (∀ φ : ℝ, cwUniversal B v v ≤ cwUniversal B v φ) ∧
    (∀ φ : ℝ, cwUniversal B v φ = cwUniversal B v v ↔ φ = v ∨ φ = -v) ∧
    cwUniversal B v v = -(1 / 2) * B * v ^ 4 ∧
    cwUniversal B v v < 0 ∧ cwUniversal B v 0 = 0 := by
  have hstrict (φ : ℝ) (hp : φ ≠ v) (hn : φ ≠ -v) : cwUniversal B v v < cwUniversal B v φ := by
    rcases le_or_gt 0 φ with hnonneg | hneg
    · exact cwUniversal_strict_at_positive hB hv hnonneg hp
    · have hpos : 0 ≤ -φ := neg_nonneg.mpr hneg.le
      have hnv : -φ ≠ v := fun h => hn (neg_eq_iff_eq_neg.mp h)
      simpa only [cwUniversal_even B v φ] using cwUniversal_strict_at_positive hB hv hpos hnv
  have hval := cwUniversal_minimum_value B v
  have heq (φ : ℝ) : cwUniversal B v φ = cwUniversal B v v ↔ φ = v ∨ φ = -v := by
    constructor
    · intro h
      by_cases hp : φ = v
      · exact Or.inl hp
      · exact Or.inr (by by_contra hn; exact (hstrict φ hp hn).ne h.symm)
    · rintro (rfl | rfl)
      · rfl
      · exact cwUniversal_even B v v
  refine ⟨cwUniversal_hasDerivAt B hv.ne', ?_, heq, hval, ?_, by simp [cwUniversal]⟩
  · intro φ
    by_cases hp : φ = v ∨ φ = -v
    · exact ((heq φ).2 hp).ge
    · exact (hstrict φ (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))).le
  · rw [hval]
    have : 0 < B * v ^ 4 := by positivity
    nlinarith

theorem cw_radiative_scalar_to_vector_mass_ratio {B v e : ℝ}
    (hB : 0 < B) (hv : 0 < v) (he : 0 < e) :
    HasDerivAt (deriv (cwUniversal B v)) (8 * B * v ^ 2) v ∧
    deriv (deriv (cwUniversal B v)) v = 8 * B * v ^ 2 ∧
    0 < deriv (deriv (cwUniversal B v)) v ∧
    ElectroweakHiggsMechanism4D.mWSq (2 * e) v = e ^ 2 * v ^ 2 ∧
    (B = cwCoeff e →
      deriv (deriv (cwUniversal B v)) v / (e ^ 2 * v ^ 2) = 3 * e ^ 2 / (8 * Real.pi ^ 2) ∧
      3 * e ^ 2 / (8 * Real.pi ^ 2) = 3 * (e ^ 2 / (4 * Real.pi)) / (2 * Real.pi)) := by
  have hfun : deriv (cwUniversal B v) =
      fun x => x ^ 3 * (0 + 4 * B * Real.log (x ^ 2 / v ^ 2)) := by
    ext x
    rw [(cwUniversal_hasDerivAt B hv.ne' x).deriv]
    ring
  have hd : HasDerivAt (deriv (cwUniversal B v)) (8 * B * v ^ 2) v := by
    rw [hfun]
    apply (hasDerivAt_pow_log hv.ne' hv.ne' 2 0 (4 * B)).congr_deriv
    rw [Real.log_div_self]
    norm_num
    ring
  have hm : ElectroweakHiggsMechanism4D.mWSq (2 * e) v = e ^ 2 * v ^ 2 := by
    unfold ElectroweakHiggsMechanism4D.mWSq
    ring
  refine ⟨hd, hd.deriv, ?_, hm, fun hb => ⟨?_, ?_⟩⟩
  · rw [hd.deriv]
    positivity
  · rw [hd.deriv, hb, cwCoeff]
    field_simp [Real.pi_ne_zero, he.ne', hv.ne']
    ring
  · field_simp [Real.pi_ne_zero]
    ring

theorem cw_callan_symanzik_rg_invariance {B M₀ M : ℝ}
    (hB : 0 < B) (hM₀ : 0 < M₀) (hM : 0 < M) (lam₀ e : ℝ) :
    M * deriv (cwRunningLam lam₀ B M₀) M = 48 * B ∧
    (B = cwCoeff e → 48 * B = 9 * e ^ 4 / (4 * Real.pi ^ 2)) ∧
    cwVev (cwRunningLam lam₀ B M₀ M) B M = cwVev lam₀ B M₀ ∧
    (∀ φ : ℝ, cwPotential (cwRunningLam lam₀ B M₀ M) B M φ = cwPotential lam₀ B M₀ φ) := by
  have hflow : cwRunningLam lam₀ B M₀ =
      GaugeUnificationRG4D.rgInvCoupling (2 * Real.pi * (48 * B)) lam₀ M₀ := by
    ext x
    unfold cwRunningLam GaugeUnificationRG4D.rgInvCoupling
    field_simp [Real.pi_ne_zero]
  have hbeta : M * deriv (cwRunningLam lam₀ B M₀) M = 48 * B := by
    rw [hflow, (GaugeUnificationRG4D.rgInvCoupling_hasDerivAt _ _ hM₀ hM).deriv]
    field_simp [Real.pi_ne_zero, hM.ne']
  have hscale : cwVev (cwRunningLam lam₀ B M₀ M) B M = cwVev lam₀ B M₀ := by
    have hexponent :
        11 / 6 - cwRunningLam lam₀ B M₀ M / (48 * B) =
          (11 / 6 - lam₀ / (48 * B)) - Real.log (M / M₀) := by
      unfold cwRunningLam
      field_simp [hB.ne']
      ring
    rw [cwVev, cwVev, hexponent, Real.exp_sub, Real.exp_log (div_pos hM hM₀)]
    field_simp [hM.ne', hM₀.ne']
  refine ⟨hbeta, ?_, hscale, ?_⟩
  · rintro rfl
    unfold cwCoeff
    ring
  · intro φ
    rw [cwPotential_eq_universal _ hB.ne' hM, cwPotential_eq_universal _ hB.ne' hM₀, hscale]

private theorem cw_log_atTop {M : ℝ} (hM : M ≠ 0) :
    Tendsto (fun x : ℝ => Real.log (x ^ 2 / M ^ 2) - 25 / 6) atTop atTop := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by decide)
  have hl : Tendsto (fun x : ℝ => Real.log (x ^ 2 / M ^ 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (hsq.atTop_div_const (sq_pos_of_ne_zero hM))
  simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(25 / 6 : ℝ)) hl

theorem cw_yukawa_vacuum_stability_threshold {M : ℝ} (hM : 0 < M) (lam B e y_t Nc : ℝ) :
    (0 < cwEffCoeff e y_t Nc ↔ 4 * Nc * y_t ^ 4 < 3 * e ^ 4) ∧
    (0 < B → Tendsto (cwPotential lam B M) atTop atTop ∧
      BddBelow (Set.range (cwPotential lam B M))) ∧
    (B < 0 → Tendsto (cwPotential lam B M) atTop atBot) := by
  have hden : 0 < 64 * Real.pi ^ 2 := by positivity
  have hfactor (x : ℝ) : cwPotential lam B M x =
      x ^ 4 * (lam / 24 + B * (Real.log (x ^ 2 / M ^ 2) - 25 / 6)) := by
    unfold cwPotential
    ring
  have hp : Tendsto (fun x : ℝ => x ^ 4) atTop atTop := tendsto_pow_atTop (by decide)
  have hl := cw_log_atTop hM.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold cwEffCoeff
    rw [lt_div_iff₀ hden, zero_mul, sub_pos]
  · intro hB
    constructor
    · rw [funext hfactor]
      exact hp.atTop_mul_atTop₀ (tendsto_const_nhds.add_atTop (hl.const_mul_atTop hB))
    · let v := cwVev lam B M
      have hv : 0 < v := cwVev_pos lam B hM
      refine ⟨cwUniversal B v v, ?_⟩
      rintro r ⟨x, rfl⟩
      rw [cwPotential_eq_universal lam hB.ne' hM]
      exact (cw_radiative_global_minimum_and_symmetry_breaking hB hv).2.1 x
  · intro hB
    rw [funext hfactor]
    exact hp.atTop_mul_atBot₀ (tendsto_const_nhds.add_atBot (hl.const_mul_atTop_of_neg hB))

end D5.S3.Quantum.Gauge.ColemanWeinbergDimensionalTransmutation4D
