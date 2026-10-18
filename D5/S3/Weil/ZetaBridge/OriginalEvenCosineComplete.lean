/- GID: D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalEvenCosineComplete
   mirror-E: none(waiver:analytic-hilbert-fourier-identification-without-executable-mirror)
   anchors: []
   utility: none
   digest: For a > 0, physical Fourier normalization and interval Parseval identify the original complex AE-even sector with the closed cosine span. -/

import D5.S3.Weil.ZetaBridge.OriginalWindowEven
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace OriginalEvenCosineComplete

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix PhysicalCosineTailProjection OriginalWindowEven

def character (a : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  @fourier (2 * a) k (x : AddCircle (2 * a))

/-- Unnormalised physical Lebesgue moment of the ORIGINAL zero extension. -/
def moment (a : ℝ) (u : WindowL2 a) (k : ℤ) : ℂ :=
  ∫ x : ℝ, character a (-k) x * zeroExtension a u x

private lemma moment_eq_window (a : ℝ) (u : WindowL2 a) (k : ℤ) :
    moment a u k = ∫ x in window a, character a (-k) x * u x := by
  have h : (fun x => character a (-k) x * zeroExtension a u x) =
      (window a).indicator (fun x => character a (-k) x * u x) := by
    funext x
    by_cases hx : x ∈ window a <;> simp [zeroExtension, hx]
  have hwindow : MeasurableSet (window a) := by
    simpa only [window] using (measurableSet_Ioc : MeasurableSet (Ioc (-a) a))
  rw [moment, h, integral_indicator hwindow]

private lemma character_neg_x (a : ℝ) (k : ℤ) (x : ℝ) :
    character a k (-x) = character a (-k) x := by
  simp only [character, AddCircle.coe_neg, fourier_apply, smul_neg, neg_smul]

private lemma moment_integrable (a : ℝ) (ha : 0 < a) (u : WindowL2 a) (k : ℤ) :
    Integrable (fun x => character a (-k) x * zeroExtension a u x) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  letI : IsFiniteMeasure (windowMeasure a) := by
    change IsFiniteMeasure (volume.restrict (Ioc (-a) a))
    infer_instance
  have hwindow : MeasurableSet (window a) := by
    simpa only [window] using (measurableSet_Ioc : MeasurableSet (Ioc (-a) a))
  have hu : Integrable (u : ℝ → ℂ) (windowMeasure a) :=
    MemLp.integrable (by norm_num) (Lp.memLp u)
  have hz : Integrable (zeroExtension a u) (volume : Measure ℝ) := by
    change Integrable ((window a).indicator (u : ℝ → ℂ)) volume
    exact (integrable_indicator_iff hwindow).mpr hu
  apply hz.bdd_mul (c := 1)
  · exact (show Continuous (character a (-k)) by unfold character; fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      change ‖@fourier (2 * a) (-k) (x : AddCircle (2 * a))‖ ≤ 1
      have hn : ‖@fourier (2 * a) (-k) (x : AddCircle (2 * a))‖ = 1 := Circle.norm_coe _
      exact hn.le

/-- No conjugation of u is involved: even complex functions have equal moments at k and -k. -/
private lemma moment_neg (a : ℝ) (u : WindowL2 a) (hu : u ∈ originalEven a) (k : ℤ) :
    moment a u (-k) = moment a u k := by
  have he := (mem_originalEven_iff a u).mp hu
  calc
    moment a u (-k) = ∫ x : ℝ, character a k x * zeroExtension a u x := by
      simp only [moment, neg_neg]
    _ = ∫ x : ℝ, character a k (-x) * zeroExtension a u (-x) :=
      (integral_neg_eq_self (fun x => character a k x * zeroExtension a u x) volume).symm
    _ = moment a u k := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [character_neg_x, hx]

private lemma character_pair (a : ℝ) (n : ℕ) (x : ℝ) :
    character a (n : ℤ) x + character a (-(n : ℤ)) x =
      2 * (Real.cos (omega a n * x) : ℂ) := by
  have hp : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) /
      (2 * (a : ℂ))) = ((omega a n * x : ℝ) : ℂ) * Complex.I := by
    simp only [omega, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_natCast]
    ring
  have hm : (2 * (Real.pi : ℂ) * Complex.I * -(n : ℂ) * (x : ℂ) /
      (2 * (a : ℂ))) = -((omega a n * x : ℝ) : ℂ) * Complex.I := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * -(n : ℂ) * (x : ℂ) /
      (2 * (a : ℂ)) = -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) /
      (2 * (a : ℂ))) by ring, hp]
    ring
  simp only [character, fourier_coe_apply, Int.cast_neg, Int.cast_natCast,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hp, hm, ← Complex.two_cos]
  simp

/-- The original physical cosine inner product; its normalization is unchanged. -/
private lemma mode_inner_integral (a : ℝ) (u : WindowL2 a) (n : ℕ) :
    inner ℂ (modeL2 a n) u = ∫ x in window a, (mode a n x : ℂ) * u x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(mode_memLp a n).coeFn_toLp] with x hx
  change modeL2 a n x = (mode a n x : ℂ) at hx
  rw [hx]
  simp [RCLike.inner_apply', mul_comm]

private lemma mode_inner_pair (a : ℝ) (ha : 0 < a) (u : WindowL2 a) (n : ℕ) :
    2 * inner ℂ (modeL2 a n) u =
      (amplitude a n : ℂ) * (moment a u (n : ℤ) + moment a u (-(n : ℤ))) := by
  have hpair : moment a u (n : ℤ) + moment a u (-(n : ℤ)) =
      ∫ x in window a, 2 * (Real.cos (omega a n * x) : ℂ) * u x := by
    rw [moment, moment, ← integral_add (moment_integrable a ha u (n : ℤ))
      (moment_integrable a ha u (-(n : ℤ)))]
    have hfun : (fun x => character a (-(n : ℤ)) x * zeroExtension a u x +
        character a (-(-(n : ℤ))) x * zeroExtension a u x) =
        (window a).indicator (fun x => 2 * (Real.cos (omega a n * x) : ℂ) * u x) := by
      funext x
      rw [neg_neg, ← add_mul, add_comm (character a (-(n : ℤ)) x), character_pair]
      by_cases hx : x ∈ window a <;> simp [zeroExtension, hx]
    have hwindow : MeasurableSet (window a) := by
      simpa only [window] using (measurableSet_Ioc : MeasurableSet (Ioc (-a) a))
    rw [hfun, integral_indicator hwindow]
  rw [mode_inner_integral, hpair]
  simp only [mode, Complex.ofReal_mul]
  simp_rw [mul_assoc, integral_const_mul]
  ring

private lemma amplitude_pos (a : ℝ) (ha : 0 < a) (n : ℕ) : 0 < amplitude a n := by
  unfold amplitude
  split_ifs <;> positivity

/-- This includes n=0 with A_0=1/sqrt(2a); for n>0 A_n=1/sqrt(a). -/
lemma even_mode_inner_eq_moment (a : ℝ) (ha : 0 < a) (u : WindowL2 a)
    (hu : u ∈ originalEven a) (n : ℕ) :
    inner ℂ (modeL2 a n) u = (amplitude a n : ℂ) * moment a u (n : ℤ) := by
  have h := mode_inner_pair a ha u n
  rw [moment_neg a u hu] at h
  linear_combination h / 2

/-- EXACT normalization inherited from normalized Haar, not a probability
measure silently substituted for physical Lebesgue measure. -/
lemma fourierCoeffOn_eq_moment (a : ℝ) (ha : 0 < a) (u : WindowL2 a) (k : ℤ) :
    fourierCoeffOn (show -a < a by linarith) (u : ℝ → ℂ) k =
      ((2 * a)⁻¹ : ℂ) * moment a u k := by
  rw [fourierCoeffOn_eq_integral (u : ℝ → ℂ) k (show -a < a by linarith),
    show a - -a = 2 * a by ring,
    intervalIntegral.integral_of_le (show -a ≤ a by linarith), moment_eq_window]
  simp only [window, character, smul_eq_mul, Complex.real_smul, one_div,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- The normalized Haar L2 lift, multiplied by the mandatory sqrt(2a). -/
def circleTransport (a : ℝ) (ha : 0 < a) (u : WindowL2 a) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (2 * a) ⟨by linarith⟩) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hu : MemLp (u : ℝ → ℂ) 2 (volume.restrict (Ioc (-a) (-a + 2 * a))) := by
    simpa only [show -a + 2 * a = a by ring, windowMeasure, window] using Lp.memLp u
  exact (Real.sqrt (2 * a) : ℂ) • hu.memLp_liftIoc.haarAddCircle.toLp _

private lemma l2_energy {α : Type*} [MeasurableSpace α] (μ : Measure α) (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp only [← norm_sq_eq_re_inner]

/-- The square-root transport pays the full dx/Haar mass ratio. -/
theorem circleTransport_norm_sq (a : ℝ) (ha : 0 < a) (u : WindowL2 a) :
    ‖circleTransport a ha u‖ ^ 2 = ‖u‖ ^ 2 := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hu : MemLp (u : ℝ → ℂ) 2 (volume.restrict (Ioc (-a) (-a + 2 * a))) := by
    simpa only [show -a + 2 * a = a by ring, windowMeasure, window] using Lp.memLp u
  let h := hu.memLp_liftIoc.haarAddCircle
  have hE : ‖h.toLp (AddCircle.liftIoc (2 * a) (-a) u)‖ ^ 2 =
      (2 * a)⁻¹ * ‖u‖ ^ 2 := by
    rw [l2_energy]
    calc
      _ = ∫ z : AddCircle (2 * a), ‖AddCircle.liftIoc (2 * a) (-a) u z‖ ^ 2
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [h.coeFn_toLp] with z hz
        rw [hz]
      _ = (2 * a)⁻¹ * ∫ x in (-a)..(-a + 2 * a), ‖u x‖ ^ 2 := by
        rw [AddCircle.integral_haarAddCircle]
        simp only [smul_eq_mul]
        congr 1
        calc
          _ = ∫ z : AddCircle (2 * a), AddCircle.liftIoc (2 * a) (-a)
              ((fun w : ℂ => ‖w‖ ^ 2) ∘ (u : ℝ → ℂ)) z := by
            apply integral_congr_ae
            exact Eventually.of_forall fun z => by
              rw [AddCircle.liftIoc_comp_apply]
          _ = _ := by
            rw [AddCircle.integral_liftIoc_eq_intervalIntegral]
            simp only [Function.comp_apply]
      _ = (2 * a)⁻¹ * ‖u‖ ^ 2 := by
        rw [show -a + 2 * a = a by ring,
          intervalIntegral.integral_of_le (show -a ≤ a by linarith), l2_energy]
        rfl
  change ‖(Real.sqrt (2 * a) : ℂ) • h.toLp _‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity), hE]
  field_simp [ha.ne']
  <;> ring

/-- Physical exponential coefficients are sqrt(2a) times normalized Haar
coefficients of the unscaled lift. This identity fixes the coefficient scale. -/
theorem circleTransport_fourierCoeff (a : ℝ) (ha : 0 < a) (u : WindowL2 a) (k : ℤ) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    fourierCoeff (circleTransport a ha u) k =
      (Real.sqrt (2 * a) : ℂ) *
        fourierCoeffOn (show -a < a by linarith) (u : ℝ → ℂ) k := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hu : MemLp (u : ℝ → ℂ) 2 (volume.restrict (Ioc (-a) (-a + 2 * a))) := by
    simpa only [show -a + 2 * a = a by ring, windowMeasure, window] using Lp.memLp u
  let h := hu.memLp_liftIoc.haarAddCircle
  have hFn : (circleTransport a ha u : AddCircle (2 * a) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun z => (Real.sqrt (2 * a) : ℂ) * AddCircle.liftIoc (2 * a) (-a) u z) := by
    filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * a) : ℂ) (h.toLp _),
      h.coeFn_toLp] with z hs hz
    simpa only [circleTransport, Pi.smul_apply, smul_eq_mul, hz] using hs
  have hlift : fourierCoeff (AddCircle.liftIoc (2 * a) (-a) u) k =
      fourierCoeffOn (show -a < a by linarith) (u : ℝ → ℂ) k := by
    simpa only [show -a + 2 * a = a by ring] using
      (fourierCoeff_liftIoc_eq (T := 2 * a) (a := -a) (u : ℝ → ℂ) k)
  rw [congrFun (fourierCoeff_congr_ae hFn) k, fourierCoeff.const_mul, hlift]

/-- Fourier injectivity on the full ORIGINAL even sector, not on a defined span. -/
theorem even_eq_zero_of_mode_inner_eq_zero (a : ℝ) (ha : 0 < a) (u : WindowL2 a)
    (hu : u ∈ originalEven a) (hmode : ∀ n : ℕ, inner ℂ (modeL2 a n) u = 0) :
    u = 0 := by
  have hm (n : ℕ) : moment a u (n : ℤ) = 0 := by
    have h := hmode n
    rw [even_mode_inner_eq_moment a ha u hu] at h
    exact (mul_eq_zero.mp h).resolve_left (by
      exact_mod_cast (ne_of_gt (amplitude_pos a ha n)))
  have hall (k : ℤ) : moment a u k = 0 := by
    rcases le_or_gt 0 k with hk | hk
    · simpa only [Int.toNat_of_nonneg hk] using hm k.toNat
    · have hp : 0 ≤ -k := by omega
      have h := hm (-k).toNat
      rw [Int.toNat_of_nonneg hp, moment_neg a u hu] at h
      exact h
  have hcoeff (k : ℤ) : fourierCoeffOn (show -a < a by linarith) (u : ℝ → ℂ) k = 0 := by
    rw [fourierCoeffOn_eq_moment a ha, hall, mul_zero]
  have hp := tsum_sq_fourierCoeffOn (show -a < a by linarith) (Lp.memLp u)
  simp only [hcoeff, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), tsum_zero,
    show a - -a = 2 * a by ring, smul_eq_mul,
    intervalIntegral.integral_of_le (show -a ≤ a by linarith)] at hp
  have hmass : (∫ x in window a, ‖u x‖ ^ 2) = 0 := by
    exact (mul_eq_zero.mp hp.symm).resolve_left (inv_ne_zero (by positivity))
  apply norm_eq_zero.mp
  have hn : ‖u‖ ^ 2 = 0 := by rw [l2_energy]; exact hmass
  nlinarith [norm_nonneg u]

def cosineClosure (a : ℝ) : Submodule ℂ (WindowL2 a) :=
  (Submodule.span ℂ (Set.range (modeL2 a))).topologicalClosure

instance cosineClosure_complete (a : ℝ) : CompleteSpace (cosineClosure a) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

private lemma cosineClosure_le_even (a : ℝ) : cosineClosure a ≤ originalEven a := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact mode_mem_originalEven a n
  · exact originalEven_isClosed a

/-- Full complex AE-even cosine completeness on the original Ioc dx carrier. -/
theorem originalEven_eq_cosineClosure (a : ℝ) (ha : 0 < a) :
    originalEven a = (Submodule.span ℂ (Set.range (modeL2 a))).topologicalClosure := by
  apply le_antisymm _ (cosineClosure_le_even a)
  intro u hu
  let p := (cosineClosure a).starProjection u
  have hp : p ∈ originalEven a := cosineClosure_le_even a
    ((cosineClosure a).starProjection_apply_mem u)
  have horth := (cosineClosure a).sub_starProjection_mem_orthogonal u
  have hz : u - p = 0 := even_eq_zero_of_mode_inner_eq_zero a ha (u - p)
    ((originalEven a).sub_mem hu hp) (fun n =>
      (Submodule.mem_orthogonal _ _).mp horth _
        (Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))))
  have heq : u = p := sub_eq_zero.mp hz
  rw [heq]
  exact (cosineClosure a).starProjection_apply_mem u

end OriginalEvenCosineComplete
