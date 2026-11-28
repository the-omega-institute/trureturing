/- GID: D5/S3/Weil/ZeroData/ZetaOrdinateDensityTransfer
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ZetaOrdinateDensityTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exponential right-tail density estimate controls the reflected zero sum. -/

import D5.S3.Weil.ZeroData.ZetaOrdinateReflectionTransfer
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Integrating the right-tail zero count bounds the signed-frequency transfer. -/

namespace D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer

open Finset MeasureTheory Set

private theorem weightedExpSubOne_le_of_tail {ι : Type*}
    (s : Finset ι) (d w : ι → ℝ) {A r : ℝ} (hr : 0 < r)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (htail : ∀ t > 0, (∑ i ∈ s.filter (fun i => t ≤ d i), w i) ≤ A * Real.exp (-r * t)) :
    (∑ i ∈ s, w i * (Real.exp ((r / 2) * d i) - 1)) ≤ A := by
  classical
  let g : ℝ → ℝ := fun t => (r / 2) * Real.exp ((r / 2) * t)
  have hg : Continuous g := by dsimp [g]; fun_prop
  let f (i : ι) := (Iic (d i)).indicator (fun t => w i * g t)
  have hfi (i : ι) (hi : i ∈ s) : IntegrableOn (f i) (Ioi 0) := by
    dsimp only [f]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    rw [show Iic (d i) ∩ Ioi (0 : ℝ) = Ioc 0 (d i) by ext t; simp [and_comm]]
    exact ((continuous_const.mul hg).intervalIntegrable 0 (d i)).1
  have hei (i : ι) (hi : i ∈ s) :
      (∫ t in Ioi (0 : ℝ), f i t) = w i * (Real.exp ((r / 2) * d i) - 1) := by
    dsimp only [f]
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    rw [show Iic (d i) ∩ Ioi (0 : ℝ) = Ioc 0 (d i) by ext t; simp [and_comm]]
    rw [← intervalIntegral.integral_of_le (hd i hi), intervalIntegral.integral_const_mul]
    congr 1
    have hderiv (t : ℝ) : HasDerivAt (fun x : ℝ => Real.exp ((r / 2) * x)) (g t) t := by
      simpa [g, mul_comm] using (((hasDerivAt_id t).const_mul (r / 2)).exp)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hg.intervalIntegrable _ _), mul_zero, Real.exp_zero]
  have hmajor : IntegrableOn (fun t => (A * (r / 2)) * Real.exp (-(r / 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(r / 2) < 0) 0).const_mul _
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (∑ i ∈ s, f i t) ≤ (A * (r / 2)) * Real.exp (-(r / 2) * t) := by
    have hsum : (∑ i ∈ s, f i t) = (∑ i ∈ s.filter (fun i => t ≤ d i), w i) * g t := by
      rw [sum_mul, sum_filter]
      apply sum_congr rfl
      intro i _
      by_cases h : t ≤ d i <;> simp [f, h]
    rw [hsum]
    calc
      _ ≤ (A * Real.exp (-r * t)) * g t :=
        mul_le_mul_of_nonneg_right (htail t ht) (by dsimp [g]; positivity)
      _ = _ := by
        unfold g
        rw [show (A * Real.exp (-r * t)) * ((r / 2) * Real.exp ((r / 2) * t)) =
          (A * (r / 2)) * (Real.exp (-r * t) * Real.exp ((r / 2) * t)) by ring,
          ← Real.exp_add]
        congr 2
        ring
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∑ i ∈ s, f i t := by
      rw [integral_finsetSum s hfi]
      exact sum_congr rfl fun i hi => (hei i hi).symm
    _ ≤ ∫ t in Ioi (0 : ℝ), (A * (r / 2)) * Real.exp (-(r / 2) * t) :=
      setIntegral_mono_on (integrable_finsetSum s hfi) hmajor measurableSet_Ioi hpoint
    _ = A := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(r / 2) < 0),
        mul_zero, Real.exp_zero]
      field_simp

private theorem quadraticExp_le_of_tail {ι : Type*}
    (s : Finset ι) (d w : ι → ℝ) {A r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b)
    (hbr : b ≤ r / 4) (hd : ∀ i ∈ s, 0 ≤ d i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (htail : ∀ t > 0, (∑ i ∈ s.filter (fun i => t ≤ d i), w i) ≤ A * Real.exp (-r * t)) :
    (∑ i ∈ s, w i * (d i ^ 2 * Real.exp (b * d i))) ≤ (32 / r ^ 2) * A := by
  classical
  have hpoint (i : ι) (hi : i ∈ s) :
      d i ^ 2 * Real.exp (b * d i) ≤ (32 / r ^ 2) * (Real.exp ((r / 2) * d i) - 1) := by
    have hd₀ := hd i hi
    have hq := Real.quadratic_le_exp_of_nonneg
      (show 0 ≤ r / 4 * d i by positivity)
    have hsq : r ^ 2 * (d i ^ 2) / 32 ≤ Real.exp (r / 4 * d i) - 1 := by
      nlinarith [mul_nonneg (show 0 ≤ r / 4 by positivity) hd₀]
    have hE : 1 ≤ Real.exp (b * d i) :=
      Real.one_le_exp (by positivity)
    have harg : (b + r / 4) * d i ≤ (r / 2) * d i :=
      mul_le_mul_of_nonneg_right (by linarith) hd₀
    have hproduct := mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg (b * d i))
    have hsum : Real.exp (r / 4 * d i) * Real.exp (b * d i) ≤
        Real.exp ((r / 2) * d i) := by
      rw [← Real.exp_add, ← add_mul, add_comm]
      exact Real.exp_le_exp.mpr harg
    rw [show (32 / r ^ 2) * (Real.exp ((r / 2) * d i) - 1) =
      (Real.exp ((r / 2) * d i) - 1) * 32 / r ^ 2 by ring]
    apply (le_div_iff₀ (sq_pos_of_pos hr)).2
    nlinarith only [hproduct, hsum, hE]
  calc
    _ ≤ ∑ i ∈ s, w i * ((32 / r ^ 2) * (Real.exp ((r / 2) * d i) - 1)) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hpoint i hi) (hw i hi)
    _ = (32 / r ^ 2) * ∑ i ∈ s, w i * (Real.exp ((r / 2) * d i) - 1) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weightedExpSubOne_le_of_tail s d w hr hd htail)
      (by positivity)

open D5.S3.Weil.ZeroData.ZetaOrdinateReflectionTransfer Zeta23

/-- An exponential bound on the multiplicity-weighted right-tail count gives a
quadratic ordinate transfer for frequencies up to one quarter of the decay rate. -/
theorem actual_reflection_bound_of_exponential_tail (v T A r : ℝ) (hr : 0 < r) (hv : |v| ≤ r / 4)
    (htail : ∀ t > 0,
      (∑ ρ ∈ (zerosIn_finite 0 T).toFinset.filter (fun ρ => 1 / 2 + t ≤ ρ.re),
        (zeroMult ρ : ℝ)) ≤ A * Real.exp (-r * t)) :
    let s := (zerosIn_finite 0 T).toFinset
    ‖(∑ ρ ∈ s, (zeroMult ρ : ℂ) * Complex.exp ((v : ℂ) * (ρ - 1 / 2))) -
      ∑ ρ ∈ s, (zeroMult ρ : ℂ) * Complex.exp (Complex.I * ((v * ρ.im : ℝ) : ℂ))‖ ≤
        64 * A * (v / r) ^ 2 := by
  classical
  let s := (zerosIn_finite 0 T).toFinset
  let d (ρ : ℂ) : ℝ := |ρ.re - 1 / 2|
  let w (ρ : ℂ) : ℝ := zeroMult ρ
  have hs (ρ : ℂ) : ρ ∈ s ↔ IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T :=
    Set.Finite.mem_toFinset _
  have htailAbs (t : ℝ) (ht : 0 < t) :
      (∑ ρ ∈ s.filter (fun ρ => t ≤ d ρ), w ρ) ≤ (2 * A) * Real.exp (-r * t) := by
    let right := s.filter (fun ρ => 1 / 2 + t ≤ ρ.re)
    let left := s.filter (fun ρ => ρ.re ≤ 1 / 2 - t)
    have hdisj : Disjoint right left := by
      refine Finset.disjoint_left.mpr fun ρ hrρ hlρ => ?_
      change ρ ∈ s.filter _ at hrρ
      change ρ ∈ s.filter _ at hlρ
      linarith [(mem_filter.mp hrρ).2, (mem_filter.mp hlρ).2]
    have heq : s.filter (fun ρ => t ≤ d ρ) = right ∪ left := by
      ext ρ
      simp only [d, right, left, Finset.mem_filter, Finset.mem_union, le_abs]
      constructor
      · rintro ⟨hρ, h | h⟩
        · exact Or.inl ⟨hρ, by linarith⟩
        · exact Or.inr ⟨hρ, by linarith⟩
      · rintro (⟨hρ, h⟩ | ⟨hρ, h⟩)
        · exact ⟨hρ, Or.inl (by linarith)⟩
        · exact ⟨hρ, Or.inr (by linarith)⟩
    have hreflect {ρ : ℂ} (hρ : ρ ∈ s) : reflect ρ ∈ s := by
      obtain ⟨hz, hlo, hhi⟩ := (hs ρ).mp hρ
      exact (hs _).mpr ⟨zeta_reflect_zero _ hz, by simpa using hlo, by simpa using hhi⟩
    have hsym : (∑ ρ ∈ left, w ρ) = ∑ ρ ∈ right, w ρ := by
      apply sum_bij (fun ρ _ => reflect ρ)
      · intro ρ hρ
        obtain ⟨hρs, hρl⟩ := mem_filter.mp hρ
        refine mem_filter.mpr ⟨hreflect hρs, ?_⟩
        rw [reflect_re]
        linarith
      · intro ρ _ σ _ h
        exact reflect_injective h
      · intro ρ hρ
        obtain ⟨hρs, hρr⟩ := mem_filter.mp hρ
        refine ⟨reflect ρ, mem_filter.mpr ⟨hreflect hρs, ?_⟩, reflect_reflect ρ⟩
        rw [reflect_re]
        linarith
      · intro ρ hρ
        dsimp [w]
        rw [zeta_mult_reflect _ ((hs _).mp (mem_filter.mp hρ).1).1]
    rw [heq, sum_union hdisj, hsym]
    have h := htail t ht
    change (∑ ρ ∈ right, w ρ) ≤ A * Real.exp (-r * t) at h
    linarith
  have hm := quadraticExp_le_of_tail s d w hr (abs_nonneg v) hv
    (fun _ _ => abs_nonneg _) (fun _ _ => Nat.cast_nonneg _) htailAbs
  have h := actual_reflection_bound v T
  dsimp only at h ⊢
  refine h.trans ?_
  calc
    _ = |v| ^ 2 * ∑ ρ ∈ s, w ρ * (d ρ ^ 2 * Real.exp (|v| * d ρ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro ρ _
      rw [abs_mul]
      dsimp [w, d]
      ring
    _ ≤ |v| ^ 2 * ((32 / r ^ 2) * (2 * A)) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ = _ := by
      rw [sq_abs, div_pow]
      ring

end D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer
