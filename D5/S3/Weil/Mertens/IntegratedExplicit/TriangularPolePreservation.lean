import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula

/-! The dyadic triangular filter preserves the simple pole contribution of every
zeta zero in the open critical strip, even after subtraction of a continuous
boundary term. -/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace TriangularPolePreservation

open D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit (U_exp_continuous)
open D5.S3.Analytic.Laplace.EulerPoleObstruction (finiteHead finiteHead_entire kernel)

def multiplier (s : ℂ) : ℂ :=
  (Complex.exp (s * (Real.log 2 : ℂ)) - 1) *
    (Complex.exp (s * (Real.log 2 : ℂ)) - 2)

theorem multiplier_norm_lower {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    0 < ((2 : ℝ) ^ s.re - 1) * (2 - (2 : ℝ) ^ s.re) ∧
      ((2 : ℝ) ^ s.re - 1) * (2 - (2 : ℝ) ^ s.re) ≤ ‖multiplier s‖ := by
  let z := Complex.exp (s * (Real.log 2 : ℂ))
  have hz : ‖z‖ = (2 : ℝ) ^ s.re := by
    simp only [z, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num), mul_comm]
  have h1 : 1 < (2 : ℝ) ^ s.re := Real.one_lt_rpow (by norm_num) hs0
  have h2 : (2 : ℝ) ^ s.re < 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) hs1
  have hleft : (2 : ℝ) ^ s.re - 1 ≤ ‖z - 1‖ := by
    simpa only [hz, norm_one] using norm_sub_norm_le z (1 : ℂ)
  have hright : 2 - (2 : ℝ) ^ s.re ≤ ‖z - 2‖ := by
    rw [← norm_sub_rev]
    simpa only [hz, Complex.norm_ofNat] using norm_sub_norm_le (2 : ℂ) z
  exact ⟨mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), by
    simpa only [multiplier, z, norm_mul] using
      mul_le_mul hleft hright (sub_nonneg.mpr h2.le) (norm_nonneg _)⟩

/-- Subtracting a continuous boundary term preserves the nonzero scaled limit. -/
theorem triangular_filtered_residue {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {boundary : ℂ → ℂ}
    (hb : ContinuousAt boundary ρ) :
    let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
    multiplier ρ * c ≠ 0 ∧
      Tendsto (fun s : ℂ => (s - ρ) * (multiplier s * transform s - boundary s))
        (𝓝[≠] ρ) (𝓝 (multiplier ρ * c)) := by
  dsimp only
  let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
  obtain ⟨_, hc, H, hH, hg⟩ := transform_integral_and_zero_germs.2 ρ hz
  have hm : multiplier ρ ≠ 0 :=
    norm_pos_iff.mp ((multiplier_norm_lower hρ0 hρ1).1.trans_le
      (multiplier_norm_lower hρ0 hρ1).2)
  refine ⟨mul_ne_zero hm hc, ?_⟩
  have hM : ContinuousAt multiplier ρ := by unfold multiplier; fun_prop
  let regular := fun s : ℂ => multiplier s * c +
    (s - ρ) * (multiplier s * H s - boundary s)
  have hregular : ContinuousAt regular ρ := by
    dsimp only [regular]
    exact (hM.mul continuousAt_const).add
      ((continuousAt_id.sub continuousAt_const).mul ((hM.mul hH.continuousAt).sub hb))
  have hlimit : Tendsto regular (𝓝[≠] ρ) (𝓝 (multiplier ρ * c)) := by
    have ht : ContinuousWithinAt regular ({ρ} : Set ℂ)ᶜ ρ :=
      hregular.continuousWithinAt
    change Tendsto regular (𝓝[≠] ρ) (𝓝 (regular ρ)) at ht
    simpa only [regular, sub_self, zero_mul, add_zero] using ht
  apply hlimit.congr'
  filter_upwards [hg, @self_mem_nhdsWithin ℂ _ ρ ({ρ} : Set ℂ)ᶜ] with s hs hne
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hne)
  dsimp only [regular, c]
  rw [hs]
  field_simp
  ring

private def g (t : ℝ) : ℝ := U (Real.exp t)

private theorem forward_shift {s : ℂ} (hs : 1 < s.re) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (kernel (fun t => g (t + h)) s) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), kernel (fun u => g (u + h)) s t) =
        Complex.exp (s * (h : ℂ)) * (transform s - finiteHead g 0 h s) := by
  let f := kernel g s
  have hf : IntegrableOn f (Ioi 0) := (transform_integral_and_zero_germs.1 s hs).1
  have htail : IntegrableOn f (Ioi h) := hf.mono_set (Ioi_subset_Ioi hh)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hf htail
  rw [intervalIntegral.integral_of_le hh] at hsplit
  have horiginal : (∫ t in Ioi (0 : ℝ), f t) = transform s :=
    (transform_integral_and_zero_germs.1 s hs).2
  rw [horiginal] at hsplit
  have htail_eq : (∫ t in Ioi h, f t) = transform s - finiteHead g 0 h s := by
    have heq : finiteHead g 0 h s + (∫ t in Ioi h, f t) = transform s := hsplit
    linear_combination heq
  have htranslated : (Ioi (0 : ℝ)).indicator (fun t => f (t + h)) =
      fun t => (Ioi h).indicator f (t + h) := by
    ext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht),
        indicator_of_mem (show t + h ∈ Ioi h by simpa only [mem_Ioi, lt_add_iff_pos_left])]
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht),
        indicator_of_notMem (show t + h ∉ Ioi h by simpa only [mem_Ioi, lt_add_iff_pos_left])]
  have hint : IntegrableOn (fun t => f (t + h)) (Ioi 0) := by
    rw [← integrable_indicator_iff measurableSet_Ioi, htranslated]
    exact (measurePreserving_add_right volume h).integrable_comp_of_integrable
      (htail.integrable_indicator measurableSet_Ioi)
  have heq : (∫ t in Ioi (0 : ℝ), f (t + h)) = ∫ t in Ioi h, f t := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi, htranslated]
    exact integral_add_right_eq_self ((Ioi h).indicator f) h
  have hfactor : (fun t => kernel (fun u => g (u + h)) s t) =
      fun t => Complex.exp (s * (h : ℂ)) * f (t + h) := by
    ext t
    dsimp [f, kernel]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · have h' : IntegrableOn (fun t => Complex.exp (s * (h : ℂ)) * f (t + h)) (Ioi 0) :=
      hint.const_mul _
    exact Eq.mpr (congrArg (fun v : ℝ → ℂ => IntegrableOn v (Ioi (0 : ℝ))) hfactor) h'
  · simp_rw [hfactor]
    rw [integral_const_mul, heq, htail_eq]

/-- The exact compact contribution removed when translating the log-Laplace transform. -/
def cutoffCorrection (s : ℂ) : ℂ :=
  Complex.exp (s * ((2 * Real.log 2 : ℝ) : ℂ)) * finiteHead g 0 (2 * Real.log 2) s -
  3 * Complex.exp (s * (Real.log 2 : ℂ)) * finiteHead g 0 (Real.log 2) s

theorem cutoffCorrection_entire : Differentiable ℂ cutoffCorrection := by
  have hg (h : ℝ) : Differentiable ℂ (finiteHead g 0 h) :=
    finiteHead_entire U_exp_continuous.integrableOn_Ioc
  unfold cutoffCorrection
  fun_prop (disch := apply hg)

def logHinge (t : ℝ) : ℝ := g (t + 2 * Real.log 2) - 3 * g (t + Real.log 2) + 2 * g t

theorem logHinge_eq (t : ℝ) :
    logHinge t = U (4 * Real.exp t) - 3 * U (2 * Real.exp t) + 2 * U (Real.exp t) := by
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have h4 : Real.exp (2 * Real.log 2) = 4 := by
    rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add, h2]
    norm_num
  simp only [logHinge, g, Real.exp_add, h2, h4, mul_comm (Real.exp t)]

/-- The transformed actual hinge is the multiplier times the original transform
minus the exact entire correction at the lower end. -/
theorem logHinge_transform {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (kernel logHinge s) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), kernel logHinge s t) =
        multiplier s * transform s - cutoffCorrection s := by
  let h := Real.log 2
  have hh : 0 ≤ h := Real.log_nonneg (by norm_num)
  obtain ⟨hi2, he2⟩ := forward_shift hs (h := 2 * h) (by positivity)
  obtain ⟨hi1, he1⟩ := forward_shift hs hh
  obtain ⟨hi0, he0⟩ := transform_integral_and_zero_germs.1 s hs
  have hi0' : IntegrableOn (kernel g s) (Ioi 0) := hi0
  have he0' : (∫ t in Ioi (0 : ℝ), kernel g s t) = transform s := he0
  have hsplit : kernel logHinge s =
      fun t => kernel (fun u => g (u + 2 * h)) s t -
        3 * kernel (fun u => g (u + h)) s t + 2 * kernel g s t := by
    ext t
    push_cast [kernel, logHinge, h]
    ring
  rw [hsplit]
  have hidiff : IntegrableOn (fun t => kernel (fun u => g (u + 2 * h)) s t -
      3 * kernel (fun u => g (u + h)) s t) (Ioi 0) := hi2.sub (hi1.const_mul 3)
  refine ⟨hidiff.add (hi0'.const_mul 2), ?_⟩
  rw [integral_add hidiff (hi0'.const_mul 2),
    integral_sub hi2 (hi1.const_mul 3), integral_const_mul, integral_const_mul,
    he2, he1, he0']
  unfold multiplier cutoffCorrection
  dsimp [h]
  rw [show s * (↑(2 * Real.log 2 : ℝ) : ℂ) =
      s * (Real.log 2 : ℂ) + s * (Real.log 2 : ℂ) by push_cast; ring, Complex.exp_add]
  ring

theorem logHinge_pole {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    let c := (analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (1 - ρ))
    multiplier ρ * c ≠ 0 ∧
      Tendsto (fun s : ℂ => (s - ρ) * (multiplier s * transform s - cutoffCorrection s))
        (𝓝[≠] ρ) (𝓝 (multiplier ρ * c)) :=
  triangular_filtered_residue hz hρ0 hρ1 (cutoffCorrection_entire.continuous.continuousAt)

open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

def filteredCoeff (k : ℕ) : ℂ := actualCoeff k * multiplier (actualZero k)

theorem filteredCoeff_summable : Summable (fun k : ℕ => ‖filteredCoeff k‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (actualCoeff_hasSum.summable.norm.mul_right 12)
  intro k
  let ρ := actualZero k
  have hρ := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2
  let z := Complex.exp (ρ * (Real.log 2 : ℂ))
  have hz : ‖z‖ ≤ 2 := by
    calc
      ‖z‖ = Real.exp (ρ.re * Real.log 2) := by
        simp only [z, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr
        (mul_le_of_le_one_left (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hρ.le)
      _ = 2 := Real.exp_log (by norm_num)
  have h1 : ‖z - 1‖ ≤ 3 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have h2 : ‖z - 2‖ ≤ 4 := (norm_sub_le _ _).trans (by
    rw [Complex.norm_ofNat]
    linarith)
  have hp : ‖z - 1‖ * ‖z - 2‖ ≤ (3 : ℝ) * 4 :=
    mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  norm_num at hp
  rw [filteredCoeff, norm_mul, multiplier, norm_mul]
  exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)

def trivialCorrection (u : ℝ) : ℝ :=
  -trivialT (u + 2 * Real.log 2) + 3 * trivialT (u + Real.log 2) - 2 * trivialT u

theorem trivialCorrection_norm_le {u : ℝ} (hu : 0 ≤ u) :
    |trivialCorrection u| ≤ 6 * Real.exp (-2 * u) := by
  have htriv {t : ℝ} (ht : u ≤ t) : |trivialT t| ≤ Real.exp (-2 * u) := by
    have ht0 := hu.trans ht
    rw [abs_of_nonneg (trivialT_nonneg ht0), trivialT]
    have hs := trivialCoeff_hasSum.summable.mul_right (Real.exp (-2 * u))
    refine ((trivialT_summable ht0).tsum_le_tsum (fun n => ?_) hs).trans ?_
    · apply mul_le_mul_of_nonneg_left _ (trivialCoeff_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) ht0]
    · rw [(trivialCoeff_hasSum.mul_right _).tsum_eq]
      apply mul_le_of_le_one_left (Real.exp_nonneg _)
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h0 := htriv le_rfl
  have h1 := htriv (show u ≤ u + Real.log 2 by linarith)
  have h2 := htriv (show u ≤ u + 2 * Real.log 2 by linarith)
  unfold trivialCorrection
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    (abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp h2).1, (abs_le.mp h2).2]

/-- The exact filtered zero expansion is valid at every positive log-scale. -/
theorem logHinge_spectrum {u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℕ => filteredCoeff k * Complex.exp ((u : ℂ) * actualZero k))
      ((logHinge u - trivialCorrection u : ℝ) : ℂ) := by
  let h := Real.log 2
  have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h0 := (actualH_summable u).hasSum
  have h1 := (actualH_summable (u + h)).hasSum.mul_left (3 : ℂ)
  have h2 := (actualH_summable (u + 2 * h)).hasSum
  have hsum := (h2.sub h1).add (h0.mul_left (2 : ℂ))
  change HasSum _ (actualH (u + 2 * h) - 3 * actualH (u + h) + 2 * actualH u) at hsum
  have hterm (k : ℕ) :
      actualCoeff k * Complex.exp (((u + 2 * h : ℝ) : ℂ) * actualZero k) -
          3 * (actualCoeff k * Complex.exp (((u + h : ℝ) : ℂ) * actualZero k)) +
            2 * (actualCoeff k * Complex.exp ((u : ℂ) * actualZero k)) =
          filteredCoeff k * Complex.exp ((u : ℂ) * actualZero k) := by
    push_cast [h]
    rw [add_mul, add_mul, mul_assoc (2 : ℂ), mul_comm (2 : ℂ)]
    rw [show (Real.log 2 : ℂ) * actualZero k * 2 =
      actualZero k * (Real.log 2 : ℂ) + actualZero k * (Real.log 2 : ℂ) by ring]
    simp only [Complex.exp_add, filteredCoeff, multiplier]
    rw [mul_comm (Real.log 2 : ℂ) (actualZero k)]
    ring
  have hval : actualH (u + 2 * h) - 3 * actualH (u + h) + 2 * actualH u =
      ((logHinge u - trivialCorrection u : ℝ) : ℂ) := by
    rw [actual_integrated_explicit_formula (show 0 < u + 2 * h by dsimp [h]; linarith),
      actual_integrated_explicit_formula (show 0 < u + h by dsimp [h]; linarith),
      actual_integrated_explicit_formula hu]
    push_cast [logHinge, trivialCorrection, g, h]
    ring
  simpa only [hterm, hval] using hsum

def distinctCoeff (n : ℕ) : ℂ :=
  (actualData.multiplicity n : ℂ) *
    (1 / (actualData.zero n * (1 - actualData.zero n)) * multiplier (actualData.zero n))

theorem distinctCoeff_summable : Summable (fun n : ℕ => ‖distinctCoeff n‖) := by
  let f (p : ActualZeroOccurrence) : ℝ :=
    ‖1 / (actualData.zero p.1 * (1 - actualData.zero p.1)) * multiplier (actualData.zero p.1)‖
  have hs : Summable f := (actualOccurrenceEquiv.summable_iff).1 (by
    simpa only [f, Function.comp_def, actualZero, filteredCoeff, actualCoeff] using
      filteredCoeff_summable)
  have h := ((summable_sigma_of_nonneg (fun p : ActualZeroOccurrence => norm_nonneg _)).1 hs).2
  simpa only [f, distinctCoeff, norm_mul, Complex.norm_natCast, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

theorem distinctCoeff_ne_zero (n : ℕ) : distinctCoeff n ≠ 0 := by
  have hz := (actualData.zero_isNontrivial n).2
  have hz0 : actualData.zero n ≠ 0 := by
    intro h
    simpa [h] using hz.1
  have hz1 : (1 : ℂ) - actualData.zero n ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [← he, Complex.one_re] at hz
    exact (lt_irrefl (1 : ℝ)) hz.2
  have hm := multiplier_norm_lower hz.1 hz.2
  exact mul_ne_zero (by exact_mod_cast (actualData.multiplicity_pos n).ne')
    (mul_ne_zero (div_ne_zero one_ne_zero (mul_ne_zero hz0 hz1))
      (norm_pos_iff.mp (hm.1.trans_le hm.2)))

theorem distinctCoeff_conjugate (n : ℕ) :
    distinctCoeff (actualData.conjugation n) = conj (distinctCoeff n) := by
  rw [distinctCoeff, actualData.zero_conjugation, actualData.multiplicity_conjugation]
  simp only [distinctCoeff, multiplier, map_mul, map_div₀, map_one, map_sub,
    map_natCast, map_ofNat, ← Complex.exp_conj, Complex.conj_ofReal]

/-- Each distinct zero appears exactly once, weighted by its analytic order. -/
theorem logHinge_distinct_spectrum {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => distinctCoeff n * Complex.exp ((u : ℂ) * actualData.zero n))
      ((logHinge u - trivialCorrection u : ℝ) : ℂ) := by
  let f (p : ActualZeroOccurrence) : ℂ :=
    (1 / (actualData.zero p.1 * (1 - actualData.zero p.1)) * multiplier (actualData.zero p.1)) *
      Complex.exp ((u : ℂ) * actualData.zero p.1)
  have hs : HasSum f ((logHinge u - trivialCorrection u : ℝ) : ℂ) :=
    (actualOccurrenceEquiv.hasSum_iff).1 (by
      simpa only [f, Function.comp_def, actualZero, filteredCoeff, actualCoeff] using
        logHinge_spectrum hu)
  have he := hs.summable.tsum_sigma
  have hn :
      Summable (fun n : ℕ => distinctCoeff n * Complex.exp ((u : ℂ) * actualData.zero n)) := by
    apply Summable.of_norm_bounded (distinctCoeff_summable.mul_right (Real.exp u))
    intro n
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Complex.norm_exp, Real.exp_le_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_of_le_one_right hu.le (actualData.zero_isNontrivial n).2.2.le
  have hEq : (∑' n : ℕ, distinctCoeff n * Complex.exp ((u : ℂ) * actualData.zero n)) =
      ((logHinge u - trivialCorrection u : ℝ) : ℂ) := by
    rw [← hs.tsum_eq, he]
    apply tsum_congr
    intro n
    simp only [f, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, distinctCoeff, mul_assoc]
  exact hEq ▸ hn.hasSum

end TriangularPolePreservation

#print axioms TriangularPolePreservation.triangular_filtered_residue
#print axioms TriangularPolePreservation.logHinge_transform
#print axioms TriangularPolePreservation.logHinge_pole
#print axioms TriangularPolePreservation.logHinge_spectrum
#print axioms TriangularPolePreservation.logHinge_distinct_spectrum
