/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-weight quadrature with the exact total variation error. -/

import D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion
import D5.S3.Arith.Robin.Analytic.OmegaTailUpper
import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Finset Set
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

private lemma prime_cdf (t : ℝ) :
    (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, if p.Prime then (1 : ℝ) else 0) = primeCount t := by
  simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [← Nat.primesLE_eq_filter_Icc_zero, Nat.primesLE_card_eq_primeCounting]
  rfl

/-- A finite prime quadrature bound keeps both endpoint discrepancies and
the total variation of the actual weight. -/
theorem prime_quadrature_upper {a b C E : ℝ} {f d : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E)
    (hd : ContinuousOn d (Set.Icc a b))
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t)
    (hcount : ∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E) :
    (∑ p ∈ primeInterval a b, f p) ≤ C * (∫ t in a..b, f t) +
      E * (|f a| + |f b| + ∫ t in a..b, |d t|) := by
  classical
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hdi : IntegrableOn d (Set.Icc a b) := hd.integrableOn_Icc
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hdt : IntegrableOn (fun t => d t * t) (Set.Icc a b) :=
    (hd.mul continuousOn_id).integrableOn_Icc
  have hdc : IntegrableOn (fun t => d t * primeCount t) (Set.Icc a b) := by
    have h := integrableOn_mul_sum_Icc
      (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) ha hdi (m := 0)
    simp_rw [prime_cdf] at h
    exact h
  have herror : IntegrableOn (fun t => d t * (primeCount t - C * t))
      (Set.Ioc a b) := by
    have h := hdc.sub (hdt.const_mul C)
    convert h.mono_set Set.Ioc_subset_Icc_self using 1
    ext t
    dsimp only [Pi.sub_apply]
    ring
  have habs : IntegrableOn (fun t => E * |d t|) (Set.Ioc a b) := by
    have h : IntegrableOn (fun t => E * |d t|) (Set.Icc a b) := hdi.abs.const_mul E
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hbound : |∫ t in Set.Ioc a b, d t * (primeCount t - C * t)| ≤
      E * (∫ t in a..b, |d t|) := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, |d t * (primeCount t - C * t)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioc a b, E * |d t| := by
        apply setIntegral_mono_on herror.abs habs measurableSet_Ioc
        intro t ht
        rw [abs_mul, mul_comm E]
        exact mul_le_mul_of_nonneg_left (hcount t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)
      _ = _ := by rw [integral_const_mul, ← intervalIntegral.integral_of_le hab]
  have hFTC : (∫ t in a..b, f t + d t * t) = b * f b - a * f a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * f t) _
      (hfi.add ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hdt))
    intro t ht
    rw [uIcc_of_le hab] at ht
    convert (hasDerivAt_id t).mul (hf t ht) using 1
    · rfl
    · simp only [id_eq, one_mul]
      ring
  have hlinear : C * (∫ t in a..b, f t) =
      f b * (C * b) - f a * (C * a) -
        ∫ t in Set.Ioc a b, d t * (C * t) := by
    rw [intervalIntegral.integral_add hfi
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hdt)] at hFTC
    have he : (∫ t in Set.Ioc a b, d t * (C * t)) =
        C * (∫ t in a..b, d t * t) := by
      rw [intervalIntegral.integral_of_le hab, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by ring)
    rw [he]
    have hcFTC := congrArg (fun r : ℝ => C * r) hFTC
    nlinarith only [hcFTC]
  have hAbel := sum_mul_eq_sub_sub_integral_mul
    (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) ha hab
      (fun t ht => (hf t ht).differentiableAt)
      (hdi.congr_fun (fun t ht => (hf t ht).deriv.symm) measurableSet_Icc)
  simp_rw [prime_cdf] at hAbel
  have hsum :
      (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f p * (if p.Prime then 1 else 0)) =
        ∑ p ∈ primeInterval a b, f p := by
    simp [primeInterval, sum_filter, mul_ite]
  rw [hsum] at hAbel
  have hid :
      (∑ p ∈ primeInterval a b, f p) - C * (∫ t in a..b, f t) =
        f b * (primeCount b - C * b) - f a * (primeCount a - C * a) -
          ∫ t in Set.Ioc a b, d t * (primeCount t - C * t) := by
    rw [hAbel, hlinear]
    have hdreplace : (fun t => deriv f t * primeCount t) =ᵐ[volume.restrict (Set.Ioc a b)]
        (fun t => d t * primeCount t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [(hf t ⟨ht.1.le, ht.2⟩).deriv]
    have hci : IntegrableOn (fun t => d t * (C * t)) (Set.Ioc a b) := by
      have h : IntegrableOn (fun t => C * (d t * t)) (Set.Icc a b) := hdt.const_mul C
      convert h.mono_set Set.Ioc_subset_Icc_self using 1
      ext t
      ring
    have hsplit : (∫ t in Set.Ioc a b, d t * (primeCount t - C * t)) =
        (∫ t in Set.Ioc a b, d t * primeCount t) -
          ∫ t in Set.Ioc a b, d t * (C * t) := by
      rw [← integral_sub (hdc.mono_set Set.Ioc_subset_Icc_self) hci]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by ring)
    rw [integral_congr_ae hdreplace, hsplit]
    ring
  have hb : |f b * (primeCount b - C * b)| ≤ |f b| * E := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcount b ⟨hab, le_rfl⟩) (abs_nonneg _)
  have ha' : |f a * (primeCount a - C * a)| ≤ |f a| * E := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcount a ⟨le_rfl, hab⟩) (abs_nonneg _)
  have habound :
      (∑ p ∈ primeInterval a b, f p) - C * (∫ t in a..b, f t) ≤
        E * (|f a| + |f b| + ∫ t in a..b, |d t|) := by
    rw [hid]
    calc
      _ ≤ |f b * (primeCount b - C * b)| + |f a * (primeCount a - C * a)| +
          |∫ t in Set.Ioc a b, d t * (primeCount t - C * t)| := by
        linarith [le_abs_self (f b * (primeCount b - C * b)),
          neg_le_abs (f a * (primeCount a - C * a)),
          neg_le_abs (∫ t in Set.Ioc a b, d t * (primeCount t - C * t))]
      _ ≤ |f b| * E + |f a| * E + E * (∫ t in a..b, |d t|) := by
        gcongr
      _ = _ := by ring
  linarith only [habound]

private lemma prime_quadrature_increasing {a b C E : ℝ} {f d : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E)
    (hd : ContinuousOn d (Set.Icc a b))
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t)
    (hcount : ∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E)
    (hdpos : ∀ t ∈ Set.Icc a b, 0 ≤ d t)
    (hfa : 0 ≤ f a) (hfb : 0 ≤ f b) :
    (∑ p ∈ primeInterval a b, f p) ≤ C * (∫ t in a..b, f t) + 2 * E * f b := by
  have hi : IntervalIntegrable d volume a b := hd.intervalIntegrable_of_Icc hab
  have hFTC : (∫ t in a..b, |d t|) = f b - f a := by
    calc
      _ = ∫ t in a..b, d t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact abs_of_nonneg (hdpos t ht)
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hf t (by rwa [uIcc_of_le hab] at ht)) hi
  have h := prime_quadrature_upper ha hab hE hd hf hcount
  rw [abs_of_nonneg hfa, abs_of_nonneg hfb, hFTC] at h
  convert h using 1 <;> ring

private lemma prime_quadrature_decreasing {a b C E : ℝ} {f d : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E)
    (hd : ContinuousOn d (Set.Icc a b))
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t)
    (hcount : ∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E)
    (hdneg : ∀ t ∈ Set.Icc a b, d t ≤ 0)
    (hfa : 0 ≤ f a) (hfb : 0 ≤ f b) :
    (∑ p ∈ primeInterval a b, f p) ≤ C * (∫ t in a..b, f t) + 2 * E * f a := by
  have hi : IntervalIntegrable d volume a b := hd.intervalIntegrable_of_Icc hab
  have hFTC : (∫ t in a..b, |d t|) = f a - f b := by
    calc
      _ = ∫ t in a..b, -d t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact abs_of_nonpos (hdneg t ht)
      _ = _ := by
        rw [intervalIntegral.integral_neg,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t ht => hf t (by rwa [uIcc_of_le hab] at ht)) hi]
        ring
  have h := prime_quadrature_upper ha hab hE hd hf hcount
  rw [abs_of_nonneg hfa, abs_of_nonneg hfb, hFTC] at h
  convert h using 1 <;> ring

/-- The central weight quadrature error is uniform in the moving sharpness
parameter. In particular the error does not acquire a factor s. -/
theorem central_prime_weight_upper :
    ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, 0 ≤ s →
      (∑ p ∈ primeInterval (P / 2) (2 * P), MovingWeight.weight P s p) ≤
        (∫ t in (P / 2)..(2 * P), MovingWeight.weight P s t) / log P +
          112 * log 2 * (P / log P ^ 2) := by
  filter_upwards [PrimeExpansion.central_prime_counting_bound,
    eventually_gt_atTop (1 : ℝ)] with P hcount hP
  intro s hs
  have hP0 : 0 < P := by linarith
  have hhalf : 0 < P / 2 := by positivity
  have hleft : P / 2 ≤ P := by linarith
  have hright : P ≤ 2 * P := by linarith
  let E : ℝ := 28 * (P / log P ^ 2)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let z : ℝ := P ^ s
  have hz : 0 < z := rpow_pos_of_pos hP0 s
  let d : ℝ → ℝ := fun t => s / t - OmegaTailUpper.abelKernel s z t
  have hdc : ContinuousOn d (Set.Icc (P / 2) P) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.div continuousOn_id
        (fun t ht => (hhalf.trans_le ht.1).ne')
    · exact OmegaTailUpper.abelKernel_continuousOn hz hhalf
  have hfc : ContinuousOn (MovingWeight.leftWeight P s) (Set.Icc (P / 2) P) :=
    fun t ht => (MovingWeight.leftWeight_deriv hP0
      (hhalf.trans_le ht.1)).continuousAt.continuousWithinAt
  have hrightc : ContinuousOn (OmegaTailUpper.logWeight s z) (Set.Icc P (2 * P)) :=
    fun t ht => (OmegaTailUpper.logWeight_deriv hz
      (hP0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hfnonneg (t : ℝ) (ht : t ∈ Set.Icc (P / 2) P) :
      0 ≤ MovingWeight.leftWeight P s t := by
    rw [MovingWeight.leftWeight_eq_weight hP0 (hhalf.trans_le ht.1) hs ht.2]
    exact MovingWeight.weight_nonneg _ _ _
  have hgnonneg (t : ℝ) (ht : t ∈ Set.Icc P (2 * P)) :
      0 ≤ OmegaTailUpper.logWeight s z t := by
    rw [show z = P ^ s by rfl,
      MovingWeight.rightWeight_eq_weight hP0 (hP0.trans_le ht.1) hs ht.1]
    exact MovingWeight.weight_nonneg _ _ _
  have hL := prime_quadrature_increasing (C := 1 / log P) hhalf.le hleft hE hdc
    (fun t ht => MovingWeight.leftWeight_deriv hP0 (hhalf.trans_le ht.1))
    (fun t ht => by
      simpa only [one_div_mul_eq_div, E] using hcount t ⟨ht.1, ht.2.trans hright⟩)
    (fun t ht => MovingWeight.leftWeight_deriv_nonneg hP0 (hhalf.trans_le ht.1) hs)
    (hfnonneg _ ⟨le_rfl, hleft⟩) (hfnonneg _ ⟨hleft, le_rfl⟩)
  have hR := prime_quadrature_decreasing (C := 1 / log P) hP0.le hright hE
    (OmegaTailUpper.abelKernel_continuousOn hz hP0).neg
    (fun t ht => OmegaTailUpper.logWeight_deriv hz (hP0.trans_le ht.1))
    (fun t ht => by
      simpa only [one_div_mul_eq_div, E] using hcount t ⟨hleft.trans ht.1, ht.2⟩)
    (fun t ht => neg_nonpos.mpr (by
      have ht0 : 0 < t := hP0.trans_le ht.1
      have htp : 0 < t ^ s := rpow_pos_of_pos ht0 s
      dsimp only [OmegaTailUpper.abelKernel]
      positivity))
    (hgnonneg _ ⟨le_rfl, hright⟩) (hgnonneg _ ⟨hright, le_rfl⟩)
  rw [MovingWeight.leftWeight_at_cutoff hP0] at hL
  rw [show z = P ^ s by rfl, MovingWeight.rightWeight_at_cutoff hP0] at hR
  have hsumL : (∑ p ∈ primeInterval (P / 2) P, MovingWeight.leftWeight P s p) =
      ∑ p ∈ primeInterval (P / 2) P, MovingWeight.weight P s p := by
    apply sum_congr rfl
    intro p hp
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hpp := (Finset.mem_filter.mp hp).2
    exact MovingWeight.leftWeight_eq_weight hP0
      (by exact_mod_cast hpp.pos) hs
      ((Nat.le_floor_iff hP0.le).mp hi.2)
  have hsumR : (∑ p ∈ primeInterval P (2 * P), OmegaTailUpper.logWeight s z p) =
      ∑ p ∈ primeInterval P (2 * P), MovingWeight.weight P s p := by
    apply sum_congr rfl
    intro p hp
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hpp := (Finset.mem_filter.mp hp).2
    exact MovingWeight.rightWeight_eq_weight hP0
      (by exact_mod_cast hpp.pos) hs
      ((Nat.floor_lt hP0.le).mp hi.1).le
  have hIL : (∫ t in (P / 2)..P, MovingWeight.leftWeight P s t) =
      ∫ t in (P / 2)..P, MovingWeight.weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hleft] at ht
    exact MovingWeight.leftWeight_eq_weight hP0 (hhalf.trans_le ht.1) hs ht.2
  have hIR : (∫ t in P..(2 * P), OmegaTailUpper.logWeight s z t) =
      ∫ t in P..(2 * P), MovingWeight.weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hright] at ht
    exact MovingWeight.rightWeight_eq_weight hP0 (hP0.trans_le ht.1) hs ht.1
  rw [hsumL, hIL] at hL
  rw [hsumR, hIR] at hR
  have hsum :
      (∑ p ∈ primeInterval (P / 2) P, MovingWeight.weight P s p) +
        (∑ p ∈ primeInterval P (2 * P), MovingWeight.weight P s p) =
          ∑ p ∈ primeInterval (P / 2) (2 * P), MovingWeight.weight P s p := by
    simp only [primeInterval, sum_filter]
    exact Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor hleft) (Nat.floor_le_floor hright)
  have hInt := intervalIntegral.integral_add_adjacent_intervals
    ((MovingWeight.weight_continuousOn (s := s) hP0 hhalf).intervalIntegrable_of_Icc
      (μ := volume) hleft)
    ((MovingWeight.weight_continuousOn (s := s) hP0 hP0).intervalIntegrable_of_Icc
      (μ := volume) hright)
  have h := add_le_add hL hR
  rw [hsum] at h
  have heq :
      (1 / log P) * (∫ t in (P / 2)..P, MovingWeight.weight P s t) +
          2 * E * log 2 +
        ((1 / log P) * (∫ t in P..(2 * P), MovingWeight.weight P s t) +
          2 * E * log 2) =
      (∫ t in (P / 2)..(2 * P), MovingWeight.weight P s t) / log P +
        112 * log 2 * (P / log P ^ 2) := by
    rw [← hInt]
    dsimp only [E]
    ring
  exact h.trans_eq heq

end D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight
