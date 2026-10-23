/- GID: D5/S3/Arith/Robin/FinitePulseKernelTransport
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/FinitePulseKernelTransport
   mirror-E: none(waiver:analytic-identity)
   anchors: []
   utility: none
   digest: Closed pulses preserve initial atoms and signed compact-kernel transport. -/

import D5.S3.Arith.Robin.DelayedAtomTransport

noncomputable section

namespace D5.S3.Arith.Robin.FinitePulseKernelTransport

open Set MeasureTheory
open D5.S3.Arith.Robin.DelayedAtomTransport

private theorem cutoff_integrable {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {t B : ℝ} (ht : 1 < t) (htB : t ≤ B) (z : ℝ) :
    IntervalIntegrable ((Iic z).indicator weight) volume t B := by
  have hc := K.continuous_weight.mono (show Icc t B ⊆ Ioi 1 from fun x hx => ht.trans_le hx.1)
  rw [intervalIntegrable_iff]
  exact (hc.intervalIntegrable_of_Icc htB).def'.indicator measurableSet_Iic

private theorem cutoff_zero {weight : ℝ → ℝ} {t B z : ℝ} (htB : t ≤ B) (hzt : z ≤ t) :
    (∫ x in t..B, (Iic z).indicator weight x) = 0 := by
  apply intervalIntegral.integral_zero_ae
  exact Filter.Eventually.of_forall (fun x hx => by
    rw [uIoc_of_le htB] at hx
    exact indicator_of_notMem (show x ∉ Iic z from not_le.mpr (hzt.trans_lt hx.1)) weight)

private theorem cutoff_full {weight : ℝ → ℝ} {t B z : ℝ} (htB : t ≤ B) (hBz : B ≤ z) :
    (∫ x in t..B, (Iic z).indicator weight x) = ∫ x in t..B, weight x := by
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  rw [uIoo_of_le htB] at hx
  exact indicator_of_mem (show x ∈ Iic z from hx.2.le.trans hBz) weight

private theorem reference_representation {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {t B D z : ℝ} (ht : 1 < t) (htB : t ≤ B) :
    referenceKernel price t B D z =
      (if t < z then (price t-price B)/D else 0) -
        (∫ x in t..B, (Iic z).indicator weight x)/D := by
  by_cases htz : t < z
  · by_cases hzB : z ≤ B
    · have hi := intervalIntegral.integral_indicator (μ := volume) (f := weight) ⟨htz.le, hzB⟩
      have he : {x : ℝ | x ≤ z} = Iic z := rfl
      rw [he] at hi
      rw [referenceKernel, if_pos ⟨htz, hzB⟩, if_pos htz, hi,
        ← curve_difference K ht htz.le]
      ring
    · rw [referenceKernel, if_neg (by simp [hzB]), if_pos htz,
        cutoff_full htB (le_of_not_ge hzB), ← curve_difference K ht htB]
      ring
  · rw [referenceKernel, if_neg (by simp [htz]), if_neg htz,
      cutoff_zero htB (le_of_not_gt htz)]
    simp

private theorem actual_representation {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {t B D z : ℝ} (ht : 1 < t) (htB : t ≤ B) :
    actualKernel price t B D z =
      (if t ≤ z then (price t-price B)/D else 0) -
        (∫ x in t..B, (Iic z).indicator weight x)/D := by
  by_cases he : z = t
  · subst z
    rw [actualKernel, if_pos ⟨le_rfl, htB⟩, if_pos le_rfl, cutoff_zero htB le_rfl]
    simp
  · have hsame : actualKernel price t B D z = referenceKernel price t B D z := by
      simp only [actualKernel, referenceKernel]
      have hp : (t ≤ z ∧ z ≤ B) ↔ (t < z ∧ z ≤ B) := by
        constructor
        · intro hx
          exact ⟨lt_of_le_of_ne hx.1 (Ne.symm he), hx.2⟩
        · intro hx
          exact ⟨hx.1.le, hx.2⟩
      simp only [hp]
    rw [hsame, reference_representation K ht htB]
    have hp : (t < z) ↔ (t ≤ z) := ⟨le_of_lt, fun hz => lt_of_le_of_ne hz (Ne.symm he)⟩
    simp only [hp]

/-- A single atom identity holds before closed exclusion, including the actual
initial atom weight and atoms crossing the terminal endpoint. -/
theorem kernel_atom_accounting {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    {a y t B D : ℝ} (hay : a < y) (ht : 1 < t) (htB : t ≤ B) :
    actualKernel price t B D y-referenceKernel price t B D a =
      (if a ≤ t ∧ t ≤ y then (price t-price B)/D else 0) -
        (∫ x in t..B, (Icc a y).indicator weight x)/D := by
  have hpoint : (fun x => (Iic y).indicator weight x-(Iic a).indicator weight x)
      =ᵐ[volume] (Icc a y).indicator weight := by
    filter_upwards [volume.ae_ne a] with x hxa
    have hxa' : x ≠ a := hxa
    by_cases hax : a ≤ x
    · have hna : ¬x ≤ a := by intro hx; exact hxa' (le_antisymm hx hax)
      by_cases hxy : x ≤ y <;> simp [hax, hna, hxy]
    · have hxa : x ≤ a := (not_le.mp hax).le
      have hxy : x ≤ y := hxa.trans hay.le
      simp [hax, hxa, hxy]
  have hi : (∫ x in t..B, (Iic y).indicator weight x) -
      (∫ x in t..B, (Iic a).indicator weight x) =
      ∫ x in t..B, (Icc a y).indicator weight x := by
    rw [← intervalIntegral.integral_sub (cutoff_integrable K ht htB y)
      (cutoff_integrable K ht htB a)]
    exact intervalIntegral.integral_congr_ae (hpoint.mono (fun _ hx _ => hx))
  rw [actual_representation K ht htB, reference_representation K ht htB]
  have he : (if t ≤ y then (price t-price B)/D else 0) -
      (if t < a then (price t-price B)/D else 0) =
      (if a ≤ t ∧ t ≤ y then (price t-price B)/D else 0) := by
    split_ifs <;> simp_all <;> linarith
  calc
    _ = ((if t ≤ y then (price t-price B)/D else 0) -
        (if t < a then (price t-price B)/D else 0)) -
        ((∫ x in t..B, (Iic y).indicator weight x) -
          (∫ x in t..B, (Iic a).indicator weight x))/D := by ring
    _ = _ := by rw [he, hi]

/-- Finite summation preserves the exact closed-pulse initial correction. -/
theorem finite_pulse_accounting {ι : Type*} (I : Finset ι)
    {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    (a y h : ι → ℝ) (hay : ∀ i ∈ I, a i < y i)
    {t B D : ℝ} (ht : 1 < t) (htB : t ≤ B) :
    (∑ i ∈ I, h i*(actualKernel price t B D (y i)-referenceKernel price t B D (a i))) =
      (∑ i ∈ I, (Icc (a i) (y i)).indicator (fun _ => h i) t)*(price t-price B)/D -
        (∫ x in t..B, (∑ i ∈ I, (Icc (a i) (y i)).indicator (fun _ => h i) x)*weight x)/D := by
  classical
  have hw : IntervalIntegrable weight volume t B :=
    (K.continuous_weight.mono (fun x (hx : x ∈ Icc t B) => ht.trans_le hx.1))
      |>.intervalIntegrable_of_Icc htB
  have hin (i : ι) :
      IntervalIntegrable (fun x => (Icc (a i) (y i)).indicator weight x) volume t B := by
    rw [intervalIntegrable_iff]
    exact hw.def'.indicator measurableSet_Icc
  have he (i : ι) : (fun x => (Icc (a i) (y i)).indicator (fun _ => h i) x*weight x) =
      (fun x => h i*(Icc (a i) (y i)).indicator weight x) := by
    funext x
    by_cases hx : x ∈ Icc (a i) (y i) <;> simp [hx]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun i _ => by rw [he]; exact (hin i).const_mul _)]
  simp_rw [Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [kernel_atom_accounting K (hay i hi) ht htB, he,
    intervalIntegral.integral_const_mul]
  by_cases hx : t ∈ Icc (a i) (y i)
  · simp only [indicator_of_mem hx, if_pos (show a i ≤ t ∧ t ≤ y i from hx)]
    ring
  · simp only [indicator_of_notMem hx, if_neg (show ¬(a i ≤ t ∧ t ≤ y i) from hx),
      zero_mul, zero_div]
    ring

/-- After exclusion, the finite signed response lies between the negative local
envelope and zero. There is no global monotonicity assumption on the integrated kernel. -/
theorem finite_pulse_bounds {ι : Type*} (I : Finset ι)
    {price weight : ℝ → ℝ} (K : PriceCurve price weight)
    (a y h : ι → ℝ) (hay : ∀ i ∈ I, a i < y i) (hh : ∀ i ∈ I, 0 ≤ h i)
    {t B D L : ℝ} (ht : 1 < t) (htB : t ≤ B) (hD : 0 < D)
    (hexcluded : ∀ i ∈ I, t ∉ Icc (a i) (y i))
    (henvelope : ∀ x ∈ Icc t B,
      (∑ i ∈ I, (Icc (a i) (y i)).indicator (fun _ => h i) x) ≤ L) :
    -(price t-price B)/D*L ≤
      (∑ i ∈ I, h i*(actualKernel price t B D (y i)-referenceKernel price t B D (a i))) ∧
      (∑ i ∈ I, h i*(actualKernel price t B D (y i)-referenceKernel price t B D (a i))) ≤ 0 := by
  classical
  let delta := fun x => ∑ i ∈ I, (Icc (a i) (y i)).indicator (fun _ => h i) x
  have hd0 (x : ℝ) : 0 ≤ delta x := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hx : x ∈ Icc (a i) (y i) <;> simp [hx, hh i hi]
  have hdt : delta t = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hexcluded i hi]
  have hw : IntervalIntegrable weight volume t B :=
    (K.continuous_weight.mono (fun x (hx : x ∈ Icc t B) => ht.trans_le hx.1))
      |>.intervalIntegrable_of_Icc htB
  have hi : IntervalIntegrable (fun x => delta x*weight x) volume t B := by
    simp only [delta, Finset.sum_mul]
    apply (intervalIntegrable_iff).mpr
    apply integrable_finsetSum I
    intro i hi
    have he : (fun x => (Icc (a i) (y i)).indicator (fun _ => h i) x*weight x) =
        (fun x => h i*(Icc (a i) (y i)).indicator weight x) := by
      funext x
      by_cases hx : x ∈ Icc (a i) (y i) <;> simp [hx]
    rw [he]
    exact (hw.def'.indicator measurableSet_Icc).const_mul _
  have hlow := intervalIntegral.integral_nonneg (μ := volume) htB (fun x hx =>
    mul_nonneg (hd0 x) (K.positive_weight x (ht.trans_le hx.1)).le)
  have hu := intervalIntegral.integral_mono_on htB hi (hw.const_mul L) (fun x hx =>
    mul_le_mul_of_nonneg_right (henvelope x hx) (K.positive_weight x (ht.trans_le hx.1)).le)
  rw [intervalIntegral.integral_const_mul, ← curve_difference K ht htB] at hu
  have he := finite_pulse_accounting I K a y h hay (D := D) ht htB
  change _ = delta t*(price t-price B)/D-(∫ x in t..B, delta x*weight x)/D at he
  rw [hdt, zero_mul, zero_div, zero_sub] at he
  rw [he]
  constructor
  · have hm := (div_le_div_iff_of_pos_right hD).mpr hu
    have hnorm : L*(price t-price B)/D = (price t-price B)/D*L := by ring
    rw [hnorm] at hm
    simpa only [neg_div, neg_mul] using neg_le_neg hm
  · exact neg_nonpos.mpr (div_nonneg hlow hD.le)

#print axioms kernel_atom_accounting
#print axioms finite_pulse_accounting
#print axioms finite_pulse_bounds

end D5.S3.Arith.Robin.FinitePulseKernelTransport
