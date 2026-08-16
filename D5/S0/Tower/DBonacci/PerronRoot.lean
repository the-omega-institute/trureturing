/- GID: D5/S0/Tower/DBonacci/PerronRoot
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/PerronRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The d-bonacci Perron root is unique, strictly increasing in d, and tends to two. -/

import D5.S0.Tower.Tribonacci.PerronRoot
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.SuccPred.Archimedean

namespace D5.S0.Tower.DBonacci.PerronRoot

open Filter

/-- The reciprocal form of the d-bonacci characteristic equation. -/
noncomputable def dbonacciReciprocalSum (d : Nat) (x : Real) : Real :=
  ∑ i ∈ Finset.range d, x⁻¹ ^ (i + 1)

theorem dbonacci_reciprocalSum_continuousOn (d : Nat) :
    ContinuousOn (dbonacciReciprocalSum d) (Set.Icc (1 : Real) 2) := by
  unfold dbonacciReciprocalSum
  apply continuousOn_finsetSum
  intro i _
  exact (continuousOn_id.inv₀ fun x hx => by
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    simpa only [id_eq] using hxpos.ne').pow (i + 1)

/-- For positive order, the reciprocal sum is strictly decreasing on the positive reals. -/
theorem dbonacci_reciprocalSum_strictAntiOn (d : Nat) (hd : 0 < d) :
    StrictAntiOn (dbonacciReciprocalSum d) (Set.Ioi (0 : Real)) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  have hypos : 0 < y := Set.mem_Ioi.mp hy
  have hinv : y⁻¹ < x⁻¹ := (inv_lt_inv₀ hypos hxpos).2 hxy
  unfold dbonacciReciprocalSum
  apply Finset.sum_lt_sum
  · intro i _
    exact (pow_lt_pow_left₀ hinv (inv_nonneg.mpr hypos.le)
      (Nat.succ_ne_zero i)).le
  · refine ⟨0, by simpa using hd, ?_⟩
    simpa using pow_lt_pow_left₀ hinv (inv_nonneg.mpr hypos.le)
      (Nat.succ_ne_zero 0)

theorem dbonacci_reciprocalSum_one (d : Nat) :
    dbonacciReciprocalSum d 1 = d := by
  simp [dbonacciReciprocalSum]

theorem dbonacci_reciprocalSum_two_lt_one (d : Nat) :
    dbonacciReciprocalSum d 2 < 1 := by
  have hgeom :
      (∑ i ∈ Finset.range d, ((2 : Real)⁻¹) ^ i) < 2 := by
    have hpowpos : 0 < ((2 : Real)⁻¹) ^ d := by positivity
    rw [geom_sum_eq (x := (2 : Real)⁻¹) (by norm_num)]
    norm_num
    nlinarith
  calc
    dbonacciReciprocalSum d 2 =
        (∑ i ∈ Finset.range d, ((2 : Real)⁻¹) ^ i) * (2 : Real)⁻¹ := by
      simp only [dbonacciReciprocalSum, pow_succ]
      rw [Finset.sum_mul]
    _ < 2 * (2 : Real)⁻¹ :=
      mul_lt_mul_of_pos_right hgeom (by norm_num)
    _ = 1 := by norm_num

/-- Multiplying the reciprocal equation by `x^d` recovers the characteristic sum. -/
theorem pow_mul_dbonacciReciprocalSum (d : Nat) {x : Real} (hx : x ≠ 0) :
    x ^ d * dbonacciReciprocalSum d x =
      ∑ i ∈ Finset.range d, x ^ i := by
  rw [dbonacciReciprocalSum, Finset.mul_sum]
  calc
    (∑ i ∈ Finset.range d, x ^ d * x⁻¹ ^ (i + 1)) =
        ∑ i ∈ Finset.range d, x ^ (d - 1 - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hle : i + 1 ≤ d := by
        simpa using Finset.mem_range.mp hi
      rw [inv_pow, ← pow_sub₀ x hx hle]
      congr 1
      omega
    _ = ∑ i ∈ Finset.range d, x ^ i :=
      Finset.sum_range_reflect (fun i => x ^ i) d

theorem dbonacci_characteristic_iff_reciprocalSum (d : Nat) {x : Real}
    (hx : x ≠ 0) :
    x ^ d = (∑ i ∈ Finset.range d, x ^ i) ↔
      dbonacciReciprocalSum d x = 1 := by
  have hid := pow_mul_dbonacciReciprocalSum d hx
  constructor
  · intro hcharacteristic
    apply mul_left_cancel₀ (pow_ne_zero d hx)
    calc
      x ^ d * dbonacciReciprocalSum d x =
          ∑ i ∈ Finset.range d, x ^ i := hid
      _ = x ^ d := hcharacteristic.symm
      _ = x ^ d * 1 := (mul_one _).symm
  · intro hreciprocal
    calc
      x ^ d = x ^ d * 1 := (mul_one _).symm
      _ = x ^ d * dbonacciReciprocalSum d x := by rw [hreciprocal]
      _ = ∑ i ∈ Finset.range d, x ^ i := hid

/-- For every order at least two, the d-bonacci characteristic equation has one root in `(1,2)`. -/
theorem exists_unique_dbonacci_root (d : Nat) (hd : 2 ≤ d) :
    ∃! x : Real,
      1 < x ∧ x < 2 ∧ x ^ d = ∑ i ∈ Finset.range d, x ^ i := by
  have hone : 1 < dbonacciReciprocalSum d 1 := by
    rw [dbonacci_reciprocalSum_one]
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hd)
  have htwo : dbonacciReciprocalSum d 2 < 1 :=
    dbonacci_reciprocalSum_two_lt_one d
  have himage := intermediate_value_Icc' (show (1 : Real) ≤ 2 by norm_num)
    (dbonacci_reciprocalSum_continuousOn d)
    (show (1 : Real) ∈ Set.Icc (dbonacciReciprocalSum d 2)
      (dbonacciReciprocalSum d 1) from ⟨htwo.le, hone.le⟩)
  obtain ⟨x, hx, hroot⟩ := himage
  have hxone : 1 < x := lt_of_le_of_ne hx.1 (by
    intro heq
    rw [← heq] at hroot
    linarith)
  have hxtwo : x < 2 := lt_of_le_of_ne hx.2 (by
    intro heq
    rw [heq] at hroot
    linarith)
  have hcharacteristic : x ^ d = ∑ i ∈ Finset.range d, x ^ i :=
    (dbonacci_characteristic_iff_reciprocalSum d
      (ne_of_gt (lt_trans zero_lt_one hxone))).2 hroot
  refine ⟨x, ⟨hxone, hxtwo, hcharacteristic⟩, ?_⟩
  intro y hy
  have hyroot : dbonacciReciprocalSum d y = 1 :=
    (dbonacci_characteristic_iff_reciprocalSum d
      (ne_of_gt (lt_trans zero_lt_one hy.1))).1 hy.2.2
  have hanti := dbonacci_reciprocalSum_strictAntiOn d (by omega)
  rcases lt_trichotomy y x with hyx | heq | hxy
  · have hlt := hanti
        (show y ∈ Set.Ioi (0 : Real) from lt_trans zero_lt_one hy.1)
        (show x ∈ Set.Ioi (0 : Real) from lt_trans zero_lt_one hxone) hyx
    rw [hroot, hyroot] at hlt
    exact False.elim (lt_irrefl 1 hlt)
  · exact heq
  · have hlt := hanti
        (show x ∈ Set.Ioi (0 : Real) from lt_trans zero_lt_one hxone)
        (show y ∈ Set.Ioi (0 : Real) from lt_trans zero_lt_one hy.1) hxy
    rw [hroot, hyroot] at hlt
    exact False.elim (lt_irrefl 1 hlt)

/-- The total root function; orders below two use `1`, outside the Perron-root domain. -/
noncomputable def dbonacciPerronRoot (d : Nat) : Real :=
  if hd : 2 ≤ d then Classical.choose (exists_unique_dbonacci_root d hd) else 1

theorem dbonacciPerronRoot_spec (d : Nat) (hd : 2 ≤ d) :
    1 < dbonacciPerronRoot d ∧ dbonacciPerronRoot d < 2 ∧
      dbonacciPerronRoot d ^ d =
        ∑ i ∈ Finset.range d, dbonacciPerronRoot d ^ i := by
  rw [dbonacciPerronRoot, dif_pos hd]
  exact (Classical.choose_spec (exists_unique_dbonacci_root d hd)).1

theorem one_lt_dbonacciPerronRoot (d : Nat) (hd : 2 ≤ d) :
    1 < dbonacciPerronRoot d :=
  (dbonacciPerronRoot_spec d hd).1

theorem dbonacciPerronRoot_lt_two (d : Nat) (hd : 2 ≤ d) :
    dbonacciPerronRoot d < 2 :=
  (dbonacciPerronRoot_spec d hd).2.1

/-- The chosen Perron root satisfies the d-bonacci characteristic equation. -/
theorem dbonacciPerronRoot_characteristic (d : Nat) (hd : 2 ≤ d) :
    dbonacciPerronRoot d ^ d =
      ∑ i ∈ Finset.range d, dbonacciPerronRoot d ^ i :=
  (dbonacciPerronRoot_spec d hd).2.2

/-- Exact interval-and-equation characterization of the chosen root. -/
theorem eq_dbonacciPerronRoot_iff (d : Nat) (hd : 2 ≤ d) {x : Real} :
    x = dbonacciPerronRoot d ↔
      1 < x ∧ x < 2 ∧ x ^ d = ∑ i ∈ Finset.range d, x ^ i := by
  constructor
  · rintro rfl
    exact dbonacciPerronRoot_spec d hd
  · intro hx
    rw [dbonacciPerronRoot, dif_pos hd]
    exact (Classical.choose_spec (exists_unique_dbonacci_root d hd)).2 x hx

/-- Away from the trivial root `1`, the characteristic equation has its two-term form. -/
theorem dbonacci_characteristic_iff_nontrivial_equation (d : Nat) {x : Real}
    (hx : x ≠ 1) :
    x ^ d = (∑ i ∈ Finset.range d, x ^ i) ↔
      x ^ (d + 1) = 2 * x ^ d - 1 := by
  have hgeom := geom_sum_mul x d
  constructor
  · intro hcharacteristic
    rw [← hcharacteristic] at hgeom
    rw [pow_succ]
    nlinarith
  · intro hnontrivial
    apply mul_right_cancel₀ (sub_ne_zero.mpr hx)
    rw [geom_sum_mul]
    rw [pow_succ] at hnontrivial
    nlinarith

theorem dbonacciPerronRoot_nontrivial_equation (d : Nat) (hd : 2 ≤ d) :
    dbonacciPerronRoot d ^ (d + 1) =
      2 * dbonacciPerronRoot d ^ d - 1 :=
  (dbonacci_characteristic_iff_nontrivial_equation d
    (ne_of_gt (one_lt_dbonacciPerronRoot d hd))).1
      (dbonacciPerronRoot_characteristic d hd)

theorem dbonacciPerronRoot_reciprocalSum (d : Nat) (hd : 2 ≤ d) :
    dbonacciReciprocalSum d (dbonacciPerronRoot d) = 1 :=
  (dbonacci_characteristic_iff_reciprocalSum d
    (ne_of_gt (lt_trans (by norm_num) (one_lt_dbonacciPerronRoot d hd)))).1
      (dbonacciPerronRoot_characteristic d hd)

/-- The distance from the upper endpoint is exactly the d-th reciprocal power. -/
theorem two_sub_dbonacciPerronRoot_eq_inv_pow (d : Nat) (hd : 2 ≤ d) :
    2 - dbonacciPerronRoot d = (dbonacciPerronRoot d)⁻¹ ^ d := by
  have hpos : 0 < dbonacciPerronRoot d :=
    lt_trans (by norm_num) (one_lt_dbonacciPerronRoot d hd)
  have hne : dbonacciPerronRoot d ≠ 0 := ne_of_gt hpos
  have hnontrivial := dbonacciPerronRoot_nontrivial_equation d hd
  rw [pow_succ] at hnontrivial
  have hproduct :
      dbonacciPerronRoot d ^ d * (2 - dbonacciPerronRoot d) = 1 := by
    nlinarith
  apply mul_left_cancel₀ (pow_ne_zero d hne)
  calc
    dbonacciPerronRoot d ^ d * (2 - dbonacciPerronRoot d) = 1 := hproduct
    _ = dbonacciPerronRoot d ^ d * (dbonacciPerronRoot d)⁻¹ ^ d := by
      rw [← mul_pow]
      simp [hne]

/-- Increasing the recurrence order strictly increases its Perron root. -/
theorem dbonacciPerronRoot_lt_succ (d : Nat) (hd : 2 ≤ d) :
    dbonacciPerronRoot d < dbonacciPerronRoot (d + 1) := by
  have hcurrent := dbonacciPerronRoot_reciprocalSum d hd
  have hnext := dbonacciPerronRoot_reciprocalSum (d + 1) (by omega)
  have hsum_greater :
      1 < dbonacciReciprocalSum (d + 1) (dbonacciPerronRoot d) := by
    have hpos : 0 < (dbonacciPerronRoot d)⁻¹ ^ (d + 1) := by
      exact pow_pos (inv_pos.mpr
        (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot d hd))) _
    calc
      1 = dbonacciReciprocalSum d (dbonacciPerronRoot d) := hcurrent.symm
      _ < dbonacciReciprocalSum d (dbonacciPerronRoot d) +
          (dbonacciPerronRoot d)⁻¹ ^ (d + 1) := lt_add_of_pos_right _ hpos
      _ = dbonacciReciprocalSum (d + 1) (dbonacciPerronRoot d) := by
        rw [dbonacciReciprocalSum, dbonacciReciprocalSum,
          Finset.sum_range_succ]
  have hanti := dbonacci_reciprocalSum_strictAntiOn (d + 1) (by omega)
  by_contra hnot
  have hle : dbonacciPerronRoot (d + 1) ≤ dbonacciPerronRoot d :=
    le_of_not_gt hnot
  rcases hle.eq_or_lt with heq | hlt
  · rw [← heq, hnext] at hsum_greater
    exact (lt_irrefl 1 hsum_greater).elim
  · have hs := hanti
        (show dbonacciPerronRoot (d + 1) ∈ Set.Ioi (0 : Real) from
          lt_trans zero_lt_one (one_lt_dbonacciPerronRoot (d + 1) (by omega)))
        (show dbonacciPerronRoot d ∈ Set.Ioi (0 : Real) from
          lt_trans zero_lt_one (one_lt_dbonacciPerronRoot d hd)) hlt
    rw [hnext] at hs
    linarith

/-- On the meaningful orders `d >= 2`, the Perron root is strictly increasing. -/
theorem dbonacciPerronRoot_strictMonoOn :
    StrictMonoOn dbonacciPerronRoot (Set.Ici 2) := by
  refine strictMonoOn_of_lt_succ Set.ordConnected_Ici ?_
  intro d _ hd _
  simpa only [Order.succ_eq_add_one] using dbonacciPerronRoot_lt_succ d hd

/-- The order-two Perron root is mathlib's real golden ratio. -/
theorem dbonacciPerronRoot_two_eq_goldenRatio :
    dbonacciPerronRoot 2 = Real.goldenRatio := by
  symm
  apply (eq_dbonacciPerronRoot_iff 2 (by norm_num)
    (x := Real.goldenRatio)).mpr
  refine ⟨Real.one_lt_goldenRatio, Real.goldenRatio_lt_two, ?_⟩
  have hsq := Real.goldenRatio_sq
  norm_num [Finset.sum_range_succ]
  nlinarith

/-- The order-three Perron root is the frozen Tribonacci constant. -/
theorem dbonacciPerronRoot_three_eq_tribonacciConstant :
    dbonacciPerronRoot 3 =
      D5.S0.Tower.Tribonacci.Values.tribonacciConstant := by
  apply D5.S0.Tower.Tribonacci.PerronRoot.eq_tribonacciConstant_iff.mpr
  refine ⟨one_lt_dbonacciPerronRoot 3 (by norm_num),
    dbonacciPerronRoot_lt_two 3 (by norm_num), ?_⟩
  have hcharacteristic := dbonacciPerronRoot_characteristic 3 (by norm_num)
  norm_num [Finset.sum_range_succ] at hcharacteristic
  nlinarith

/-- The d-bonacci Perron roots converge to the upper endpoint two as `d` tends to infinity. -/
theorem dbonacciPerronRoot_tendsto_two :
    Tendsto dbonacciPerronRoot atTop (nhds 2) := by
  have hbase_nonneg : 0 ≤ Real.goldenRatio⁻¹ :=
    (inv_pos.mpr Real.goldenRatio_pos).le
  have hbase_lt_one : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hpow : Tendsto (fun d : Nat => Real.goldenRatio⁻¹ ^ d)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt_one
  have hdeficit : Tendsto (fun d : Nat => 2 - dbonacciPerronRoot d)
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun d : Nat => Real.goldenRatio⁻¹ ^ d)
    · filter_upwards [eventually_ge_atTop 2] with d hd
      exact sub_nonneg.mpr (dbonacciPerronRoot_lt_two d hd).le
    · filter_upwards [eventually_ge_atTop 2] with d hd
      have hphi_le : Real.goldenRatio ≤ dbonacciPerronRoot d := by
        rw [← dbonacciPerronRoot_two_eq_goldenRatio]
        exact dbonacciPerronRoot_strictMonoOn.monotoneOn (by simp) hd hd
      have hinv_le : (dbonacciPerronRoot d)⁻¹ ≤ Real.goldenRatio⁻¹ :=
        (inv_le_inv₀
          (lt_trans (by norm_num) (one_lt_dbonacciPerronRoot d hd))
          Real.goldenRatio_pos).2 hphi_le
      rw [two_sub_dbonacciPerronRoot_eq_inv_pow d hd]
      exact pow_le_pow_left₀ (inv_nonneg.mpr
        (lt_trans (by norm_num) (one_lt_dbonacciPerronRoot d hd)).le) hinv_le d
    · exact hpow
  have hrecover : Tendsto
      (fun d : Nat => (2 : Real) - (2 - dbonacciPerronRoot d))
      atTop (nhds ((2 : Real) - 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : Real)) atTop (nhds 2)).sub
      hdeficit
  simpa using hrecover

end D5.S0.Tower.DBonacci.PerronRoot
