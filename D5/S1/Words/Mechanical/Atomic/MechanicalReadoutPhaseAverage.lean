/- GID: D5/S1/Words/Mechanical/Atomic/MechanicalReadoutPhaseAverage
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/Atomic/MechanicalReadoutPhaseAverage
   mirror-E: none(waiver:actual-mechanical-phase-average)
   anchors: []
   utility: none
   digest: Uniform phase averaging of the numbered geometric atomic measure is Lebesgue measure. -/

import D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Interval.Set.Union

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure

open Set Finset MeasureTheory
open scoped BigOperators
open Classical
open D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries

/-- Averaging the actual numbered atomic measure over uniform phases gives
Lebesgue measure on the unit interval. The phase domain is half-open, as in
the mechanical word; adding its missing endpoint does not change the integral. -/
theorem geometric_atomic_phase_average (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (A : Set ℝ) (hA : MeasurableSet A) (hAunit : A ⊆ Set.Icc (0 : ℝ) 1) :
    ∫⁻ x in Set.Ico (0 : ℝ) 1, geometricAtomicMeasure r x A ∂volume = volume A := by
  classical
  let cell (n : ℕ) (i : Fin (n + 1)) : Set ℝ :=
    Set.Ioc ((i.val : ℝ) / ((n + 1 : ℕ) : ℝ))
      (((i.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
  have hpointMap (n : ℕ) (i : Fin (n + 1)) :
      Measure.map (fun x : ℝ => atomicPoint x ⟨n, i⟩)
          (volume.restrict (Set.Ico (0 : ℝ) 1)) =
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) • volume.restrict (cell n i) := by
    let k : ℝ := ((n + 1 : ℕ) : ℝ)
    let j : ℝ := ((i.val + 1 : ℕ) : ℝ)
    have hk : 0 < k := by dsimp [k]; positivity
    have hk0 : k ≠ 0 := ne_of_gt hk
    let T : ℝ → ℝ := fun x => (j - x) / k
    have hT : T = fun x => atomicPoint x ⟨n, i⟩ := by
      funext x
      rfl
    have hcontinuous : Continuous T := by
      dsimp [T]
      fun_prop
    have hinjective : Function.Injective T := by
      intro x y h
      dsimp [T] at h
      have heq := (div_left_inj' hk0).mp h
      linarith
    have hE : MeasurableEmbedding T := hcontinuous.measurableEmbedding hinjective
    have hfull : Measure.map T (volume : Measure ℝ) =
        ENNReal.ofReal k • volume := by
      have hcomp : T = (fun y : ℝ => k⁻¹ * y) ∘ (fun x : ℝ => j - x) := by
        funext x
        dsimp [T, Function.comp_def]
        ring
      rw [hcomp, Measure.map_map (by fun_prop) (by fun_prop)]
      rw [(volume.measurePreserving_sub_left j).map_eq]
      rw [Real.map_volume_mul_left (inv_ne_zero hk0)]
      simp [abs_of_pos hk]
    have himage : T '' Set.Ico (0 : ℝ) 1 = cell n i := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (i.val : ℝ) / k < (j - x) / k ∧
          (j - x) / k ≤ j / k
        constructor
        · apply div_lt_div_of_pos_right _ hk
          dsimp [j]
          push_cast
          linarith [hx.2]
        · exact div_le_div_of_nonneg_right (by linarith [hx.1]) hk.le
      · intro hy
        change (i.val : ℝ) / k < y ∧ y ≤ j / k at hy
        refine ⟨j - k * y, ?_, ?_⟩
        · constructor
          · have h := (div_le_iff₀ hk).1 hy.2
            nlinarith
          · have h := (div_lt_iff₀ hk).1 hy.1
            dsimp [j]
            push_cast at h
            nlinarith
        · dsimp [T]
          field_simp [hk0]
          ring
    have hpre : T ⁻¹' cell n i = Set.Ico (0 : ℝ) 1 := by
      rw [← himage]
      exact Set.preimage_image_eq _ hinjective
    calc
      Measure.map (fun x : ℝ => atomicPoint x ⟨n, i⟩)
          (volume.restrict (Set.Ico (0 : ℝ) 1)) =
          Measure.map T (volume.restrict (Set.Ico (0 : ℝ) 1)) := by rw [hT]
      _ = (Measure.map T volume).restrict (cell n i) := by
        simpa [hpre] using (hE.restrict_map volume (cell n i)).symm
      _ = ENNReal.ofReal k • volume.restrict (cell n i) := by
        rw [hfull, Measure.restrict_smul]
  have hcell (n : ℕ) (i : Fin (n + 1)) :
      ∫⁻ x in Set.Ico (0 : ℝ) 1,
          Measure.dirac (atomicPoint x ⟨n, i⟩) A ∂volume =
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) * volume (A ∩ cell n i) := by
    let T : ℝ → ℝ := fun x => atomicPoint x ⟨n, i⟩
    have hmeas : Measurable T := by
      dsimp [T, atomicPoint]
      fun_prop
    have hindicator : (fun x : ℝ => Measure.dirac (T x) A) =
        (T ⁻¹' A).indicator 1 := by
      funext x
      simp [Measure.dirac_apply' _ hA, Set.indicator]
    calc
      ∫⁻ x in Set.Ico (0 : ℝ) 1,
          Measure.dirac (atomicPoint x ⟨n, i⟩) A ∂volume =
          (Measure.map T (volume.restrict (Set.Ico (0 : ℝ) 1))) A := by
            rw [Measure.map_apply hmeas hA]
            change (∫⁻ x, Measure.dirac (T x) A
              ∂(volume.restrict (Set.Ico (0 : ℝ) 1))) = _
            rw [hindicator, lintegral_indicator_one (hA.preimage hmeas)]
      _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) * volume (A ∩ cell n i) := by
        rw [hpointMap n i, Measure.smul_apply, Measure.restrict_apply hA]
        rw [Set.inter_comm]
        rfl
  have hpartition (n : ℕ) :
      (∑ i : Fin (n + 1), volume (A ∩ cell n i)) =
        volume (A ∩ Set.Ioc (0 : ℝ) 1) := by
    let k : ℝ := ((n + 1 : ℕ) : ℝ)
    have hk : 0 < k := by dsimp [k]; positivity
    have hcover : (⋃ i : Fin (n + 1), cell n i) = Set.Ioc (0 : ℝ) 1 := by
      apply Set.Subset.antisymm
      · rintro y ⟨i, hi⟩
        change (i.val : ℝ) / k < y ∧
          y ≤ (((i.val + 1 : ℕ) : ℝ)) / k at hi
        constructor
        · have hnonneg : (0 : ℝ) ≤ (i.val : ℝ) / k := div_nonneg (by positivity) hk.le
          linarith
        · have hle : i.val + 1 ≤ n + 1 := i.isLt
          have hle' : (((i.val + 1 : ℕ) : ℝ)) / k ≤ 1 := by
            apply (div_le_iff₀ hk).2
            simpa [k] using (show (((i.val + 1 : ℕ) : ℝ)) ≤
              (((n + 1 : ℕ) : ℝ)) by exact_mod_cast hle)
          exact hi.2.trans hle'
      · intro y hy
        have hsub := Ioc_subset_biUnion_Ioc (n + 1)
          (fun m : ℕ => (m : ℝ) / k)
        have htop : (((n + 1 : ℕ) : ℝ)) / k = 1 := by
          change k / k = 1
          exact div_self (ne_of_gt hk)
        have hy' : y ∈ Set.Ioc ((0 : ℝ) / k) (((n + 1 : ℕ) : ℝ) / k) := by
          simpa [htop] using hy
        rcases Set.mem_iUnion.mp (hsub hy') with ⟨m, hm⟩
        rcases Set.mem_iUnion.mp hm with ⟨hmrange, hcellmem⟩
        exact Set.mem_iUnion.mpr
          ⟨⟨m, Finset.mem_range.mp hmrange⟩, hcellmem⟩
    have hdisjoint : Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin (n + 1))))
        (fun i => A ∩ cell n i) := by
      intro i _ j _ hij
      apply Set.disjoint_left.mpr
      intro y hyi hyj
      have hne : i.val ≠ j.val := by
        intro h
        exact hij (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hbound : (((i.val + 1 : ℕ) : ℝ)) / k ≤ (j.val : ℝ) / k := by
          apply div_le_div_of_nonneg_right _ hk.le
          exact_mod_cast (Nat.succ_le_iff.mpr hlt)
        have hi : y ≤ (((i.val + 1 : ℕ) : ℝ)) / k := hyi.2.2
        have hj : (j.val : ℝ) / k < y := hyj.2.1
        linarith
      · have hbound : (((j.val + 1 : ℕ) : ℝ)) / k ≤ (i.val : ℝ) / k := by
          apply div_le_div_of_nonneg_right _ hk.le
          exact_mod_cast (Nat.succ_le_iff.mpr hgt)
        have hj : y ≤ (((j.val + 1 : ℕ) : ℝ)) / k := hyj.2.2
        have hi : (i.val : ℝ) / k < y := hyi.2.1
        linarith
    have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        MeasurableSet (A ∩ cell n i) := by
      intro i _
      exact hA.inter measurableSet_Ioc
    have hsum := measure_biUnion_finset (μ := volume) hdisjoint hmeas
    have hunion : (⋃ i : Fin (n + 1), A ∩ cell n i) =
        A ∩ Set.Ioc (0 : ℝ) 1 := by
      rw [← Set.inter_iUnion, hcover]
    simpa [hunion] using hsum.symm
  have hdiracMeas (a : AtomicIndex) :
      Measurable (fun x : ℝ => Measure.dirac (atomicPoint x a) A) := by
    have hp : Measurable (fun x : ℝ => atomicPoint x a) := by
      dsimp [atomicPoint]
      fun_prop
    simp_rw [Measure.dirac_apply' _ hA]
    exact (measurable_const.indicator hA).comp hp
  have htermMeas (a : AtomicIndex) :
      Measurable (fun x : ℝ =>
        ENNReal.ofReal (atomicCoefficient r a) *
          Measure.dirac (atomicPoint x a) A) :=
    measurable_const.mul (hdiracMeas a)
  have hweight : Summable
      (fun n : ℕ => (1 - r) ^ 2 * r ^ n * (((n + 1 : ℕ) : ℝ))) := by
    have hrnorm : ‖r‖ < 1 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr0.le] using hr1
    have hgeom : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) * r ^ n)) := by
      simpa using (summable_choose_mul_geometric_of_norm_lt_one 1 hrnorm)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hgeom.mul_left ((1 - r) ^ 2)
  have hmass : (∑' n : ℕ, (1 - r) ^ 2 * r ^ n * (((n + 1 : ℕ) : ℝ))) = 1 :=
    (geometric_readout_floor_series_and_mass r 0 0 hr0.le hr1
      (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
      (by norm_num : (0 : ℝ) ∈ Set.Ico 0 1)).2.1
  have hAend : volume (A ∩ Set.Ioc (0 : ℝ) 1) = volume A := by
    have hdiff : A \ Set.Ioc (0 : ℝ) 1 ⊆ {(0 : ℝ)} := by
      intro y hy
      have hunit := hAunit hy.1
      simp only [Set.mem_diff, Set.mem_Ioc, not_and] at hy
      simp only [Set.mem_singleton_iff]
      rcases lt_or_eq_of_le hunit.1 with hlt | heq
      · exact False.elim (hy.2 hlt hunit.2)
      · exact heq.symm
    exact measure_inter_conull' (measure_mono_null hdiff (by simp))
  calc
    ∫⁻ x in Set.Ico (0 : ℝ) 1, geometricAtomicMeasure r x A ∂volume =
        ∑' a : AtomicIndex, ∫⁻ x in Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (atomicCoefficient r a) *
            Measure.dirac (atomicPoint x a) A ∂volume := by
      simp_rw [geometricAtomicMeasure, Measure.sum_apply _ hA, Measure.smul_apply]
      rw [lintegral_tsum (fun a => (htermMeas a).aemeasurable)]
    _ = ∑' n : ℕ, ENNReal.ofReal ((1 - r) ^ 2 * r ^ n) *
          ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) * volume (A ∩ Set.Ioc 0 1) := by
      have hfactor (a : AtomicIndex) :
          (∫⁻ x in Set.Ico (0 : ℝ) 1,
            ENNReal.ofReal (atomicCoefficient r a) *
              Measure.dirac (atomicPoint x a) A ∂volume) =
          ENNReal.ofReal (atomicCoefficient r a) *
            ∫⁻ x in Set.Ico (0 : ℝ) 1,
              Measure.dirac (atomicPoint x a) A ∂volume :=
        lintegral_const_mul _ (hdiracMeas a)
      simp_rw [hfactor]
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro n
      rw [tsum_fintype]
      simp_rw [hcell n]
      simp only [atomicCoefficient]
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum, hpartition n]
    _ = volume A := by
      simp_rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le _))]
      rw [ENNReal.tsum_mul_right]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le _)) (by positivity))
        hweight, hmass, ENNReal.ofReal_one, one_mul, hAend]

#print axioms geometric_atomic_phase_average

end D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
