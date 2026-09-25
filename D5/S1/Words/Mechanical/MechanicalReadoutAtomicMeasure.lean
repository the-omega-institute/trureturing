/- GID: D5/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalReadoutAtomicMeasure
   mirror-E: none(waiver:actual-mechanical-atomic-measure)
   anchors: []
   utility: none
   digest: Geometric mechanical readouts induce a measure of numbered threshold atoms. -/

import D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure

open Set Finset MeasureTheory
open scoped BigOperators
open Classical
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalReadoutOrder
open D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries

/-- An atom remembers both its time and its threshold number; coincident
locations from different times retain their separate weights. -/
abbrev AtomicIndex := Σ n : ℕ, Fin (n + 1)

def atomicPoint (x : ℝ) (a : AtomicIndex) : ℝ :=
  (((a.2.val + 1 : ℕ) : ℝ) - x) / (((a.1 + 1 : ℕ) : ℝ))

def atomicCoefficient (r : ℝ) (a : AtomicIndex) : ℝ :=
  (1 - r) ^ 2 * r ^ a.1

def geometricAtomicMeasure (r x : ℝ) : Measure ℝ :=
  Measure.sum fun a : AtomicIndex =>
    ENNReal.ofReal (atomicCoefficient r a) • Measure.dirac (atomicPoint x a)

/-- The numbered threshold atoms have unit total mass, and every atom lies
strictly above zero and at most one for a phase in the unit half-open interval. -/
theorem geometric_atomic_probability_and_carrier
    (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx : x ∈ Ico (0 : ℝ) 1) :
    IsProbabilityMeasure (geometricAtomicMeasure r x) ∧
      geometricAtomicMeasure r x (Ioc (0 : ℝ) 1) = 1 := by
  let c : AtomicIndex → ℝ := atomicCoefficient r
  have hc0 (a : AtomicIndex) : 0 ≤ c a := by
    dsimp [c, atomicCoefficient]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _)
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hgeom : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) * r ^ n)) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one 1 hrnorm)
  have houter : Summable
      (fun n : ℕ => (1 - r) ^ 2 * r ^ n * (((n + 1 : ℕ) : ℝ))) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hgeom.mul_left ((1 - r) ^ 2)
  have hfinite (n : ℕ) :
      (∑ i : Fin (n + 1), c ⟨n, i⟩) =
        (1 - r) ^ 2 * r ^ n * (((n + 1 : ℕ) : ℝ)) := by
    simp [c, atomicCoefficient, Finset.sum_const, nsmul_eq_mul]
    ring
  have hc : Summable c := by
    apply (summable_sigma_of_nonneg hc0).2
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype, hfinite] using houter
  have hmass :
      (∑' n : ℕ, (1 - r) ^ 2 * r ^ n * (((n + 1 : ℕ) : ℝ))) = 1 :=
    (geometric_readout_floor_series_and_mass r 0 x hr0 hr1
      (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) hx).2.1
  have hctsum : (∑' a : AtomicIndex, c a) = 1 := by
    rw [hc.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
    simpa only [tsum_fintype, hfinite] using hmass
  have hprob : IsProbabilityMeasure (geometricAtomicMeasure r x) := by
    change IsProbabilityMeasure
      (Measure.sum fun a : AtomicIndex =>
        ENNReal.ofReal (c a) • Measure.dirac (atomicPoint x a))
    apply HasSum.isProbabilityMeasure_sum_dirac hc0
    exact hctsum ▸ hc.hasSum
  have hpoint (a : AtomicIndex) : atomicPoint x a ∈ Ioc (0 : ℝ) 1 := by
    rcases a with ⟨n, i⟩
    have hden : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hnum : (0 : ℝ) < (((i.val + 1 : ℕ) : ℝ)) - x := by
      have hi : (1 : ℝ) ≤ (((i.val + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.val)
      linarith [hx.2]
    have hle : (((i.val + 1 : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) := by
      have hi : i.val + 1 ≤ n + 1 := i.isLt
      exact_mod_cast hi
    change 0 < (_ - x) / _ ∧ (_ - x) / _ ≤ 1
    constructor
    · exact div_pos hnum hden
    · apply (div_le_iff₀ hden).2
      linarith [hx.1]
  constructor
  · exact hprob
  · change (Measure.sum fun a : AtomicIndex =>
      ENNReal.ofReal (c a) • Measure.dirac (atomicPoint x a)) (Ioc 0 1) = 1
    rw [Measure.sum_apply _ measurableSet_Ioc]
    have hterm (a : AtomicIndex) :
        (ENNReal.ofReal (c a) • Measure.dirac (atomicPoint x a)) (Ioc 0 1) =
          ENNReal.ofReal (c a) := by
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem (hpoint a)]
      simp
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg hc0 hc, hctsum]
    norm_num

/-- The distribution function of the atomic measure is the completed
mechanical readout, including every coincident threshold atom. -/
theorem geometric_atomic_apply_Iic
    (r alpha x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : alpha ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    geometricAtomicMeasure r x (Set.Iic alpha) =
      ENNReal.ofReal (geometricReadout r alpha x) := by
  let c : AtomicIndex → ℝ := atomicCoefficient r
  let f : AtomicIndex → ℝ := fun a =>
    c a * if atomicPoint x a ≤ alpha then 1 else 0
  have hc0 (a : AtomicIndex) : 0 ≤ c a := by
    dsimp [c, atomicCoefficient]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _)
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hgeom : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) * r ^ n)) := by
    simpa using (summable_choose_mul_geometric_of_norm_lt_one 1 hrnorm)
  have houter : Summable
      (fun n : ℕ => (1 - r) ^ 2 * r ^ n * (((n + 1 : ℕ) : ℝ))) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hgeom.mul_left ((1 - r) ^ 2)
  have hfinite (n : ℕ) :
      (∑ i : Fin (n + 1), c ⟨n, i⟩) =
        (1 - r) ^ 2 * r ^ n * (((n + 1 : ℕ) : ℝ)) := by
    simp [c, atomicCoefficient, Finset.sum_const, nsmul_eq_mul]
    ring
  have hc : Summable c := by
    apply (summable_sigma_of_nonneg hc0).2
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype, hfinite] using houter
  have hf0 (a : AtomicIndex) : 0 ≤ f a := by
    dsimp [f]
    split_ifs <;> simp [hc0 a]
  have hfle (a : AtomicIndex) : f a ≤ c a := by
    dsimp [f]
    split_ifs <;> simp [hc0 a]
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfle hc
  have hseries :=
    (geometric_readout_floor_series_and_mass r alpha x hr0 hr1 ha hx).2.2
  have hreal : (∑' a : AtomicIndex, f a) = geometricReadout r alpha x := by
    rw [hf.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
    rw [hseries]
    apply tsum_congr
    intro n
    simp only [tsum_fintype]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [f, c, atomicCoefficient, atomicPoint, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    geometricAtomicMeasure r x (Set.Iic alpha) =
        ∑' a : AtomicIndex, ENNReal.ofReal (f a) := by
      rw [geometricAtomicMeasure, Measure.sum_apply _ measurableSet_Iic]
      apply tsum_congr
      intro a
      by_cases h : atomicPoint x a ≤ alpha
      · simp [f, c, h, Measure.smul_apply, Measure.dirac_apply',
          Set.indicator_of_mem]
      · simp [f, c, h, Measure.smul_apply, Measure.dirac_apply',
          Set.indicator_of_notMem]
    _ = ENNReal.ofReal (∑' a : AtomicIndex, f a) :=
      (ENNReal.ofReal_tsum_of_nonneg hf0 hf).symm
    _ = ENNReal.ofReal (geometricReadout r alpha x) := by rw [hreal]

private theorem atomicPoint_injective_level (x : ℝ) (n : ℕ) :
    Function.Injective (fun i : Fin (n + 1) => atomicPoint x ⟨n, i⟩) := by
  intro i j h
  apply Fin.ext
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  dsimp [atomicPoint] at h
  have hnum := (div_left_inj' hn).mp h
  have hval : (i.val : ℝ) = j.val := by
    push_cast at hnum
    linarith
  exact_mod_cast hval

private theorem atomicPoint_integer_hit_iff
    (x alpha : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (ha : alpha ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (∃ i : Fin (n + 1), atomicPoint x ⟨n, i⟩ = alpha) ↔
      ∃ z : ℤ, (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha := by
  have hden : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨((i.val + 1 : ℕ) : ℤ), ?_⟩
    dsimp [atomicPoint] at hi
    have hmul := (div_eq_iff hden).mp hi
    exact_mod_cast (show (((i.val + 1 : ℕ) : ℝ)) =
      x + (((n + 1 : ℕ) : ℝ)) * alpha by linarith)
  · rintro ⟨z, hz⟩
    have hposR : (0 : ℝ) < z := by
      rw [hz]
      nlinarith [ha.1, hx.1, (show (0 : ℝ) < (n + 1 : ℕ) by positivity)]
    have hltR : (z : ℝ) < (((n + 2 : ℕ) : ℝ)) := by
      rw [hz]
      have hmul : (((n + 1 : ℕ) : ℝ)) * alpha < (((n + 1 : ℕ) : ℝ)) := by
        simpa using mul_lt_mul_of_pos_left ha.2
          (show (0 : ℝ) < (n + 1 : ℕ) by positivity)
      have hcast : (((n + 2 : ℕ) : ℝ)) = (((n + 1 : ℕ) : ℝ)) + 1 := by
        push_cast
        ring
      rw [hcast]
      have hxlt : x < 1 := hx.2
      linarith [hmul, hxlt]
    have hposZ : (0 : ℤ) < z := by exact_mod_cast hposR
    have hltZ : z < ((n + 2 : ℕ) : ℤ) := by exact_mod_cast hltR
    have hznat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hposZ.le
    have hnat0 : 0 < z.toNat := by omega
    have hnatlt : z.toNat < n + 2 := by omega
    let i : Fin (n + 1) := ⟨z.toNat - 1, by omega⟩
    have hival : (((i.val + 1 : ℕ) : ℝ)) = (z : ℝ) := by
      have hstep : i.val + 1 = z.toNat := by dsimp [i]; omega
      rw [hstep]
      exact_mod_cast hznat
    refine ⟨i, ?_⟩
    dsimp [atomicPoint]
    rw [div_eq_iff hden, hival, hz]
    ring

/-- At an interior slope, the singleton mass is the sum over every integer
hit time, with all coincident times retained. -/
theorem geometric_atomic_singleton_hit
    (r x alpha : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (ha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    geometricAtomicMeasure r x {alpha} =
      ∑' n : ℕ, if ∃ z : ℤ,
          (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
        ENNReal.ofReal ((1 - r) ^ 2 * r ^ n) else 0 := by
  classical
  have hterm (a : AtomicIndex) :
      (ENNReal.ofReal (atomicCoefficient r a) •
        Measure.dirac (atomicPoint x a)) {alpha} =
        if atomicPoint x a = alpha then
          ENNReal.ofReal (atomicCoefficient r a) else 0 := by
    by_cases h : atomicPoint x a = alpha
    · simp [h, Measure.smul_apply]
    · simp [h, Measure.smul_apply, Measure.dirac_apply']
  rw [geometricAtomicMeasure, Measure.sum_apply _ (measurableSet_singleton alpha)]
  simp_rw [hterm]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  by_cases he : ∃ i : Fin (n + 1), atomicPoint x ⟨n, i⟩ = alpha
  · obtain ⟨i, hi⟩ := he
    have hhit : ∃ z : ℤ, (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha :=
      (atomicPoint_integer_hit_iff x alpha hx ha n).mp ⟨i, hi⟩
    rw [if_pos hhit]
    rw [Finset.sum_eq_single i]
    · simp [hi, atomicCoefficient]
    · intro j hj hji
      have hne : atomicPoint x ⟨n, j⟩ ≠ alpha := by
        intro hj'
        exact hji (atomicPoint_injective_level x n (hj'.trans hi.symm))
      simp [hne]
    · simp
  · have hmiss : ¬∃ z : ℤ,
        (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha := by
      intro hz
      exact he ((atomicPoint_integer_hit_iff x alpha hx ha n).mpr hz)
    rw [if_neg hmiss]
    simp only [not_exists] at he
    simp [he]

private def approximatingIndex (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (n : ℕ) : Fin (n + 1) :=
  ⟨⌊y * (((n + 1 : ℕ) : ℝ))⌋₊, by
    apply (Nat.floor_lt (mul_nonneg hy.1 (by positivity))).2
    have hk : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
    simpa using mul_lt_mul_of_pos_right hy.2 hk⟩

private theorem approximatingPoint_tendsto (x y : ℝ)
    (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    Filter.Tendsto
      (fun n : ℕ => atomicPoint x ⟨n, approximatingIndex y hy n⟩)
      Filter.atTop (nhds y) := by
  have hk : Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [(Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop b)] with n hn
    exact hn.trans (by exact_mod_cast Nat.le_succ n)
  have hfloor : Filter.Tendsto
      (fun n : ℕ => (((⌊y * (((n + 1 : ℕ) : ℝ))⌋₊ : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ))) Filter.atTop (nhds y) :=
    (tendsto_nat_floor_mul_div_atTop hy.1).comp hk
  have hinv : Filter.Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hk
  have hcorrection : Filter.Tendsto
      (fun n : ℕ => (1 - x) * (((n + 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hinv)
  convert hfloor.add hcorrection using 1
  · ext n
    simp only [atomicPoint, approximatingIndex]
    have hden : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  · simp

/-- Every point of the closed unit interval is approached by positive-mass
numbered threshold atoms; no point outside that interval has support mass. -/
theorem geometric_atomic_support (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (geometricAtomicMeasure r x).support = Set.Icc (0 : ℝ) 1 := by
  let μ := geometricAtomicMeasure r x
  have hpoint (a : AtomicIndex) : atomicPoint x a ∈ μ.support := by
    rw [Measure.support_eq_forall_isOpen]
    intro U hmem hU
    have hc : 0 < atomicCoefficient r a := by
      unfold atomicCoefficient
      exact mul_pos (sq_pos_of_ne_zero (by linarith)) (pow_pos hr0 _)
    have hterm :
        (ENNReal.ofReal (atomicCoefficient r a) •
          Measure.dirac (atomicPoint x a)) U =
          ENNReal.ofReal (atomicCoefficient r a) := by
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem hmem]
      simp
    calc
      0 < ENNReal.ofReal (atomicCoefficient r a) := ENNReal.ofReal_pos.mpr hc
      _ = (ENNReal.ofReal (atomicCoefficient r a) •
          Measure.dirac (atomicPoint x a)) U := hterm.symm
      _ ≤ μ U := by
        change _ ≤ geometricAtomicMeasure r x U
        rw [geometricAtomicMeasure, Measure.sum_apply _ hU.measurableSet]
        exact ENNReal.le_tsum a
  have hIco : Set.Ico (0 : ℝ) 1 ⊆ μ.support := by
    intro y hy
    exact Measure.isClosed_support.mem_of_tendsto
      (approximatingPoint_tendsto x y hy)
      (Filter.Eventually.of_forall fun n => hpoint ⟨n, approximatingIndex y hy n⟩)
  have hforward : Set.Icc (0 : ℝ) 1 ⊆ μ.support := by
    rw [← closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    exact closure_minimal hIco Measure.isClosed_support
  have ⟨hprob, hcarrier⟩ :=
    geometric_atomic_probability_and_carrier r x hr0.le hr1 hx
  have hcarrier' : μ (Set.Ioc (0 : ℝ) 1) = 1 := hcarrier
  have hzero : μ (Set.Ioc (0 : ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Ioc (by rw [hcarrier']; norm_num)]
    letI : IsProbabilityMeasure μ := hprob
    simp [hcarrier']
  have hsubset : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ (Set.Ioc 0 1)ᶜ := by
    intro y hy hIoc
    exact hy ⟨hIoc.1.le, hIoc.2⟩
  have hclosed : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    apply le_antisymm
    · calc
        μ (Set.Icc (0 : ℝ) 1)ᶜ ≤ μ (Set.Ioc 0 1)ᶜ := measure_mono hsubset
        _ = 0 := hzero
    · exact bot_le
  have hbackward : μ.support ⊆ Set.Icc (0 : ℝ) 1 :=
    Measure.support_subset_of_isClosed isClosed_Icc (by simpa [mem_ae_iff] using hclosed)
  exact Set.Subset.antisymm hbackward hforward

#print axioms geometric_atomic_probability_and_carrier
#print axioms geometric_atomic_apply_Iic
#print axioms geometric_atomic_singleton_hit
#print axioms geometric_atomic_support

end D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
