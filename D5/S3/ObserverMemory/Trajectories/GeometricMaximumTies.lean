/- GID: D5/S3/ObserverMemory/Trajectories/GeometricMaximumTies
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/GeometricMaximumTies
   mirror-E: none(waiver:exact-probability-bound)
   anchors: [mathlib/module/Mathlib.Probability.Independence.Basic]
   utility: none
   digest: Exact tied-maximum series and reciprocal size bound for independent geometric samples. -/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.ObserverMemory.Trajectories.GeometricMaximumTies

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

/-- All ties count as maxima. With `n` competitors there are `n + 1` samples;
when `n = 0`, the comparison is empty and its probability is one. The marginal
law is the zero-start geometric law, equivalent to shifting positive lengths
down by one. Both the convergent series and its bound concern the actual joint
event on the given probability space. -/
theorem tied_maximum_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℕ) (X : Fin (n + 1) → Ω → ℕ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ)
    (hlaw : ∀ i j, μ.real {ω | X i ω = j} = (1 - p) * p ^ j) :
    HasSum (fun j : ℕ => (1 - p) * p ^ j * (1 - p ^ (j + 1)) ^ n)
      (μ.real {ω | ∀ i : Fin n, X i.succ ω ≤ X 0 ω}) ∧
    μ.real {ω | ∀ i : Fin n, X i.succ ω ≤ X 0 ω} ≤
      (1 - (1 - p) ^ (n + 1)) / (p * (n + 1)) ∧
    μ.real {ω | ∀ i : Fin n, X i.succ ω ≤ X 0 ω} ≤ 1 / (p * (n + 1)) := by
  classical
  have hcdf (i : Fin (n + 1)) (j : ℕ) :
      μ.real {ω | X i ω ≤ j} = 1 - p ^ (j + 1) := by
    have hsum := sum_measureReal_preimage_singleton (μ := μ) (Finset.range (j + 1))
      (f := X i) (fun k _ => (hX i) (measurableSet_singleton k))
    have hset : (X i) ⁻¹' (↑(Finset.range (j + 1)) : Set ℕ) = {ω | X i ω ≤ j} := by
      ext ω
      simp only [mem_preimage, Finset.mem_coe, Finset.mem_range, mem_ofPred_eq]
      omega
    rw [hset] at hsum
    rw [← hsum]
    simp only [show ∀ k, (X i) ⁻¹' ({k} : Set ℕ) = {ω | X i ω = k} from fun _ => rfl,
      hlaw, ← Finset.mul_sum]
    have hg := geom_sum_mul_neg p (j + 1)
    nlinarith
  let E : ℕ → Set Ω := fun j => {ω | X 0 ω = j ∧ ∀ i : Fin n, X i.succ ω ≤ j}
  have hE (j : ℕ) : MeasurableSet (E j) := by
    have hall : MeasurableSet {ω | ∀ i : Fin n, X i.succ ω ≤ j} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i : Fin n => hX i.succ (measurableSet_Iic (a := j))
    exact (hX 0 (measurableSet_singleton j)).inter hall
  have hmass (j : ℕ) : μ.real (E j) = (1 - p) * p ^ j * (1 - p ^ (j + 1)) ^ n := by
    let S : Fin (n + 1) → Set ℕ := Fin.cases {j} (fun _ => Iic j)
    have hi := hind.measure_inter_preimage_eq_mul Finset.univ
      (sets := S) (fun i _ => MeasurableSet.of_discrete)
    have hrect : (⋂ i ∈ (Finset.univ : Finset (Fin (n + 1))), X i ⁻¹' S i) = E j := by
      ext ω
      simp only [Finset.mem_univ, iInter_true, mem_iInter, mem_preimage]
      change (∀ i, X i ω ∈ S i) ↔ X 0 ω = j ∧ ∀ i : Fin n, X i.succ ω ≤ j
      rw [Fin.forall_fin_succ]
      rfl
    rw [hrect] at hi
    have hr := congrArg ENNReal.toReal hi
    simp only [ENNReal.toReal_prod, ← measureReal_def] at hr
    rw [hr, Fin.prod_univ_succ]
    change μ.real {ω | X 0 ω = j} * (∏ i : Fin n, μ.real {ω | X i.succ ω ≤ j}) = _
    simp only [hlaw, hcdf, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdisj : Pairwise (fun j k => Disjoint (E j) (E k)) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro ω hj hk
    exact hjk (hj.1.symm.trans hk.1)
  have hunion : (⋃ j, E j) = {ω | ∀ i : Fin n, X i.succ ω ≤ X 0 ω} := by
    ext ω
    simp only [mem_iUnion, E, mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, hle⟩
      simpa only [hj] using hle
    · intro h
      exact ⟨X 0 ω, rfl, h⟩
  have hm := measure_iUnion hdisj hE (μ := μ)
  rw [hunion] at hm
  have hs := ENNReal.hasSum_toReal (f := fun j => μ (E j)) (by rw [← hm]; exact measure_ne_top _ _)
  rw [← ENNReal.tsum_toReal_eq (fun j => measure_ne_top μ (E j)), ← hm] at hs
  simp only [← measureReal_def, hmass] at hs
  refine ⟨hs, ?_⟩
  have hden : 0 < p * (n + 1 : ℝ) := mul_pos hp (by positivity)
  let a : ℕ → ℝ := fun j => 1 - p ^ (j + 1)
  have ha (j : ℕ) : 0 ≤ a j := sub_nonneg.mpr (pow_le_one₀ hp.le hp1.le)
  have hadiff (j : ℕ) : a (j + 1) - a j = p * ((1 - p) * p ^ j) := by
    dsimp [a]
    simp only [pow_succ]
    ring
  have hstep (j : ℕ) :
      (p * (n + 1)) * ((1 - p) * p ^ j * a j ^ n) ≤
        a (j + 1) ^ (n + 1) - a j ^ (n + 1) := by
    have hd : 0 ≤ a (j + 1) - a j := by
      rw [hadiff]
      exact mul_nonneg hp.le (mul_nonneg (sub_nonneg.mpr hp1.le) (pow_nonneg hp.le j))
    have h := pow_add_mul_le_add_pow (ha j)
      (show 0 ≤ 2 * a j + (a (j + 1) - a j) by linarith [ha j]) (n + 1)
    rw [add_sub_cancel, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hadiff] at h
    nlinarith
  have hfinite (m : ℕ) :
      (∑ j ∈ Finset.range m, (1 - p) * p ^ j * (1 - p ^ (j + 1)) ^ n) ≤
        (1 - (1 - p) ^ (n + 1)) / (p * (n + 1)) := by
    apply (le_div_iff₀ hden).mpr
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range m) => hstep j)
    rw [← Finset.mul_sum] at h
    rw [Finset.sum_range_sub (fun j => a j ^ (n + 1)) m] at h
    have htop : a m ^ (n + 1) ≤ 1 :=
      pow_le_one₀ (ha m) (sub_le_self _ (pow_nonneg hp.le _))
    have hz : a 0 = 1 - p := by simp [a]
    rw [hz] at h
    dsimp only [a] at h
    nlinarith
  have hbound := le_of_tendsto hs.tendsto_sum_nat (Filter.Eventually.of_forall hfinite)
  refine ⟨hbound, hbound.trans ?_⟩
  apply div_le_div_of_nonneg_right _ hden.le
  have : 0 ≤ (1 - p) ^ (n + 1) := pow_nonneg (sub_nonneg.mpr hp1.le) _
  linarith

#print axioms tied_maximum_bound

end D5.S3.ObserverMemory.Trajectories.GeometricMaximumTies
