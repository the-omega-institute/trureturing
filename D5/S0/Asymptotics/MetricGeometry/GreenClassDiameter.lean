/- GID: D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter
   generality: G
   mirror-B: D5/B/S0/Asymptotics/MetricGeometry/GreenClassDiameter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: In the PiNat prefix metric over a nontrivial discrete alphabet, the Green class determined by a finite support S has diameter exactly (1/2)^(firstHole S); consequently, among supports of fixed cardinality, the prefix support Finset.range S.card uniquely minimizes diameter, attaining (1/2)^S.card. -/

import D5.S0.Naming.FirstHoleBound
import D5.S0.Naming.GreenClassMeasure
import Mathlib.Topology.MetricSpace.PiNat

namespace D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter

open D5.S0.Naming.FirstHoleBound
open D5.S0.Naming.GreenClassMeasure

attribute [local instance] PiNat.metricSpace PiNat.boundedSpace

private theorem mem_greenClass_iff {O : Type*} {S : Finset ℕ} {t x : ℕ → O} :
    x ∈ greenClass S t ↔ ∀ i ∈ S, x i = t i := by
  simp [greenClass]

/-- The exact diameter of a Green class in the PiNat prefix metric. -/
theorem green_class_diameter {O : Type*} [TopologicalSpace O] [DiscreteTopology O]
    [Nontrivial O] (S : Finset ℕ) (t : ℕ → O) :
    Metric.diam (greenClass S t) = (1 / 2 : ℝ) ^ firstHole S := by
  classical
  apply le_antisymm
  · refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp
    rw [PiNat.dist_eq_of_ne hxy]
    apply (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).2
    by_contra hle
    have hlt : PiNat.firstDiff x y < firstHole S := Nat.lt_of_not_ge hle
    have hmem : PiNat.firstDiff x y ∈ S := by
      by_contra hnot
      have hfirst : firstHole S ≤ PiNat.firstDiff x y := by
        rw [firstHole]
        exact Nat.find_le hnot
      omega
    exact PiNat.apply_firstDiff_ne hxy (by
      calc
        x (PiNat.firstDiff x y) = t (PiNat.firstDiff x y) :=
          (mem_greenClass_iff.mp hx) _ hmem
        _ = y (PiNat.firstDiff x y) := (mem_greenClass_iff.mp hy _ hmem).symm)
  · obtain ⟨a, ha⟩ := exists_ne (t (firstHole S))
    let x := Function.update t (firstHole S) a
    have ht : t ∈ greenClass S t := by
      simp [greenClass]
    have hx : x ∈ greenClass S t := by
      rw [mem_greenClass_iff]
      intro i hi
      have hne : i ≠ firstHole S := by
        intro hieq
        subst i
        exact (Nat.find_spec (Infinite.exists_notMem_finset S)) hi
      simp [x, hne]
    have hxt : x ≠ t := by
      intro h
      apply ha
      simpa [x] using congrFun h (firstHole S)
    have hdist : dist x t = (1 / 2 : ℝ) ^ firstHole S := by
      rw [PiNat.dist_eq_of_ne hxt]
      congr 1
      apply le_antisymm
      · rw [PiNat.firstDiff_def, dif_pos hxt]
        exact Nat.find_le (by simp [x, ha])
      · by_contra hle
        have hlt : PiNat.firstDiff x t < firstHole S := Nat.lt_of_not_ge hle
        exact PiNat.apply_firstDiff_ne hxt (by simp [x, ne_of_lt hlt])
    rw [← hdist]
    exact Metric.dist_le_diam_of_mem (Bornology.IsBounded.all _) hx ht

/-- Prefix supports uniquely minimize the diameter among supports with the same cardinality. -/
theorem prefix_support_minimizes_diameter {O : Type*} [TopologicalSpace O] [DiscreteTopology O]
    [Nontrivial O] (S : Finset ℕ) (t : ℕ → O) :
    (1 / 2 : ℝ) ^ S.card ≤ Metric.diam (greenClass S t) ∧
      (Metric.diam (greenClass S t) = (1 / 2 : ℝ) ^ S.card ↔
        S = Finset.range S.card) := by
  rw [green_class_diameter]
  have hfirst := firstHole_le_card_and_eq_iff S
  constructor
  · exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).2 hfirst.1
  · constructor
    · intro h
      exact hfirst.2.1 ((pow_right_strictAnti₀ (by norm_num) (by norm_num)).injective h)
    · intro h
      rw [hfirst.2.2 h]

example {O : Type*} [TopologicalSpace O] [DiscreteTopology O] [Nontrivial O]
    (m : ℕ) (t : ℕ → O) :
    Metric.diam (greenClass (Finset.range m) t) = (1 / 2 : ℝ) ^ m := by
  rw [green_class_diameter, firstHole_range]

end D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter
