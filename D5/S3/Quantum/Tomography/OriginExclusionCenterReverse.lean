/- GID: D5/S3/Quantum/Tomography/OriginExclusionCenterReverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/OriginExclusionCenterReverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A strict reverse ordering of two full-effect readings at exclusion-ball centres. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.Quantum.Tomography.OriginExclusionCenterReverse

/-! The algebraic core of XI135.2.  The sets `ballP` and `ballQ` stand for the
    complete exclusion balls.  The hypotheses record only the source proof's
    two reflection points, effect bounds, and the unique-maximizer fact on the
    second ball; no classification or physical operation is assumed. -/

structure SeparationData (E : Type*) [AddCommGroup E] [Module ℝ E] where
  ballP : Set E
  ballQ : Set E
  centreP : E
  centreQ : E
  pureP : E
  pureQ : E
  reflectedP : E
  reflectedQ : E
  effect : E →ₗ[ℝ] ℝ
  reflectedP_eq : reflectedP = 2 • centreP - pureQ
  reflectedQ_eq : reflectedQ = 2 • centreQ - pureP
  pureQ_mem_ballP : pureQ ∈ ballP
  reflectedP_mem_ballP : reflectedP ∈ ballP
  reflectedP_mem_ballQ : reflectedP ∈ ballQ
  reflectedQ_mem_ballQ : reflectedQ ∈ ballQ
  pureP_not_mem_ballP : pureP ∉ ballP
  pureP_effect : effect pureP = 1
  pureQ_effect : effect pureQ = 0
  bounds_ballP : ∀ x ∈ ballP, 0 ≤ effect x ∧ effect x ≤ 1
  bounds_ballQ : ∀ x ∈ ballQ, 0 ≤ effect x ∧ effect x ≤ 1
  unique_max_ballQ : ∀ {x : E}, x ∈ ballQ → effect x = 1 → x = pureP

theorem centre_reverse_weak_bounds
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : SeparationData E) :
    d.effect d.centreP ≤ (1 : ℝ) / 2 ∧
      (1 : ℝ) / 2 ≤ d.effect d.centreQ := by
  have hp := d.bounds_ballP d.reflectedP d.reflectedP_mem_ballP
  have hq := d.bounds_ballQ d.reflectedQ d.reflectedQ_mem_ballQ
  rw [d.reflectedP_eq] at hp
  rw [d.reflectedQ_eq] at hq
  simp only [map_sub, map_add, map_nsmul, two_smul, d.pureQ_effect, d.pureP_effect] at hp hq
  constructor <;> linarith

theorem strict_centre_reverse
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : SeparationData E) :
    d.effect d.centreP ≤ (1 : ℝ) / 2 ∧
      (1 : ℝ) / 2 ≤ d.effect d.centreQ ∧
      d.effect d.centreP < d.effect d.centreQ := by
  have hweak := centre_reverse_weak_bounds d
  have hle : d.effect d.centreP ≤ d.effect d.centreQ :=
    hweak.1.trans hweak.2
  have hne : d.effect d.centreP ≠ d.effect d.centreQ := by
    intro heq
    have hhalf : d.effect d.centreP = (1 : ℝ) / 2 := by
      linarith [hweak.1, hweak.2]
    have hreflect : d.effect d.reflectedP = 1 := by
      rw [d.reflectedP_eq]
      simp only [map_sub, map_add, map_nsmul, two_smul, d.pureQ_effect]
      linarith
    have heqpoint := d.unique_max_ballQ d.reflectedP_mem_ballQ hreflect
    exact d.pureP_not_mem_ballP (heqpoint ▸ d.reflectedP_mem_ballP)
  exact ⟨hweak.1, hweak.2, lt_of_le_of_ne hle hne⟩

#print axioms centre_reverse_weak_bounds
#print axioms strict_centre_reverse

end D5.S3.Quantum.Tomography.OriginExclusionCenterReverse
