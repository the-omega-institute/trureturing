/- GID: D5/S3/QuantumContext/IntervalLocalMinimumCounterexample
   generality: I
   mirror-B: D5/B/S3/QuantumContext/IntervalLocalMinimumCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Order.IntermediateValue, mathlib/module/Mathlib.Topology.Instances.Real]
   utility: none
   digest: The closed unit interval has connected affine exposed faces, while its right endpoint is a relative local but not global minimum of the coordinate.
-/

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! A concrete interval obstruction to the local-to-global minimum implication. -/

namespace D5.S3.QuantumContext.IntervalLocalMinimumCounterexample

/-! The concrete interval model used for the one-dimensional obstruction. -/

def intervalK : Set ℝ := Set.Icc 0 1

def pureEndpoints : Set ℝ := ({0, 1} : Set ℝ)

def exposedFace (g : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ intervalK ∧ ∀ y ∈ intervalK, g y ≤ g x}

def relativeLocalMinimum (f : ℝ → ℝ) (s : Set ℝ) (p : ℝ) : Prop :=
  p ∈ s ∧ ∃ ε > 0, ∀ x, x ∈ s → |x - p| < ε → f p ≤ f x

def globalMinimum (f : ℝ → ℝ) (s : Set ℝ) (p : ℝ) : Prop :=
  p ∈ s ∧ ∀ x, x ∈ s → f p ≤ f x

def coordinate (x : ℝ) : ℝ := x

private lemma affine_exposed_face_eq_interval (b : ℝ) :
    exposedFace (fun x : ℝ => 0 * x + b) = intervalK := by
  ext x
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx, ?_⟩
    intro y hy
    simp

private lemma affine_exposed_face_eq_right (m b : ℝ) (hm : 0 < m) :
    exposedFace (fun x : ℝ => m * x + b) = ({1} : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    have h1 : (1 : ℝ) ∈ intervalK := by
      simp [intervalK]
    have hle : m * (1 : ℝ) + b ≤ m * x + b := hmax 1 h1
    have hxle : x ≤ 1 := by simpa [intervalK] using hx.2
    have hxeq : x = 1 := by nlinarith [hle, hm]
    simpa [hxeq]
  · intro hx
    have hxeq : x = 1 := by simpa using hx
    subst x
    refine ⟨by simp [intervalK], ?_⟩
    intro y hy
    have hyle : y ≤ 1 := by simpa [intervalK] using hy.2
    nlinarith [hm, hyle]

private lemma affine_exposed_face_eq_left (m b : ℝ) (hm : m < 0) :
    exposedFace (fun x : ℝ => m * x + b) = ({0} : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    have h0 : (0 : ℝ) ∈ intervalK := by
      simp [intervalK]
    have hle : m * (0 : ℝ) + b ≤ m * x + b := hmax 0 h0
    have hxge : 0 ≤ x := by simpa [intervalK] using hx.1
    have hxeq : x = 0 := by nlinarith [hle, hm]
    simpa [hxeq]
  · intro hx
    have hxeq : x = 0 := by simpa using hx
    subst x
    refine ⟨by simp [intervalK], ?_⟩
    intro y hy
    have hyge : 0 ≤ y := by simpa [intervalK] using hy.1
    nlinarith [hm, hyge]

/-- The interval model from the one-dimensional obstruction has connected affine exposed
faces, but its right endpoint is a relative local minimum which is not global. -/
theorem interval_affine_faces_and_endpoint_counterexample :
    IsCompact intervalK ∧
      IsCompact pureEndpoints ∧
        (∀ m b : ℝ, IsConnected (exposedFace (fun x => m * x + b))) ∧
          relativeLocalMinimum coordinate pureEndpoints 1 ∧
            ¬ globalMinimum coordinate pureEndpoints 1 := by
  have hK : IsCompact intervalK := by
    simpa [intervalK] using (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  have hP : IsCompact pureEndpoints := by
    simpa [pureEndpoints] using
      (isCompact_singleton.union (isCompact_singleton : IsCompact ({1} : Set ℝ)))
  refine ⟨hK, hP, ?_, ?_, ?_⟩
  · intro m b
    by_cases hm0 : m = 0
    · subst m
      rw [affine_exposed_face_eq_interval]
      exact isConnected_Icc (by norm_num)
    · by_cases hm : 0 < m
      · rw [affine_exposed_face_eq_right m b hm]
        exact isConnected_singleton
      · have hmneg : m < 0 := lt_of_le_of_ne (le_of_not_gt hm) hm0
        rw [affine_exposed_face_eq_left m b hmneg]
        exact isConnected_singleton
  · refine ⟨by simp [pureEndpoints], (1 / 2 : ℝ), by norm_num, ?_⟩
    intro x hx hdist
    simp only [pureEndpoints, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · norm_num at hdist
    · norm_num [coordinate]
  · intro hglobal
    have hzero := hglobal.2 0 (by simp [pureEndpoints])
    norm_num [coordinate] at hzero

end D5.S3.QuantumContext.IntervalLocalMinimumCounterexample
