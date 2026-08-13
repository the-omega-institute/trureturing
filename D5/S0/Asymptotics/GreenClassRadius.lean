/- GID: D5/S0/Asymptotics/GreenClassRadius
   generality: G
   mirror-B: D5/B/S0/Asymptotics/GreenClassRadius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An agreement class has a sharp radius set by its first unpinned coordinate. -/

import D5.S0.Naming.FirstHoleBound
import Mathlib.Topology.MetricSpace.PiNat

namespace D5.S0.Asymptotics.GreenClassRadius

open D5.S0.Naming.FirstHoleBound

attribute [local instance] PiNat.dist

variable {O : Type*}

/-- The class of sequences agreeing with `t` on the finite support `S`. -/
def greenClass (S : Finset ℕ) (t : ℕ → O) : Set (ℕ → O) :=
  {x | ∀ i ∈ S, x i = t i}

/-- Every member of a finite-support agreement class lies within the radius determined by the
first coordinate outside its support. -/
theorem dist_le_firstHole_radius (S : Finset ℕ) (t x : ℕ → O) (hx : x ∈ greenClass S t) :
    dist x t ≤ (1 / 2 : ℝ) ^ firstHole S := by
  rw [← PiNat.mem_cylinder_iff_dist_le]
  intro i hi
  exact hx i (by
    by_contra hnot
    have hle : firstHole S ≤ i := by
      rw [firstHole]
      exact Nat.find_le hnot
    omega)

/-- If the alphabet has another symbol at the first unpinned coordinate, the radius bound is
attained by changing exactly that coordinate. -/
theorem exists_dist_eq_firstHole_radius (S : Finset ℕ) (t : ℕ → O)
    (hother : ∃ y : O, y ≠ t (firstHole S)) :
    ∃ x ∈ greenClass S t, dist x t = (1 / 2 : ℝ) ^ firstHole S := by
  classical
  rcases hother with ⟨y, hy⟩
  let x := Function.update t (firstHole S) y
  refine ⟨x, ?_, ?_⟩
  · intro i hi
    have hne : i ≠ firstHole S := by
      intro hieq
      subst i
      exact (Nat.find_spec (Infinite.exists_notMem_finset S)) hi
    simp [x, hne]
  · have hxt : x ≠ t := by
      intro h
      apply hy
      simpa [x] using congrFun h (firstHole S)
    rw [PiNat.dist_eq_of_ne hxt]
    congr 1
    apply le_antisymm
    · rw [PiNat.firstDiff_def, dif_pos hxt]
      exact Nat.find_le (by simp [x, hy])
    · by_contra hle
      have hlt : PiNat.firstDiff x t < firstHole S := Nat.lt_of_not_ge hle
      exact PiNat.apply_firstDiff_ne hxt (by simp [x, ne_of_lt hlt])

/-- The prefix-metric radius of the agreement class is exactly determined by the first unpinned
coordinate, provided the alphabet has another symbol available there. -/
theorem green_class_radius_sharp (S : Finset ℕ) (t : ℕ → O)
    (hother : ∃ y : O, y ≠ t (firstHole S)) :
    (∀ x ∈ greenClass S t, dist x t ≤ (1 / 2 : ℝ) ^ firstHole S) ∧
      ∃ x ∈ greenClass S t, dist x t = (1 / 2 : ℝ) ^ firstHole S := by
  exact ⟨fun x hx => dist_le_firstHole_radius S t x hx,
    exists_dist_eq_firstHole_radius S t hother⟩

end D5.S0.Asymptotics.GreenClassRadius
