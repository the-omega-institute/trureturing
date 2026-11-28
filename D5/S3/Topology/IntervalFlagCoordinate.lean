/- GID: D5/S3/Topology/IntervalFlagCoordinate
   generality: G
   mirror-B: D5/B/S3/Topology/IntervalFlagCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Extremal coordinates and exact recovery of a subdivided path face. -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Coordinates under a single ordinary subdivision of a path. -/

set_option autoImplicit false

namespace D5.S3.Topology.IntervalFlagCoordinate

/-- A retained point doubles its coordinate, and an edge barycenter has
the sum of the two old endpoint coordinates. -/
def coordinate (s : Finset ℕ) : ℕ :=
  if h : s.Nonempty then s.min' h + s.max' h else 0

/-- The list decoder and the face-set coordinate coincide. -/
theorem list_coordinate (l : List ℕ) :
    (match l with
      | [] => 0
      | a :: t => t.foldl min a + t.foldl max a) = coordinate l.toFinset := by
  cases l with
  | nil => simp [coordinate]
  | cons a t =>
    have hl : a :: t ≠ [] := List.cons_ne_nil _ _
    have hs : (a :: t).toFinset.Nonempty :=
      ⟨a, List.mem_toFinset.mpr List.mem_cons_self⟩
    have hmin : ((a :: t).toFinset).min' hs = (a :: t).min hl := by
      apply (Finset.min'_eq_iff _ _ _).2
      exact ⟨List.mem_toFinset.mpr (List.min_mem hl), fun _ h =>
        List.min_le_of_mem (List.mem_toFinset.mp h)⟩
    have hmax : ((a :: t).toFinset).max' hs = (a :: t).max hl := by
      apply (Finset.max'_eq_iff _ _ _).2
      exact ⟨List.mem_toFinset.mpr (List.max_mem hl), fun _ h =>
        List.le_max_of_mem (List.mem_toFinset.mp h)⟩
    rw [coordinate, dif_pos hs, hmin, hmax]
    rfl

/-- For a nonempty face of an interval graph, the parity face at the
new coordinate recovers the original face exactly. -/
theorem face_of_coordinate (s : Finset ℕ) (hs : s.Nonempty)
    (hstep : ∀ a ∈ s, ∀ b ∈ s, a ≤ b + 1) :
    Finset.Icc (coordinate s / 2) ((coordinate s + 1) / 2) = s := by
  let lo := s.min' hs
  let hi := s.max' hs
  have hlo : lo ∈ s := Finset.min'_mem _ _
  have hhi : hi ∈ s := Finset.max'_mem _ _
  have hle : lo ≤ hi := Finset.min'_le _ _ hhi
  have hnear : hi ≤ lo + 1 := hstep hi hhi lo hlo
  have hcoord : coordinate s = lo + hi := dif_pos hs
  have hleft : (lo + hi) / 2 = lo := by omega
  have hright : (lo + hi + 1) / 2 = hi := by omega
  rw [hcoord, hleft, hright]
  ext k
  rw [Finset.mem_Icc]
  constructor
  · intro h
    have hk : k = lo ∨ k = hi := by omega
    rcases hk with rfl | rfl
    · exact hlo
    · exact hhi
  · intro h
    exact ⟨Finset.min'_le _ _ h, Finset.le_max' _ _ h⟩


/-- An injective unit-step labelling of a finite path is determined by
its initial value zero. -/
theorem eq_index_of_injective_unit_step {length : ℕ} (f : Fin (length + 1) → ℕ)
    (hinj : Function.Injective f) (hzero : f 0 = 0)
    (hstep : ∀ a b : Fin (length + 1), b.val = a.val + 1 →
      f a ≤ f b + 1 ∧ f b ≤ f a + 1) (i : Fin (length + 1)) :
    f i = i.val := by
  have result (k : ℕ) : ∀ (hk : k < length + 1), f ⟨k, hk⟩ = k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      cases k with
      | zero => exact hzero
      | succ k =>
        let a : Fin (length + 1) := ⟨k, by omega⟩
        let b : Fin (length + 1) := ⟨k + 1, hk⟩
        have ha : f a = k := ih k (Nat.lt_succ_self k) a.isLt
        have hib : f b ≠ k := by
          intro h
          have hab := congrArg Fin.val (hinj (ha.trans h.symm))
          change k = k + 1 at hab
          omega
        have hstep' := hstep a b rfl
        change f b = k + 1
        cases k with
        | zero => omega
        | succ j =>
          let z : Fin (length + 1) := ⟨j, by omega⟩
          have hz : f z = j := ih j (by omega) z.isLt
          have hnot : f b ≠ j := by
            intro h
            have hval := congrArg Fin.val (hinj (h.trans hz.symm))
            change j + 1 + 1 = j at hval
            omega
          omega
  exact result i.val i.isLt

end D5.S3.Topology.IntervalFlagCoordinate
