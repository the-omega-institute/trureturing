/- GID: D5/S3/Topology/IntervalSubdivisionCoordinates
   generality: G
   mirror-B: D5/B/S3/Topology/IntervalSubdivisionCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Recursive interval coordinates agree with oriented subdivision charts. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.IntervalFlagCoordinate
import D5.S3.Topology.GraphSubdivisionIntervals

/-! Ordinary subdivision of path coordinates, with exact face recovery. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.IntervalSubdivisionCoordinates

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (sd retainedVertex faceImage)
open BarycentricNeighborhoodIteration (iteratedAmbient iteratedSubcomplex subdivision)
open GraphSubdivisionIntervals (faceImage_singleton)
open private iterated_le_ambient from D5.S3.Topology.GraphSubdivisionIntervals
open IntervalFlagCoordinate (coordinate face_of_coordinate eq_index_of_injective_unit_step)
open PathContiguity (intervalComplex)

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {X : Type} {K : PreAbstractSimplicialComplex X}

/-- The coordinate of a subdivision vertex is the sum of the extremal
coordinates of its underlying face. -/
def next (f : X → ℕ) (a : Face K) : ℕ :=
  coordinate (a.val.image f)

private theorem spread {s t : Finset ℕ} (hs : s.Nonempty)
    (ht : t.Nonempty) (hle : s ⊆ t)
    (hn : ∀ a ∈ t, ∀ b ∈ t, a ≤ b + 1) :
    coordinate s ≤ coordinate t + 1 ∧ coordinate t ≤ coordinate s + 1 := by
  let lo := t.min' ht
  let hi := t.max' ht
  let a := s.min' hs
  let b := s.max' hs
  have hlo : lo ≤ a := Finset.min'_le _ _ (hle (Finset.min'_mem _ _))
  have hhi : b ≤ hi := Finset.le_max' _ _ (hle (Finset.max'_mem _ _))
  have hab : a ≤ b := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hnear : hi ≤ lo + 1 := hn _ (Finset.max'_mem _ _) _ (Finset.min'_mem _ _)
  have hc₁ : coordinate s = a + b := dite_eq_left hs
  have hc₂ : coordinate t = lo + hi := dite_eq_left ht
  rw [hc₁, hc₂]
  constructor
  · have ha : a ≤ lo + 1 := hab.trans (hhi.trans hnear)
    simpa only [Nat.add_right_comm lo 1 hi] using Nat.add_le_add ha hhi
  · have hb : hi ≤ b + 1 := hnear.trans (Nat.add_le_add_right (hlo.trans hab) 1)
    simpa only [Nat.add_assoc] using Nat.add_le_add hlo hb

/-- Subdividing a simplicial map into a path doubles the path length. -/
theorem next_face {n : ℕ} (f : X → ℕ) (hf : ∀ s ∈ K, s.image f ∈ intervalComplex n)
    {t : Finset (Face K)} (ht : t ∈ sd K) :
    t.image (next f) ∈ intervalComplex (2 * n) := by
  refine ⟨ht.1.image _, ?_, ?_⟩
  · intro k hk
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
    have ha := hf a.val a.property
    change coordinate (a.val.image f) ≤ 2 * n
    rw [coordinate, dite_eq_left ha.1]
    have hlo := ha.2.1 _ (Finset.min'_mem _ ha.1)
    have hhi := ha.2.1 _ (Finset.max'_mem _ ha.1)
    exact Nat.le_trans (Nat.add_le_add hlo hhi) (by rw [Nat.two_mul])
  · intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    by_cases he : a = b
    · rw [he]
      exact Nat.le_succ _
    have hfa := hf a.val a.property
    have hfb := hf b.val b.property
    change coordinate (a.val.image f) ≤ coordinate (b.val.image f) + 1
    rcases ht.2.1 ha hb he with h | h
    · exact (spread hfa.1 hfb.1 (Finset.image_subset_image h.le) hfb.2.2).1
    · exact (spread hfb.1 hfa.1 (Finset.image_subset_image h.le) hfa.2.2).2

private theorem next_injOn {P : PreAbstractSimplicialComplex X} {n : ℕ} (f : X → ℕ)
    (hf : ∀ s ∈ K, s.image f ∈ intervalComplex n)
    (hinj : Set.InjOn f {x | ({x} : Finset X) ∈ P}) :
    Set.InjOn (next (K := K) f) {a | ({a} : Finset (Face K)) ∈ subdivision K P} := by
  intro a ha' b hb' h
  have haP : a.val ∈ P := ha'.2.2 a (Finset.mem_singleton_self a)
  have hbP : b.val ∈ P := hb'.2.2 b (Finset.mem_singleton_self b)
  have ha := hf a.val a.property
  have hb := hf b.val b.property
  have he := face_of_coordinate (a.val.image f) ha.1 ha.2.2
  have he' := face_of_coordinate (b.val.image f) hb.1 hb.2.2
  have himage := he.symm.trans ((congrArg (fun k => Finset.Icc (k / 2) ((k + 1) / 2)) h).trans he')
  have hsub {s : Finset X} (hs : s ∈ P) : ↑s ⊆ {x | ({x} : Finset X) ∈ P} := by
    intro x hx
    exact (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty _)
  apply Subtype.ext
  apply Finset.coe_injective
  exact (hinj.image_eq_image_iff (hsub haP) (hsub hbP)).mp
    (by simpa only [Finset.coe_image] using congrArg (fun t : Finset ℕ => (t : Set ℕ)) himage)

/-- Recursively compute the ordinary path coordinates on the subdivision. -/
def iterate (f : X → ℕ) : (m : ℕ) → (iteratedAmbient K m).1 → ℕ
  | 0 => f
  | m + 1 => next (iterate f m)

/-- A simplicial coordinate into an interval is still simplicial
after subdividing both complexes. -/
theorem iterate_face {n : ℕ} (f : X → ℕ)
    (hf : ∀ s ∈ K, s.image f ∈ intervalComplex n) (m : ℕ) :
    ∀ s ∈ (iteratedAmbient K m).2, s.image (iterate f m) ∈ intervalComplex (2 ^ m * n) := by
  induction m with
  | zero =>
    change ∀ s ∈ K, s.image f ∈ intervalComplex (2 ^ 0 * n)
    rw [pow_zero, one_mul]
    exact hf
  | succ m ih =>
    intro s hs
    rw [pow_succ', mul_assoc]
    exact next_face _ ih hs

/-- An interval coordinate can fold the ambient graph but stays
injective inside an edge where the original coordinate is injective. -/
theorem iterate_injOn {P : PreAbstractSimplicialComplex X} {n : ℕ} (f : X → ℕ)
    (hf : ∀ s ∈ K, s.image f ∈ intervalComplex n)
    (hinj : Set.InjOn f {x | ({x} : Finset X) ∈ P}) (m : ℕ) :
    Set.InjOn (iterate (K := K) f m)
      {x | ({x} : Finset (iteratedAmbient K m).1) ∈ iteratedSubcomplex K P m} := by
  induction m with
  | zero => exact hinj
  | succ m ih => exact next_injOn _ (iterate_face f hf m) ih

theorem iterate_retained_zero (f : X → ℕ) (x : Vertex K) (hx : f x.val = 0)
    (m : ℕ) : iterate (K := K) f m (retainedVertex m x).val = 0 := by
  induction m with
  | zero => exact hx
  | succ m ih =>
    change coordinate (({(retainedVertex m x).val} : Finset _).image (iterate f m)) = 0
    rw [Finset.image_singleton, ih]
    simp [coordinate]

/-- The recursive coordinate agrees with every simplicial parametrization
of a subdivided interval that starts at its left endpoint. -/
theorem iterate_eq_chart_index {P : PreAbstractSimplicialComplex X}
    (hPK : P ≤ K)
    (f : X → ℕ) (hf : ∀ s ∈ K, s.image f ∈ intervalComplex 1)
    (hinj : Set.InjOn f {x | ({x} : Finset X) ∈ P}) (m : ℕ)
    (chart : Vertex (intervalComplex (2 ^ m)) → Vertex (iteratedAmbient K m).2)
    (hc : Function.Injective chart)
    (hface : ∀ s (hs : s ∈ intervalComplex (2 ^ m)),
      faceImage chart hs ∈ iteratedSubcomplex K P m)
    (x : Vertex K) (hx : f x.val = 0)
    (hstart : ∀ i : Vertex (intervalComplex (2 ^ m)), i.val = 0 → chart i = retainedVertex m x)
    (i : Vertex (intervalComplex (2 ^ m))) :
    iterate (K := K) f m (chart i).val = i.val := by
  let point (j : Fin (2 ^ m + 1)) : Vertex (intervalComplex (2 ^ m)) :=
    ⟨j.val, Finset.singleton_nonempty _, fun k hk => (Finset.mem_singleton.mp hk).symm ▸
      Nat.le_of_lt_succ j.isLt, fun a ha b hb => by
        rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
        exact Nat.le_succ _⟩
  let label (j : Fin (2 ^ m + 1)) := iterate f m (chart (point j)).val
  have hmem (j : Fin (2 ^ m + 1)) :
      ({(chart (point j)).val} : Finset _) ∈ iteratedSubcomplex K P m := by
    rw [← faceImage_singleton]
    exact hface _ (point j).property
  have hlabel : Function.Injective label := by
    intro a b hab
    apply Fin.ext
    exact congrArg Subtype.val (hc (Subtype.ext
      (iterate_injOn f hf hinj m (hmem a) (hmem b) hab)))
  have hzero : label 0 = 0 := by
    change iterate f m (chart (point 0)).val = 0
    rw [hstart _ rfl]
    exact iterate_retained_zero f x hx m
  have hstep (a b : Fin (2 ^ m + 1)) (hab : b.val = a.val + 1) :
      label a ≤ label b + 1 ∧ label b ≤ label a + 1 := by
    have hp : ({a.val, b.val} : Finset ℕ) ∈ intervalComplex (2 ^ m) := by
      refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact Nat.le_of_lt_succ a.isLt
        · exact Nat.le_of_lt_succ b.isLt
      · intro j hj k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
        rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        · exact Nat.le_succ _
        · exact Nat.le_succ_of_le (Nat.le_of_lt (hab ▸ Nat.lt_succ_self _))
        · exact hab.le
        · exact Nat.le_succ _
    have hcface : faceImage chart hp ∈ (iteratedAmbient K m).2 :=
      iterated_le_ambient hPK m (hface _ hp)
    have hinterval := iterate_face f hf m _ hcface
    have hm (j : Fin (2 ^ m + 1)) (hj : j.val ∈ ({a.val, b.val} : Finset ℕ)) :
        label j ∈ (faceImage chart hp).image (iterate f m) := by
      exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨⟨j.val, hj⟩, Finset.mem_attach _ _, rfl⟩, rfl⟩
    have ha' := hm a (Finset.mem_insert_self _ _)
    have hb' := hm b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ⟨hinterval.2.2 _ ha' _ hb', hinterval.2.2 _ hb' _ ha'⟩
  let j : Fin (2 ^ m + 1) := ⟨i.val, Nat.lt_succ_of_le
    (i.property.2.1 _ (Finset.mem_singleton_self _))⟩
  have hj : point j = i := Subtype.ext rfl
  have he := eq_index_of_injective_unit_step label hlabel hzero hstep j
  change iterate f m (chart (point j)).val = i.val at he
  rwa [hj] at he

end

end D5.S3.Topology.IntervalSubdivisionCoordinates
