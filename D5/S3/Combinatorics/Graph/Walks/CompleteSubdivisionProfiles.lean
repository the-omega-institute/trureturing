/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Data.Multiset.Filter]
   utility: none
   digest: Actual incidence edges and full-landmark distance multisets of subdivided complete graphs. -/
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
import Mathlib.Data.Multiset.Filter

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles

open SimpleGraph
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric

variable {n : ℕ}

/-- The actual unordered graph edge at the `u` end of the subdivided edge `uv`. -/
def incidence (u v : Fin n) (h : u ≠ v) : Sym2 (Vertex n) :=
  s(Sum.inl u, Sum.inr (subdivisionVertex u v h))

theorem incidence_mem (u v : Fin n) (h : u ≠ v) :
    incidence u v h ∈ (graph n).edgeSet := by
  exact Sym2.mem_mk_left u v

theorem incidence_eq_iff (u v x y : Fin n) (h : u ≠ v) (k : x ≠ y) :
    incidence u v h = incidence x y k ↔ u = x ∧ v = y := by
  simp only [incidence, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, false_and, or_false]
  constructor
  · rintro ⟨rfl, he⟩
    have he' := congrArg Subtype.val he
    simp only [subdivisionVertex, Sym2.eq_iff] at he'
    aesop
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem edge_iff_incidence (e : Sym2 (Vertex n)) :
    e ∈ (graph n).edgeSet ↔ ∃ u v : Fin n, ∃ h : u ≠ v, e = incidence u v h := by
  constructor
  · induction e using Sym2.ind with
    | _ a b =>
      intro he
      have hab := (graph n).mem_edgeSet.mp he
      have mid (u : Fin n) (f : Midpoint n) (hf : u ∈ f.val) :
          ∃ v : Fin n, ∃ h : u ≠ v, f = subdivisionVertex u v h := by
        obtain ⟨v, hv⟩ := Sym2.mem_iff_exists.mp hf
        have h : u ≠ v := by
          intro huv
          apply f.property
          rw [hv, Sym2.mk_isDiag_iff]
          exact huv
        exact ⟨v, h, Subtype.ext hv⟩
      cases a with
      | inl u =>
        cases b with
        | inl v => exact hab.elim
        | inr f =>
          obtain ⟨v, h, rfl⟩ := mid u f hab
          exact ⟨u, v, h, rfl⟩
      | inr f =>
        cases b with
        | inr g => exact hab.elim
        | inl u =>
          obtain ⟨v, h, rfl⟩ := mid u f hab
          exact ⟨u, v, h, Sym2.eq_swap⟩
  · rintro ⟨u, v, h, rfl⟩
    exact incidence_mem u v h

/-- Minimum of the two actual shortest endpoint distances, independent of edge orientation. -/
noncomputable def edgeDistance (s : Vertex n) : Sym2 (Vertex n) → ℕ :=
  Sym2.lift ⟨fun x y => min ((graph n).dist s x) ((graph n).dist s y),
    fun _ _ => min_comm _ _⟩

theorem edgeDistance_original (u v w : Fin n) (h : u ≠ v) :
    edgeDistance (.inl w) (incidence u v h) =
      if w = u then 0 else if w = v then 1 else 2 := by
  classical
  simp only [edgeDistance, incidence, Sym2.lift_mk, dist_original_original,
    dist_original_midpoint, subdivisionVertex, Sym2.mem_iff]
  by_cases hwu : w = u <;> by_cases hwv : w = v <;> simp_all

theorem edgeDistance_midpoint (u v : Fin n) (h : u ≠ v) (f : Midpoint n) :
    edgeDistance (.inr f) (incidence u v h) =
      if f = subdivisionVertex u v h then 0 else
        if u ∈ f.val then 1 else if v ∈ f.val then 2 else 3 := by
  classical
  have meet : (∃ w, w ∈ f.val ∧ w ∈ (subdivisionVertex u v h).val) ↔
      u ∈ f.val ∨ v ∈ f.val := by
    simp only [subdivisionVertex, Sym2.mem_iff]
    aesop
  simp only [edgeDistance, incidence, Sym2.lift_mk,
    (graph n).dist_comm (u := .inr f) (v := .inl u),
    dist_original_midpoint, dist_midpoint_midpoint, meet]
  by_cases he : f = subdivisionVertex u v h
  · simp [he, subdivisionVertex]
  · by_cases hu : u ∈ f.val <;> by_cases hv : v ∈ f.val <;> simp [he, hu, hv]

theorem edgeDistance_le_three (s : Vertex n) (e : Sym2 (Vertex n))
    (he : e ∈ (graph n).edgeSet) : edgeDistance s e ≤ 3 := by
  obtain ⟨u, v, h, rfl⟩ := (edge_iff_incidence e).mp he
  cases s with
  | inl w => rw [edgeDistance_original]; split_ifs <;> omega
  | inr f => rw [edgeDistance_midpoint]; split_ifs <;> omega

/-- Mapping the landmark multiset keeps every distance with its full multiplicity. -/
noncomputable def profile (S : Finset (Vertex n)) (e : Sym2 (Vertex n)) : Multiset ℕ :=
  S.val.map (fun s => edgeDistance s e)

/-- Pairwise distinguishability is required on all actual unordered graph edges. -/
def Resolves (S : Finset (Vertex n)) : Prop :=
  Set.InjOn (profile S) (graph n).edgeSet

theorem profile_count (S : Finset (Vertex n)) (e : Sym2 (Vertex n)) (k : ℕ) :
    (profile S e).count k = (S.filter fun s => edgeDistance s e = k).card := by
  classical
  rw [profile, Multiset.count_map]
  change (S.val.filter fun s => k = edgeDistance s e).card =
    (S.val.filter fun s => edgeDistance s e = k).card
  simp only [eq_comm]

theorem profile_eq_iff_four_counts (S T : Finset (Vertex n))
    (e f : Sym2 (Vertex n)) (he : e ∈ (graph n).edgeSet) (hf : f ∈ (graph n).edgeSet) :
    profile S e = profile T f ↔
      ∀ k : Fin 4, (profile S e).count k.val = (profile T f).count k.val := by
  constructor
  · intro h k; rw [h]
  · intro h
    apply Multiset.ext.mpr
    intro k
    by_cases hk : k < 4
    · exact h ⟨k, hk⟩
    · have absent (U : Finset (Vertex n)) (g : Sym2 (Vertex n))
          (hg : g ∈ (graph n).edgeSet) : k ∉ profile U g := by
        intro hmem
        obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hmem
        have := edgeDistance_le_three s g hg
        omega
      simp [Multiset.count_eq_zero_of_notMem (absent S e he),
        Multiset.count_eq_zero_of_notMem (absent T f hf)]

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles
