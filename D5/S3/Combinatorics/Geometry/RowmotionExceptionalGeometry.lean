/- GID: D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native endpoint counting for the complement of separated three-row states. -/

import D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
import Mathlib.Order.Interval.Set.OrdConnectedLinear
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder

namespace D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry

/-- All actual interval-closed states, including the empty set. -/
def convexStates (n : ℕ) : Finset (Set (Fin 3 × Fin n)) := by
  classical
  exact Finset.univ.filter Set.OrdConnected

/-- The original separated family is excluded on the full state carrier. -/
def exceptionalGeometry (n : ℕ) : Finset (Set (Fin 3 × Fin n)) := by
  classical
  exact (convexStates n).filter (fun I => ¬ Separated I)

private def rowState {n : ℕ} (a b : Fin 3 → Fin n) : Set (Fin 3 × Fin n) :=
  {p | a p.1 ≤ p.2 ∧ p.2 ≤ b p.1}

private theorem row_representation {n : ℕ} (hn : 2 ≤ n)
    (I : Set (Fin 3 × Fin n)) (hI : I.OrdConnected) :
    ∃ a b : Fin 3 → Fin n, rowState a b = I := by
  classical
  have rows (r : Fin 3) : ∃ a b : Fin n,
      ∀ x : Fin n, (r, x) ∈ I ↔ a ≤ x ∧ x ≤ b := by
    let s : Finset (Fin n) := Finset.univ.filter (fun x => (r, x) ∈ I)
    by_cases hs : s.Nonempty
    · refine ⟨s.min' hs, s.max' hs, ?_⟩
      intro x
      constructor
      · intro hx
        have hm : x ∈ s := by simpa [s] using hx
        exact ⟨s.min'_le x hm, s.le_max' x hm⟩
      · intro hx
        have ha : (r, s.min' hs) ∈ I := by
          simpa [s] using s.min'_mem hs
        have hb : (r, s.max' hs) ∈ I := by
          simpa [s] using s.max'_mem hs
        exact hI.out ha hb ⟨⟨le_rfl, hx.1⟩, ⟨le_rfl, hx.2⟩⟩
    · refine ⟨⟨1, by omega⟩, ⟨0, by omega⟩, ?_⟩
      intro x
      have hnone : (r, x) ∉ I := by
        intro hx
        apply hs
        exact ⟨x, by simpa [s] using hx⟩
      simp only [hnone, false_iff]
      intro hx
      have h₁ := hx.1
      have h₂ := hx.2
      change 1 ≤ x.val at h₁
      change x.val ≤ 0 at h₂
      omega
  choose a b hab using rows
  refine ⟨a, b, ?_⟩
  ext p
  exact (hab p.1 p.2).symm

private theorem endpoints_antitone {n : ℕ} (a b : Fin 3 → Fin n)
    (h : (rowState a b).OrdConnected) (hne : ∀ r, a r ≤ b r) :
    Antitone a ∧ Antitone b := by
  constructor
  · intro r s hrs
    by_contra hn
    have has : a r < a s := lt_of_not_ge hn
    have ha : (r, a r) ∈ rowState a b := ⟨le_rfl, hne r⟩
    have hb : (s, a s) ∈ rowState a b := ⟨le_rfl, hne s⟩
    have hc : (s, a r) ∈ rowState a b :=
      h.out ha hb ⟨⟨hrs, le_rfl⟩, ⟨le_rfl, has.le⟩⟩
    exact (not_le_of_gt has) hc.1
  · intro r s hrs
    by_contra hn
    have hbs : b r < b s := lt_of_not_ge hn
    have ha : (r, b r) ∈ rowState a b := ⟨hne r, le_rfl⟩
    have hb : (s, b s) ∈ rowState a b := ⟨hne s, le_rfl⟩
    have hc : (r, b s) ∈ rowState a b :=
      h.out ha hb ⟨⟨le_rfl, hbs.le⟩, ⟨hrs, le_rfl⟩⟩
    exact (not_le_of_gt hbs) hc.2

end D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry
