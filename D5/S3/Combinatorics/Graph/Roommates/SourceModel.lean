/- GID: D5/S3/Combinatorics/Graph/Roommates/SourceModel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/SourceModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: Pinned supplier model for range-two cyclic stable partial matchings. -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0. See the retained full license at
  docs/reports/licenses/formal-conjectures-mertens-Apache-2.0.txt
This is a minimal consumed compatibility port, not a new mathematical result.
Supplier: bocowgill/formal-conjectures, dc0fa7334537d8733edceaba09fd88163eeb7cef,
FormalConjectures/Arxiv/0509221/LocalStableMatchings.lean and
FormalConjecturesForMathlib/Combinatorics/Roommates.lean.
Changes: omit unrelated stability-threshold APIs and conjecture proof placeholder;
replace supplier infrastructure imports/attributes with project-compatible Mathlib imports;
place consumed definitions in this namespace. The N=n+5 convention is unchanged.
Retire this port when this project's pinned Mathlib provides equivalent definitions
and lemmas, replacing uses by direct imports at that pinned revision.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Graph.Roommates.SourceModel

/-- A possibly partial matching, with fixed points representing single agents. -/
abbrev Matching (α : Type*) := {μ : Equiv.Perm α // Function.Involutive μ}

/-- Matchings form a finite type when the agents do. -/
instance {α : Type*} [Fintype α] [DecidableEq α] : Fintype (Matching α) := by
  letI : DecidablePred (fun μ : Equiv.Perm α ↦ Function.Involutive μ) := fun μ ↦ by
    unfold Function.Involutive
    infer_instance
  exact Subtype.fintype _

/-- The matching in which every agent is single. -/
def emptyMatching (α : Type*) : Matching α := ⟨Equiv.refl α, fun _ ↦ rfl⟩

/-- Every matched pair must be an edge of the acceptability graph. -/
def IsAcceptable {α : Type*} (G : SimpleGraph α) (μ : Matching α) : Prop :=
  ∀ i, μ.val i = i ∨ G.Adj i (μ.val i)

/-- An acceptable pair blocks when both endpoints strictly prefer it to their assignments. -/
def IsBlockingPair {α : Type*} (G : SimpleGraph α) (rank : α → α → ℕ)
    (μ : Matching α) (i j : α) : Prop :=
  G.Adj i j ∧ μ.val i ≠ j ∧ rank i j < rank i (μ.val i) ∧ rank j i < rank j (μ.val j)

/-- A stable matching is acceptable and has no blocking pair. -/
def IsStable {α : Type*} (G : SimpleGraph α) (rank : α → α → ℕ)
    (μ : Matching α) : Prop :=
  IsAcceptable G μ ∧ ∀ i j, ¬ IsBlockingPair G rank μ i j

/-- The offsets $1,2,-1,-2$ in the cyclic group with $n+5$ vertices. -/
def offset (n : ℕ) : Fin 4 → Fin (n + 5) :=
  ![⟨1, by omega⟩, ⟨2, by omega⟩, ⟨n + 4, by omega⟩, ⟨n + 3, by omega⟩]

/-- The four neighbor offsets are distinct at every permitted market size. -/
theorem offset_injective (n : ℕ) : Function.Injective (offset n) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [offset, Fin.ext_iff]

/-- No neighbor offset is zero. -/
theorem offset_ne_zero (n : ℕ) (s : Fin 4) : offset n s ≠ 0 := by
  fin_cases s <;> simp [offset, Fin.ext_iff]

/-- The neighborhood contains the reverse of every offset. -/
theorem exists_offset_neg (n : ℕ) (s : Fin 4) : ∃ t, offset n t = -(offset n s) := by
  fin_cases s
  · refine ⟨2, ?_⟩
    apply Fin.ext
    simp [offset, Fin.neg_def, Nat.mod_eq_of_lt (show n + 4 < n + 5 by omega)]
  · refine ⟨3, ?_⟩
    apply Fin.ext
    simp [offset, Fin.neg_def, Nat.mod_eq_of_lt (show n + 3 < n + 5 by omega)]
  · refine ⟨0, ?_⟩
    apply Fin.ext
    simp [offset, Fin.neg_def]
  · refine ⟨1, ?_⟩
    apply Fin.ext
    have h := Nat.mod_eq_of_lt (show 2 < n + 5 by omega)
    simpa [offset, Fin.neg_def] using h.symm

/-- Edges join agents at cyclic distance one or two. -/
def ring (n : ℕ) : SimpleGraph (Fin (n + 5)) where
  Adj x y := ∃ s, y = x + offset n s
  symm := ⟨by
    intro x y ⟨s, hs⟩
    obtain ⟨t, ht⟩ := exists_offset_neg n s
    exact ⟨t, by simp [hs, ht]⟩⟩
  loopless := ⟨by
    intro x ⟨s, hs⟩
    apply offset_ne_zero n s
    apply add_left_cancel (a := x)
    simpa using hs.symm⟩

/-- A profile assigns each vertex a permutation of the four neighbor labels, as ranks. -/
abbrev Profile (n : ℕ) := Fin (n + 5) → Equiv.Perm (Fin 4)

/-- Neighbor ranks run from zero to three; being single has rank four.
Values on other non-neighbors are also four and are ignored by acceptability. -/
noncomputable def rank {n : ℕ} (p : Profile n) (x y : Fin (n + 5)) : ℕ :=
  if h : ∃ s, y = x + offset n s then (p x (Classical.choose h)).val else 4

/-- A listed neighbor receives its prescribed rank. -/
theorem rank_neighbor {n : ℕ} (p : Profile n) (x : Fin (n + 5)) (s : Fin 4) :
    rank p x (x + offset n s) = (p x s).val := by
  have h : ∃ t, x + offset n s = x + offset n t := ⟨s, rfl⟩
  rw [rank, dif_pos h]
  have he : Classical.choose h = s :=
    offset_injective n (add_left_cancel (Classical.choose_spec h).symm)
  rw [he]

/-- Being single has rank four. -/
theorem rank_self {n : ℕ} (p : Profile n) (x : Fin (n + 5)) : rank p x x = 4 := by
  have h : ¬ ∃ s, x = x + offset n s := (ring n).irrefl
  rw [rank, dif_neg h]

/-- Every neighbor is preferable to being single. -/
theorem rank_neighbor_lt_self {n : ℕ} (p : Profile n) (x : Fin (n + 5)) (s : Fin 4) :
    rank p x (x + offset n s) < rank p x x := by
  rw [rank_neighbor, rank_self]
  exact (p x s).isLt

/-- A profile admits an acceptable stable matching, possibly with single agents. -/
def HasStableMatching {n : ℕ} (p : Profile n) : Prop :=
  ∃ μ : Matching (Fin (n + 5)), IsStable (ring n) (rank p) μ

/-- Probability of admitting a stable matching under independent uniform neighbor rankings.
Uniformity on the finite profile type is the product of the uniform laws on its lists. -/
noncomputable def solutionProbability (n : ℕ) : ℝ := by
  classical
  exact (Fintype.card {p : Profile n // HasStableMatching p} : ℝ) /
    Fintype.card (Profile n)

/-- Each of the $n+5$ agents independently chooses one of $24$ strict neighbor rankings. -/
theorem card_profile (n : ℕ) : Fintype.card (Profile n) = 24 ^ (n + 5) := by
  simp [Profile, Fintype.card_perm, Nat.factorial]


end D5.S3.Combinatorics.Graph.Roommates.SourceModel
