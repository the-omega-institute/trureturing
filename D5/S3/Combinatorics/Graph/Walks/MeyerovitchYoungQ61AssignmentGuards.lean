/- GID: D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice.Fold]
   utility: none
   digest: Exact assignment guards and potential bounds for finite min-plus walks. -/
import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete
import Mathlib.Data.Finset.Lattice.Fold

/-!
For the offline complete-Bob graph game of Meyerovitch–Young (equation (6)
and Question 6.1), the endpoint recurrence starts at zero and the least final
coordinate gives the free-endpoint payoff of the fixed word.

In sum-of-scores units, every chosen assignment bounds the one-step increment,
with equality exactly on its closed difference guards. On this guard the
update acts on differences by a permutation and offsets. Along a legal Alice
walk, supplied edge caps and a vertex potential give a telescoping bound whose
equality tests the scores reached by the actual recurrence. Over an ordered
field, a finite system of difference guards that implies a spread bound
admits a complete matrix realizing the specified affine rule on its guard.

These finite certificates correspond to parts of Section 1 of the research
note `q61-three-state-assignment-threshold.txt`.
-/

namespace Q61AssignmentGuards

open Maths MeyerovitchYoungQ61Complete
open scoped BigOperators

noncomputable section

variable {W V E K : Type*} [Fintype W] [Nonempty W]

section OrderedRing

variable [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The min-plus update on the complete Bob graph, with sources indexing rows. -/
def endpointUpdate (M : Matrix W W K) (x : W → K) (j : W) : K :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => x i + M i j)

theorem endpointUpdate_le (M : Matrix W W K) (x : W → K) (i j : W) :
    endpointUpdate M x j ≤ x i + M i j := by
  unfold endpointUpdate
  exact Finset.inf'_le (fun k => x k + M k j) (Finset.mem_univ i)

/-- Endpoint scores after an edge word, from any initial score vector. -/
def endpointScores (M : E → Matrix W W K) (x : W → K) (a : List E) : W → K :=
  a.foldl (fun q e => endpointUpdate (M e) q) x

theorem endpointScores_snoc (M : E → Matrix W W K) (x : W → K) (a : List E) (e : E) :
    endpointScores M x (a ++ [e]) = endpointUpdate (M e) (endpointScores M x a) := by
  simp [endpointScores, List.foldl_append]

private theorem wordCost_concat (M : E → Matrix W W K) (a : List E) (e : E)
    {s i j : W} (p : (completeGraph W).Walk s i) (hlen : p.length = a.length) :
    wordCost (matrixCost M) (a ++ [e]) (p.concat (i, j) rfl).edges =
      wordCost (matrixCost M) a p.edges + M e i j := by
  erw [EdgeGraph.Walk.edges_concat]
  rw [wordCost_append _ (by simpa using hlen.symm)]
  simp [wordCost, matrixCost]

/-- At zero initial scores, each coordinate is the attained minimum over
complete Bob walks ending at that coordinate. -/
theorem endpointScores_spec (M : E → Matrix W W K) (a : List E) (j : W) :
    (∃ s, ∃ p : (completeGraph W).Walk s j, p.length = a.length ∧
      wordCost (matrixCost M) a p.edges = endpointScores M (fun _ => 0) a j) ∧
    ∀ s (p : (completeGraph W).Walk s j), p.length = a.length →
      endpointScores M (fun _ => 0) a j ≤ wordCost (matrixCost M) a p.edges := by
  induction a using List.reverseRecOn generalizing j with
  | nil =>
    exact ⟨⟨j, .nil, rfl, rfl⟩, fun s p h => by cases p <;> simp_all [endpointScores, wordCost]⟩
  | append_singleton a e ih =>
    rw [endpointScores_snoc]
    constructor
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := W))
        (fun i => endpointScores M (fun _ => 0) a i + M e i j)
      change endpointUpdate (M e) (endpointScores M (fun _ => 0) a) j =
        endpointScores M (fun _ => 0) a i + M e i j at hi
      obtain ⟨s, p, hp, hcost⟩ := (ih i).1
      exact ⟨s, p.concat (i, j) rfl, by simp [hp],
        (wordCost_concat M a e p hp).trans (by rw [hcost, hi])⟩
    · intro s p hlen
      cases p with
      | nil => simp at hlen
      | @concat i p f hf =>
        rcases f with ⟨i', j'⟩
        change i' = i at hf
        subst i'
        have hp : p.length = a.length := by simpa using hlen
        erw [wordCost_concat M a e p hp]
        exact (endpointUpdate_le _ _ i j').trans (add_le_add ((ih i).2 s p hp) le_rfl)

/-- The physical free-endpoint payoff of the repository is the least final score. -/
theorem matrixMinimum_eq_inf (M : E → Matrix W W K) (a : List E) :
    matrixMinimum M a = Finset.univ.inf' Finset.univ_nonempty
      (endpointScores M (fun _ => 0) a) := by
  obtain ⟨⟨b, hb, hlen, hcost⟩, hmin⟩ := matrixMinimum_spec M a
  apply le_antisymm
  · apply Finset.le_inf' Finset.univ_nonempty _
    intro j _
    obtain ⟨s, p, hp, hscore⟩ := (endpointScores_spec M a j).1
    exact (hmin p.edges ⟨s, j, p, rfl⟩ (by simpa using hp)).trans_eq hscore
  · obtain ⟨s, j, p, rfl⟩ := hb
    rw [← hcost]
    exact (Finset.inf'_le _ (Finset.mem_univ j)).trans
      ((endpointScores_spec M a j).2 s p (by simpa using hlen))

def scoreIncrement (M : Matrix W W K) (x : W → K) : K :=
  (∑ j, endpointUpdate M x j) - ∑ i, x i

/-- The permutation chooses one source for each destination column. -/
def assignmentCost (M : Matrix W W K) (σ : Equiv.Perm W) : K :=
  ∑ j, M (σ j) j

def AssignmentGuards (M : Matrix W W K) (x : W → K) (σ : Equiv.Perm W) : Prop :=
  ∀ j i, i ≠ σ j → x (σ j) - x i ≤ M i j - M (σ j) j

theorem endpointUpdate_eq_assignment_iff (M : Matrix W W K) (x : W → K)
    (σ : Equiv.Perm W) :
    (∀ j, endpointUpdate M x j = x (σ j) + M (σ j) j) ↔ AssignmentGuards M x σ := by
  constructor
  · intro h j i _
    have hi := endpointUpdate_le M x i j
    rw [h j] at hi
    linarith only [hi]
  · intro h j
    apply le_antisymm (endpointUpdate_le M x (σ j) j)
    unfold endpointUpdate
    apply Finset.le_inf' Finset.univ_nonempty _
    intro i _
    by_cases hi : i = σ j
    · subst i
      exact le_rfl
    · linarith only [h j i hi]

/-- Every permutation bounds the total score increment. Equality keeps every
assigned candidate at its column minimum, including ties. -/
theorem assignment_certificate (M : Matrix W W K) (x : W → K) (σ : Equiv.Perm W) :
    scoreIncrement M x ≤ assignmentCost M σ ∧
      (scoreIncrement M x = assignmentCost M σ ↔ AssignmentGuards M x σ) := by
  have hcol (j : W) (_ : j ∈ (Finset.univ : Finset W)) :
      endpointUpdate M x j ≤ x (σ j) + M (σ j) j := endpointUpdate_le M x (σ j) j
  have hsum : (∑ j, (x (σ j) + M (σ j) j)) = (∑ i, x i) + assignmentCost M σ := by
    simp only [Finset.sum_add_distrib, _root_.Equiv.sum_comp σ x, assignmentCost]
  refine ⟨?_, ?_⟩
  · have hle := Finset.sum_le_sum hcol
    rw [hsum] at hle
    unfold scoreIncrement
    linarith only [hle]
  · rw [← endpointUpdate_eq_assignment_iff M x σ]
    have heq := Finset.sum_eq_sum_iff_of_le hcol
    constructor
    · intro h
      unfold scoreIncrement at h
      have h' : (∑ j, endpointUpdate M x j) = ∑ j, (x (σ j) + M (σ j) j) := by
        rw [hsum]
        linarith only [h]
      exact fun j => heq.mp h' j (Finset.mem_univ j)
    · intro h
      have h' := heq.mpr (fun j _ => h j)
      rw [hsum] at h'
      unfold scoreIncrement
      linarith only [h']

/-- A tight edge acts on differences by the assigned permutation and offsets. -/
theorem endpointUpdate_difference (M : Matrix W W K) (x : W → K) (σ : Equiv.Perm W)
    (h : AssignmentGuards M x σ) (o j : W) :
    endpointUpdate M x j - endpointUpdate M x o =
      (x (σ j) - x (σ o)) + (M (σ j) j - M (σ o) o) := by
  have hm := (endpointUpdate_eq_assignment_iff M x σ).mpr h
  rw [hm j, hm o]
  ring

/-- Every edge saturates its potential-adjusted bound and its guards hold
at the actual score vector reached by its prefix. -/
def TightAlong (G : EdgeGraph V E) (M : E → Matrix W W K) (σ : E → Equiv.Perm W)
    (cap : E → K) (H : V → K) (x : W → K) {s : V} : {t : V} → G.Walk s t → Prop
  | _, .nil => True
  | _, .concat p e _ =>
    TightAlong G M σ cap H x p ∧
      assignmentCost (M e) (σ e) = cap e + H (G.source e) - H (G.target e) ∧
      AssignmentGuards (M e) (endpointScores M x p.edges) (σ e)

/-- Along a legal Alice walk the potential telescopes, and equality is exactly
tightness at every physical prefix. -/
theorem walk_assignment_certificate (G : EdgeGraph V E) (M : E → Matrix W W K)
    (σ : E → Equiv.Perm W) (cap : E → K) (H : V → K)
    (hcap : ∀ e, assignmentCost (M e) (σ e) ≤ cap e + H (G.source e) - H (G.target e))
    (x : W → K) {s t : V} (p : G.Walk s t) :
    let gain := (∑ j, endpointScores M x p.edges j) - ∑ j, x j
    let bound := (p.edges.map cap).sum + H s - H t
    gain ≤ bound ∧ (gain = bound ↔ TightAlong G M σ cap H x p) := by
  induction p with
  | nil => simp [EdgeGraph.Walk.edges, endpointScores, TightAlong]
  | @concat u p e he ih =>
    dsimp only at ih ⊢
    have hprefix := ih.1
    have hlocal := assignment_certificate (M e) (endpointScores M x p.edges) (σ e)
    have hstep := hlocal.1
    unfold scoreIncrement at hstep
    have hedge := hcap e
    rw [he] at hedge
    simp only [EdgeGraph.Walk.edges_concat, endpointScores_snoc, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      TightAlong]
    refine ⟨by linarith only [hprefix, hstep, hedge], ?_⟩
    constructor
    · intro h
      refine ⟨ih.2.mp ?_, ?_, hlocal.2.mp ?_⟩
      · linarith only [h, hprefix, hstep, hedge]
      · rw [he]
        linarith only [h, hprefix, hstep, hedge]
      · unfold scoreIncrement
        linarith only [h, hprefix, hstep, hedge]
    · rintro ⟨hp, hc, hg⟩
      have hp' := ih.2.mpr hp
      have hg' := hlocal.2.mpr hg
      unfold scoreIncrement at hg'
      rw [he] at hc
      linarith only [hp', hc, hg']

end OrderedRing

section OrderedField

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Put the centered offset on the assigned entry and use each difference
bound as the corresponding off-assignment excess. -/
def guardMatrix (σ : Equiv.Perm W) (η : W → K) (c : W → W → K) : Matrix W W K := by
  classical
  let μ := (∑ j, η j) / (Fintype.card W : K)
  exact Matrix.of fun i j => η j - μ + (if i = σ j then 0 else c i (σ j))

theorem guardMatrix_spec (σ : Equiv.Perm W) (η : W → K) (c : W → W → K) :
    let M := guardMatrix σ η c
    assignmentCost M σ = 0 ∧ ∀ x : W → K,
      scoreIncrement M x ≤ 0 ∧
      (scoreIncrement M x = 0 ↔ ∀ i k, i ≠ k → x k - x i ≤ c i k) ∧
      ((∀ i k, i ≠ k → x k - x i ≤ c i k) → ∀ o j,
        endpointUpdate M x j - endpointUpdate M x o =
          (x (σ j) - x (σ o)) + (η j - η o)) := by
  classical
  let M := guardMatrix σ η c
  let μ := (∑ j, η j) / (Fintype.card W : K)
  change assignmentCost M σ = 0 ∧ _
  have hdiag (j : W) : M (σ j) j = η j - μ := by
    simp [M, guardMatrix, Matrix.of_apply, μ]
  have hoff (i j : W) (h : i ≠ σ j) : M i j - M (σ j) j = c i (σ j) := by
    have hentry : M i j = η j - μ + c i (σ j) := by
      simp [M, guardMatrix, Matrix.of_apply, μ, h]
    rw [hentry, hdiag j]
    ring
  have hn : (Fintype.card W : K) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := W)).ne'
  have hcost : assignmentCost M σ = 0 := by
    simp only [assignmentCost, hdiag, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, μ, mul_div_cancel₀ _ hn, sub_self]
  refine ⟨hcost, fun x => ?_⟩
  have hguards : AssignmentGuards M x σ ↔ ∀ i k, i ≠ k → x k - x i ≤ c i k := by
    constructor
    · intro h i k hik
      obtain ⟨j, rfl⟩ := σ.surjective k
      simpa only [hoff i j hik] using h j i hik
    · intro h j i hij
      rw [hoff i j hij]
      exact h i (σ j) hij
  have h := assignment_certificate M x σ
  rw [hcost, hguards] at h
  refine ⟨h.1, h.2, fun hx o j => ?_⟩
  rw [endpointUpdate_difference M x σ (hguards.mpr hx), hdiag j, hdiag o]
  ring

/-- Realize a bounded finite system of closed difference inequalities between
distinct coordinates. Repeated bounds take their minimum and missing pairs
receive the redundant spread bound. The offset may be given in any normalization. -/
theorem exists_matrix_realizing_bounded_guards {I : Type*} [Fintype I]
    (src dst : I → W) (weight : I → K) (hne : ∀ g, src g ≠ dst g)
    (B : K) (hB : ∀ x : W → K, (∀ g, x (dst g) - x (src g) ≤ weight g) →
      ∀ i k, i ≠ k → x k - x i ≤ B)
    (σ : Equiv.Perm W) (η : W → K) :
    ∃ M : Matrix W W K, assignmentCost M σ = 0 ∧ ∀ x : W → K,
      scoreIncrement M x ≤ 0 ∧
      (scoreIncrement M x = 0 ↔ ∀ g, x (dst g) - x (src g) ≤ weight g) ∧
      ((∀ g, x (dst g) - x (src g) ≤ weight g) → ∀ o j,
        endpointUpdate M x j - endpointUpdate M x o =
          (x (σ j) - x (σ o)) + (η j - η o)) := by
  classical
  let pair (i k : W) := Finset.univ.filter (fun g => src g = i ∧ dst g = k)
  let c (i k : W) := if h : (pair i k).Nonempty then (pair i k).inf' h weight else B
  have hcomplete (x : W → K) :
      (∀ i k, i ≠ k → x k - x i ≤ c i k) ↔ ∀ g, x (dst g) - x (src g) ≤ weight g := by
    constructor
    · intro hx g
      have hg : g ∈ pair (src g) (dst g) := by simp [pair]
      have hp : (pair (src g) (dst g)).Nonempty := ⟨g, hg⟩
      have hc : c (src g) (dst g) ≤ weight g := by
        simpa only [c, dite_eq_left hp] using Finset.inf'_le weight hg
      exact (hx _ _ (hne g)).trans hc
    · intro hx i k hik
      by_cases hp : (pair i k).Nonempty
      · simp only [c, dite_eq_left hp]
        apply Finset.le_inf' hp _
        intro g hg
        obtain ⟨hs, ht⟩ := (Finset.mem_filter.mp hg).2
        simpa only [hs, ht] using hx g
      · simpa only [c, dite_eq_right hp] using hB x hx i k hik
  obtain ⟨hcost, hspec⟩ := guardMatrix_spec σ η c
  refine ⟨guardMatrix σ η c, hcost, fun x => ?_⟩
  obtain ⟨hle, heq, hupdate⟩ := hspec x
  exact ⟨hle, heq.trans (hcomplete x), fun hx => hupdate ((hcomplete x).mpr hx)⟩

end OrderedField

end

end Q61AssignmentGuards
