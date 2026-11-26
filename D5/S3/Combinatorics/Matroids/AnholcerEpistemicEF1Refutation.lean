/- GID: D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.claim; result=D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.result; claim=D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.claim
   digest: Two heterogeneous two-colorable matroids refute Conjecture 4 on four goods. -/

/-
proof_shape: bind-only for result and all six private theorems, by finite decision,
instantiation, projection and normalization. No escape content is claimed.
escape_witness: none.
admission_basis: open-problem-resolution (#25693; Refuted).
Direct frozen dependencies: none, for every declaration.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).

Private theorem consumers:
* matroids_indep_iff: coloring_independent, feasible_rigid.
* matroids_ground: result.
* coloring_independent: two_colorable.
* two_colorable: result.
* feasible_rigid: feasible_not_fair.
* feasible_not_fair: result.
-/
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Tactic.FinCases
import Mathlib.Data.ENat.Lattice
import Mathlib.Basic.NNReal.Defs

/-!
Definitions for Conjecture 4 of Anholcer, Bartkowiak, Bosek and Grytczuk,
Epistemic fair division of independence structures, arXiv:2606.11494v1, Section 5.
Fin m enumerates E and Fin n enumerates the agents. Matroids and independence are
Mathlib's Matroid and Matroid.Indep; the claim requires every ground set to be E.
The type aliases in #25693 are expanded to their underlying function types.
The conjecture uses additive nonnegative valuations and ordinary EF1.
-/

namespace D5.S3.Combinatorics.Matroids.AnholcerEpistemicEF1Refutation

open scoped BigOperators

/-- Pairwise disjoint bundles whose union is the whole ground set. -/
def IsPartition {m n : ℕ} (X : (Fin n → Finset (Fin m))) : Prop :=
  (∀ i j : Fin n, i ≠ j → Disjoint (X i) (X j)) ∧
    (∀ e : Fin m, ∃ i : Fin n, e ∈ X i)

/-- A partition into independent sets of a single matroid. -/
def IndependentPartition {m q : ℕ} (M : Matroid (Fin m))
    (X : (Fin q → Finset (Fin m))) : Prop :=
  IsPartition X ∧ ∀ i : Fin q, M.Indep (X i : Set (Fin m))

/-- Least number of independent parts; infinity if no finite coloring exists. -/
noncomputable def chromaticNumber {m : ℕ} (M : Matroid (Fin m)) : ℕ∞ :=
  sInf {c : ℕ∞ | ∃ q : ℕ, c = (q : ℕ∞) ∧
    ∃ X : (Fin q → Finset (Fin m)), IndependentPartition M X}

/-- Each agent's bundle must be independent in that agent's own matroid. -/
def Feasible {m n : ℕ} (M : Fin n → Matroid (Fin m))
    (X : (Fin n → Finset (Fin m))) : Prop :=
  IsPartition X ∧ ∀ i : Fin n, (M i).Indep (X i : Set (Fin m))

/-- The source's additive extension v_i(S) = sum of its singleton values. -/
def value {m n : ℕ} (w : (Fin n → Fin m → NNReal)) (i : Fin n)
    (S : Finset (Fin m)) : NNReal := ∑ e ∈ S, w i e

/-- Source goods-EF1, including its explicit empty-bundle convention. -/
def GoodsEF1 {m n : ℕ} (w : (Fin n → Fin m → NNReal)) (X : (Fin n → Finset (Fin m))) : Prop :=
  ∀ i j : Fin n, X j = ∅ ∨
    ∃ g ∈ X j, value w i (X j \ {g}) ≤ value w i (X i)

/-- Source chores-EF1: delete a chore from the envying agent's own bundle. -/
def ChoresEF1 {m n : ℕ} (w : (Fin n → Fin m → NNReal)) (X : (Fin n → Finset (Fin m))) : Prop :=
  ∀ i j : Fin n, i ≠ j → X i = ∅ ∨
    ∃ c ∈ X i, value w i (X i \ {c}) ≤ value w i (X j)

/-- Conjecture 4 asserts existence separately for goods and for chores. -/
def claim : Prop :=
  ∀ m n : ℕ, 0 < n →
    ∀ M : Fin n → Matroid (Fin m),
      (∀ i : Fin n, (M i).E = Set.univ) →
      (∀ i : Fin n, chromaticNumber (M i) ≤ (n : ℕ∞)) →
      ∀ w : (Fin n → Fin m → NNReal),
        (∃ X : (Fin n → Finset (Fin m)), Feasible M X ∧ GoodsEF1 w X) ∧
        (∃ X : (Fin n → Finset (Fin m)), Feasible M X ∧ ChoresEF1 w X)

end D5.S3.Combinatorics.Matroids.AnholcerEpistemicEF1Refutation

namespace D5.S3.Combinatorics.Matroids.AnholcerEpistemicEF1Refutation

open scoped BigOperators

/-- The two block maps, in the source's order relabeled by Fin 4. -/
private def block (i : Fin 2) (e : Fin 4) : Fin 2 :=
  if i = 0 then (if e.val < 2 then 0 else 1)
  else (if e = 1 ∨ e = 2 then 0 else 1)

/-- Capacity one in each fiber of the block map. -/
private def matroids (i : Fin 2) : Matroid (Fin 4) :=
  (Matroid.freeOn (Set.univ : Set (Fin 2))).comap (block i)

private def oddBundle : Finset (Fin 4) := {0, 2}
private def evenBundle : Finset (Fin 4) := {1, 3}

private def parityAllocation : (Fin 2 → Finset (Fin 4)) :=
  fun i => if i = 0 then oddBundle else evenBundle

private def swappedAllocation : (Fin 2 → Finset (Fin 4)) :=
  fun i => if i = 0 then evenBundle else oddBundle

private def weights : (Fin 2 → Fin 4 → NNReal) :=
  fun _ e => if e = 0 ∨ e = 2 then 3 else 1


set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem matroids_indep_iff (i : Fin 2) (S : Finset (Fin 4)) :
    (matroids i).Indep (S : Set (Fin 4)) ↔ Set.InjOn (block i) (S : Set (Fin 4)) := by
  simp [matroids]

private theorem matroids_ground (i : Fin 2) : (matroids i).E = Set.univ := by
  exact Set.eq_univ_of_univ_subset fun ⦃a⦄ ha => ha

private theorem coloring_independent (i : Fin 2) :
    IndependentPartition (matroids i) parityAllocation := by
  refine ⟨by unfold IsPartition; decide, ?_⟩
  intro j
  rw [matroids_indep_iff]
  fin_cases i <;> fin_cases j <;> decide

private theorem two_colorable (i : Fin 2) :
    chromaticNumber (matroids i) ≤ (2 : ℕ∞) := by
  exact sInf_le ⟨2, rfl, parityAllocation, coloring_independent i⟩

private theorem feasible_rigid (X : (Fin 2 → Finset (Fin 4))) (h : Feasible matroids X) :
    X = parityAllocation ∨ X = swappedAllocation := by
  have certificate : ∀ (S T : Finset (Fin 4)),
      Disjoint S T →
      (∀ e : Fin 4, e ∈ S ∨ e ∈ T) →
      Set.InjOn (block 0) (S : Set (Fin 4)) →
      Set.InjOn (block 1) (T : Set (Fin 4)) →
      (S = oddBundle ∧ T = evenBundle) ∨
      (S = evenBundle ∧ T = oddBundle) := by decide
  have coverage : ∀ e : Fin 4, e ∈ X 0 ∨ e ∈ X 1 :=
    fun e => Fin.exists_fin_two.mp (h.1.2 e)
  have h0 := (matroids_indep_iff 0 (X 0)).1 (h.2 0)
  have h1 := (matroids_indep_iff 1 (X 1)).1 (h.2 1)
  rcases certificate (X 0) (X 1) (h.1.1 0 1 (by decide)) coverage h0 h1 with hp | hp
  · left
    funext i
    fin_cases i
    · simpa [parityAllocation] using hp.1
    · simpa [parityAllocation] using hp.2
  · right
    funext i
    fin_cases i
    · simpa [swappedAllocation] using hp.1
    · simpa [swappedAllocation] using hp.2

private theorem feasible_not_fair (X : (Fin 2 → Finset (Fin 4))) (h : Feasible matroids X) :
    ¬ GoodsEF1 weights X ∧ ¬ ChoresEF1 weights X := by
  rcases feasible_rigid X h with rfl | rfl
  · constructor
    · intro H
      have Hbad := H 1 0
      norm_num [parityAllocation, oddBundle, evenBundle, value, weights, Finset.sdiff_eq_filter,
        Finset.filter_insert, Finset.filter_singleton] at Hbad
    · intro H
      have Hbad := H 0 1 (by decide)
      norm_num [parityAllocation, oddBundle, evenBundle, value, weights, Finset.sdiff_eq_filter,
        Finset.filter_insert, Finset.filter_singleton] at Hbad
  · constructor
    · intro H
      have Hbad := H 0 1
      norm_num [swappedAllocation, oddBundle, evenBundle, value, weights, Finset.sdiff_eq_filter,
        Finset.filter_insert, Finset.filter_singleton] at Hbad
    · intro H
      have Hbad := H 1 0 (by decide)
      norm_num [swappedAllocation, oddBundle, evenBundle, value, weights, Finset.sdiff_eq_filter,
        Finset.filter_insert, Finset.filter_singleton] at Hbad

theorem result : ¬ claim := by
  intro hc
  obtain ⟨⟨X, hX, hEF⟩, _⟩ :=
    hc 4 2 (by decide) matroids matroids_ground two_colorable weights
  exact (feasible_not_fair X hX).1 hEF

end D5.S3.Combinatorics.Matroids.AnholcerEpistemicEF1Refutation
