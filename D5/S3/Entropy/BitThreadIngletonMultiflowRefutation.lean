/- GID: D5/S3/Entropy/BitThreadIngletonMultiflowRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/BitThreadIngletonMultiflowRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.claim; result=D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.result; claim=D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.claim
   digest: Star Ingleton bit-thread combination refutation on a capacitated 2-graph star. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- The definitions below use `i < j` as the single representative of each
   unordered boundary pair. -/
set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Entropy.BitThreadIngletonMultiflowRefutation

def cutValue {V : Type} [Fintype V] [DecidableEq V]
    (cap : V → V → ℝ) (W : Finset V) : ℝ :=
  ∑ u : V, ∑ v : V, if u ∈ W ∧ v ∉ W then cap u v else 0

def admissibleCuts {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
    (b : Fin k ↪ V) (I : Finset (Fin k)) : Finset (Finset V) :=
  Finset.univ.filter (fun W => ∀ i, b i ∈ W ↔ i ∈ I)

noncomputable def minCut {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
    (cap : V → V → ℝ) (b : Fin k ↪ V) (I : Finset (Fin k)) : ℝ :=
  (admissibleCuts b I).image (cutValue cap) |>.min' (by
    classical
    refine ⟨cutValue cap (Finset.image b I), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨Finset.image b I, ?_, rfl⟩
    simp [admissibleCuts, Finset.mem_image])

def IsMultiflow {V : Type} [Fintype V] [DecidableEq V]
    {k : ℕ} (cap : V → V → ℝ) (b : Fin k ↪ V)
    (f : Fin k → Fin k → V → V → ℝ) (n : Fin k → Fin k → ℝ) : Prop :=
  (∀ i j u v, i < j → f i j u v = -f i j v u) ∧
  (∀ i j u, i < j → u ≠ b i → u ≠ b j → ∑ v : V, f i j u v = 0) ∧
  (∀ i j, i < j → 0 ≤ n i j ∧
    (∑ v : V, f i j (b i) v = n i j) ∧
    (∑ v : V, f i j (b j) v = -n i j)) ∧
  (∀ u v, (∑ i : Fin k, ∑ j : Fin k,
    if i < j then |f i j u v| else 0) ≤ cap u v)

def subflow {k : ℕ} (n : Fin k → Fin k → ℝ) (I : Finset (Fin k)) : ℝ :=
  ∑ i ∈ I, ∑ j : Fin k, if j ∉ I then if i < j then n i j else n j i else 0

def IsMaxMultiflow {V : Type} [Fintype V] [DecidableEq V]
    {k : ℕ} (cap : V → V → ℝ) (b : Fin k ↪ V)
    (f : Fin k → Fin k → V → V → ℝ) (n : Fin k → Fin k → ℝ) : Prop :=
  IsMultiflow cap b f n ∧ ∀ i, subflow n {i} = minCut cap b {i}

def combo {k : ℕ} (α : Finset (Fin k) → ℝ) (X : Finset (Fin k) → ℝ) : ℝ :=
  ∑ I : Finset (Fin k), α I * X I

def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (k : ℕ)
    (cap : V → V → ℝ) (b : Fin k ↪ V) (α : Finset (Fin k) → ℝ),
    (∀ u v, cap u v = cap v u) →
    (∀ u, cap u u = 0) →
    (∀ u v, 0 ≤ cap u v) →
    (∀ f n, IsMultiflow cap b f n → combo α (subflow n) ≥ 0) →
    (∃ f n, IsMultiflow cap b f n ∧ combo α (subflow n) ≠ 0) →
    ∀ f n, IsMaxMultiflow cap b f n →
      combo α (minCut cap b) = combo α (subflow n)

private def starBoundary : Fin 5 ↪ Fin 6 :=
  ⟨Fin.castSucc, by intro a c h; exact Fin.castSucc_injective 5 h⟩

private def starCapacity (u v : Fin 6) : ℝ :=
  if u = 5 then if v.val < 4 then 1 else if v = 4 then 2 else 0
  else if v = 5 then if u.val < 4 then 1 else if u = 4 then 2 else 0 else 0

private def starWeight (I : Finset (Fin 5)) : ℝ :=
  ∑ i : Fin 5, if i ∈ I then (if i.val < 4 then 1 else 2) else 0

private def ingletonCoefficient (I : Finset (Fin 5)) : ℝ :=
  if I = {0, 1} then 1 else if I = {0, 2} then 1 else if I = {0, 3} then 1
  else if I = {1, 2} then 1 else if I = {1, 3} then 1
  else if I = {0} then -1 else if I = {1} then -1
  else if I = {2, 3} then -1 else if I = {0, 1, 2} then -1
  else if I = {0, 1, 3} then -1 else 0

private def witnessThreads (i j : Fin 5) : ℝ :=
  if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) then 1 else 0

private def pathFlow (i j : Fin 5) (u v : Fin 6) : ℝ :=
  if u = starBoundary i ∧ v = 5 then 1
  else if u = 5 ∧ v = starBoundary i then -1
  else if u = 5 ∧ v = starBoundary j then 1
  else if u = starBoundary j ∧ v = 5 then -1 else 0

private def witnessFlow (i j : Fin 5) (u v : Fin 6) : ℝ :=
  witnessThreads i j * pathFlow i j u v

private lemma combo_identity :
    ∀ n : Fin 5 → Fin 5 → ℝ,
      combo ingletonCoefficient (subflow n) = 2 * n 0 1 + 2 * n 2 3 := by sorry

private lemma star_cut_values :
    ∀ I : Finset (Fin 5), minCut starCapacity starBoundary I =
      min (starWeight I) (6 - starWeight I) := by sorry

private lemma witness_is_multiflow :
    IsMultiflow starCapacity starBoundary witnessFlow witnessThreads := by sorry

private lemma witness_max :
    IsMaxMultiflow starCapacity starBoundary witnessFlow witnessThreads := by sorry

private lemma star_min_combo :
    combo ingletonCoefficient (minCut starCapacity starBoundary) = 0 := by sorry

private lemma star_witness_combo :
    combo ingletonCoefficient (subflow witnessThreads) = 2 := by sorry

private lemma star_nonnegative :
    ∀ f n, IsMultiflow starCapacity starBoundary f n →
      combo ingletonCoefficient (subflow n) ≥ 0 := by sorry

theorem result : ¬ claim := by
  intro h
  have hnonneg := star_nonnegative
  have hex : ∃ f n, IsMultiflow starCapacity starBoundary f n ∧
      combo ingletonCoefficient (subflow n) ≠ 0 :=
    ⟨witnessFlow, witnessThreads, witness_is_multiflow, by norm_num [star_witness_combo]⟩
  have heq := h (Fin 6) 5 starCapacity starBoundary ingletonCoefficient
    (by sorry) (by sorry) (by sorry) hnonneg hex witnessFlow witnessThreads witness_max
  rw [star_min_combo, star_witness_combo] at heq
  norm_num at heq

end D5.S3.Entropy.BitThreadIngletonMultiflowRefutation
