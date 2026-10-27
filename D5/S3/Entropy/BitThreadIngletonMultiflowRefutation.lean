/- GID: D5/S3/Entropy/BitThreadIngletonMultiflowRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/BitThreadIngletonMultiflowRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.claim; result=D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.result; claim=D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.claim
   digest: Star Ingleton bit-thread combination refutation on a capacitated 2-graph star. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Pair flows are oriented from `i` to `j`, using `i < j` as the single
representative of each unordered boundary pair. -/
set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Entropy.BitThreadIngletonMultiflowRefutation

def cutValue {vtx : Type} [Fintype vtx] [DecidableEq vtx]
    (cap : vtx → vtx → ℝ) (w : Finset vtx) : ℝ :=
  ∑ u : vtx, ∑ v : vtx, if u ∈ w ∧ v ∉ w then cap u v else 0

def admissibleCuts {vtx : Type} [Fintype vtx] [DecidableEq vtx] {k : ℕ}
    (b : Fin k ↪ vtx) (s : Finset (Fin k)) : Finset (Finset vtx) :=
  Finset.univ.filter (fun w => ∀ i, b i ∈ w ↔ i ∈ s)

noncomputable def minCut {vtx : Type} [Fintype vtx] [DecidableEq vtx] {k : ℕ}
    (cap : vtx → vtx → ℝ) (b : Fin k ↪ vtx) (s : Finset (Fin k)) : ℝ :=
  (admissibleCuts b s).image (cutValue cap) |>.min' (by
    classical
    refine ⟨cutValue cap (Finset.image b s), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨Finset.image b s, ?_, rfl⟩
    delta admissibleCuts
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    constructor
    · intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      have hji := b.injective hji
      subst j
      exact hj
    · exact Finset.mem_image_of_mem b)

def IsMultiflow {vtx : Type} [Fintype vtx] [DecidableEq vtx]
    {k : ℕ} (cap : vtx → vtx → ℝ) (b : Fin k ↪ vtx)
    (f : Fin k → Fin k → vtx → vtx → ℝ) (n : Fin k → Fin k → ℝ) : Prop :=
  (∀ i j u v, i < j → f i j u v = -f i j v u) ∧
  (∀ i j u, i < j → u ≠ b i → u ≠ b j → ∑ v : vtx, f i j u v = 0) ∧
  (∀ i j, i < j → 0 ≤ n i j ∧
    (∑ v : vtx, f i j (b i) v = n i j) ∧
    (∑ v : vtx, f i j (b j) v = -n i j)) ∧
  (∀ u v, (∑ i : Fin k, ∑ j : Fin k,
    if i < j then |f i j u v| else 0) ≤ cap u v)

def subflow {k : ℕ} (n : Fin k → Fin k → ℝ) (s : Finset (Fin k)) : ℝ :=
  ∑ i ∈ s, ∑ j : Fin k, if j ∉ s then if i < j then n i j else n j i else 0

def IsMaxMultiflow {vtx : Type} [Fintype vtx] [DecidableEq vtx]
    {k : ℕ} (cap : vtx → vtx → ℝ) (b : Fin k ↪ vtx)
    (f : Fin k → Fin k → vtx → vtx → ℝ) (n : Fin k → Fin k → ℝ) : Prop :=
  IsMultiflow cap b f n ∧ ∀ i, subflow n {i} = minCut cap b {i}

def combo {k : ℕ} (α : Finset (Fin k) → ℝ) (x : Finset (Fin k) → ℝ) : ℝ :=
  ∑ s : Finset (Fin k), α s * x s

def claim : Prop :=
  ∀ (vtx : Type) [Fintype vtx] [DecidableEq vtx] (k : ℕ)
    (cap : vtx → vtx → ℝ) (b : Fin k ↪ vtx) (α : Finset (Fin k) → ℝ),
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
  (if I = {0, 1} then 1 else 0) + (if I = {0, 2} then 1 else 0) +
  (if I = {0, 3} then 1 else 0) + (if I = {1, 2} then 1 else 0) +
  (if I = {1, 3} then 1 else 0) - (if I = {0} then 1 else 0) -
  (if I = {1} then 1 else 0) - (if I = {2, 3} then 1 else 0) -
  (if I = {0, 1, 2} then 1 else 0) - (if I = {0, 1, 3} then 1 else 0)

private def witnessThreads (i j : Fin 5) : ℝ :=
  if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) then 1 else 0

private def pathFlow (i j : Fin 5) (u v : Fin 6) : ℝ :=
  if u = starBoundary i ∧ v = 5 then 1
  else if u = 5 ∧ v = starBoundary i then -1
  else if u = 5 ∧ v = starBoundary j then 1
  else if u = starBoundary j ∧ v = 5 then -1 else 0

private def witnessFlow (i j : Fin 5) (u v : Fin 6) : ℝ :=
  witnessThreads i j * pathFlow i j u v

private lemma ingleton_combo (x : Finset (Fin 5) → ℝ) :
    combo ingletonCoefficient x =
      x {0, 1} + x {0, 2} + x {0, 3} + x {1, 2} + x {1, 3} -
      x {0} - x {1} - x {2, 3} - x {0, 1, 2} - x {0, 1, 3} := by
  delta combo ingletonCoefficient
  simp only [add_mul, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private lemma combo_identity :
    ∀ n : Fin 5 → Fin 5 → ℝ,
      combo ingletonCoefficient (subflow n) = 2 * n 0 1 + 2 * n 2 3 := by
  intro n
  rw [ingleton_combo]
  delta subflow
  norm_num [Fin.sum_univ_succ]
  ring

private lemma star_weight_expand (I : Finset (Fin 5)) :
    starWeight I =
      (if 0 ∈ I then 1 else 0) + (if 1 ∈ I then 1 else 0) +
      (if 2 ∈ I then 1 else 0) + (if 3 ∈ I then 1 else 0) +
      (if 4 ∈ I then 2 else 0) := by
  delta starWeight
  simp only [Fin.sum_univ_succ]
  norm_num
  ring

private lemma star_cut (I : Finset (Fin 5)) (W : Finset (Fin 6))
    (h : ∀ i, starBoundary i ∈ W ↔ i ∈ I) :
    cutValue starCapacity W =
      if (5 : Fin 6) ∈ W then 6 - starWeight I else starWeight I := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  change (0 : Fin 6) ∈ W ↔ (0 : Fin 5) ∈ I at h0
  change (1 : Fin 6) ∈ W ↔ (1 : Fin 5) ∈ I at h1
  change (2 : Fin 6) ∈ W ↔ (2 : Fin 5) ∈ I at h2
  change (3 : Fin 6) ∈ W ↔ (3 : Fin 5) ∈ I at h3
  change (4 : Fin 6) ∈ W ↔ (4 : Fin 5) ∈ I at h4
  rw [star_weight_expand I]
  delta cutValue starCapacity
  by_cases hc : (5 : Fin 6) ∈ W
  · simp [hc, h0, h1, h2, h3, h4, Fin.sum_univ_succ]
    split_ifs <;> ring
  · simp [hc, h0, h1, h2, h3, h4, Fin.sum_univ_succ]
    split_ifs <;> ring

private lemma star_cut_values :
    ∀ I : Finset (Fin 5), minCut starCapacity starBoundary I =
      min (starWeight I) (6 - starWeight I) := by
  intro I
  classical
  have hb (i : Fin 5) : starBoundary i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have hi (i : Fin 5) : starBoundary i ∈ Finset.image starBoundary I ↔ i ∈ I := by
    constructor
    · intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      have hji := starBoundary.injective hji
      subst j
      exact hj
    · exact Finset.mem_image_of_mem starBoundary
  have hc : (5 : Fin 6) ∉ Finset.image starBoundary I := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact hb i hi
  have hio (i : Fin 5) :
      starBoundary i ∈ Finset.image starBoundary I ∪ {5} ↔ i ∈ I := by
    simp only [Finset.mem_union, Finset.mem_singleton, hb i, or_false, hi]
  have ha : Finset.image starBoundary I ∈ admissibleCuts starBoundary I := by
    delta admissibleCuts
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hao : Finset.image starBoundary I ∪ {5} ∈ admissibleCuts starBoundary I := by
    delta admissibleCuts
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hio⟩
  have hva := star_cut I (Finset.image starBoundary I) hi
  rw [ite_eq_right hc] at hva
  have hvao := star_cut I (Finset.image starBoundary I ∪ {5}) hio
  rw [ite_eq_left (Finset.mem_union_right _ (Finset.mem_singleton_self _))] at hvao
  delta minCut
  apply le_antisymm
  · apply le_min
    · rw [← hva]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_, ha, rfl⟩)
    · rw [← hvao]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_, hao, rfl⟩)
  · apply Finset.le_min'
    intro x hx
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hx
    have hv := star_cut I W (Finset.mem_filter.mp hW).2
    rw [hv]
    split_ifs
    · exact min_le_right _ _
    · exact min_le_left _ _

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
private lemma witness_is_multiflow :
    IsMultiflow starCapacity starBoundary witnessFlow witnessThreads := by
  have hb (i : Fin 5) : starBoundary i = i.castSucc := rfl
  delta IsMultiflow
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j u v hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals delta witnessFlow witnessThreads
    all_goals norm_num
    all_goals fin_cases u <;> fin_cases v <;> delta pathFlow
    all_goals norm_num [hb, Fin.ext_iff]
  · intro i j u hij hui huj
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals fin_cases u <;> norm_num [hb, Fin.ext_iff] at hui
    all_goals norm_num [hb, Fin.ext_iff] at huj
    all_goals simp only [Fin.sum_univ_succ]
    all_goals delta witnessFlow witnessThreads pathFlow
    all_goals norm_num [hb, Fin.ext_iff]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals simp only [Fin.sum_univ_succ]
    all_goals delta witnessFlow witnessThreads pathFlow
    all_goals norm_num [hb, Fin.ext_iff]
  · intro u v
    fin_cases u <;> fin_cases v <;>
      simp only [Fin.sum_univ_succ]
    all_goals delta witnessFlow witnessThreads pathFlow starCapacity
    all_goals norm_num [hb, Fin.ext_iff]

private lemma witness_max :
    IsMaxMultiflow starCapacity starBoundary witnessFlow witnessThreads := by
  refine ⟨witness_is_multiflow, ?_⟩
  intro i
  rw [star_cut_values]
  fin_cases i <;> delta subflow starWeight
  all_goals simp only [Fin.sum_univ_succ]
  all_goals delta witnessThreads
  all_goals norm_num

private lemma star_min_combo :
    combo ingletonCoefficient (minCut starCapacity starBoundary) = 0 := by
  rw [ingleton_combo]
  repeat rw [star_cut_values]
  delta starWeight
  simp only [Fin.sum_univ_succ]
  norm_num

private lemma star_witness_combo :
    combo ingletonCoefficient (subflow witnessThreads) = 2 := by
  rw [combo_identity]
  delta witnessThreads
  norm_num

private lemma star_nonnegative :
    ∀ f n, IsMultiflow starCapacity starBoundary f n →
      combo ingletonCoefficient (subflow n) ≥ 0 := by
  intro f n h
  rw [combo_identity]
  exact add_nonneg (mul_nonneg (by norm_num) (h.2.2.1 0 1 (by decide)).1)
    (mul_nonneg (by norm_num) (h.2.2.1 2 3 (by decide)).1)

private lemma star_symmetric : ∀ u v, starCapacity u v = starCapacity v u := by
  intro u v
  fin_cases u <;> fin_cases v <;> delta starCapacity
  all_goals norm_num

private lemma star_loopless : ∀ u, starCapacity u u = 0 := by
  intro u
  fin_cases u <;> delta starCapacity
  all_goals norm_num

private lemma star_capacity_nonnegative : ∀ u v, 0 ≤ starCapacity u v := by
  intro u v
  fin_cases u <;> fin_cases v <;> delta starCapacity
  all_goals norm_num

theorem result : ¬ claim := by
  intro h
  have hnonneg := star_nonnegative
  have hex : ∃ f n, IsMultiflow starCapacity starBoundary f n ∧
      combo ingletonCoefficient (subflow n) ≠ 0 :=
    ⟨witnessFlow, witnessThreads, witness_is_multiflow, by norm_num [star_witness_combo]⟩
  have heq := h (Fin 6) 5 starCapacity starBoundary ingletonCoefficient
    star_symmetric star_loopless star_capacity_nonnegative hnonneg hex
    witnessFlow witnessThreads witness_max
  rw [star_min_combo, star_witness_combo] at heq
  norm_num at heq


end D5.S3.Entropy.BitThreadIngletonMultiflowRefutation
