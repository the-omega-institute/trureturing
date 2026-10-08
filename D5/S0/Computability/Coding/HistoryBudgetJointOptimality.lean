/- GID: D5/S0/Computability/Coding/HistoryBudgetJointOptimality
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/HistoryBudgetJointOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-history rows have the same joint code optimum as an extreme iid law. -/

import D5.S0.Computability.Coding.HistoryTreeRelabeling

open scoped BigOperators ENNReal

namespace D5.S0.Computability.Coding.HistoryBudgetJointOptimality

open DepthBudgetIidGreedyOptimality HistoryTreeRelabeling PrefixFreeCode

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Every finite history has an independently allowed normalized row. -/
def Admissible (δ : ℝ) (q : List α → α → ℝ) : Prop :=
  ∀ h, (∀ a, δ ≤ q h a) ∧ ∑ a, q h a = 1

/-- Put all row mass above the lower bounds on one letter. -/
def extremeRow (δ : ℝ) (heavy a : α) : ℝ :=
  δ + if a = heavy then 1 - (Fintype.card α : ℝ) * δ else 0

/-- Choose an actual maximizing letter from the finite nonempty alphabet. -/
private noncomputable def bestLetter (V : α → ℝ) : α :=
  Classical.choose (Finset.exists_max_image Finset.univ V Finset.univ_nonempty)

private theorem best_letter_max (V : α → ℝ) (a : α) : V a ≤ V (bestLetter V) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ V
    Finset.univ_nonempty)).2 a (Finset.mem_univ a)

/-- Sum all rewards encountered through a fixed number of continuation edges. -/
noncomputable def value (q : List α → α → ℝ) (z : List α → ℝ) : ℕ → List α → ℝ
  | 0, h => z h
  | n + 1, h => z h + ∑ a, q h a * value q z n (h ++ [a])

/-- Backward optimization independently chooses one extreme row at each node. -/
noncomputable def envelope (δ : ℝ) (z : List α → ℝ) : ℕ → List α → ℝ
  | 0, h => z h
  | n + 1, h => z h + ∑ a,
      extremeRow δ (bestLetter (fun c => envelope δ z n (h ++ [c]))) a *
        envelope δ z n (h ++ [a])

/-- A single process on all histories implements the finite backward choices. -/
noncomputable def optimizingProcess (δ : ℝ) (z : List α → ℝ) (N : ℕ)
    (h : List α) (a : α) : ℝ :=
  extremeRow δ (bestLetter (fun c => envelope δ z (N - h.length - 1) (h ++ [c]))) a

private theorem extreme_row_sum (δ : ℝ) (heavy : α) :
    ∑ a, extremeRow δ heavy a = 1 := by
  classical
  simp [extremeRow, Finset.sum_add_distrib]

private theorem extreme_row_lower (δ : ℝ) (hc : (Fintype.card α : ℝ) * δ ≤ 1)
    (heavy a : α) : δ ≤ extremeRow δ heavy a := by
  unfold extremeRow
  split_ifs <;> linarith

private theorem row_bound (δ : ℝ) (q V : α → ℝ)
    (hq : ∀ a, δ ≤ q a) (hsum : ∑ a, q a = 1) :
    ∑ a, q a * V a ≤ ∑ a, extremeRow δ (bestLetter V) a * V a := by
  classical
  have bound : (∑ a, (q a - δ) * V a) ≤
      ∑ a, (q a - δ) * V (bestLetter V) := by
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (best_letter_max V a) (sub_nonneg.mpr (hq a))
  have decomp : (∑ a, q a * V a) =
      δ * (∑ a, V a) + ∑ a, (q a - δ) * V a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have residual : (∑ a, (q a - δ) * V (bestLetter V)) =
      (1 - (Fintype.card α : ℝ) * δ) * V (bestLetter V) := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hsum]
    simp
  have extremal : (∑ a, extremeRow δ (bestLetter V) a * V a) =
      δ * (∑ a, V a) + (1 - (Fintype.card α : ℝ) * δ) * V (bestLetter V) := by
    simp [extremeRow, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul]
  rw [decomp, extremal]
  exact add_le_add le_rfl (bound.trans_eq residual)

/-- Every history process is dominated at all horizons by the backward envelope. -/
theorem value_le_envelope (δ : ℝ) (hδ : 0 ≤ δ)
    (q : List α → α → ℝ) (hq : Admissible δ q) (z : List α → ℝ) :
    ∀ n h, value q z n h ≤ envelope δ z n h := by
  intro n
  induction n with
  | zero => intro h; exact le_rfl
  | succ n ih =>
    intro h
    simp only [value, envelope]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ a, q h a * envelope δ z n (h ++ [a]) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (ih _) (hδ.trans ((hq h).1 a))
      _ ≤ _ := row_bound δ (q h) _ (hq h).1 (hq h).2

/-- The finite choices attain the envelope simultaneously on the same tree. -/
theorem optimizing_process_attains (δ : ℝ)
    (hc : (Fintype.card α : ℝ) * δ ≤ 1) (z : List α → ℝ) (N : ℕ) :
    Admissible δ (optimizingProcess δ z N) ∧
    ∀ n h, h.length + n = N →
      value (optimizingProcess δ z N) z n h = envelope δ z n h := by
  refine ⟨fun h => ⟨fun a => extreme_row_lower δ hc _ a, extreme_row_sum δ _⟩, ?_⟩
  intro n
  induction n with
  | zero => intro h _; rfl
  | succ n ih =>
    intro h hlen
    simp only [value, envelope]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [ih (h ++ [a]) (by simp only [List.length_append, List.length_singleton]; omega)]
    have remaining : N - h.length - 1 = n := by omega
    simp only [optimizingProcess, remaining]

/-- The optimizing rows are transported to one extreme iid vector by tree swaps. -/
theorem optimizing_process_relabel (δ : ℝ) (z : List α → ℝ) (N : ℕ) (base : α) :
    ∃ π : List α → Equiv.Perm α,
      ∀ h a, optimizingProcess δ z N h a = extremeRow δ base (π h a) := by
  classical
  let heavy (h : List α) :=
    bestLetter (fun c => envelope δ z (N - h.length - 1) (h ++ [c]))
  refine ⟨fun h => Equiv.swap (heavy h) base, ?_⟩
  intro h a
  have atHeavy : Equiv.swap (heavy h) base (heavy h) = base := Equiv.swap_apply_left _ _
  have he : Equiv.swap (heavy h) base a = base ↔ a = heavy h := by
    constructor
    · intro ha
      exact (Equiv.swap (heavy h) base).injective (ha.trans atHeavy.symm)
    · rintro rfl; exact atHeavy
  simp only [optimizingProcess, extremeRow, he, heavy]

/-- Partition a word level by its first letter. -/
private theorem word_sum_succ (f : List α → ℝ) (n : ℕ) :
    (∑ w ∈ words (n + 1), f w) = ∑ a, ∑ w ∈ words n, f (a :: w) := by
  classical
  symm
  rw [← Finset.sum_product (f := fun x : α × List α => f (x.1 :: x.2))]
  apply Finset.sum_bij (fun x _ => x.1 :: x.2)
  · intro x hx
    apply (mem_words _ _).mpr
    have hw := (mem_words _ _).mp (Finset.mem_product.mp hx).2
    simp only [List.length_cons, hw]
  · intro x _ y _ he
    obtain ⟨ha, hw⟩ := List.cons.inj he
    exact Prod.ext ha hw
  · intro w hw
    have hl := (mem_words _ _).mp hw
    cases w with
    | nil => simp at hl
    | cons a w =>
      refine ⟨(a,w), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      apply (mem_words _ _).mpr
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using hl
  · intro _ _; rfl

/-- The recursive value equals its sums over all actual finite paths. -/
theorem value_path_sum (q : List α → α → ℝ) (z : List α → ℝ) :
    ∀ n h, value q z n h =
      ∑ k ∈ Finset.range (n + 1), ∑ w ∈ words k, pathMass q h w * z (h ++ w) := by
  classical
  have wzero : words (α := α) 0 = {[]} := by
    ext w; simp only [mem_words, Finset.mem_singleton, List.length_eq_zero_iff]
  intro n
  induction n with
  | zero => intro h; simp [value, wzero, pathMass]
  | succ n ih =>
    intro h
    rw [value, Finset.sum_range_succ']
    simp only [wzero, Finset.sum_singleton, pathMass, List.append_nil, one_mul]
    conv_rhs => rw [add_comm]
    congr 1
    simp_rw [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [word_sum_succ]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro w _
    simp only [pathMass, mul_assoc, List.append_assoc, List.singleton_append]

/-- Indicator rewards recover exactly the canonical truncated code mass. -/
private theorem value_code_mass (q : List α → α → ℝ) (F : Set (List α)) (N : ℕ) :
    value q (F.indicator (fun _ => 1)) N [] = historyTruncatedMass q F N := by
  classical
  rw [value_path_sum, historyTruncatedMass]
  apply Finset.sum_congr rfl
  intro n _
  simp [level, Finset.sum_filter, Set.indicator_apply]

/-- Finite-horizon mass is bounded by the frozen iid greedy maximum. -/
theorem finite_joint_bound (δ : ℝ) (hδ : 0 < δ)
    (hc : (Fintype.card α : ℝ) * δ ≤ 1) (base : α)
    (b : ℕ → ℕ) (tie : ℕ → LinearOrder (List α))
    (q : List α → α → ℝ) (hq : Admissible δ q)
    (F : Set (List α)) (hF : Legal b F) (N : ℕ) :
    historyTruncatedMass q F N ≤
      truncatedMass (extremeRow δ base)
        (greedyCode (fun n => priority (extremeRow δ base) (tie n)) b) N := by
  classical
  let K : Set (List α) := {w | w ∈ F ∧ w.length ≤ N}
  have hK : Legal b K := by
    refine ⟨fun _ hu _ hv h => hF.1 hu.1 hv.1 h,
      fun h => hF.2.1 h.1, fun n => ?_⟩
    apply (Finset.card_le_card ?_).trans (hF.2.2 n)
    intro w hw
    obtain ⟨hl, hm⟩ := (mem_level K w n).mp hw
    exact (mem_level F w n).mpr ⟨hl, hm.1⟩
  have levels (n : ℕ) (hn : n ≤ N) : level K n = level F n := by
    ext w
    rw [mem_level, mem_level]
    change (w.length = n ∧ w ∈ F ∧ w.length ≤ N) ↔ (w.length = n ∧ w ∈ F)
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.1 ▸ hn⟩⟩
  have truncation : historyTruncatedMass q F N = historyTruncatedMass q K N := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [levels n (by have := Finset.mem_range.mp hn; omega)]
  let z : List α → ℝ := K.indicator (fun _ => 1)
  let qstar := optimizingProcess δ z N
  obtain ⟨π, hπ⟩ := optimizing_process_relabel δ z N base
  obtain ⟨himage, htransport, _⟩ := HistoryTreeRelabeling.result π
    (extremeRow δ base) qstar hπ b K hK
  have imageDepth : ∀ w ∈ relabel π [] '' K, w.length ≤ N := by
    rintro _ ⟨v, hv, rfl⟩
    rw [relabel_length]
    exact hv.2
  have iid := depth_budget_iid_greedy_optimality (extremeRow δ base)
    (fun a => hδ.trans_le (extreme_row_lower δ hc base a)) (extreme_row_sum δ base) b tie
  calc
    historyTruncatedMass q F N = historyTruncatedMass q K N := truncation
    _ = value q z N [] := (value_code_mass q K N).symm
    _ ≤ envelope δ z N [] := value_le_envelope δ hδ.le q hq z N []
    _ = value qstar z N [] := ((optimizing_process_attains δ hc z N).2 N [] (by simp)).symm
    _ = historyTruncatedMass qstar K N := value_code_mass qstar K N
    _ = truncatedMass (extremeRow δ base) (relabel π [] '' K) N := htransport N
    _ ≤ _ := (iid.2.1 N).2 ⟨relabel π [] '' K, himage, imageDepth, rfl⟩

end D5.S0.Computability.Coding.HistoryBudgetJointOptimality
