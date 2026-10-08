/- GID: D5/S0/Computability/Coding/HistoryBudgetJointOptimality
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/HistoryBudgetJointOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-history rows have the same joint code optimum as an extreme iid law. -/

import D5.S0.Computability.Coding.HistoryTreeRelabeling
import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import D5.S0.History.FinitePrefixAntichainBudget
import Mathlib.Order.Iterate

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

local notation "bestLetter" => (fun V : α → ℝ =>
  Classical.choose (Finset.exists_max_image Finset.univ V Finset.univ_nonempty))

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
  let f : (List α → ℝ) → List α → ℝ :=
    fun V h => z h + ∑ a, q h a * V (h ++ [a])
  have monotone : Monotone f := by
    intro V W hVW h
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (hVW _) (hδ.trans ((hq h).1 a))
  exact monotone.seq_le_seq (x := value q z) (y := envelope δ z) n le_rfl
    (fun _ _ => le_rfl)
    (fun k _ h => add_le_add le_rfl (row_bound δ (q h)
      (fun a => envelope δ z k (h ++ [a])) (hq h).1 (hq h).2))

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
    obtain ⟨a, v, he, hv⟩ := List.length_eq_succ_iff.mp hl
    refine ⟨(a,v), Finset.mem_product.mpr ⟨Finset.mem_univ _, (mem_words v n).mpr hv⟩, he⟩
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
  have hK : Legal b K := legal_depth_truncation b F hF N
  have levels (n : ℕ) (hn : n ≤ N) : level K n = level F n :=
    level_depth_truncation F n N hn
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

private theorem path_mass_nonneg (q : List α → α → ℝ)
    (hq : ∀ h a, 0 ≤ q h a) (h w : List α) : 0 ≤ pathMass q h w := by
  induction w generalizing h with
  | nil => exact zero_le_one
  | cons a w ih => exact mul_nonneg (hq h a) (ih _)

/-- Nonnegative masses are the supremum of their canonical finite truncations. -/
private theorem mass_limit (m : List α → ℝ) (hm : ∀ w, 0 ≤ m w) (F : Set (List α)) :
    (∑' w : F, ENNReal.ofReal (m w.1)) =
      ⨆ N, ENNReal.ofReal (∑ n ∈ Finset.range (N + 1), ∑ w ∈ level F n, m w) := by
  classical
  have grouped : (∑' w : F, ENNReal.ofReal (m w.1)) =
      ∑' n, ∑ w ∈ level F n, ENNReal.ofReal (m w) := by
    rw [← ENNReal.tsum_fiberwise (fun w : F => ENNReal.ofReal (m w.1))
      (fun w : F => w.1.length)]
    apply tsum_congr
    intro n
    let e : {w : F // w.1.length = n} ≃ ↥(level F n) :=
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun w => w ∈ F) (fun w => w.length = n)).trans
        (Equiv.subtypeEquivRight (fun w => and_comm.trans (mem_level F w n).symm))
    calc
      _ = ∑' w : level F n, ENNReal.ofReal (m w.1) := e.tsum_eq _
      _ = _ := Finset.tsum_subtype (level F n) (fun w => ENNReal.ofReal (m w))
  rw [grouped, ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
  apply iSup_congr
  intro N
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hm w)]
  exact (ENNReal.ofReal_sum_of_nonneg
    (fun n _ => Finset.sum_nonneg (fun w _ => hm w))).symm

private theorem history_code_mass_le_one (q : List α → α → ℝ)
    (hpos : ∀ h a, 0 ≤ q h a) (hsum : ∀ h, ∑ a, q h a = 1)
    (F : Set (List α)) (hF : IsPrefixFree F) : historyCodeMass q F ≤ 1 := by
  classical
  have localBudget (h : List α) (C : Finset α) :
      ∑ a ∈ C, pathMass q [] (h ++ [a]) ≤ pathMass q [] h := by
    calc
      _ = pathMass q [] h * ∑ a ∈ C, q h a := by
        simp_rw [path_mass_append]
        simp only [pathMass, mul_one, List.nil_append, ← Finset.mul_sum]
      _ ≤ pathMass q [] h * ∑ a, q h a :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
            (fun a _ _ => hpos h a)) (path_mass_nonneg q hpos [] h)
      _ = _ := by rw [hsum, mul_one]
  rw [historyCodeMass, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  have bound := D5.S0.History.FinitePrefixAntichainBudget.result
    (pathMass q []) localBudget (S.image Subtype.val) (by
      rintro u hu v hv hpref
      obtain ⟨u', _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp hv
      exact hF u'.2 v'.2 hpref)
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at bound
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => path_mass_nonneg q hpos [] w.1)]
  simpa only [pathMass, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal bound

private theorem uniform_rows (δ : ℝ) (hcard : (Fintype.card α : ℝ) * δ = 1)
    (q : List α → α → ℝ) (hq : Admissible δ q) (h : List α) (a : α) : q h a = δ := by
  have hsum : ∑ c, (q h c - δ) = 0 := by
    rw [Finset.sum_sub_distrib, (hq h).2]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun c (_ : c ∈ Finset.univ) => sub_nonneg.mpr ((hq h).1 c))).mp hsum a
      (Finset.mem_univ a)
  exact sub_eq_zero.mp hz

private theorem row_mixture (δ : ℝ) (q : α → ℝ)
    (hq : ∀ a, δ ≤ q a) (hsum : ∑ a, q a = 1)
    (hstrict : (Fintype.card α : ℝ) * δ < 1) :
    let c := 1 - (Fintype.card α : ℝ) * δ
    (∀ a, 0 ≤ (q a - δ) / c) ∧
    (∑ a, (q a - δ) / c) = 1 ∧
    ∀ a, q a = ∑ heavy, ((q heavy - δ) / c) * extremeRow δ heavy a := by
  classical
  let c := 1 - (Fintype.card α : ℝ) * δ
  have hcpos : 0 < c := sub_pos.mpr hstrict
  have weightSum : (∑ a, (q a - δ) / c) = 1 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact div_self hcpos.ne'
  refine ⟨fun a => div_nonneg (sub_nonneg.mpr (hq a)) hcpos.le, weightSum, ?_⟩
  intro a
  have mix : (∑ heavy, ((q heavy - δ) / c) * extremeRow δ heavy a) =
      δ + ((q a - δ) / c) * c := by
    simp [extremeRow, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      mul_ite, weightSum, c]
  rw [mix, div_mul_cancel₀ _ hcpos.ne']
  ring

/-- All finite bounds, the infinite joint maximum, its complement and actual iid
attainment use the same frozen greedy code. The uniform endpoint includes all histories. -/
theorem result (δ : ℝ) (hδ : 0 < δ)
    (hcard : 2 ≤ Fintype.card α) (hc : (Fintype.card α : ℝ) * δ ≤ 1)
    (base : α) (b : ℕ → ℕ) (tie : ℕ → LinearOrder (List α)) :
    let p := extremeRow δ base
    let G := greedyCode (fun n => priority p (tie n)) b
    let J := {x : ℝ≥0∞ | ∃ q : List α → α → ℝ, Admissible δ q ∧
      ∃ F : Set (List α), Legal b F ∧ x = historyCodeMass q F}
    Legal b G ∧ Admissible δ (fun _ => p) ∧
    (∀ q : List α → α → ℝ, Admissible δ q → ∀ F : Set (List α), Legal b F → ∀ N,
      historyTruncatedMass q F N ≤ truncatedMass p G N) ∧
    IsGreatest J (codeMass p G) ∧ sSup J = codeMass p G ∧ codeMass p G ≤ 1 ∧
    (1 - sSup J : ℝ≥0∞) = 1 - codeMass p G ∧
    (1 - (sSup J).toReal : ℝ) = 1 - (codeMass p G).toReal ∧
    historyCodeMass (fun _ => p) G = codeMass p G ∧
    (δ < 1 / (Fintype.card α : ℝ) →
      ∀ q : List α → α → ℝ, Admissible δ q → ∀ h,
        let c := 1 - (Fintype.card α : ℝ) * δ
        (∀ a, 0 ≤ (q h a - δ) / c) ∧ (∑ a, (q h a - δ) / c) = 1 ∧
        ∀ a, q h a = ∑ heavy, ((q h heavy - δ) / c) * extremeRow δ heavy a) ∧
    (δ = 1 / (Fintype.card α : ℝ) →
      (∀ a, p a = δ) ∧ ∀ q : List α → α → ℝ, Admissible δ q → ∀ h a, q h a = δ) := by
  classical
  let p := extremeRow δ base
  let G := greedyCode (fun n => priority p (tie n)) b
  let J := {x : ℝ≥0∞ | ∃ q : List α → α → ℝ, Admissible δ q ∧
      ∃ F : Set (List α), Legal b F ∧ x = historyCodeMass q F}
  have hp : ∀ a, 0 < p a := fun a => hδ.trans_le (extreme_row_lower δ hc base a)
  have hadm : Admissible δ (fun _ : List α => p) :=
    fun _ => ⟨extreme_row_lower δ hc base, extreme_row_sum δ base⟩
  have iid := depth_budget_iid_greedy_optimality p hp (extreme_row_sum δ base) b tie
  have attain : historyCodeMass (fun _ : List α => p) G = codeMass p G := by
    apply tsum_congr
    intro w
    exact congrArg ENNReal.ofReal (path_mass_iid p [] w.1)
  have greatest : IsGreatest J (codeMass p G) := by
    refine ⟨⟨fun _ => p, hadm, G, iid.1, attain.symm⟩, ?_⟩
    rintro x ⟨q, hq, F, hF, rfl⟩
    rw [historyCodeMass,
      mass_limit (pathMass q []) (path_mass_nonneg q (fun h a => hδ.le.trans ((hq h).1 a)) []),
      code_mass_by_level p hp G,
      ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
    apply iSup_mono
    intro N
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by
      apply Finset.sum_nonneg
      intro w _
      rw [← path_mass_iid p [] w]
      exact path_mass_nonneg (fun _ => p) (fun _ a => (hp a).le) [] w)]
    exact ENNReal.ofReal_le_ofReal (finite_joint_bound δ hδ hc base b tie q hq F hF N)
  have supEq : sSup J = codeMass p G := greatest.csSup_eq
  have massBound : codeMass p G ≤ 1 := by
    rw [← attain]
    exact history_code_mass_le_one (fun _ => p) (fun _ a => (hp a).le)
      (fun _ => extreme_row_sum δ base) G iid.1.1
  refine ⟨iid.1, hadm, fun q hq F hF N => finite_joint_bound δ hδ hc base b tie q hq F hF N,
    greatest, supEq, massBound, by rw [supEq], by rw [supEq], attain, ?_, ?_⟩
  · intro hstrict q hq h
    apply row_mixture δ (q h) (hq h).1 (hq h).2
    have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast (show 0 < Fintype.card α by omega)
    have ht := (lt_div_iff₀ hn).mp hstrict
    simpa only [mul_comm] using ht
  · intro huni
    have hn : (Fintype.card α : ℝ) ≠ 0 := by
      have : 0 < Fintype.card α := by omega
      exact_mod_cast this.ne'
    have hunit : (Fintype.card α : ℝ) * δ = 1 := by rw [huni]; field_simp
    refine ⟨fun a => ?_, fun q hq h a => uniform_rows δ hunit q hq h a⟩
    simp only [extremeRow, hunit, sub_self, ite_self, add_zero]
end D5.S0.Computability.Coding.HistoryBudgetJointOptimality
