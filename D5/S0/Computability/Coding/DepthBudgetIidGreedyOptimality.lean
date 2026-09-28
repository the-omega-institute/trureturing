/- GID: D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/DepthBudgetIidGreedyOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One iid greedy prefix code maximizes deleted mass at every depth and in the limit. -/

import D5.S0.Computability.Coding.PrefixFreeCode
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Vector
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

open scoped BigOperators ENNReal

namespace D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality

open PrefixFreeCode

/-- Comparison of finite weighted populations by every upper mass threshold. -/
def ThresholdLE {α : Type*} (w : α → ℝ) (s t : Finset α) : Prop :=
  ∀ z : ℝ, (s.filter (fun x => z ≤ w x)).card ≤
    (t.filter (fun x => z ≤ w x)).card

/-- The iid mass of a word. -/
def wordMass {α : Type*} (p : α → ℝ) (v : List α) : ℝ := (v.map p).prod

/-- Append one letter to every member of a frontier. -/
noncomputable def expand {α : Type*} [Fintype α] [DecidableEq α] (s : Finset (List α)) :
    Finset (List α) := by
  classical
  exact (s ×ˢ Finset.univ).image (fun q => q.1 ++ [q.2])

/-- All words at one depth. -/
noncomputable def words {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) : Finset (List α) := by
  classical
  exact Finset.univ.image (fun v : List.Vector α n => v.1)

/-- A prescribed total priority order, with larger iid masses first. -/
@[instance_reducible] noncomputable def priority {α : Type*} (p : α → ℝ)
    (tie : LinearOrder (List α)) : LinearOrder (List α) := by
  letI := tie
  exact LinearOrder.lift' (fun v => toLex ((OrderDual.toDual (wordMass p v)), v))
    (fun _ _ h => congrArg (fun q => (ofLex q).2) h)

/-- The fixed order chooses the initial segment, including exhaustion and zero. -/
noncomputable def pick {α : Type*} [DecidableEq α] (o : LinearOrder (List α))
    (s : Finset (List α)) (b : ℕ) : Finset (List α) := by
  let l : List (List α) := by
    letI := o
    exact s.sort
  exact (l.take b).toFinset

/-- The same frontier recursion is used for all horizons. -/
noncomputable def frontier {α : Type*} [Fintype α] [DecidableEq α] (o : ℕ → LinearOrder (List α))
    (b : ℕ → ℕ) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => by
    classical
    let s := expand (frontier o b n)
    exact s \ pick (o (n + 1)) s (b (n + 1))

/-- Words selected at a positive level, with no root selection. -/
noncomputable def selected {α : Type*} [Fintype α] [DecidableEq α] (o : ℕ → LinearOrder (List α))
    (b : ℕ → ℕ) : ℕ → Finset (List α)
  | 0 => ∅
  | n + 1 => pick (o (n + 1)) (expand (frontier o b n)) (b (n + 1))

/-- The single infinite code determined by the recursion. -/
def greedyCode {α : Type*} [Fintype α] [DecidableEq α] (o : ℕ → LinearOrder (List α))
    (b : ℕ → ℕ) : Set (List α) := {v | ∃ n, v ∈ selected o b n}

/-- The selected words of a possibly infinite code at one depth. -/
noncomputable def level {α : Type*} [Fintype α] [DecidableEq α] (F : Set (List α)) (n : ℕ) : Finset (List α) := by
  classical
  exact (words (α := α) n).filter (fun v => v ∈ F)

/-- Prefix-free codes subject only to positive-depth cardinality bounds. -/
def Legal {α : Type*} [Fintype α] [DecidableEq α] (b : ℕ → ℕ) (F : Set (List α)) : Prop :=
  IsPrefixFree F ∧ [] ∉ F ∧ ∀ n, (level F n).card ≤ b n

/-- Finite truncated mass; depth zero is included and contributes nothing for legal codes. -/
noncomputable def truncatedMass {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (F : Set (List α)) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ v ∈ level F n, wordMass p v

/-- The nonnegative countable sum of all codeword masses. -/
noncomputable def codeMass {α : Type*} (p : α → ℝ) (F : Set (List α)) : ℝ≥0∞ :=
  ∑' v : F, ENNReal.ofReal (wordMass p v.1)

/-- A single horizon-independent iid greedy code is legal and maximizes every finite
truncation and the total countable mass, for arbitrary depth budgets and fixed ties. -/
theorem depth_budget_iid_greedy_optimality {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (b : ℕ → ℕ) (tie : ℕ → LinearOrder (List α)) :
    let o := fun n => priority p (tie n)
    let G := greedyCode o b
    Legal b G ∧
    (∀ N, IsGreatest {x : ℝ | ∃ F, Legal b F ∧
        (∀ v ∈ F, v.length ≤ N) ∧ x = truncatedMass p F N}
      (truncatedMass p G N)) ∧
    IsGreatest {x : ℝ≥0∞ | ∃ F, Legal b F ∧ x = codeMass p F} (codeMass p G) := by
  classical
  have greedy_deletion_threshold (w : List α → ℝ)
      (s t a c : Finset (List α)) (b : ℕ)
      (hst : ThresholdLE w s t) (ha : a ⊆ s)
      (hac : a.card = min b s.card) (hcc : c.card ≤ b)
      (heavy : ∀ x ∈ s \ a, ∀ y ∈ a, w x ≤ w y) :
      ThresholdLE w (s \ a) (t \ c) := by
    classical
    intro z
    by_cases hempty : ((s \ a).filter (fun x => z ≤ w x)).Nonempty
    · obtain ⟨x, hx⟩ := hempty
      have hall : ∀ y ∈ a, z ≤ w y := fun y hy =>
        (Finset.mem_filter.mp hx).2.trans (heavy x (Finset.mem_filter.mp hx).1 y hy)
      have ha' : a ⊆ s.filter (fun x => z ≤ w x) := fun y hy =>
        Finset.mem_filter.mpr ⟨ha hy, hall y hy⟩
      have heq : (s \ a).filter (fun x => z ≤ w x) =
          s.filter (fun x => z ≤ w x) \ a := by ext y; simp; tauto
      have hsmall : b ≤ s.card := by
        by_contra hn
        have heqa : a = s := Finset.eq_of_subset_of_card_le ha (by omega)
        simp [heqa] at hx
      have hca : a.card = b := by rw [hac, Nat.min_eq_left hsmall]
      have hleft := Finset.card_sdiff_add_card_eq_card ha'
      have hright := Finset.card_le_card_sdiff_add_card
        (s := t.filter (fun x => z ≤ w x)) (t := c)
      have heqt : t.filter (fun x => z ≤ w x) \ c =
          (t \ c).filter (fun x => z ≤ w x) := by ext y; simp; tauto
      rw [← heq, hca] at hleft
      rw [heqt] at hright
      have hz := hst z
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
  have iid_frontier_comparison
      (p : α → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
      (o : ℕ → LinearOrder (List α))
      (ho : ∀ n u v, (o n).le u v → wordMass p v ≤ wordMass p u)
      (b : ℕ → ℕ) (R C : ℕ → Finset (List α))
      (hr0 : R 0 = {[]})
      (hr : ∀ n, R (n+1) = expand (R n) \ C (n+1))
      (hc : ∀ n, C (n+1) ⊆ expand (R n))
      (hbudget : ∀ n, (C (n+1)).card ≤ b (n+1)) :
      (∀ n, ThresholdLE (wordMass p) (frontier o b n) (R n)) ∧
      ∀ N, (∑ n ∈ Finset.range N, ∑ v ∈ C (n+1), wordMass p v) ≤
        ∑ n ∈ Finset.range N, ∑ v ∈ selected o b (n+1), wordMass p v := by
    classical
    have inj : Function.Injective (fun q : List α × α => q.1 ++ [q.2]) := by
      rintro ⟨u,a⟩ ⟨v,c⟩ h
      obtain ⟨h₁,h₂⟩ := List.append_inj' h (by simp)
      simp only [List.cons.injEq, and_true] at h₂
      exact Prod.ext h₁ h₂
    have masspos (v : List α) : 0 ≤ wordMass p v :=
      List.prod_nonneg (by simpa only [List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] using fun a (_ : a ∈ v) => (hp a).le)
    have pprops (n : ℕ) (s : Finset (List α)) (k : ℕ) :
        pick (o n) s k ⊆ s ∧ (pick (o n) s k).card = min k s.card ∧
        ∀ u ∈ s \ pick (o n) s k, ∀ v ∈ pick (o n) s k,
          wordMass p u ≤ wordMass p v := by
      letI := o n
      have sub : pick (o n) s k ⊆ s := by
        intro v hv
        have hv' : v ∈ s.sort (· ≤ ·) := List.mem_of_mem_take (by simpa [pick] using hv)
        simpa using hv'
      refine ⟨sub, ?_, ?_⟩
      · dsimp only [pick]
        rw [List.toFinset_card_of_nodup]
        · simp only [List.length_take, Finset.length_sort]
        · exact (s.sort_nodup _).take
      · intro u hu v hv
        have hu' : u ∈ (s.sort.drop k) := by
          have hh : u ∈ s.sort.take k ++ s.sort.drop k := by
            simpa using (Finset.mem_sdiff.mp hu).1
          rcases List.mem_append.mp hh with hh | hh
          · exact ((Finset.mem_sdiff.mp hu).2 (by simpa [pick] using hh)).elim
          · exact hh
        have hpw := s.pairwise_sort (· ≤ ·)
        rw [← List.take_append_drop k (s.sort (· ≤ ·))] at hpw
        exact ho n v u ((List.pairwise_append.mp hpw).2.2 v
          (by simpa [pick] using hv) u hu')
    have expsum (s : Finset (List α)) :
        (∑ v ∈ expand s, wordMass p v) = ∑ v ∈ s, wordMass p v := by
      rw [expand, Finset.sum_image (fun _ _ _ _ h => inj h), Finset.sum_product]
      simp_rw [wordMass, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      simp_rw [← Finset.mul_sum, hsum, mul_one]
    have expcount (s : Finset (List α)) (z : ℝ) :
        ((expand s).filter (fun v => z ≤ wordMass p v)).card =
        ∑ a, (s.filter (fun v => z / p a ≤ wordMass p v)).card := by
      rw [expand, Finset.filter_image, Finset.card_image_of_injective _ inj]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      simp [wordMass, ← div_le_iff₀ (hp a)]
      rfl
    have th : ∀ n, ThresholdLE (wordMass p) (frontier o b n) (R n) := by
      intro n
      induction n with
      | zero => rw [hr0]; exact fun _ => le_rfl
      | succ n ih =>
        have he : ThresholdLE (wordMass p) (expand (frontier o b n)) (expand (R n)) := by
          intro z
          rw [expcount, expcount]
          exact Finset.sum_le_sum fun a _ => ih (z / p a)
        rw [frontier, hr]
        exact greedy_deletion_threshold _ _ _ _ _ _ he (pprops (n+1) _ _).1
          (pprops (n+1) _ _).2.1 (hbudget n) (pprops (n+1) _ _).2.2
    have sumle (s t : Finset (List α)) (h : ThresholdLE (wordMass p) s t) :
        (∑ v ∈ s, wordMass p v) ≤ ∑ v ∈ t, wordMass p v := by
      have hall : ∀ a : Finset s, a.card ≤
          (a.biUnion (fun v => t.filter (fun w => wordMass p v.1 ≤ wordMass p w))).card := by
        intro a
        by_cases ha : a.Nonempty
        · obtain ⟨v,hv,hmin⟩ := a.exists_min_image (fun v => wordMass p v.1) ha
          have hh : a.card ≤ (s.filter (fun w => wordMass p v.1 ≤ wordMass p w)).card :=
            Finset.card_le_card_of_injOn Subtype.val
              (fun x hx => Finset.mem_filter.mpr ⟨x.2, hmin x hx⟩)
              (fun _ _ _ _ h => Subtype.ext h)
          apply (hh.trans (h _)).trans
          apply Finset.card_le_card
          intro w hw
          exact Finset.mem_biUnion.mpr ⟨v,hv,hw⟩
        · simp [Finset.not_nonempty_iff_eq_empty.mp ha]
      obtain ⟨f,hinj,hf⟩ :=
        (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp hall
      calc
        (∑ v ∈ s, wordMass p v) = ∑ v : s, wordMass p v.1 := by
          simp only [Finset.univ_eq_attach, Finset.sum_attach]
        _ ≤ ∑ v : s, wordMass p (f v) := Finset.sum_le_sum fun v _ =>
          (Finset.mem_filter.mp (hf v)).2
        _ = ∑ v ∈ Finset.univ.image f, wordMass p v :=
          (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
        _ ≤ ∑ v ∈ t, wordMass p v :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.image_subset_iff.mpr (fun v _ => (Finset.mem_filter.mp (hf v)).1))
            (fun v _ _ => masspos v)
    have conserved (S D : ℕ → Finset (List α)) (h0 : S 0 = {[]})
        (hrec : ∀ n, S (n+1) = expand (S n) \ D (n+1))
        (hsub : ∀ n, D (n+1) ⊆ expand (S n)) :
        ∀ N, (∑ n ∈ Finset.range N, ∑ v ∈ D (n+1), wordMass p v) +
          (∑ v ∈ S N, wordMass p v) = 1 := by
      intro N
      induction N with
      | zero => simp [h0, wordMass]
      | succ n ih =>
        have he := Finset.sum_sdiff (hsub n) (f := wordMass p)
        rw [expsum] at he
        rw [Finset.sum_range_succ, hrec]
        linarith
    refine ⟨th, fun N => ?_⟩
    have hR := conserved R C hr0 hr hc N
    have hG := conserved (frontier o b) (selected o b) rfl
      (fun _ => rfl) (fun n => (pprops (n+1) _ _).1) N
    have hle := sumle (frontier o b N) (R N) (th N)
    linarith
  let o := fun n => priority p (tie n)
  let G := greedyCode o b
  change Legal b G ∧ _
  have mw (v : List α) (n : ℕ) : v ∈ words n ↔ v.length = n := by
    simp only [words, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨u,h⟩ => h ▸ u.2, fun h => ⟨⟨v,h⟩,rfl⟩⟩
  have ml (F : Set (List α)) (v : List α) (n : ℕ) :
      v ∈ level F n ↔ v.length = n ∧ v ∈ F := by simp [level, mw]
  have me (S : Finset (List α)) (v : List α) :
      v ∈ expand S ↔ ∃ u ∈ S, ∃ a, u ++ [a] = v := by
    simp [expand, Finset.mem_image, Prod.exists]
  have ps (n : ℕ) (S : Finset (List α)) (k : ℕ) : pick (o n) S k ⊆ S := by
    letI := o n
    intro v hv
    have hv' : v ∈ S.sort (· ≤ ·) := List.mem_of_mem_take (by simpa [pick] using hv)
    simpa using hv'
  have pc (n : ℕ) (S : Finset (List α)) (k : ℕ) :
      (pick (o n) S k).card = min k S.card := by
    letI := o n
    dsimp only [pick]
    rw [List.toFinset_card_of_nodup]
    · simp only [List.length_take, Finset.length_sort]
    · exact (S.sort_nodup _).take
  have fl : ∀ n v, v ∈ frontier o b n → v.length = n := by
    intro n
    induction n with
    | zero => intro v hv; simpa [frontier] using hv
    | succ n ih =>
      intro v hv
      obtain ⟨u,hu,a,rfl⟩ := (me _ _).mp (Finset.mem_sdiff.mp hv).1
      simp [ih u hu]
  have sl : ∀ n v, v ∈ selected o b n → v.length = n := by
    intro n v hv
    cases n with
    | zero => simpa [selected] using hv
    | succ n =>
      obtain ⟨u,hu,a,rfl⟩ := (me _ _).mp (ps (n+1) _ _ hv)
      simp [fl n u hu]
  have avoid : ∀ n v, v ∈ frontier o b n →
      ∀ m ≤ n, ∀ u ∈ selected o b m, ¬u <+: v := by
    intro n
    induction n with
    | zero =>
      intro v hv m hm u hu
      have hm0 : m = 0 := by omega
      simp [hm0, selected] at hu
    | succ n ih =>
      intro v hv m hm u hu hup
      have hpre := (Finset.mem_sdiff.mp hv).1
      have hnot := (Finset.mem_sdiff.mp hv).2
      by_cases he : m = n+1
      · subst m
        have huv := hup.eq_of_length ((sl _ u hu).trans (fl _ v hv).symm)
        exact hnot (huv ▸ hu)
      · obtain ⟨w,hw,a,hwa⟩ := (me _ _).mp hpre
        have hupw : u <+: w := List.prefix_of_prefix_length_le hup
          (hwa ▸ List.prefix_append w [a]) (by rw [sl _ u hu, fl _ w hw]; omega)
        exact ih w hw m (by omega) u hu hupw
  have gl (v : List α) : v ∈ G ↔ v ∈ selected o b v.length := by
    constructor
    · rintro ⟨n,hn⟩
      rw [sl n v hn]
      exact hn
    · intro h; exact ⟨v.length,h⟩
  have lg (n : ℕ) : level G n = selected o b n := by
    ext v
    rw [ml]
    constructor
    · rintro ⟨hl,hv⟩; simpa [hl] using (gl v).mp hv
    · intro hv; exact ⟨sl n v hv, ⟨n,hv⟩⟩
  have glegal : Legal b G := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv hup
      have hu' := (gl u).mp hu
      have hv' := (gl v).mp hv
      by_cases hlen : u.length = v.length
      · exact hup.eq_of_length hlen
      · cases hn : v.length with
        | zero => simp [hn, selected] at hv'
        | succ n =>
          rw [hn] at hv'
          obtain ⟨w,hw,a,he⟩ := (me _ _).mp (ps (n+1) _ _ hv')
          have hlu : u.length ≤ n := by have := hup.length_le; omega
          have huw := List.prefix_of_prefix_length_le hup
            (he ▸ List.prefix_append w [a]) (by rw [fl _ w hw]; exact hlu)
          exact (avoid n w hw _ hlu u hu' huw).elim
    · intro h; have := (gl []).mp h; simpa [selected] using this
    · intro n; rw [lg]; cases n with
      | zero => simp [selected]
      | succ n => exact (pc (n+1) _ _).le.trans (Nat.min_le_left _ _)
  have ho : ∀ n u v, (o n).le u v → wordMass p v ≤ wordMass p u := by
    intro n u v huv
    letI := tie n
    change toLex (OrderDual.toDual (wordMass p u), u) ≤
      toLex (OrderDual.toDual (wordMass p v), v) at huv
    exact Prod.Lex.monotone_fst _ _ huv
  have finiteopt (F : Set (List α)) (hF : Legal b F) (N : ℕ) :
      truncatedMass p F N ≤ truncatedMass p G N := by
    let R : ℕ → Finset (List α) := fun n =>
      (words n).filter (fun v => ∀ u ∈ F, ¬u <+: v)
    have mr (v : List α) (n : ℕ) : v ∈ R n ↔
        v.length = n ∧ ∀ u ∈ F, ¬u <+: v := by simp [R, mw]
    have split (v : List α) (n : ℕ) (hv : v.length = n+1) :
        ∃ a, v.take n ++ [a] = v := by
      obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp (show (v.drop n).length = 1 by simp [hv])
      exact ⟨a, by rw [← ha, List.take_append_drop]⟩
    have rzero : R 0 = {[]} := by
      ext v
      rw [mr]
      simp only [Finset.mem_singleton, List.length_eq_zero_iff]
      constructor
      · exact And.left
      · rintro rfl; refine ⟨rfl,?_⟩
        intro u hu hup
        exact hF.2.1 (hup.eq_of_length_le (by simp) ▸ hu)
    have rc : ∀ n, R (n+1) = expand (R n) \ level F (n+1) := by
      intro n; ext v
      rw [mr, Finset.mem_sdiff, me, ml]
      constructor
      · rintro ⟨hlen,havoid⟩
        obtain ⟨a,ha⟩ := split v n hlen
        refine ⟨⟨v.take n, (mr _ _).mpr ⟨by simp [hlen], ?_⟩,a,ha⟩,?_⟩
        · intro u hu hup
          exact havoid u hu (hup.trans (List.take_prefix _ _))
        · intro hf; exact havoid v hf.2 List.prefix_rfl
      · rintro ⟨⟨w,hw,a,rfl⟩,hnot⟩
        obtain ⟨hwlen,hwavoid⟩ := (mr _ _).mp hw
        have hlen : (w ++ [a]).length = n+1 := by simp [hwlen]
        refine ⟨hlen,?_⟩
        intro u hu hup
        have hne : u ≠ w ++ [a] := by rintro rfl; exact hnot ⟨hlen,hu⟩
        have hlt : u.length ≤ n := by
          have := hup.length_le
          have hh : u.length ≠ (w ++ [a]).length := fun h => hne (hup.eq_of_length h)
          omega
        exact hwavoid u hu (List.prefix_of_prefix_length_le hup
          (List.prefix_append _ _) (by rw [hwlen]; exact hlt))
    have cs : ∀ n, level F (n+1) ⊆ expand (R n) := by
      intro n v hv
      obtain ⟨hlen,hvF⟩ := (ml _ _ _).mp hv
      obtain ⟨a,ha⟩ := split v n hlen
      apply (me _ _).mpr
      refine ⟨v.take n,(mr _ _).mpr ⟨by simp [hlen],?_⟩,a,ha⟩
      intro u hu hup
      have he := hF.1 hu hvF (hup.trans (List.take_prefix _ _))
      have hle := hup.length_le
      simp [he,hlen] at hle
    have bound := (iid_frontier_comparison p hp hsum o ho b R (level F)
      rzero rc cs (fun n => hF.2.2 (n+1))).2 N
    have levzero (H : Set (List α)) (hH : [] ∉ H) : level H 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hl,hm⟩ := (ml _ _ _).mp hv
      exact hH ((List.length_eq_zero_iff.mp hl) ▸ hm)
    have trunc (H : Set (List α)) (hH : [] ∉ H) : truncatedMass p H N =
        ∑ n ∈ Finset.range N, ∑ v ∈ level H (n+1), wordMass p v := by
      rw [truncatedMass, Finset.sum_range_succ']
      simp [levzero H hH]
    rw [trunc F hF.2.1, trunc G glegal.2.1]
    simpa only [lg] using bound
  have total_eq (F : Set (List α)) : codeMass p F =
      ∑' n, ENNReal.ofReal (∑ v ∈ level F n, wordMass p v) := by
    rw [codeMass, ← ENNReal.tsum_fiberwise
      (fun v : F => ENNReal.ofReal (wordMass p v.1)) (fun v : F => v.1.length)]
    apply tsum_congr
    intro n
    let e : ((fun v : F => v.1.length) ⁻¹' {n}) ≃ ↥(level F n) :=
      { toFun := fun v => ⟨v.1.1, (ml _ _ _).mpr ⟨v.2, v.1.2⟩⟩
        invFun := fun v => ⟨⟨v.1, ((ml _ _ _).mp v.2).2⟩, ((ml _ _ _).mp v.2).1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      _ = ∑' v : level F n, ENNReal.ofReal (wordMass p v.1) := e.tsum_eq _
      _ = ∑ v ∈ level F n, ENNReal.ofReal (wordMass p v) :=
        Finset.tsum_subtype (level F n) (fun v => ENNReal.ofReal (wordMass p v))
      _ = ENNReal.ofReal (∑ v ∈ level F n, wordMass p v) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro v _
        apply List.prod_nonneg
        intro a ha
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
        exact (hp a).le
  refine ⟨glegal, ?_, ?_⟩
  · intro N
    let K : Set (List α) := {v | v ∈ G ∧ v.length ≤ N}
    have hk : Legal b K := by
      refine ⟨fun _ hu _ hv huv => glegal.1 hu.1 hv.1 huv,
        fun h => glegal.2.1 h.1, fun n => ?_⟩
      apply (Finset.card_le_card ?_).trans (glegal.2.2 n)
      intro v hv
      exact (ml _ _ _).mpr ⟨((ml _ _ _).mp hv).1, ((ml _ _ _).mp hv).2.1⟩
    have htr : truncatedMass p K N = truncatedMass p G N := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
      have heq : level K n = level G n := by
        ext v
        rw [ml, ml]
        change (v.length = n ∧ v ∈ G ∧ v.length ≤ N) ↔ (v.length = n ∧ v ∈ G)
        exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,by omega⟩⟩
      rw [heq]
    refine ⟨⟨K,hk,fun v hv => hv.2,htr.symm⟩,?_⟩
    rintro x ⟨F,hF,_,rfl⟩
    exact finiteopt F hF N
  · refine ⟨⟨G,glegal,rfl⟩,?_⟩
    rintro x ⟨F,hF,rfl⟩
    change codeMass p F ≤ codeMass p G
    rw [total_eq F, total_eq G, ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_eq_iSup_nat]
    apply iSup_mono
    intro N
    cases N with
    | zero => simp
    | succ N =>
      have hn (H : Set (List α)) (n : ℕ) :
          0 ≤ ∑ v ∈ level H n, wordMass p v := by
        apply Finset.sum_nonneg
        intro v _
        apply List.prod_nonneg
        intro a ha
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
        exact (hp a).le
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hn F n),
        ← ENNReal.ofReal_sum_of_nonneg (fun n _ => hn G n)]
      exact ENNReal.ofReal_le_ofReal (finiteopt F hF N)

#print axioms depth_budget_iid_greedy_optimality



end D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
