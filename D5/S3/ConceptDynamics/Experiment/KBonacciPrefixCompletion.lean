/- GID: D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Off-diagonal cumulative products determine positive-object nonnegative-reader relations. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion

open scoped BigOperators

/-- An unknown positive object and a fixed unknown nonzero nonnegative reader. -/
structure World (k : ℕ) where
  c : Fin k → ℝ
  ell : Fin k → ℝ
  c_pos : ∀ i, 0 < c i
  ell_nonneg : ∀ i, 0 ≤ ell i
  ell_ne_zero : ell ≠ 0

/-- The initial relation, without choosing an absolute scale for either factor. -/
def target {k : ℕ} (w : World k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i t => w.c i * w.ell t

/-- The cumulative of length j, with zero terms outside that prefix. -/
def cumulative {k : ℕ} (c : Fin k → ℝ) (j : ℕ) : ℝ :=
  ∑ i, if i.val < j then c i else 0

/-- The paid preparation reading. -/
def initial {k : ℕ} (w : World k) : ℝ := ∑ i, w.c i * w.ell i

/-- Rows are indexed by r=j-1, so the omitted source position j=t+1 is r=t. -/
def offDiagonal (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun q => q.1 ≠ q.2)

/-- Equality of the preparation reading and the selected cumulative products. -/
def SameData {k : ℕ} (S : Finset (Fin k × Fin k)) (w v : World k) : Prop :=
  initial w = initial v ∧ ∀ q ∈ S,
    cumulative w.c (q.1.val + 1) * w.ell q.2 =
      cumulative v.c (q.1.val + 1) * v.ell q.2

/-- Fiber constancy on the full world domain. -/
def Identifies {k : ℕ} (S : Finset (Fin k × Fin k)) : Prop :=
  ∀ w v : World k, SameData S w v → target w = target v

private lemma prefix_zero {k : ℕ} (c : Fin k → ℝ) : cumulative c 0 = 0 := by
  simp [cumulative]

private lemma prefix_step {k : ℕ} (c : Fin k → ℝ) (i : Fin k) :
    cumulative c (i.val + 1) = cumulative c i.val + c i := by
  classical
  have split (s : Fin k) :
      (if s.val < i.val + 1 then c s else 0) =
        (if s.val < i.val then c s else 0) + (if s = i then c i else 0) := by
    by_cases h : s = i
    · subst s; simp
    · have hn : s.val ≠ i.val := fun he => h (Fin.ext he)
      by_cases hs : s.val < i.val
      · simp [h, hs, show s.val < i.val + 1 by omega]
      · simp [h, hs, show ¬s.val < i.val + 1 by omega]
  simp only [cumulative, split, Finset.sum_add_distrib]
  simp

private lemma prefix_pos {k : ℕ} (w : World k) (r : Fin k) :
    0 < cumulative w.c (r.val + 1) := by
  classical
  apply Finset.sum_pos'
  · intro i _
    split_ifs <;> [exact (w.c_pos i).le; exact le_rfl]
  · exact ⟨r, Finset.mem_univ r, by simpa using w.c_pos r⟩

private lemma reader_positive {k : ℕ} (w : World k) : ∃ t, 0 < w.ell t := by
  by_contra h
  push_neg at h
  apply w.ell_ne_zero
  funext t
  exact le_antisymm (h t) (w.ell_nonneg t)

private lemma initial_singleton {k : ℕ} (w : World k) (a : Fin k)
    (h : ∀ t, t ≠ a → w.ell t = 0) : initial w = w.c a * w.ell a := by
  classical
  exact Finset.sum_eq_single a (by intro b _ hb; simp [h b hb]) (by simp)

private lemma entries_of_prefixes {k : ℕ} (w v : World k) (a b : Fin k)
    (h : ∀ r : Fin k, cumulative w.c (r.val + 1) * w.ell a =
      cumulative v.c (r.val + 1) * v.ell b) :
    ∀ i, w.c i * w.ell a = v.c i * v.ell b := by
  intro i
  have hi := h i
  have prev : cumulative w.c i.val * w.ell a = cumulative v.c i.val * v.ell b := by
    by_cases hz : i.val = 0
    · simp [hz, prefix_zero]
    · let r : Fin k := ⟨i.val - 1, by omega⟩
      simpa [r, Nat.sub_add_cancel (by omega : 1 ≤ i.val)] using h r
  rw [prefix_step, prefix_step, add_mul, add_mul] at hi
  linarith

/-- All omitted diagonal products can be recovered for every unknown nonempty reader
support. One active column uses the preparation reading; two active columns use a
common observed row, which exists in every dimension at least three. -/
theorem off_diagonal_identifies (k : ℕ) (hk : 3 ≤ k) : Identifies (offDiagonal k) := by
  classical
  intro w v hd
  have observed (r t : Fin k) (hne : r ≠ t) :
      cumulative w.c (r.val + 1) * w.ell t =
        cumulative v.c (r.val + 1) * v.ell t :=
    hd.2 (r,t) (by simp [offDiagonal, hne])
  have support (t : Fin k) : w.ell t = 0 ↔ v.ell t = 0 := by
    obtain ⟨r, hr⟩ := Fintype.exists_ne_of_one_lt_card
      (show 1 < Fintype.card (Fin k) by simp; omega) t
    have he := observed r t hr
    have hp := prefix_pos w r
    have hq := prefix_pos v r
    constructor
    · intro hz
      rw [hz, mul_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left (ne_of_gt hq)
    · intro hz
      rw [hz, mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hp)
  obtain ⟨a, ha⟩ := reader_positive w
  have hva : 0 < v.ell a := lt_of_le_of_ne (v.ell_nonneg a)
    (Ne.symm (fun hz => (ne_of_gt ha) ((support a).mpr hz)))
  by_cases single : ∀ t, t ≠ a → w.ell t = 0
  · have singlev : ∀ t, t ≠ a → v.ell t = 0 :=
      fun t ht => (support t).mp (single t ht)
    have diag : w.c a * w.ell a = v.c a * v.ell a := by
      simpa [initial_singleton w a single, initial_singleton v a singlev] using hd.1
    have all : ∀ r : Fin k, cumulative w.c (r.val + 1) * w.ell a =
        cumulative v.c (r.val + 1) * v.ell a := by
      intro r
      by_cases hr : r = a
      · subst r
        have prev : cumulative w.c a.val * w.ell a = cumulative v.c a.val * v.ell a := by
          by_cases hz : a.val = 0
          · simp [hz, prefix_zero]
          · let r : Fin k := ⟨a.val - 1, by omega⟩
            have hn : r ≠ a := by intro he; have := congrArg Fin.val he; dsimp [r] at this; omega
            simpa [r, Nat.sub_add_cancel (by omega : 1 ≤ a.val)] using observed r a hn
        rw [prefix_step, prefix_step, add_mul, add_mul]
        linarith
      · exact observed r a hr
    funext i t
    by_cases ht : t = a
    · subst t; exact entries_of_prefixes w v a a all i
    · simp [target, single t ht, singlev t ht]
  · push_neg at single
    obtain ⟨b, hba, hb⟩ := single
    have hvb : v.ell b ≠ 0 := fun hz => hb ((support b).mpr hz)
    obtain ⟨r, hra, hrb⟩ : ∃ r : Fin k, r ≠ a ∧ r ≠ b := by
      have card : 2 < Fintype.card (Fin k) := by simp; omega
      have := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({a,b} : Finset (Fin k))) (t := Finset.univ)
        (by rw [Finset.card_pair (Ne.symm hba)]; simpa using card)
      obtain ⟨r, _, hr⟩ := this
      exact ⟨r, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hr⟩
    have ea := observed r a hra
    have eb := observed r b hrb
    have ratio : w.ell b * v.ell a = v.ell b * w.ell a := by
      apply mul_left_cancel₀ (ne_of_gt (prefix_pos w r))
      linear_combination v.ell a * eb - v.ell b * ea
    have all : ∀ s : Fin k, cumulative w.c (s.val + 1) * w.ell a =
        cumulative v.c (s.val + 1) * v.ell a := by
      intro s
      by_cases hs : s = a
      · subst s
        have eb := observed a b (Ne.symm hba)
        apply mul_right_cancel₀ hvb
        linear_combination v.ell a * eb - cumulative w.c (a.val + 1) * ratio
      · exact observed s a hs
    have scaled (t : Fin k) : w.ell t * v.ell a = v.ell t * w.ell a := by
      obtain ⟨s, hs⟩ := Fintype.exists_ne_of_one_lt_card
        (show 1 < Fintype.card (Fin k) by simp; omega) t
      have et := observed s t hs
      have es := all s
      apply mul_left_cancel₀ (ne_of_gt (prefix_pos w s))
      linear_combination v.ell a * et - v.ell t * es
    funext i t
    have ei := entries_of_prefixes w v a a all i
    have et := scaled t
    change w.c i * w.ell t = v.c i * v.ell t
    apply mul_right_cancel₀ (ne_of_gt hva)
    linear_combination v.ell t * ei + w.c i * et

#print axioms off_diagonal_identifies

private lemma no_perturbation {k : ℕ} (S : Finset (Fin k × Fin k))
    (ident : Identifies S) (ell h : Fin k → ℝ)
    (hn : ∀ t, 0 ≤ ell t) (hp : ∃ t, 0 < ell t)
    (hd : ∑ i, h i * ell i = 0)
    (ho : ∀ q ∈ S, ell q.2 ≠ 0 → cumulative h (q.1.val + 1) = 0) : h = 0 := by
  classical
  have hell : ell ≠ 0 := by
    obtain ⟨t, ht⟩ := hp
    intro he
    simpa [he] using ht
  let w : World k := ⟨fun i => |h i| + 1, ell,
    fun i => by linarith [abs_nonneg (h i)], hn, hell⟩
  let v : World k := ⟨fun i => |h i| + 1 + h i, ell,
    fun i => by linarith [neg_abs_le (h i)], hn, hell⟩
  have pv (j : ℕ) : cumulative v.c j = cumulative w.c j + cumulative h j := by
    simp only [cumulative, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w, v]
    split_ifs <;> ring
  have data : SameData S w v := by
    constructor
    · change (∑ i, (|h i| + 1) * ell i) = ∑ i, (|h i| + 1 + h i) * ell i
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hd]
      ring
    · intro q hq
      change cumulative w.c _ * ell _ = cumulative v.c _ * ell _
      rw [pv]
      by_cases hz : ell q.2 = 0
      · simp [hz]
      · rw [ho q hq hz, add_zero]
  have eq := ident w v data
  obtain ⟨t, ht⟩ := hp
  funext i
  have hi := congrFun (congrFun eq i) t
  change (|h i| + 1) * ell t = (|h i| + 1 + h i) * ell t at hi
  have hc : |h i| + 1 = |h i| + 1 + h i := mul_right_cancel₀ (ne_of_gt ht) hi
  change h i = 0
  linarith

/-- The distinct selected prefix lengths in a fixed reader column. -/
def column {k : ℕ} (S : Finset (Fin k × Fin k)) (t : Fin k) : Finset (Fin k) :=
  Finset.univ.filter (fun r => (r,t) ∈ S)

private lemma column_bound {k : ℕ} (S : Finset (Fin k × Fin k))
    (ident : Identifies S) (t : Fin k) : k - 1 ≤ (column S t).card := by
  classical
  by_contra small
  let J := column S t
  let A : Matrix (Option ↥J) (Fin k) ℝ := fun r i =>
    match r with
    | none => if i = t then 1 else 0
    | some r => if i.val < r.val.val + 1 then 1 else 0
  let f := A.mulVecLin
  have ker : f.ker ≠ ⊥ := by
    intro he
    have dim := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp he)
    have bad : k ≤ J.card + 1 := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
        Fintype.card_option, Fintype.card_coe] using dim
    dsimp [J] at bad
    omega
  obtain ⟨h, hh, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ker
  have ah : A.mulVec h = 0 := LinearMap.mem_ker.mp hh
  have ht : h t = 0 := by
    have hi := congrFun ah none
    simpa [A, Matrix.mulVec, dotProduct] using hi
  have pre (r : Fin k) (hr : r ∈ J) : cumulative h (r.val + 1) = 0 := by
    have hi := congrFun ah (some ⟨r,hr⟩)
    simpa [A, Matrix.mulVec, dotProduct, cumulative, ite_mul] using hi
  apply hn
  apply no_perturbation S ident (fun i => if i = t then 1 else 0) h
  · intro i; split_ifs <;> norm_num
  · exact ⟨t, by simp⟩
  · simpa using ht
  · intro q hq hpos
    have he : q.2 = t := by simpa only [ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] using hpos
    apply pre q.1
    have hq' : (q.1,q.2) ∈ S := hq
    simpa [J, column, he] using hq'

private def impulse {k : ℕ} (r : Fin k) : Fin k → ℝ := fun i => if i = r then 1 else 0

private lemma impulse_prefix {k : ℕ} (r : Fin k) (j : ℕ) :
    cumulative (impulse r) j = if r.val < j then 1 else 0 := by
  classical
  rw [cumulative, Finset.sum_eq_single r]
  · simp [impulse]
  · intro i _ hi
    simp [impulse, hi]
  · simp

private def direction {k : ℕ} (r : Fin k) : Fin k → ℝ :=
  fun i => impulse r i - if i.val = r.val + 1 then 1 else 0

private lemma direction_at {k : ℕ} (r : Fin k) : direction r r = 1 := by
  simp [direction, impulse]

private lemma direction_prefix {k : ℕ} (r s : Fin k) (hs : s ≠ r) :
    cumulative (direction r) (s.val + 1) = 0 := by
  classical
  by_cases hr : r.val + 1 < k
  · let next : Fin k := ⟨r.val + 1, hr⟩
    have hd : direction r = impulse r - impulse next := by
      funext i
      simp only [direction, Pi.sub_apply, impulse]
      congr 1
      exact if_congr (by simp [next, Fin.ext_iff]) rfl rfl
    rw [hd]
    have lin : cumulative (impulse r - impulse next) (s.val + 1) =
        cumulative (impulse r) (s.val + 1) - cumulative (impulse next) (s.val + 1) := by
      simp only [cumulative, ← Finset.sum_sub_distrib, Pi.sub_apply]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [lin, impulse_prefix, impulse_prefix]
    have hne : s.val ≠ r.val := fun he => hs (Fin.ext he)
    have eq : (r.val < s.val + 1) ↔ (next.val < s.val + 1) := by dsimp [next]; omega
    simp only [eq, sub_self]
  · have hd : direction r = impulse r := by
      funext i
      have hi : i.val ≠ r.val + 1 := by omega
      simp [direction, hi]
    rw [hd, impulse_prefix, if_neg (by
      have hne : s.val ≠ r.val := fun he => hs (Fin.ext he)
      omega)]

private lemma missing_near {k : ℕ} (S : Finset (Fin k × Fin k))
    (ident : Identifies S) (r t : Fin k) (missing : (r,t) ∉ S) :
    r = t ∨ r.val + 1 = t.val := by
  classical
  by_contra far
  push_neg at far
  have hzero : direction r = 0 := by
    apply no_perturbation S ident (impulse t) (direction r)
    · intro i; simp [impulse]; split_ifs <;> norm_num
    · exact ⟨t, by simp [impulse]⟩
    · have ht : direction r t = 0 := by
        simp [direction, impulse, Ne.symm far.1, Ne.symm far.2]
      simpa [impulse] using ht
    · intro q hq hl
      have qt : q.2 = t := by
        by_contra hn
        exact hl (by simp [impulse, hn])
      apply direction_prefix r q.1
      intro he
      apply missing
      have hq' : (q.1,q.2) ∈ S := hq
      simpa only [he, qt] using hq'
  have hi := congrFun hzero r
  rw [direction_at] at hi
  norm_num at hi

private lemma no_adjacent_missing {k : ℕ} (S : Finset (Fin k × Fin k))
    (ident : Identifies S) (r t : Fin k) (next : r.val + 1 = t.val)
    (left : (r,r) ∉ S) (right : (r,t) ∉ S) : False := by
  classical
  have rt : r ≠ t := by intro he; have := congrArg Fin.val he; omega
  let ell := impulse r + impulse t
  have hzero : direction r = 0 := by
    apply no_perturbation S ident ell (direction r)
    · intro i
      dsimp [ell, impulse]
      positivity
    · exact ⟨r, by simp [ell, impulse, rt]⟩
    · have ht : direction r t = -1 := by
        simp [direction, impulse, Ne.symm rt, ← next]
      simp [ell, mul_add, Finset.sum_add_distrib, impulse, direction_at, ht]
    · intro q hq hl
      apply direction_prefix r q.1
      intro he
      have live : q.2 = r ∨ q.2 = t := by
        by_contra hn
        push_neg at hn
        exact hl (by simp [ell, impulse, hn.1, hn.2])
      rcases live with hr | ht
      · have hq' : (q.1,q.2) ∈ S := hq
        exact left (by simpa only [he, hr] using hq')
      · have hq' : (q.1,q.2) ∈ S := hq
        exact right (by simpa only [he, ht] using hq')
  have hi := congrFun hzero r
  rw [direction_at] at hi
  norm_num at hi

/-- With at most k(k-1) distinct prefix products, the complete-domain identifiable
patterns are exactly the off-diagonal pattern. -/
theorem endpoint_pattern_classification (k : ℕ) (hk : 3 ≤ k)
    (S : Finset (Fin k × Fin k)) (budget : S.card ≤ k * (k - 1)) :
    Identifies S ↔ S = offDiagonal k := by
  classical
  constructor
  · intro ident
    have count : S.card = ∑ t : Fin k, (column S t).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
        (by intro q hq; exact Finset.mem_univ q.2)]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.card_bij (fun q _ => q.1)
      · intro q hq
        simp only [Finset.mem_filter] at hq
        have hq' : (q.1,q.2) ∈ S := hq.1
        simpa [column, hq.2] using hq' 
      · intro a ha b hb he
        simp only [Finset.mem_filter] at ha hb
        exact Prod.ext he (ha.2.trans hb.2.symm)
      · intro r hr
        refine ⟨(r,t), ?_, rfl⟩
        simpa [column] using hr
    have bounds : ∀ t : Fin k, k-1 ≤ (column S t).card := column_bound S ident
    have sumEq : (∑ t : Fin k, (k-1)) = ∑ t : Fin k, (column S t).card := by
      have ge := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin k))) => bounds t)
      have lhs : (∑ _ : Fin k, (k-1)) = k*(k-1) := by simp
      omega
    have exactCount (t : Fin k) : (column S t).card = k-1 :=
      ((Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun t _ => bounds t)).mp sumEq t (Finset.mem_univ t)).symm
    have missing : ∀ t : Fin k, ∃ m : Fin k, (column S t)ᶜ = {m} := by
      intro t
      apply Finset.card_eq_one.mp
      rw [Finset.card_compl, Fintype.card_fin, exactCount]
      omega
    choose m hm using missing
    have membership (r t : Fin k) : (r,t) ∈ S ↔ r ≠ m t := by
      have he := congrArg (fun X : Finset (Fin k) => r ∈ X) (hm t)
      simp only [Finset.mem_compl, Finset.mem_singleton, column, Finset.mem_filter,
        Finset.mem_univ, true_and] at he
      tauto
    have near (t : Fin k) : m t = t ∨ (m t).val + 1 = t.val :=
      missing_near S ident (m t) t (by simp [membership])
    have correct : ∀ n : ℕ, ∀ t : Fin k, t.val = n → m t = t := by
      intro n
      induction n with
      | zero =>
        intro t ht
        rcases near t with he | he
        · exact he
        · omega
      | succ n ih =>
        intro t ht
        rcases near t with he | he
        · exact he
        · let r : Fin k := ⟨n, by omega⟩
          have mr : m t = r := Fin.ext (by dsimp [r]; omega)
          have correctr : m r = r := ih r rfl
          exact False.elim (no_adjacent_missing S ident r t (by dsimp [r]; omega)
            (by simp [membership, correctr]) (by simp [membership, mr]))
    ext q
    rcases q with ⟨r,t⟩
    simp [membership, offDiagonal, correct t.val t rfl]
  · intro he
    subst S
    exact off_diagonal_identifies k hk

#print axioms endpoint_pattern_classification

end D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion
