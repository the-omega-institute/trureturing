/- GID: D5/S1/Recurrence/MendoncaMinPlusTriangle
   generality: I
   mirror-B: D5/B/S1/Recurrence/MendoncaMinPlusTriangle
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Strict decrease of the min-plus configuration counts from depth three onward. -/

/-
result:
  proof_shape: content
  escape_witness: Preservation.strict_preservation
  admission_basis: open-problem-resolution (#19612; Proved)
Direct frozen dependencies: none (all declarations; only Mathlib imports).
All helpers are private; the public proposition uses the source's ordered-tree count.
The complete tree with integer leaf times in CompleteBinaryTreeRootTime has a different evaluator.
Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/19724 (source-family realization and variation evidence).
Helper classification (all direct frozen dependencies are none):
value_bounds: proof_shape: content; consumer: T_outside, sum_by_value; escape_witness: value_bounds.
T_zero: proof_shape: bind-only; consumer: T_eq_row; escape_witness: none.
T_outside: proof_shape: bind-only; consumer: T_recurrence, T_eq_row, result; escape_witness: none.
value_attainable: proof_shape: content; consumer: T_positive; escape_witness: value_attainable.
T_positive: proof_shape: bind-only; consumer: result; escape_witness: none.
T_as_sum: proof_shape: bind-only; consumer: sum_by_value, T_succ_double_sum; escape_witness: none.
sum_by_value: proof_shape: bind-only; consumer: T_succ_double_sum; escape_witness: none.
T_succ_double_sum: proof_shape: bind-only; consumer: T_recurrence; escape_witness: none.
plus_kernel: proof_shape: bind-only; consumer: double_kernel; escape_witness: none.
min_pointwise: proof_shape: bind-only; consumer: min_kernel; escape_witness: none.
min_kernel: proof_shape: bind-only; consumer: double_kernel; escape_witness: none.
double_kernel: proof_shape: bind-only; consumer: T_recurrence; escape_witness: none.
conv_difference: proof_shape: bind-only; consumer: conv_difference_centered; escape_witness: none.
difference_telescope: proof_shape: bind-only; consumer: conv_difference_centered; escape_witness: none.
conv_difference_centered: proof_shape: bind-only; consumer: adjacent_difference; escape_witness: none.
tail_split: proof_shape: bind-only; consumer: adjacent_difference; escape_witness: none.
adjacent_difference: proof_shape: bind-only; consumer: strict_preservation; escape_witness: none.
extension_order: proof_shape: bind-only; consumer: strict_preservation; escape_witness: none.
strict_preservation: proof_shape: content; consumer: result; escape_witness: strict_preservation.
T_recurrence: proof_shape: bind-only; consumer: T_eq_row, result; escape_witness: none.
row_zero: proof_shape: bind-only; consumer: T_eq_row; escape_witness: none.
T_eq_row: proof_shape: bind-only; consumer: row_three_strict; escape_witness: none.
row_three_strict: proof_shape: bind-only; consumer: result; escape_witness: none.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace D5.S1.Recurrence.MendoncaMinPlusTriangle

/-- The two operators `+` and `min`. -/
inductive Op
  | plus
  | min

/-- The complete plane binary tree of depth `n` with its internal vertices labeled by `+` or `min`: depth `0` is a
single leaf; at depth `n + 1` the root carries a label and has a left and a right subtree of depth `n`. -/
inductive LabeledTree : ℕ → Type
  | leaf : LabeledTree 0
  | node {n : ℕ} (op : Op) (left right : LabeledTree n) : LabeledTree (n + 1)

/-- The value at the root: every leaf equals `1`, and each internal vertex applies its operator to the values of its
two children. -/
def value : {n : ℕ} → LabeledTree n → ℕ
  | _, .leaf => 1
  | _, .node .plus left right => value left + value right
  | _, .node .min left right => min (value left) (value right)

/-- `T(n, k)`: the number of labelings of the depth-`n` tree that evaluate to `k` at the root. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.card {t : LabeledTree n // value t = k}

/-- The strict-monotonicity conjecture of A400584. -/
def claim : Prop :=
  ∀ n k : ℕ, 3 ≤ n → 1 ≤ k → k < 2 ^ n → T n (k + 1) < T n k



private instance instDecidableEqOp : DecidableEq Op := by
  intro x y
  cases x <;> cases y <;>
    first | exact isTrue rfl | exact isFalse (by intro h; cases h)

private instance instFintypeOp : Fintype Op := ⟨{.plus, .min}, by intro x; cases x <;> simp⟩

private def zeroEquiv : LabeledTree 0 ≃ Unit where
  toFun _ := ()
  invFun _ := .leaf
  left_inv t := by cases t; rfl
  right_inv u := by cases u; rfl

private def succEquiv (n : ℕ) : LabeledTree (n + 1) ≃ Op × LabeledTree n × LabeledTree n where
  toFun t := match t with | .node op l r => (op, l, r)
  invFun t := .node t.1 t.2.1 t.2.2
  left_inv t := by cases t; rfl
  right_inv t := by rcases t with ⟨op,l,r⟩; rfl

private noncomputable instance treeFintype : (n : ℕ) → Fintype (LabeledTree n)
  | 0 => Fintype.ofEquiv Unit zeroEquiv.symm
  | n + 1 => letI := treeFintype n; Fintype.ofEquiv _ (succEquiv n).symm

private theorem value_bounds {n : ℕ} (t : LabeledTree n) : 1 ≤ value t ∧ value t ≤ 2 ^ n := by
  induction t with
  | leaf => simp [value]
  | @node n op l r hl hr =>
    cases op <;> simp only [value, pow_succ]
    · constructor <;> omega
    · exact ⟨le_min hl.1 hr.1, (min_le_left _ _).trans (by omega)⟩

private theorem T_zero (k : ℕ) : T 0 k = if k = 1 then 1 else 0 := by
  classical
  rw [T, Nat.card_eq_fintype_card]
  by_cases hk : k = 1
  · subst k
    have : Unique {t : LabeledTree 0 // value t = 1} :=
      { default := ⟨.leaf, rfl⟩, uniq := by intro t; rcases t with ⟨t,h⟩; cases t; rfl }
    simp
  · have : IsEmpty {t : LabeledTree 0 // value t = k} :=
      ⟨by intro ⟨t,h⟩; cases t; exact hk h.symm⟩
    simp [hk]

private theorem T_outside (n k : ℕ) (h : k = 0 ∨ 2 ^ n < k) : T n k = 0 := by
  have : IsEmpty {t : LabeledTree n // value t = k} := ⟨by
    intro ⟨t,ht⟩
    have hb := value_bounds t
    rcases h with h | h <;> omega⟩
  simp [T]

private theorem value_attainable (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ 2^n) :
    ∃ t : LabeledTree n, value t = k := by
  induction n generalizing k with
  | zero =>
    have : k=1 := Nat.le_antisymm hkn hk
    subst k
    exact ⟨.leaf, rfl⟩
  | succ n ih =>
    rw [pow_succ] at hkn
    by_cases h : k ≤ 2^n
    · obtain ⟨t,ht⟩ := ih k hk h
      exact ⟨.node .min t t, by simp [value,ht]⟩
    · obtain ⟨l,hl⟩ := ih (2^n) (by have h := pow_pos (by decide : 0 < (2:ℕ)) n; omega) le_rfl
      obtain ⟨r,hr⟩ := ih (k-2^n) (by omega) (by omega)
      exact ⟨.node .plus l r, by simp only [value,hl,hr]; omega⟩

private theorem T_positive (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ 2^n) : 0 < T n k := by
  obtain ⟨t,ht⟩ := value_attainable n k hk hkn
  have : Nonempty {t : LabeledTree n // value t = k} := ⟨⟨t,ht⟩⟩
  exact Nat.card_pos

open Finset

private theorem T_as_sum (n k : ℕ) : T n k = ∑ t : LabeledTree n, if value t = k then 1 else 0 := by
  classical
  rw [T, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem sum_by_value (n : ℕ) (g : ℕ → ℕ) :
    (∑ t : LabeledTree n, g (value t)) = ∑ i ∈ Ico 1 (2^n+1), T n i * g i := by
  classical
  have h := sum_fiberwise_of_maps_to' (s := (univ : Finset (LabeledTree n)))
    (t := Ico 1 (2^n+1)) (g := fun t => value t)
    (fun t _ => mem_Ico.mpr ⟨(value_bounds t).1, by have := (value_bounds t).2; omega⟩) g
  rw [← h]
  apply sum_congr rfl
  intro i hi
  rw [sum_const, Nat.nsmul_eq_mul]
  congr 1
  rw [T_as_sum]
  rw [card_eq_sum_ones, sum_filter]

private theorem T_succ_double_sum (n k : ℕ) :
    T (n+1) k = ∑ i ∈ Ico 1 (2^n+1), ∑ j ∈ Ico 1 (2^n+1),
      T n i * T n j * ((if i+j=k then 1 else 0) + (if min i j=k then 1 else 0)) := by
  classical
  rw [T_as_sum]
  rw [Fintype.sum_equiv (succEquiv n) _
    (fun p => if value (.node p.1 p.2.1 p.2.2) = k then 1 else 0)
    (by intro t; cases t; rfl)]
  simp only [Fintype.sum_prod_type]
  have hop (l r : LabeledTree n) :
      (∑ op : Op, if value (.node op l r) = k then 1 else 0) =
      (if value l + value r = k then 1 else 0) + (if min (value l) (value r) = k then 1 else 0) := by
    exact (Nat.add_zero _).symm
  rw [show (∑ op : Op, ∑ l : LabeledTree n, ∑ r : LabeledTree n,
      if value (.node op l r) = k then 1 else 0) =
      ∑ l : LabeledTree n, ∑ r : LabeledTree n, ∑ op : Op,
      if value (.node op l r) = k then 1 else 0 by
        rw [sum_comm]; apply sum_congr rfl; intro l hl; rw [sum_comm]]
  simp only [hop]
  rw [sum_by_value n (fun i => ∑ r : LabeledTree n,
    ((if i + value r = k then 1 else 0) + (if min i (value r) = k then 1 else 0)))]
  apply sum_congr rfl
  intro i hi
  rw [sum_by_value n (fun j => (if i+j=k then 1 else 0) + (if min i j=k then 1 else 0))]
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  ring


open Finset
namespace Kernels

private def natStep (a : ℕ → ℕ) (m k : ℕ) : ℕ :=
  a k ^ 2 + 2*a k*(∑ j ∈ Ico (k+1) (m+1), a j) +
    ∑ i ∈ Ico 1 k, a i*a (k-i)

private theorem plus_kernel (a : ℕ → ℕ) {m k : ℕ} (_hk : 1 ≤ k)
    (hz : ∀ i, m < i → a i = 0) :
    (∑ i ∈ Ico 1 (m+1), ∑ j ∈ Ico 1 (m+1),
      if i+j=k then a i*a j else 0) = ∑ i ∈ Ico 1 k, a i*a (k-i) := by
  have hinner (i : ℕ) (hi : i ∈ Ico 1 (m+1)) :
      (∑ j ∈ Ico 1 (m+1), if i+j=k then a i*a j else 0) =
        if i < k then a i*a (k-i) else 0 := by
    by_cases hik : i < k
    · by_cases hki : k-i ≤ m
      · rw [sum_eq_single (k-i)]
        · simp [Nat.add_sub_of_le hik.le, hik]
        · intro b hb hne
          have : i+b ≠ k := by omega
          simp [this]
        · intro hnot
          exact (hnot (mem_Ico.mpr ⟨by omega, by omega⟩)).elim
      · rw [hz (k-i) (by omega)]
        simp only [mul_zero, ite_self]
        apply sum_eq_zero
        intro j hj
        have : i+j ≠ k := by have := mem_Ico.mp hj; omega
        simp [this]
    · have hzero : ∀ j ∈ Ico 1 (m+1), i+j ≠ k := by
        intro j hj; have := mem_Ico.mp hj; omega
      rw [ite_eq_right hik]
      apply sum_eq_zero
      intro j hj
      simp [hzero j hj]
  rw [show (∑ i ∈ Ico 1 (m+1), ∑ j ∈ Ico 1 (m+1),
      if i+j=k then a i*a j else 0) =
      ∑ i ∈ Ico 1 (m+1), (if i < k then a i*a (k-i) else 0) by
    apply sum_congr rfl
    intro i hi
    exact hinner i hi]
  rw [← sum_filter]
  apply sum_subset
  · intro i hi
    simp only [mem_filter, mem_Ico] at *
    omega
  · intro i hi hnot
    simp only [mem_Ico, mem_filter] at *
    have : m < i := by omega
    simp [hz i this]

private theorem min_pointwise (a : ℕ → ℕ) (i j k : ℕ) :
    (if min i j=k then a i*a j else 0) =
      (if i=k then if k≤j then a k*a j else 0 else 0) +
      (if j=k then if k < i then a i*a k else 0 else 0) := by
  by_cases h : i ≤ j
  · rw [min_eq_left h]
    by_cases hi : i = k
    · subst i
      simp [h]
    · by_cases hj : j = k
      · subst j
        simp [hi, not_lt_of_ge h]
      · simp [hi, hj]
  · have hji : j ≤ i := le_of_not_ge h
    rw [min_eq_right hji]
    by_cases hj : j = k
    · subst j
      have hki : k < i := lt_of_not_ge h
      have hi : i ≠ k := ne_of_gt hki
      simp [hi, hki]
    · by_cases hi : i = k
      · subst i
        simp [hj, h]
      · simp [hi, hj]

private theorem min_kernel (a : ℕ → ℕ) {m k : ℕ} (hk : 1 ≤ k)
    (hz : ∀ i, m < i → a i = 0) :
    (∑ i ∈ Ico 1 (m+1), ∑ j ∈ Ico 1 (m+1),
      if min i j=k then a i*a j else 0) =
      a k ^ 2 + 2*a k*(∑ j ∈ Ico (k+1) (m+1), a j) := by
  simp_rw [min_pointwise, sum_add_distrib]
  by_cases hkm : k ≤ m
  · have hmem : k ∈ Ico 1 (m+1) := mem_Ico.mpr ⟨hk, by omega⟩
    have hfilter : {i ∈ Ico 1 (m+1) | k < i} = Ico (k+1) (m+1) := by
      simpa only [Nat.add_one_le_iff] using
        (Ico_filter_le_of_left_le (by omega : 1 ≤ k+1) :
          {i ∈ Ico 1 (m+1) | k+1 ≤ i} = Ico (k+1) (m+1))
    have hfilter' : {i ∈ Ico 1 (m+1) | k ≤ i} = Ico k (m+1) :=
      Ico_filter_le_of_left_le hk
    simp_rw [sum_ite_irrel]
    simp only [sum_const_zero, sum_ite_eq', hmem, ite_true]
    rw [← sum_filter, ← sum_filter, hfilter', hfilter,
      sum_eq_sum_Ico_succ_bot (by omega : k < m+1)]
    simp only [← mul_sum, ← sum_mul]
    ring
  · have hak := hz k (by omega)
    simp only [hak, mul_zero, zero_mul, ite_self, sum_const_zero, add_zero,
      zero_pow (by decide : 2 ≠ 0)]

private theorem double_kernel (a : ℕ → ℕ) {m k : ℕ} (hk : 1 ≤ k)
    (hz : ∀ i, m < i → a i = 0) :
    (∑ i ∈ Ico 1 (m+1), ∑ j ∈ Ico 1 (m+1), a i*a j *
      ((if i+j=k then 1 else 0)+(if min i j=k then 1 else 0))) = natStep a m k := by
  simp_rw [mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib]
  rw [plus_kernel a hk hz, min_kernel a hk hz]
  unfold natStep
  omega

end Kernels


open Finset
namespace Preservation

private def conv (a : ℕ → ℤ) (k : ℕ) : ℤ := ∑ i ∈ Ico 1 k, a i * a (k - i)
private def tail (a : ℕ → ℤ) (m k : ℕ) : ℤ := ∑ j ∈ Ico (k + 1) (m + 1), a j
private def step (a : ℕ → ℤ) (m k : ℕ) : ℤ := a k ^ 2 + 2 * a k * tail a m k + conv a k

private theorem conv_difference (a : ℕ → ℤ) {k : ℕ} (hk : 1 ≤ k) :
    conv a k - conv a (k + 1) =
      (∑ i ∈ Ico 1 k, a i * (a (k-i) - a (k+1-i))) - a k * a 1 := by
  unfold conv
  rw [sum_Ico_succ_top hk]
  simp only [Nat.add_sub_cancel_left, mul_sub, sum_sub_distrib]
  ring

private theorem difference_telescope (a : ℕ → ℤ) {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ Ico 1 k, (a (k-i) - a (k+1-i))) = a 1 - a k := by
  calc
    _ = ∑ i ∈ Ico 1 k, (a (k-i) - a (k-i+1)) := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_Ico.mp hi
      congr 2; omega
    _ = ∑ i ∈ Ico 1 k, (a i - a (i+1)) := by
      simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using
        (sum_Ico_reflect (fun i => a i-a (i+1)) 1
          (m := k) (n := k) (by omega : k ≤ k+1))
    _ = a 1 - a k := by
      simpa only [← sum_neg_distrib, neg_sub] using congrArg Neg.neg (sum_Ico_sub a hk)

private theorem conv_difference_centered (a : ℕ → ℤ) {k : ℕ} (hk : 1 ≤ k) :
    conv a k - conv a (k+1) =
      (∑ i ∈ Ico 1 k, (a i-a k)*(a (k-i)-a (k+1-i))) - a k ^ 2 := by
  rw [conv_difference a hk]
  simp only [sub_mul, sum_sub_distrib, ← mul_sum, difference_telescope a hk]
  ring

private theorem tail_split (a : ℕ → ℤ) {m k : ℕ} (hz : ∀ j, m < j → a j = 0) :
    tail a m k = a (k+1) + tail a m (k+1) := by
  unfold tail
  by_cases h : k < m
  · simpa only [Nat.add_assoc] using (sum_eq_sum_Ico_succ_bot (by omega : k+1 < m+1) a)
  · have hak : a (k+1) = 0 := hz _ (by omega)
    simp [Ico_eq_empty_of_le (by omega : m+1 ≤ k+1),
      Ico_eq_empty_of_le (by omega : m+1 ≤ k+1+1), hak]

private theorem adjacent_difference (a : ℕ → ℤ) {m k : ℕ} (hk : 1 ≤ k)
    (hz : ∀ j, m < j → a j = 0) :
    step a m k - step a m (k+1) =
      (∑ i ∈ Ico 1 k, (a i-a k)*(a (k-i)-a (k+1-i))) +
      a (k+1) * (2*a k-a (k+1)) +
      2*(a k-a (k+1))*tail a m (k+1) := by
  unfold step
  rw [tail_split a hz]
  have h := conv_difference_centered a hk
  linear_combination h


private theorem extension_order (a : ℕ → ℤ) {m : ℕ}
    (hp : ∀ i, 1 ≤ i → i ≤ m → 0 < a i)
    (hs : StrictAntiOn a (Set.Icc 1 m))
    (hz : ∀ i, m < i → a i = 0) :
    (∀ i, 1 ≤ i → 0 ≤ a i) ∧ (∀ i j, 1 ≤ i → i ≤ j → a j ≤ a i) := by
  have hn : ∀ i, 1 ≤ i → 0 ≤ a i := by
    intro i hi
    by_cases him : i ≤ m
    · exact (hp i hi him).le
    · rw [hz i (by omega)]
  refine ⟨hn, ?_⟩
  intro i j hi hij
  by_cases hjm : j ≤ m
  · rcases eq_or_lt_of_le hij with h | h
    · simp [h]
    · exact (hs ⟨hi, hij.trans hjm⟩ ⟨hi.trans hij, hjm⟩ h).le
  · rw [hz j (by omega)]
    exact hn i hi

private theorem strict_preservation (a : ℕ → ℤ) {m : ℕ} (hm : 2 ≤ m)
    (hp : ∀ i, 1 ≤ i → i ≤ m → 0 < a i)
    (hs : StrictAntiOn a (Set.Icc 1 m))
    (hz : ∀ i, m < i → a i = 0)
    {k : ℕ} (hk : 1 ≤ k) (hkm : k < 2*m) :
    step a m (k+1) < step a m k := by
  obtain ⟨hn, ha⟩ := extension_order a hp hs hz
  have hterm (i : ℕ) (hi : i ∈ Ico 1 k) :
      0 ≤ (a i-a k)*(a (k-i)-a (k+1-i)) := by
    obtain ⟨hi1,hik⟩ := mem_Ico.mp hi
    apply mul_nonneg
    · exact sub_nonneg.mpr (ha i k hi1 hik.le)
    · exact sub_nonneg.mpr (ha (k-i) (k+1-i) (by omega) (by omega))
  have hsum : 0 ≤ ∑ i ∈ Ico 1 k, (a i-a k)*(a (k-i)-a (k+1-i)) :=
    sum_nonneg hterm
  have hcentral : 0 ≤ a (k+1)*(2*a k-a (k+1)) := by
    apply mul_nonneg (hn _ (by omega))
    have h := ha k (k+1) hk (by omega)
    have h' := hn k hk
    linarith
  have htail : 0 ≤ 2*(a k-a (k+1))*tail a m (k+1) := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (ha k (k+1) hk (by omega)))
    · apply sum_nonneg
      intro i hi
      exact hn i (by have := (mem_Ico.mp hi).1; omega)
  have hid := adjacent_difference a hk hz
  rcases lt_trichotomy k m with h | h | h
  · have hac : 0 < a (k+1) := hp _ (by omega) (by omega)
    have hd := hs ⟨hk, h.le⟩ ⟨by omega, by omega⟩ (by omega : k < k+1)
    have : 0 < a (k+1)*(2*a k-a (k+1)) := mul_pos hac (by linarith)
    linarith
  · subst k
    have hi : 1 ∈ Ico 1 m := mem_Ico.mpr ⟨by omega, by omega⟩
    have h1 := hs ⟨by omega, by omega⟩ ⟨by omega, le_refl m⟩ (by omega : 1 < m)
    have h2 := hs ⟨by omega, by omega⟩ ⟨by omega, le_refl m⟩ (by omega : m-1 < m)
    have ht : 0 < (a 1-a m)*(a (m-1)-a (m+1-1)) := by
      simpa using mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)
    have hle := single_le_sum hterm hi
    linarith
  · have hi : k-m ∈ Ico 1 k := mem_Ico.mpr ⟨by omega, by omega⟩
    have ht : 0 < (a (k-m)-a k)*(a (k-(k-m))-a (k+1-(k-m))) := by
      rw [hz k h, show k-(k-m)=m by omega,
        show k+1-(k-m)=m+1 by omega, hz (m+1) (by omega)]
      simpa using mul_pos (hp (k-m) (by omega) (by omega)) (hp m (by omega) (by omega))
    have hle := single_le_sum hterm hi
    linarith

end Preservation
open Finset Kernels

private theorem T_recurrence (n k : ℕ) (hk : 1 ≤ k) :
    T (n+1) k = natStep (T n) (2^n) k := by
  rw [T_succ_double_sum]
  exact double_kernel (T n) hk (fun i hi => T_outside n i (Or.inr hi))

private def row : ℕ → ℕ → ℕ
  | 0,k => if k=1 then 1 else 0
  | n+1,k => natStep (row n) (2^n) k

private theorem row_zero (n : ℕ) : row n 0 = 0 := by
  induction n with
  | zero => norm_num [row]
  | succ n ih => simp [row, natStep, ih]

private theorem T_eq_row (n k : ℕ) : T n k = row n k := by
  induction n generalizing k with
  | zero => exact T_zero k
  | succ n ih =>
    by_cases hk : k=0
    · subst k; rw [T_outside _ _ (Or.inl rfl), row_zero]
    · rw [T_recurrence n k (by omega), row]
      congr 1
      funext i
      exact ih i

private theorem row_three_strict {k : ℕ} (hk : 1 ≤ k) (hk8 : k < 8) :
    T 3 (k+1) < T 3 k := by
  rw [T_eq_row, T_eq_row]
  interval_cases k <;> decide

theorem result : claim := by
  intro n k hn hk hkn
  induction n, hn using Nat.le_induction generalizing k with
  | base => exact row_three_strict hk (by norm_num at hkn ⊢; exact hkn)
  | succ n hn ih =>
    have hm : 2 ≤ 2^n := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ n)
      norm_num at h
      exact h
    have hs : StrictAntiOn (fun i => (T n i : ℤ)) (Set.Icc 1 (2^n)) := by
      apply strictAntiOn_of_add_one_lt Set.ordConnected_Icc
      intro i _ hi hi'
      exact_mod_cast ih i hi.1 (by have := hi'.2; omega)
    have h := Preservation.strict_preservation
      (fun i => (T n i : ℤ)) hm
      (fun i hi him => by exact_mod_cast T_positive n i hi him) hs
      (fun i hi => by simp [T_outside n i (Or.inr hi)]) hk
      (by simpa [pow_succ, Nat.mul_comm] using hkn)
    rw [T_recurrence n (k+1) (by omega), T_recurrence n k hk]
    unfold Preservation.step Preservation.tail Preservation.conv at h
    unfold natStep
    dsimp only at h
    exact_mod_cast h

end D5.S1.Recurrence.MendoncaMinPlusTriangle
