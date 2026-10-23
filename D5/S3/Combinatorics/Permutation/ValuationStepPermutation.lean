/- GID: D5/S3/Combinatorics/Permutation/ValuationStepPermutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/ValuationStepPermutation
   mirror-E: none(waiver:theorem-has-no-separate-numeric-evidence)
   anchors: []
   utility: none
   digest: The valuation-step greedy sequence enumerates every positive integer exactly once. -/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The rule never stalls: `exists_next` supplies an unused positive value at the next
valuation level. Minimizing that value therefore gives precisely the lexicographically
 earliest sequence specified by OEIS A382357. This is an unbounded history-dependent
construction, not a bounded enumeration or a numerical certificate. -/

namespace D5.S3.Combinatorics.Permutation.ValuationStepPermutation

/-- Adjacent terms must have 2-adic valuations differing by exactly one. -/
def Adjacent (x y : ℕ) : Prop := padicValNat 2 x + 1 = padicValNat 2 y ∨
  padicValNat 2 y + 1 = padicValNat 2 x

private def level (k r : ℕ) : ℕ := 2 ^ k * (2 * r + 1)

private theorem level_pos (k r : ℕ) : 0 < level k r := by
  unfold level
  positivity

private theorem level_val (k r : ℕ) : padicValNat 2 (level k r) = k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : ¬2 ∣ 2 * r + 1 := by omega
  rw [level, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd ho, Nat.add_zero]

private theorem level_order (k r s : ℕ) : level k r ≤ level k s ↔ r ≤ s := by
  unfold level
  constructor
  · intro h
    have hp : 0 < 2 ^ k := by positivity
    have hb := Nat.le_of_mul_le_mul_left h hp
    omega
  · intro h
    exact Nat.mul_le_mul_left (2 ^ k) (by omega)

private theorem level_repr (m : ℕ) (hm : 0 < m) :
    ∃ r, m = level (padicValNat 2 m) r := by
  obtain ⟨k, t, ⟨r, hr⟩, he⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : m ≠ 0)
  have ht : t = 2 * r + 1 := by omega
  have he : m = level k r := by simpa [level, ht] using he
  have hk : padicValNat 2 m = k := by rw [he, level_val]
  exact ⟨r, by rw [hk]; exact he⟩

private theorem mem_le_sum (l : List ℕ) (m : ℕ) (hm : m ∈ l) : m ≤ l.sum := by
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) m hm

private theorem exists_next (l : List ℕ) (c : ℕ) :
    ∃ m, 0 < m ∧ m ∉ l ∧ Adjacent c m := by
  refine ⟨level (padicValNat 2 c + 1) (l.sum + 1), level_pos _ _, ?_, ?_⟩
  · intro hm
    have hb := mem_le_sum _ _ hm
    have hp : 0 < 2 ^ (padicValNat 2 c + 1) := by positivity
    have hl := Nat.le_mul_of_pos_left (2 * (l.sum + 1) + 1) hp
    dsimp [level] at hb
    omega
  · exact Or.inl (level_val _ _).symm

/-- The least positive integer outside `l` adjacent to `c`. -/
noncomputable def next (l : List ℕ) (c : ℕ) : ℕ := by
  classical exact Nat.find (exists_next l c)

/-- `terms n = [a(n+1), a(n), …, a(1)]` in OEIS indexing; `terms 0 = [1]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => next (terms n) ((terms n).headD 1) :: terms n

/-- OEIS A382357, zero-indexed: `a 0 = 1` is the OEIS term a(1). -/
noncomputable def a (n : ℕ) : ℕ := (terms n).headD 1

/-- A382357 conjecture: the sequence is a permutation of the positive integers. -/
def claim : Prop := Function.Injective a ∧ ∀ m : ℕ, 0 < m → ∃ n : ℕ, a n = m

private theorem next_spec (l : List ℕ) (c : ℕ) :
    0 < next l c ∧ next l c ∉ l ∧ Adjacent c (next l c) := by
  classical
  exact Nat.find_spec (exists_next l c)

private theorem next_least (l : List ℕ) (c m : ℕ)
    (hp : 0 < m) (hm : m ∉ l) (ha : Adjacent c m) : next l c ≤ m := by
  classical
  exact Nat.find_min' (exists_next l c) ⟨hp, hm, ha⟩

private theorem terms_nodup (n : ℕ) : (terms n).Nodup := by
  induction n with
  | zero => simp [terms]
  | succ n ih =>
      rw [terms, List.nodup_cons]
      exact ⟨(next_spec _ _).2.1, ih⟩

private theorem mem_terms (n m : ℕ) : m ∈ terms n ↔ ∃ i ≤ n, a i = m := by
  induction n with
  | zero => simp [terms, a, eq_comm]
  | succ n ih =>
      simp only [terms, List.mem_cons, ih]
      have hs : a (n + 1) = next (terms n) ((terms n).headD 1) := rfl
      constructor
      · rintro (hm | ⟨i, hi, hm⟩)
        · exact ⟨n + 1, le_rfl, hs.trans hm.symm⟩
        · exact ⟨i, by omega, hm⟩
      · rintro ⟨i, hi, hm⟩
        by_cases he : i = n + 1
        · left; subst i; exact hm.symm.trans hs
        · right; exact ⟨i, by omega, hm⟩

private theorem a_pos (n : ℕ) : 0 < a n := by
  cases n with
  | zero => exact Nat.zero_lt_one
  | succ n => exact (next_spec _ _).1

private theorem a_injective : Function.Injective a := by
  suffices h : ∀ i j, i < j → a i ≠ a j by
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim (h i j hij he)
    · exact hij
    · exact False.elim (h j i hij he.symm)
  intro i j hij he
  cases j with
  | zero => omega
  | succ j =>
      have hm : a (j + 1) ∈ terms j :=
        (mem_terms j _).2 ⟨i, by omega, he⟩
      exact (List.nodup_cons.mp (terms_nodup (j + 1))).1 hm

private noncomputable def height (n : ℕ) : ℕ := padicValNat 2 (a n)

private theorem height_zero : height 0 = 0 := by simp [height, a, terms]

private theorem height_step (n : ℕ) :
    height n + 1 = height (n + 1) ∨ height (n + 1) + 1 = height n :=
  (next_spec (terms n) (a n)).2.2

private noncomputable def visits : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => visits n k + if height (n + 1) = k then 1 else 0

private theorem queue (n k r : ℕ) : level k r ∈ terms n ↔ r < visits n k := by
  induction n generalizing k r with
  | zero =>
      have hv := level_val k r
      by_cases hk : k = 0
      · subst k
        simp [terms, visits, level] <;> omega
      · have hn : level k r ≠ 1 := by intro he; rw [he] at hv; simp at hv; omega
        simp [terms, visits, hk, hn]
  | succ n ih =>
      obtain ⟨s, hs⟩ := level_repr (a (n + 1)) (a_pos _)
      change a (n + 1) = level (height (n + 1)) s at hs
      have hn := (next_spec (terms n) (a n)).2.1
      have hu : visits n (height (n + 1)) ≤ s := by
        have hnot : level (height (n + 1)) s ∉ terms n := by
          rw [← hs]; exact hn
        exact Nat.le_of_not_gt (by simpa [ih] using hnot)
      have hc : Adjacent (a n) (level (height (n + 1)) (visits n (height (n + 1)))) := by
        unfold Adjacent
        rw [level_val]
        exact height_step n
      have hl := next_least (terms n) (a n) _ (level_pos _ _)
        (by rw [ih]; omega) hc
      change a (n + 1) ≤ _ at hl
      rw [hs] at hl
      have he : s = visits n (height (n + 1)) := by
        have := (level_order _ _ _).1 hl
        omega
      have ha : a (n + 1) = level (height (n + 1)) (visits n (height (n + 1))) := by
        rw [hs, he]
      by_cases hk : height (n + 1) = k
      · rw [visits, if_pos hk]
        change level k r ∈ a (n + 1) :: terms n ↔ _
        rw [List.mem_cons, ih, ha, hk]
        have heq : level k r = level k (visits n k) ↔ r = visits n k := by
          constructor
          · intro he
            have h1 := (level_order k r (visits n k)).1 (Nat.le_of_eq he)
            have h2 := (level_order k (visits n k) r).1 (Nat.le_of_eq he.symm)
            omega
          · exact congrArg (level k)
        rw [heq]
        omega
      · rw [visits, if_neg hk, Nat.add_zero]
        change level k r ∈ a (n + 1) :: terms n ↔ _
        rw [List.mem_cons, ih]
        have heq : level k r ≠ a (n + 1) := by
          intro he
          have := congrArg (padicValNat 2) he
          rw [level_val] at this
          exact hk this.symm
        simp [heq]

private theorem eventually_large (f : ℕ → ℕ) (hf : Function.Injective f) (b : ℕ) :
    ∃ N, ∀ n, N ≤ n → b < f n := by
  exact Filter.eventually_atTop.1
    (hf.nat_tendsto_atTop.eventually (Filter.eventually_gt_atTop b))

private def Recurrent (k : ℕ) : Prop := ∀ N, ∃ n, N ≤ n ∧ height n = k

private theorem recurrent_covers (k m : ℕ) (hk : Recurrent k) (hm : 0 < m)
    (ha : k + 1 = padicValNat 2 m ∨ padicValNat 2 m + 1 = k) :
    ∃ n, a n = m := by
  by_contra he
  obtain ⟨N, hN⟩ := eventually_large a a_injective m
  obtain ⟨n, hn, hv⟩ := hk N
  have hmnot : m ∉ terms n := by
    rw [mem_terms]
    rintro ⟨i, _, hi⟩
    exact he ⟨i, hi⟩
  have hadj : Adjacent (a n) m := by
    change height n + 1 = _ ∨ _ + 1 = height n
    rw [hv]
    exact ha
  have hle := next_least (terms n) (a n) m hm hmnot hadj
  change a (n + 1) ≤ m at hle
  have := hN (n + 1) (by omega)
  omega

private theorem recurrent_neighbor (k j : ℕ) (hk : Recurrent k)
    (hj : k + 1 = j ∨ j + 1 = k) : Recurrent j := by
  intro N
  let r := (terms N).sum + 1
  obtain ⟨n, hn⟩ := recurrent_covers k (level j r) hk (level_pos _ _)
    (by rw [level_val]; exact hj)
  refine ⟨n, ?_, ?_⟩
  · by_contra hlt
    have hm := (mem_terms N _).2 ⟨n, by omega, hn⟩
    have hb := mem_le_sum _ _ hm
    have hp : 0 < 2 ^ j := by positivity
    have hl := Nat.le_mul_of_pos_left (2 * r + 1) hp
    dsimp [level, r] at hb hl
    omega
  · dsimp [height]
    rw [hn, level_val]

private theorem recurrent_all (h0 : Recurrent 0) : ∀ k, Recurrent k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => exact recurrent_neighbor k (k + 1) ih (Or.inl rfl)

private theorem covers_of_recurrent_zero (h0 : Recurrent 0) :
    ∀ m : ℕ, 0 < m → ∃ n : ℕ, a n = m := by
  intro m hm
  let k := padicValNat 2 m
  exact recurrent_covers (k + 1) m (recurrent_all h0 (k + 1)) hm (Or.inr rfl)
 
private theorem escape_above (h0 : ¬Recurrent 0) (k : ℕ) :
    ∃ N, ∀ n, N ≤ n → k < height n := by
  have hnrec : ∀ j, ¬Recurrent j := by
    intro j hj
    have hd : ∀ i, Recurrent i → Recurrent 0 := by
      intro i
      induction i with
      | zero => exact fun h => h
      | succ i ih =>
          intro h
          exact ih (recurrent_neighbor (i + 1) i h (Or.inr rfl))
    exact h0 (hd j hj)
  have cutoff : ∀ j, ∃ N, ∀ n, N ≤ n → height n ≠ j := by
    intro j
    have h := hnrec j
    simp only [Recurrent, not_forall, not_exists, not_and] at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, hN⟩
  induction k with
  | zero =>
      obtain ⟨N, hN⟩ := cutoff 0
      refine ⟨N, ?_⟩
      intro n hn
      have := hN n hn
      omega
  | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨K, hK⟩ := cutoff (k + 1)
      refine ⟨N + K, ?_⟩
      intro n hn
      have := hN n (by omega)
      have := hK n (by omega)
      omega

private theorem cross_between (s n k : ℕ) (hs : s ≤ n)
    (hl : height s ≤ k) (hu : k ≤ height n) :
    ∃ i, s ≤ i ∧ i ≤ n ∧ height i = k := by
  induction n with
  | zero =>
      have he : s = 0 := by omega
      subst s
      exact ⟨0, le_rfl, le_rfl, by omega⟩
  | succ n ih =>
      by_cases he : height (n + 1) = k
      · exact ⟨n + 1, hs, le_rfl, he⟩
      · have hsn : s ≤ n := by
          by_contra hn
          have hse : s = n + 1 := by omega
          rw [hse] at hl
          omega
        have hh := height_step n
        obtain ⟨i, hi, hin, hik⟩ := ih hsn (by omega)
        exact ⟨i, hi, by omega, hik⟩

private theorem chosen (n : ℕ) :
    a (n + 1) = level (height (n + 1)) (visits n (height (n + 1))) := by
  obtain ⟨r, hr⟩ := level_repr (a (n + 1)) (a_pos _)
  change a (n + 1) = level (height (n + 1)) r at hr
  have hn := (next_spec (terms n) (a n)).2.1
  have hu : visits n (height (n + 1)) ≤ r := by
    have hnot : level (height (n + 1)) r ∉ terms n := by rw [← hr]; exact hn
    rw [queue] at hnot
    omega
  have ha : Adjacent (a n) (level (height (n + 1)) (visits n (height (n + 1)))) := by
    unfold Adjacent
    rw [level_val]
    exact height_step n
  have hl := next_least (terms n) (a n) _ (level_pos _ _)
    (by rw [queue]; omega) ha
  change a (n + 1) ≤ _ at hl
  rw [hr] at hl
  have he : r = visits n (height (n + 1)) := by
    have := (level_order _ _ _).1 hl
    omega
  rw [hr, he]

private theorem visits_mono (s n k : ℕ) (hs : s ≤ n) : visits s k ≤ visits n k := by
  induction n with
  | zero =>
      have he : s = 0 := by omega
      subst s
      exact le_rfl
  | succ n ih =>
      by_cases he : s = n + 1
      · subst s; exact le_rfl
      · have := ih (by omega)
        rw [visits]
        omega


private noncomputable def down : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => down n k +
      if height n = k ∧ height (n + 1) + 1 = k then 1 else 0

private theorem down_zero (n : ℕ) : down n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hc : ¬(height n = 0 ∧ height (n + 1) + 1 = 0) := by omega
      simp only [down, ih, if_neg hc, Nat.add_zero]

private theorem crossing_identity (n k : ℕ) :
    visits n k = down n k + down n (k + 1) +
      if k ≤ height n then 1 else 0 := by
  induction n with
  | zero =>
      simp only [visits, down, height_zero]
      split_ifs <;> omega
  | succ n ih =>
      rw [visits, down, down, ih]
      rcases height_step n with hs | hs <;> split_ifs <;> omega

private theorem down_constant (k s t : ℕ) (hst : s ≤ t)
    (hn : ∀ i, s < i → i ≤ t → height i + 1 ≠ k) :
    down t k = down s k := by
  induction t generalizing s with
  | zero =>
      have he : s = 0 := by omega
      subst s
      rfl
  | succ t ih =>
      by_cases he : s = t + 1
      · subst s; rfl
      · have hst0 : s ≤ t := by omega
        have hi := ih s hst0 (fun i his hit => hn i his (by omega))
        have hc : ¬(height t = k ∧ height (t + 1) + 1 = k) := by
          have ht := hn (t + 1) (by omega) le_rfl
          exact fun he => ht he.2
        simp only [down, hi, if_neg hc, Nat.add_zero]

private theorem descent_bound (D : ℕ → ℕ) (M : ℕ) (hzero : D 0 = 0)
    (hineq : ∀ j, 1 ≤ j → j ≤ M →
      4 * D (j + 1) + 1 ≤ D (j - 1) + D j) : M ≤ 2 * D 1 := by
  have hp : ∀ i, i ≤ M → i + (D i + 2 * D (i + 1)) ≤ 2 * D 1 := by
    intro i
    induction i with
    | zero => intro hi; simp [hzero]
    | succ i ih =>
        intro hi
        have ht := ih (by omega)
        have hs := hineq (i + 1) (by omega) hi
        simp only [Nat.add_sub_cancel] at hs
        omega
  have hm := hp M le_rfl
  omega

private theorem exit_inequality (N i : ℕ) (hN : i + 1 < height N) :
    4 * down N (i + 2) + 1 ≤ down N i + down N (i + 1) := by
  classical
  obtain ⟨u, _, hu, hv⟩ := cross_between 0 N (i + 1) (by omega)
    (by rw [height_zero]; omega) (by omega)
  let t := Nat.findGreatest (fun n => height n = i + 1) N
  have ht : t ≤ N := Nat.findGreatest_le (P := fun n => height n = i + 1) N
  have hv : height t = i + 1 :=
    Nat.findGreatest_spec (P := fun n => height n = i + 1) hu hv
  have hn : ∀ n, t < n → n ≤ N → height n ≠ i + 1 := by
    intro n htn hnN
    exact Nat.findGreatest_is_greatest (P := fun n => height n = i + 1) htn hnN
  have htN : t < N := by
    by_contra hn
    have he : t = N := by omega
    rw [he] at hv
    omega
  have habove : ∀ n, t < n → n ≤ N → i + 1 < height n := by
    intro n htn hnN
    by_contra hlow
    obtain ⟨u, hnu, huN, huv⟩ := cross_between n N (i + 1) hnN (by omega) (by omega)
    exact hn u (by omega) huN huv
  have hup : height (t + 1) = i + 2 := by
    have hh := height_step t
    have ha := habove (t + 1) (by omega) (by omega)
    omega
  have hd : down N (i + 2) = down t (i + 2) := by
    apply down_constant (i + 2) t N ht
    intro n htn hnN he
    have hh := hn n htn hnN
    omega
  have hq : down N (i + 2) ≤ visits t (i + 2) := by
    rw [hd, crossing_identity]
    omega
  have ha : Adjacent (a t) (level i (visits t i)) := by
    change height t + 1 = _ ∨ _ + 1 = height t
    rw [level_val, hv]
    exact Or.inr rfl
  have hl := next_least (terms t) (a t) (level i (visits t i))
    (level_pos _ _) (by rw [queue]; omega) ha
  change a (t + 1) ≤ _ at hl
  rw [chosen, hup] at hl
  have hupper := (level_order (i + 2) _ _).2 hq
  have hlower := (level_order i _ _).2 (visits_mono t N i ht)
  have hb := hupper.trans (hl.trans hlower)
  have hc : visits N i = down N i + down N (i + 1) + 1 := by
    rw [crossing_identity, if_pos (by omega)]
  simp only [level, pow_add, show 2 ^ 2 = 4 by norm_num, Nat.mul_assoc] at hb
  have hp : 0 < 2 ^ i := by positivity
  have hb := Nat.le_of_mul_le_mul_left hb hp
  rw [hc] at hb
  omega

private theorem recurrent_zero : Recurrent 0 := by
  by_contra h0
  obtain ⟨K, hK⟩ := escape_above h0 1
  let M := 2 * down K 1 + 1
  obtain ⟨L, hL⟩ := escape_above h0 (M + 1)
  let N := K + L
  have hN : M + 1 < height N := hL N (by dsimp [N]; omega)
  have hd : down N 1 = down K 1 := by
    apply down_constant 1 K N (by dsimp [N]; omega)
    intro n hKn _ he
    have := hK n (by omega)
    omega
  have hb := descent_bound (down N) M (down_zero N) (by
    intro j hj hjM
    cases j with
    | zero => omega
    | succ i =>
        simpa only [Nat.add_sub_cancel] using exit_inequality N i (by omega))
  rw [hd] at hb
  dsimp [M] at hb
  omega

/-- The exact valuation-step greedy sequence is a permutation of the positive integers. -/
theorem result : claim := ⟨a_injective, covers_of_recurrent_zero recurrent_zero⟩

end D5.S3.Combinatorics.Permutation.ValuationStepPermutation
