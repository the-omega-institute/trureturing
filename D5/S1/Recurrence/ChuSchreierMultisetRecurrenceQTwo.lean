/- GID: D5/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo
   generality: G
   mirror-B: D5/B/S1/Recurrence/ChuSchreierMultisetRecurrenceQTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Multiset.Interval, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: none
   digest: The q=2 Schreier counts satisfy the conjectured order-three recurrence. -/

/-
proof_shape: result: content
escape_witness: (W) bridge identity a n = c (2n-2) + c (2n-1) (have-chain inside result)
admission_basis: open-problem-resolution (issue #9284)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Multiset.Interval
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace D5.S1.Recurrence.ChuSchreierMultisetRecurrenceQTwo

/--
The page-19 ground multiset `{1,...,1,...,n-1,...,n-1,n}` with `s = 2`:
two copies of each of `1..n-1` and one copy of `n`.
-/
def ground (n : ℕ) : Multiset ℕ :=
  ((Finset.Icc 1 (n - 1)).val.bind fun i => Multiset.replicate 2 i) + {n}

/--
`A^{(2)}_{1,2,n}` as printed: the sub-multisets `F` of the ground multiset
with `n ∈ F` and `2 · min F ≥ |F|` (`min F` is `F.toFinset.min'` on the
nonempty witness `n ∈ F`; `|F|` is `Multiset.card`).
-/
def A (n : ℕ) : Finset (Multiset ℕ) :=
  (ground n).powerset.toFinset.filter fun F =>
    ∃ h : n ∈ F, Multiset.card F ≤ 2 * F.toFinset.min' ⟨n, Multiset.mem_toFinset.2 h⟩

/-- `a_n = |A^{(2)}_{1,2,n}|`. -/
def a (n : ℕ) : ℕ := (A n).card

/--
Item 1 of page 19 as printed, for every `n ≥ 4`
(the smallest index at which all four indices are `≥ 1`).
-/
def claim : Prop := ∀ n : ℕ, 4 ≤ n → a n = a (n - 1) + 2 * a (n - 2) + a (n - 3)

example : ground 3 = {1, 1, 2, 2, 3} := by decide +kernel
example : a 1 = 1 := by decide +kernel
example : a 2 = 2 := by decide +kernel
example : a 3 = 4 := by decide +kernel
example : a 4 = 9 := by decide +kernel
example : a 5 = 19 := by decide +kernel

/-- Data: ordered compositions of a natural number with every part in `{2, 3, 4}`. -/
private def comps : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | T + 1 =>
      (if 2 ≤ T + 1 then (comps (T + 1 - 2)).image (2 :: ·) else ∅) ∪
      (if 3 ≤ T + 1 then (comps (T + 1 - 3)).image (3 :: ·) else ∅) ∪
      (if 4 ≤ T + 1 then (comps (T + 1 - 4)).image (4 :: ·) else ∅)
termination_by T => T
decreasing_by
  all_goals apply Nat.sub_lt <;> omega

/-- Data: the number of ordered compositions represented by `comps`. -/
private def c (T : ℕ) : ℕ := (comps T).card

/--
Data: encode a sub-multiset by its multiplicities from its half-cardinality
threshold onward.
-/
private def encode (n : ℕ) (F : Multiset ℕ) : List ℕ :=
  (List.range' ((F.card + 1) / 2) (n - (F.card + 1) / 2)).map fun i => 2 + F.count i

/-- Data: decode shifted multiplicities beginning at a specified value. -/
private def decodeFrom : ℕ → List ℕ → Multiset ℕ
  | _, [] => 0
  | i, d :: ds => Multiset.replicate (d - 2) i + decodeFrom (i + 1) ds

/-- Data: decode a composition at size `n` and restore its distinguished copy of `n`. -/
private def decode (n : ℕ) (l : List ℕ) : Multiset ℕ :=
  decodeFrom (n - l.length) l + {n}

set_option maxHeartbeats 1000000 in
-- Folding the bijection proof into one declaration needs additional elaboration budget.
/-- The conjectured recurrence holds. -/
theorem result : claim := by
  have count_ground (n x : ℕ) :
      (ground n).count x = (if 1 ≤ x ∧ x < n then 2 else 0) + if x = n then 1 else 0 := by
    simp only [ground, Multiset.count_add, Multiset.count_bind]
    simp only [Multiset.count_replicate]
    change (∑ b ∈ Finset.Icc 1 (n - 1), if b = x then 2 else 0) +
        Multiset.count x {n} = _
    simp [Finset.mem_Icc, Multiset.count_singleton]
    split_ifs <;> omega

  have mem_comps (T : ℕ) (l : List ℕ) :
      l ∈ comps T ↔ l.sum = T ∧ ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4 := by
    induction T using Nat.strong_induction_on generalizing l with
    | h T ih =>
        by_cases hsmall : T < 4
        · interval_cases T <;>
            cases l with
            | nil => simp [comps]
            | cons d l =>
                cases l with
                | nil =>
                    simp [comps]
                    omega
                | cons e l =>
                    simp [comps]
                    omega
        · obtain ⟨u, rfl⟩ : ∃ u, T = u + 4 := by
            exact ⟨T - 4, by omega⟩
          rw [comps]
          simp only [if_pos (by omega : 2 ≤ u + 4), if_pos (by omega : 3 ≤ u + 4),
            if_pos (by omega : 4 ≤ u + 4)]
          simp only [show u + 4 - 2 = u + 2 by omega, show u + 4 - 3 = u + 1 by omega,
            show u + 4 - 4 = u by omega]
          rw [Finset.mem_union, Finset.mem_union]
          simp only [Finset.mem_image]
          cases l with
          | nil => simp
          | cons d l =>
              constructor
              · rintro ((⟨r, hr, hrl⟩ | ⟨r, hr, hrl⟩) | ⟨r, hr, hrl⟩)
                · simp only [List.cons.injEq] at hrl
                  obtain ⟨rfl, rfl⟩ := hrl
                  obtain ⟨hs, hp⟩ := (ih (u + 2) (by omega) r).mp hr
                  constructor
                  · simp only [List.sum_cons]
                    omega
                  · intro x hx
                    simp only [List.mem_cons] at hx
                    rcases hx with rfl | hx
                    · exact Or.inl rfl
                    · exact hp x hx
                · simp only [List.cons.injEq] at hrl
                  obtain ⟨rfl, rfl⟩ := hrl
                  obtain ⟨hs, hp⟩ := (ih (u + 1) (by omega) r).mp hr
                  constructor
                  · simp only [List.sum_cons]
                    omega
                  · intro x hx
                    simp only [List.mem_cons] at hx
                    rcases hx with rfl | hx
                    · exact Or.inr (Or.inl rfl)
                    · exact hp x hx
                · simp only [List.cons.injEq] at hrl
                  obtain ⟨rfl, rfl⟩ := hrl
                  obtain ⟨hs, hp⟩ := (ih u (by omega) r).mp hr
                  constructor
                  · simp only [List.sum_cons]
                    omega
                  · intro x hx
                    simp only [List.mem_cons] at hx
                    rcases hx with rfl | hx
                    · exact Or.inr (Or.inr rfl)
                    · exact hp x hx
              · intro h
                have hs := h.1
                have hd := h.2 d (by simp)
                have hp : ∀ x ∈ l, x = 2 ∨ x = 3 ∨ x = 4 := by
                  intro x hx
                  exact h.2 x (by simp [hx])
                simp only [List.sum_cons] at hs
                rcases hd with rfl | rfl | rfl
                · exact Or.inl (Or.inl
                    ⟨l, (ih (u + 2) (by omega) l).mpr ⟨by omega, hp⟩, rfl⟩)
                · exact Or.inl (Or.inr
                    ⟨l, (ih (u + 1) (by omega) l).mpr ⟨by omega, hp⟩, rfl⟩)
                · exact Or.inr ⟨l, (ih u (by omega) l).mpr ⟨by omega, hp⟩, rfl⟩

  have c_recurrence (T : ℕ) (hT : 4 ≤ T) :
      c T = c (T - 2) + c (T - 3) + c (T - 4) := by
    obtain ⟨u, rfl⟩ : ∃ u, T = u + 4 := by
      exact ⟨T - 4, by omega⟩
    unfold c
    rw [comps]
    simp only [if_pos (by omega : 2 ≤ u + 4), if_pos (by omega : 3 ≤ u + 4),
      if_pos (by omega : 4 ≤ u + 4)]
    simp only [show u + 4 - 2 = u + 2 by omega, show u + 4 - 3 = u + 1 by omega,
      show u + 4 - 4 = u by omega]
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_union_of_disjoint]
      · simp only [Finset.card_image_of_injective _ List.cons_injective]
      · simp only [Finset.disjoint_left, Finset.mem_image]
        rintro l ⟨l₂, -, rfl⟩ ⟨l₃, -, h⟩
        simp at h
    · simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_image]
      rintro l (⟨l₂, -, rfl⟩ | ⟨l₃, -, rfl⟩) ⟨l₄, -, h⟩ <;> simp at h

  have card_decodeFrom (i : ℕ) (l : List ℕ) :
      (decodeFrom i l).card = (l.map (fun d => d - 2)).sum := by
    induction l generalizing i with
    | nil => simp [decodeFrom]
    | cons d ds ih => simp [decodeFrom, ih]

  have mem_decodeFrom (i x : ℕ) (l : List ℕ) (hx : x ∈ decodeFrom i l) :
      i ≤ x ∧ x < i + l.length := by
    induction l generalizing i with
    | nil => simp [decodeFrom] at hx
    | cons d ds ih =>
        simp only [decodeFrom, Multiset.mem_add, Multiset.mem_replicate] at hx
        rcases hx with ⟨-, rfl⟩ | hx
        · simp
        · have h := ih (i + 1) hx
          simp only [List.length_cons]
          omega

  have count_decodeFrom_of_lt (i x : ℕ) (l : List ℕ) (hx : x < i) :
      (decodeFrom i l).count x = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact (Nat.not_le_of_gt hx) (mem_decodeFrom i x l hm).1

  have count_decodeFrom_ge (i x : ℕ) (l : List ℕ) (hx : i + l.length ≤ x) :
      (decodeFrom i l).count x = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact (Nat.not_lt_of_ge hx) (mem_decodeFrom i x l hm).2

  have mem_A {n : ℕ} {F : Multiset ℕ} :
      F ∈ A n ↔ F ≤ ground n ∧ n ∈ F ∧ ∀ x ∈ F, F.card ≤ 2 * x := by
    simp only [A, Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_powerset]
    constructor
    · rintro ⟨hle, hnF, hmin⟩
      refine ⟨hle, hnF, ?_⟩
      intro x hx
      exact hmin.trans (Nat.mul_le_mul_left 2
        (F.toFinset.min'_le x (Multiset.mem_toFinset.2 hx)))
    · rintro ⟨hle, hnF, hall⟩
      refine ⟨hle, hnF, ?_⟩
      exact hall _ (Multiset.mem_toFinset.1
        (F.toFinset.min'_mem ⟨n, Multiset.mem_toFinset.2 hnF⟩))

  have ground_count_n (n : ℕ) (hn : 1 ≤ n) : (ground n).count n = 1 := by
    rw [count_ground]
    simp [hn]

  have ground_count_le_two (n x : ℕ) : (ground n).count x ≤ 2 := by
    rw [count_ground]
    split_ifs <;> omega

  have mem_ground_le {n x : ℕ} (hx : x ∈ ground n) : x ≤ n := by
    have hp := Multiset.count_pos.mpr hx
    rw [count_ground] at hp
    split_ifs at hp <;> omega

  have A_count_n {n : ℕ} (hn : 1 ≤ n) {F : Multiset ℕ} (hF : F ∈ A n) :
      F.count n = 1 := by
    have hle := Multiset.le_iff_count.mp (mem_A.mp hF).1 n
    have hpos : 0 < F.count n := Multiset.count_pos.mpr (mem_A.mp hF).2.1
    rw [ground_count_n n hn] at hle
    omega

  have A_count_le_two {n : ℕ} {F : Multiset ℕ} (hF : F ∈ A n) (x : ℕ) :
      F.count x ≤ 2 := by
    exact (Multiset.le_iff_count.mp (mem_A.mp hF).1 x).trans (ground_count_le_two n x)

  have A_threshold_le_n {n : ℕ} {F : Multiset ℕ} (hF : F ∈ A n) :
      (F.card + 1) / 2 ≤ n := by
    have hc := (mem_A.mp hF).2.2 n (mem_A.mp hF).2.1
    omega

  have A_threshold_le_of_mem {n : ℕ} {F : Multiset ℕ} (hF : F ∈ A n)
      {x : ℕ} (hx : x ∈ F) : (F.card + 1) / 2 ≤ x := by
    have hc := (mem_A.mp hF).2.2 x hx
    omega

  have A_mem_le_n {n : ℕ} {F : Multiset ℕ} (hF : F ∈ A n)
      {x : ℕ} (hx : x ∈ F) : x ≤ n := by
    exact mem_ground_le (Multiset.mem_of_le (mem_A.mp hF).1 hx)

  have encode_length (n : ℕ) (F : Multiset ℕ) :
      (encode n F).length = n - (F.card + 1) / 2 := by
    simp [encode]

  have encode_parts {n : ℕ} {F : Multiset ℕ} (hF : F ∈ A n) :
      ∀ d ∈ encode n F, d = 2 ∨ d = 3 ∨ d = 4 := by
    intro d hd
    simp only [encode, List.mem_map, List.mem_range'_1] at hd
    obtain ⟨x, -, rfl⟩ := hd
    have := A_count_le_two hF x
    omega

  have sum_counts_interval {n : ℕ} (hn : 1 ≤ n) {F : Multiset ℕ} (hF : F ∈ A n) :
      ((List.range' ((F.card + 1) / 2) (n - (F.card + 1) / 2)).map fun x => F.count x).sum = F.card - 1 := by
    have htn := A_threshold_le_n hF
    have hsupp : ∀ x ∈ F.erase n, x ∈ Finset.Ico ((F.card + 1) / 2) n := by
      intro x hx
      have hxF := Multiset.mem_of_mem_erase hx
      simp only [Finset.mem_Ico]
      constructor
      · exact A_threshold_le_of_mem hF hxF
      · have hxn := A_mem_le_n hF hxF
        have hne : x ≠ n := by
          intro h
          subst x
          have hc := Multiset.count_pos.mpr hx
          rw [Multiset.count_erase_self, A_count_n hn hF] at hc
          omega
        omega
    have hsum := Multiset.sum_count_eq_card (s := Finset.Ico ((F.card + 1) / 2) n)
      (m := F.erase n) hsupp
    have herase : (F.erase n).card = F.card - 1 :=
      Multiset.card_erase_of_mem (mem_A.mp hF).2.1
    rw [herase] at hsum
    rw [Nat.Ico_eq_range'] at hsum
    change ((List.range' ((F.card + 1) / 2) (n - (F.card + 1) / 2)).map
      fun x => (F.erase n).count x).sum = F.card - 1 at hsum
    rw [← hsum]
    congr 1
    apply List.map_congr_left
    intro x hx
    symm
    apply Multiset.count_erase_of_ne
    have hx' := List.mem_range'_1.mp hx
    omega

  have encode_sum {n : ℕ} (hn : 1 ≤ n) {F : Multiset ℕ} (hF : F ∈ A n) :
      (encode n F).sum = 2 * (n - (F.card + 1) / 2) + (F.card - 1) := by
    unfold encode
    rw [List.sum_map_add]
    simp [sum_counts_interval hn hF, mul_comm]

  let target (n : ℕ) : Finset (List ℕ ⊕ List ℕ) :=
    (comps (2 * n - 2)).disjSum (comps (2 * n - 1))

  let encodeTag (n : ℕ) (F : Multiset ℕ) : List ℕ ⊕ List ℕ :=
    if F.card % 2 = 1 then Sum.inl (encode n F) else Sum.inr (encode n F)

  have encode_mem_target {n : ℕ} (hn : 1 ≤ n) {F : Multiset ℕ} (hF : F ∈ A n) :
      encodeTag n F ∈ target n := by
    unfold encodeTag target
    by_cases hp : F.card % 2 = 1
    · rw [if_pos hp]
      rw [Finset.mem_disjSum]
      apply Or.inl
      refine ⟨encode n F, ?_, rfl⟩
      rw [mem_comps]
      constructor
      · have hs := encode_sum hn hF
        have ht := A_threshold_le_n hF
        omega
      · exact encode_parts hF
    · rw [if_neg hp]
      rw [Finset.mem_disjSum]
      apply Or.inr
      refine ⟨encode n F, ?_, rfl⟩
      rw [mem_comps]
      constructor
      · have hs := encode_sum hn hF
        have ht := A_threshold_le_n hF
        have hm := Nat.mod_lt F.card (by omega : 0 < 2)
        have hp0 : F.card % 2 = 0 := by omega
        have hc : 1 ≤ F.card := Multiset.card_pos_iff_exists_mem.mpr ⟨n, (mem_A.mp hF).2.1⟩
        omega
      · exact encode_parts hF

  have map_range_count_inj (F G : Multiset ℕ) (i L : ℕ)
      (h : (List.range' i L).map (fun x => 2 + F.count x) =
        (List.range' i L).map (fun x => 2 + G.count x)) :
      ∀ x, i ≤ x → x < i + L → F.count x = G.count x := by
    induction L generalizing i with
    | zero => intro x hix hxi; omega
    | succ L ih =>
        simp only [List.range'_succ, List.map_cons, List.cons.injEq] at h
        intro x hix hxi
        by_cases hxi' : x = i
        · subst x
          omega
        · exact ih (i + 1) h.2 x (by omega) (by omega)

  have encode_injective {n : ℕ} (hn : 1 ≤ n) {F G : Multiset ℕ}
      (hF : F ∈ A n) (hG : G ∈ A n) (he : encodeTag n F = encodeTag n G) : F = G := by
    have hlist : encode n F = encode n G := by
      unfold encodeTag at he
      split at he <;> split at he <;> simp_all
    have hlen := congrArg List.length hlist
    rw [encode_length, encode_length] at hlen
    have htF := A_threshold_le_n hF
    have htG := A_threshold_le_n hG
    have ht : (F.card + 1) / 2 = (G.card + 1) / 2 := by omega
    apply Multiset.ext.mpr
    intro x
    by_cases hlo : x < (F.card + 1) / 2
    · have hzF : F.count x = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hx
        exact (Nat.not_le_of_gt hlo) (A_threshold_le_of_mem hF hx)
      have hzG : G.count x = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hx
        have hxlo := A_threshold_le_of_mem hG hx
        rw [← ht] at hxlo
        exact (Nat.not_le_of_gt hlo) hxlo
      rw [hzF, hzG]
    · by_cases hxn : x < n
      · unfold encode at hlist
        rw [ht] at hlist
        exact map_range_count_inj F G ((G.card + 1) / 2) (n - (G.card + 1) / 2) hlist x
          (by omega) (by omega)
      · by_cases hx : x = n
        · subst x
          rw [A_count_n hn hF, A_count_n hn hG]
        · have hzF : F.count x = 0 := by
            apply Multiset.count_eq_zero.mpr
            intro hxm
            have := A_mem_le_n hF hxm
            omega
          have hzG : G.count x = 0 := by
            apply Multiset.count_eq_zero.mpr
            intro hxm
            have := A_mem_le_n hG hxm
            omega
          rw [hzF, hzG]

  have two_mul_length_le_sum {l : List ℕ}
      (hp : ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4) : 2 * l.length ≤ l.sum := by
    induction l with
    | nil => simp
    | cons d ds ih =>
        have hd := hp d (by simp)
        have hds : ∀ e ∈ ds, e = 2 ∨ e = 3 ∨ e = 4 := by
          intro e he
          exact hp e (by simp [he])
        simp only [List.length_cons, List.sum_cons]
        have := ih hds
        omega

  have sum_sub_two {l : List ℕ}
      (hp : ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4) :
      (l.map fun d => d - 2).sum = l.sum - 2 * l.length := by
    induction l with
    | nil => simp
    | cons d ds ih =>
        have hd := hp d (by simp)
        have hds : ∀ e ∈ ds, e = 2 ∨ e = 3 ∨ e = 4 := by
          intro e he
          exact hp e (by simp [he])
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih hds]
        have hle := two_mul_length_le_sum hds
        rcases hd with rfl | rfl | rfl <;> omega

  have decode_card (n : ℕ) {l : List ℕ}
      (hp : ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4) :
      (decode n l).card = l.sum - 2 * l.length + 1 := by
    simp only [decode, Multiset.card_add, Multiset.card_singleton, card_decodeFrom]
    rw [sum_sub_two hp]

  have ground_count_eq_two {n x : ℕ} (hx0 : 1 ≤ x) (hxn : x < n) :
      (ground n).count x = 2 := by
    rw [count_ground]
    have hne : x ≠ n := by omega
    simp [hx0, hxn, hne]

  have count_decodeFrom_le_two (i : ℕ) {l : List ℕ}
      (hp : ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4) (x : ℕ) :
      (decodeFrom i l).count x ≤ 2 := by
    induction l generalizing i x with
    | nil => simp [decodeFrom]
    | cons d ds ih =>
        have hd := hp d (by simp)
        have hds : ∀ e ∈ ds, e = 2 ∨ e = 3 ∨ e = 4 := by
          intro e he
          exact hp e (by simp [he])
        by_cases hxi : x = i
        · subst x
          simp [decodeFrom, count_decodeFrom_of_lt]
          rcases hd with rfl | rfl | rfl <;> omega
        · have hne : i ≠ x := by omega
          simp only [decodeFrom, Multiset.count_add, Multiset.count_replicate, if_neg hne,
            zero_add]
          simpa using ih (i + 1) hds x

  have decodeFrom_encode (i : ℕ) {l : List ℕ}
      (hp : ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4) :
      (List.range' i l.length).map (fun x => 2 + (decodeFrom i l).count x) = l := by
    induction l generalizing i with
    | nil => simp
    | cons d ds ih =>
        have hd := hp d (by simp)
        have hds : ∀ e ∈ ds, e = 2 ∨ e = 3 ∨ e = 4 := by
          intro e he
          exact hp e (by simp [he])
        simp only [List.length_cons, List.range'_succ, List.map_cons, List.cons.injEq]
        constructor
        · simp [decodeFrom, count_decodeFrom_of_lt]
          rcases hd with rfl | rfl | rfl <;> omega
        · calc
            (List.range' (i + 1) ds.length).map
                (fun x => 2 + (decodeFrom i (d :: ds)).count x) =
              (List.range' (i + 1) ds.length).map
                (fun x => 2 + (decodeFrom (i + 1) ds).count x) := by
                  apply List.map_congr_left
                  intro x hx
                  have hix : i < x := (List.mem_range'_1.mp hx).1
                  have hne : x ≠ i := by omega
                  simp [decodeFrom, Multiset.mem_replicate, hne]
            _ = ds := ih (i + 1) hds

  have decodeFrom_count_n {n : ℕ} {l : List ℕ} (hlen : l.length ≤ n) :
      (decodeFrom (n - l.length) l).count n = 0 := by
    apply count_decodeFrom_ge
    omega

  have decode_encode {n : ℕ} {l : List ℕ}
      (hlen : l.length ≤ n)
      (hp : ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4)
      (ht : ((decode n l).card + 1) / 2 = n - l.length) :
      encode n (decode n l) = l := by
    unfold encode
    rw [ht]
    have hnlen : n - (n - l.length) = l.length := by omega
    rw [hnlen]
    calc
      (List.range' (n - l.length) l.length).map
          (fun x => 2 + (decode n l).count x) =
        (List.range' (n - l.length) l.length).map
          (fun x => 2 + (decodeFrom (n - l.length) l).count x) := by
            apply List.map_congr_left
            intro x hx
            simp only [decode, Multiset.count_add, Multiset.count_singleton]
            have hxn : x ≠ n := by
              have hx' := List.mem_range'_1.mp hx
              omega
            simp [hxn]
      _ = l := decodeFrom_encode (n - l.length) hp

  have decode_mem_A {n : ℕ} (hn : 1 ≤ n) {l : List ℕ}
      (hp : ∀ d ∈ l, d = 2 ∨ d = 3 ∨ d = 4)
      (hlen : l.length < n)
      (hcard : (decode n l).card ≤ 2 * (n - l.length)) :
      decode n l ∈ A n := by
    rw [mem_A]
    have hstart : 1 ≤ n - l.length := by omega
    have hsumlen : n - l.length + l.length = n := by omega
    constructor
    · rw [Multiset.le_iff_count]
      intro x
      by_cases hxn : x = n
      · subst x
        rw [ground_count_n n hn]
        simp [decode, decodeFrom_count_n (Nat.le_of_lt hlen)]
      · simp only [decode, Multiset.count_add, Multiset.count_singleton, if_neg hxn,
          add_zero]
        by_cases hx0 : (decodeFrom (n - l.length) l).count x = 0
        · simp [hx0]
        · have hxm : x ∈ decodeFrom (n - l.length) l :=
            Multiset.count_pos.mp (Nat.pos_of_ne_zero hx0)
          have hbounds := mem_decodeFrom (n - l.length) x l hxm
          rw [ground_count_eq_two (by omega) (by omega)]
          exact count_decodeFrom_le_two (n - l.length) hp x
    · constructor
      · simp [decode]
      · intro x hx
        simp only [decode, Multiset.mem_add, Multiset.mem_singleton] at hx
        rcases hx with hx | rfl
        · have hix := (mem_decodeFrom (n - l.length) x l hx).1
          omega
        · omega

  have decode_left_data {n : ℕ} (hn : 1 ≤ n) {l : List ℕ}
      (hl : l ∈ comps (2 * n - 2)) :
      decode n l ∈ A n ∧ ((decode n l).card + 1) / 2 = n - l.length ∧
        encodeTag n (decode n l) = Sum.inl l := by
    have hdata := (mem_comps (2 * n - 2) l).mp hl
    have hsum := hdata.1
    have hp := hdata.2
    have hlen2 := two_mul_length_le_sum hp
    have hlen : l.length < n := by omega
    have hc := decode_card n hp
    have hcardeq : (decode n l).card = 2 * (n - l.length) - 1 := by omega
    have ht : ((decode n l).card + 1) / 2 = n - l.length := by
      omega
    have hmem : decode n l ∈ A n := decode_mem_A hn hp hlen (by omega)
    refine ⟨hmem, ht, ?_⟩
    unfold encodeTag
    rw [if_pos]
    · exact congrArg Sum.inl (decode_encode (Nat.le_of_lt hlen) hp ht)
    · rw [hcardeq]
      omega

  have decode_right_data {n : ℕ} (hn : 1 ≤ n) {l : List ℕ}
      (hl : l ∈ comps (2 * n - 1)) :
      decode n l ∈ A n ∧ ((decode n l).card + 1) / 2 = n - l.length ∧
        encodeTag n (decode n l) = Sum.inr l := by
    have hdata := (mem_comps (2 * n - 1) l).mp hl
    have hsum := hdata.1
    have hp := hdata.2
    have hlen2 := two_mul_length_le_sum hp
    have hlen : l.length < n := by omega
    have hc := decode_card n hp
    have hcardeq : (decode n l).card = 2 * (n - l.length) := by omega
    have ht : ((decode n l).card + 1) / 2 = n - l.length := by
      omega
    have hmem : decode n l ∈ A n := decode_mem_A hn hp hlen (by omega)
    refine ⟨hmem, ht, ?_⟩
    unfold encodeTag
    rw [if_neg]
    · exact congrArg Sum.inr (decode_encode (Nat.le_of_lt hlen) hp ht)
    · rw [hcardeq]
      omega

  have bridge_identity (n : ℕ) (hn : 1 ≤ n) :
      a n = c (2 * n - 2) + c (2 * n - 1) := by
    unfold a c
    rw [← Finset.card_disjSum]
    apply Finset.card_bij (fun F _ => encodeTag n F)
    · intro F hF
      exact encode_mem_target hn hF
    · intro F hF G hG he
      exact encode_injective hn hF hG he
    · intro b hb
      rw [Finset.mem_disjSum] at hb
      rcases hb with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
      · refine ⟨decode n l, (decode_left_data hn hl).1, ?_⟩
        exact (decode_left_data hn hl).2.2
      · refine ⟨decode n l, (decode_right_data hn hl).1, ?_⟩
        exact (decode_right_data hn hl).2.2
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have ha4 : a (m + 4) = c (2 * m + 6) + c (2 * m + 7) := by
    simpa only [show 2 * (m + 4) - 2 = 2 * m + 6 by omega,
      show 2 * (m + 4) - 1 = 2 * m + 7 by omega] using
        bridge_identity (m + 4) (by omega)
  have ha3 : a (m + 3) = c (2 * m + 4) + c (2 * m + 5) := by
    simpa only [show 2 * (m + 3) - 2 = 2 * m + 4 by omega,
      show 2 * (m + 3) - 1 = 2 * m + 5 by omega] using
        bridge_identity (m + 3) (by omega)
  have ha2 : a (m + 2) = c (2 * m + 2) + c (2 * m + 3) := by
    simpa only [show 2 * (m + 2) - 2 = 2 * m + 2 by omega,
      show 2 * (m + 2) - 1 = 2 * m + 3 by omega] using
        bridge_identity (m + 2) (by omega)
  have ha1 : a (m + 1) = c (2 * m) + c (2 * m + 1) := by
    simpa only [show 2 * (m + 1) - 2 = 2 * m by omega,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega] using
        bridge_identity (m + 1) (by omega)
  have hc6 : c (2 * m + 6) = c (2 * m + 4) + c (2 * m + 3) + c (2 * m + 2) := by
    simpa only [show 2 * m + 6 - 2 = 2 * m + 4 by omega,
      show 2 * m + 6 - 3 = 2 * m + 3 by omega,
      show 2 * m + 6 - 4 = 2 * m + 2 by omega] using
        c_recurrence (2 * m + 6) (by omega)
  have hc7 : c (2 * m + 7) = c (2 * m + 5) + c (2 * m + 4) + c (2 * m + 3) := by
    simpa only [show 2 * m + 7 - 2 = 2 * m + 5 by omega,
      show 2 * m + 7 - 3 = 2 * m + 4 by omega,
      show 2 * m + 7 - 4 = 2 * m + 3 by omega] using
        c_recurrence (2 * m + 7) (by omega)
  have hc4 : c (2 * m + 4) = c (2 * m + 2) + c (2 * m + 1) + c (2 * m) := by
    simpa only [show 2 * m + 4 - 2 = 2 * m + 2 by omega,
      show 2 * m + 4 - 3 = 2 * m + 1 by omega,
      show 2 * m + 4 - 4 = 2 * m by omega] using
        c_recurrence (2 * m + 4) (by omega)
  simp only [show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  rw [ha4, ha3, ha2, ha1, hc6, hc7, hc4]
  omega

end D5.S1.Recurrence.ChuSchreierMultisetRecurrenceQTwo
