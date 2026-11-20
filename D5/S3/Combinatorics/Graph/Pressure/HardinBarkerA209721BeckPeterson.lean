/- GID: D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721BeckPeterson
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721BeckPeterson
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The three-column array count is A029744(n+1)+1, obeys a two-step law, counts sides. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#224)
escape_witness: two_step (the order-three recurrence and the initial values force
  a(n+3) - 2 a(n+1) to stay at a(3) - 2 a(1) = -1)
proof_shape:
  IsA029744, thirdSides, claim: source definitions; consumers: range_seq and nth_eq,
    third_iff, beck_peterson respectively.
  seq: private definition; consumers: seq_lt_succ, seq_odd, seq_even, range_seq, nth_eq,
    closed, beck_peterson.
  seq_lt_succ: content (induction through the doubling step); consumers: nth_eq, beck_peterson.
  seq_odd, seq_even: content (induction); consumer: range_seq.
  range_seq: content (parity split of the index); consumer: nth_eq.
  nth_eq: content (two strictly monotone enumerations of one set agree); consumer: beck_peterson.
  two_step: content (induction on the frozen recurrence); consumers: closed, beck_peterson.
  closed: content (induction on two_step); consumer: beck_peterson.
  third_iff: content (integrality of the triangle inequalities); consumer: beck_peterson.
  beck_peterson: content via the helpers above.
Direct frozen dependency: D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences
  (a, result.1, a_initial). a_initial was private there; it is made public and its owner
  re-pinned instead of re-proving the initial values.
-/

import D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721EdgeDifferences
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card

/-! # Beck and Peterson identities for the three-column array count

Let `a n` be one quarter of the number of `(n+1) × 3` arrays over `0..2` whose consecutive
`2 × 2` squares have distinct clockwise edge differences (OEIS A209721). For `n ≥ 1`,
`a n = A029744(n+1) + 1`, where A029744 lists the numbers `2^k` and `3·2^k` in increasing
order. For `n ≥ 3`, `a n = 2 a (n-2) - 1`, and `a n` counts the positive integers `c` that
form a nondegenerate triangle with sides `a (n-1)` and `a (n-2)`; these are exactly
`a (n-1) - a (n-2) + 1 ≤ c ≤ a (n-1) + a (n-2) - 1`.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721BeckPeterson

open D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721EdgeDifferences

/-- OEIS A029744: numbers of the form `2^k` or `3*2^k`. Its offset is one, so
`Nat.nth IsA029744 n` is the term `A029744(n+1)`. -/
def IsA029744 (m : ℕ) : Prop :=
  (∃ k, m = 2 ^ k) ∨ ∃ k, m = 3 * 2 ^ k

/-- The positive integers `c` such that `x`, `y`, `c` are the sides of a nondegenerate
triangle. -/
def thirdSides (x y : ℚ) : Set ℕ :=
  {c | 0 < c ∧ (c : ℚ) < x + y ∧ x < y + c ∧ y < x + c}

/-- The terms `A029744(n+1)`, enumerated by doubling every second term. -/
private def seq : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | n + 3 => 2 * seq (n + 1)

private theorem seq_lt_succ : ∀ n, seq n < seq (n + 1)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    have := seq_lt_succ (n + 1)
    simp only [seq] at this ⊢
    omega

private theorem seq_odd : ∀ k, seq (2 * k + 1) = 2 ^ (k + 1)
  | 0 => rfl
  | k + 1 => by
    rw [show 2 * (k + 1) + 1 = (2 * k) + 3 by ring, seq, seq_odd k, pow_succ]
    ring

private theorem seq_even : ∀ k, seq (2 * k + 2) = 3 * 2 ^ k
  | 0 => rfl
  | k + 1 => by
    rw [show 2 * (k + 1) + 2 = (2 * k + 1) + 3 by ring, seq,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring, seq_even k, pow_succ]
    ring

private theorem range_seq : Set.range seq = Set.ofPred IsA029744 := by
  ext m
  rw [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases k with _ | k
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inr ⟨k, by rw [show 2 * (k + 1) = 2 * k + 2 by ring, seq_even]⟩
    · exact Or.inl ⟨k + 1, seq_odd k⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · rcases k with _ | k
      · exact ⟨0, rfl⟩
      · exact ⟨2 * k + 1, seq_odd k⟩
    · exact ⟨2 * k + 2, seq_even k⟩

private theorem nth_eq : Nat.nth IsA029744 = seq := by
  have hmono : StrictMono seq := strictMono_nat_of_lt_succ seq_lt_succ
  have hinf : (Set.ofPred IsA029744).Infinite := by
    rw [← range_seq]
    exact Set.infinite_range_of_injective hmono.injective
  exact (StrictMono.range_inj_of_wellFoundedLT (Nat.nth_strictMono hinf) hmono).1
    (by rw [Nat.range_nth_of_infinite hinf, range_seq])

/-- Peterson's two-step recurrence: the quantity `a (n+3) - 2 a (n+1)` is constant. -/
private theorem two_step : ∀ n, a (n + 3) = 2 * a (n + 1) - 1
  | 0 => by
    obtain ⟨h1, -, h3⟩ := a_initial
    rw [h3, h1]; norm_num
  | n + 1 => by
    have := two_step n
    have hr := result.1 n
    linarith

private theorem closed : ∀ n, a (n + 1) = (seq (n + 1) : ℚ) + 1
  | 0 => by rw [a_initial.1]; norm_num [seq]
  | 1 => by rw [a_initial.2.1]; norm_num [seq]
  | n + 2 => by
    rw [two_step n, closed n, seq]
    push_cast
    ring

private theorem third_iff (X Y c : ℕ) (h : Y < X) :
    c ∈ thirdSides ((X : ℚ) + 1) ((Y : ℚ) + 1) ↔ X - Y + 1 ≤ c ∧ c ≤ X + Y + 1 := by
  simp only [thirdSides, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, h1, h2, -⟩
    have h1' : c < X + Y + 2 := by exact_mod_cast (show (c : ℚ) < X + Y + 2 by linarith)
    have h2' : X < Y + c := by exact_mod_cast (show (X : ℚ) < Y + c by linarith)
    omega
  · rintro ⟨h1, h2⟩
    have h1' : X + 1 ≤ Y + c := by omega
    have h1q : (X : ℚ) + 1 ≤ Y + c := by exact_mod_cast h1'
    have h2q : (c : ℚ) ≤ X + Y + 1 := by exact_mod_cast h2
    have hq : (Y : ℚ) < X := by exact_mod_cast h
    refine ⟨by omega, by linarith, by linarith, by linarith⟩

/-- OEIS A209721 comments of George Beck and Richard Locke Peterson. With offset one,
`Nat.nth IsA029744 n` is `A029744(n+1)`. For `n ≥ 3` the third sides are counted against the
two previous terms `a (n-1)` and `a (n-2)`. -/
def claim : Prop :=
  (∀ n, 1 ≤ n → a n = (Nat.nth IsA029744 n : ℚ) + 1) ∧
  (∀ n, 3 ≤ n → a n = 2 * a (n - 2) - 1) ∧
  (∀ n, 3 ≤ n →
    (∀ c : ℕ, c ∈ thirdSides (a (n - 1)) (a (n - 2)) ↔
      a (n - 1) - a (n - 2) + 1 ≤ c ∧ (c : ℚ) ≤ a (n - 1) + a (n - 2) - 1) ∧
    ((thirdSides (a (n - 1)) (a (n - 2))).ncard : ℚ) = a n)

theorem beck_peterson : claim := by
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [closed, nth_eq]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 2 = m + 1 by omega]
    exact two_step m
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, closed (m + 1),
      closed m, closed (m + 2)]
    have hlt : seq (m + 1) < seq (m + 2) := seq_lt_succ (m + 1)
    have hset : thirdSides ((seq (m + 2) : ℚ) + 1) ((seq (m + 1) : ℚ) + 1) =
        ↑(Finset.Icc (seq (m + 2) - seq (m + 1) + 1) (seq (m + 2) + seq (m + 1) + 1)) := by
      ext c
      rw [third_iff _ _ _ hlt, Finset.coe_Icc, Set.mem_Icc]
    refine ⟨fun c => ?_, ?_⟩
    · rw [third_iff _ _ _ hlt]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : seq (m + 2) + 1 ≤ seq (m + 1) + c := by omega
        have h1q : ((seq (m + 2) : ℕ) : ℚ) + 1 ≤ seq (m + 1) + c := by exact_mod_cast h1'
        have h2q : (c : ℚ) ≤ seq (m + 2) + seq (m + 1) + 1 := by exact_mod_cast h2
        constructor <;> linarith
      · rintro ⟨h1, h2⟩
        have h1' : seq (m + 2) + 1 ≤ seq (m + 1) + c := by
          exact_mod_cast (show ((seq (m + 2) : ℕ) : ℚ) + 1 ≤ seq (m + 1) + c by linarith)
        have h2' : c ≤ seq (m + 2) + seq (m + 1) + 1 := by
          exact_mod_cast (show (c : ℚ) ≤ seq (m + 2) + seq (m + 1) + 1 by linarith)
        omega
    · rw [hset, Set.ncard_coe_finset, Nat.card_Icc,
        show seq (m + 2) + seq (m + 1) + 1 + 1 - (seq (m + 2) - seq (m + 1) + 1) =
          2 * seq (m + 1) + 1 by omega, show m + 2 + 1 = m + 3 from rfl, seq]
      push_cast
      ring

end D5.S3.Combinatorics.Graph.Pressure.HardinBarkerA209721BeckPeterson
