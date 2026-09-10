/- GID: D5/S1/Words/Complexity/ThueMorseReducedAbelianEven
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ThueMorseReducedAbelianEven
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: All-start alternation extrema and even reduced abelian complexity. -/

import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators

namespace D5.S1.Words.Complexity

open private transition alternations alternations_le runs runs_le
  thueMorse_zero thueMorse_two_mul thueMorse_two_mul_add_one
  transition_two_mul transition_two_mul_add_one
  alternations_double_even alternations_double_odd
  exists_complement_factor reducedAbelianCodes mem_reducedAbelianCodes_iff
  reducedAbelianCodes_card_eq_classes
  from D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd

open scoped BigOperators

/-- Minimum number of transitions in a factor with `n` edges, over all starts. -/
noncomputable def minAlternations (n : Nat) : Nat :=
  sInf (Set.range fun s => (reducedAbelianCode (n + 1) s).1 - 1)

/-- Maximum number of transitions in a factor with `n` edges, over all starts. -/
noncomputable def maxAlternations (n : Nat) : Nat :=
  sSup (Set.range fun s => (reducedAbelianCode (n + 1) s).1 - 1)

private theorem code_edges (n s : Nat) :
    (reducedAbelianCode (n + 1) s).1 - 1 = alternations n s := by
  simp [reducedAbelianCode, runs]

private theorem alt_bdd (n : Nat) : BddAbove (Set.range (alternations n)) :=
  ⟨n, by rintro _ ⟨s, rfl⟩; exact alternations_le n s⟩

private theorem min_attained (n : Nat) : ∃ s, alternations n s = minAlternations n := by
  simpa [minAlternations, code_edges] using
    (Nat.sInf_mem (Set.range_nonempty (alternations n)))

private theorem max_attained (n : Nat) : ∃ s, alternations n s = maxAlternations n := by
  simpa [maxAlternations, code_edges] using
    (Nat.sSup_mem (Set.range_nonempty (alternations n)) (alt_bdd n))

private theorem min_le_alt (n s : Nat) : minAlternations n ≤ alternations n s := by
  simpa [minAlternations, code_edges] using
    (Nat.sInf_le (Set.mem_range_self s) : sInf (Set.range (alternations n)) ≤ _)

private theorem alt_le_max (n s : Nat) : alternations n s ≤ maxAlternations n := by
  simpa [maxAlternations, code_edges] using
    (le_csSup (alt_bdd n) (Set.mem_range_self s))

private theorem extrema_bounds (n : Nat) :
    minAlternations n ≤ maxAlternations n ∧ maxAlternations n ≤ n := by
  obtain ⟨s, hs⟩ := max_attained n
  constructor
  · simpa [hs] using min_le_alt n s
  · simpa [hs] using alternations_le n s

private theorem transition_le_one (s : Nat) : transition s ≤ 1 := by
  unfold transition
  split <;> omega

private theorem alt_snoc (n s : Nat) :
    alternations (n + 1) s = alternations n s + transition (s + n) := by
  induction n generalizing s with
  | zero => simp [alternations]
  | succ n ih =>
      change transition s + alternations (n + 1) (s + 1) =
        (transition s + alternations n (s + 1)) + transition (s + (n + 1))
      rw [ih]
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem extrema_step (n : Nat) :
    minAlternations n ≤ minAlternations (n + 1) ∧
      maxAlternations n ≤ maxAlternations (n + 1) := by
  obtain ⟨s, hs⟩ := min_attained (n + 1)
  obtain ⟨t, ht⟩ := max_attained n
  have hmin := min_le_alt n s
  have hmax := alt_le_max (n + 1) t
  rw [alt_snoc] at hs hmax
  omega

private theorem alt_odd_even (n q : Nat) :
    alternations (2 * n + 1) (2 * q) = 2 * n + 1 - alternations n q := by
  rw [alternations, transition_two_mul, alternations_double_odd]
  have h := alternations_le n q
  omega

private theorem alt_odd_odd (n q : Nat) :
    alternations (2 * n + 1) (2 * q + 1) =
      2 * n + 1 - alternations (n + 1) q := by
  rw [alternations, transition_two_mul_add_one]
  rw [show 2 * q + 1 + 1 = 2 * (q + 1) by omega, alternations_double_even]
  have h := alternations_le n (q + 1)
  have ht := transition_le_one q
  simp only [alternations]
  omega

private theorem extrema_even (n : Nat) :
    minAlternations (2 * n) = 2 * n - maxAlternations n ∧
      maxAlternations (2 * n) = 2 * n - minAlternations n := by
  have hb := extrema_bounds n
  have formula (s : Nat) :
      alternations (2 * n) s = 2 * n - alternations n (s / 2) := by
    obtain ⟨q, rfl | rfl⟩ := s.even_or_odd'
    · simpa using alternations_double_even n q
    · simpa only [show (2 * q + 1) / 2 = q by omega] using alternations_double_odd n q
  obtain ⟨s, hs⟩ := min_attained (2 * n)
  obtain ⟨t, ht⟩ := max_attained (2 * n)
  obtain ⟨u, hu⟩ := min_attained n
  obtain ⟨v, hv⟩ := max_attained n
  have h1 := min_le_alt (2 * n) (2 * v)
  have h2 := alt_le_max (2 * n) (2 * u)
  have h3 := alt_le_max n (s / 2)
  have h4 := min_le_alt n (t / 2)
  rw [alternations_double_even, hv] at h1
  rw [alternations_double_even, hu] at h2
  rw [formula] at hs ht
  constructor <;> omega

private theorem extrema_odd (n : Nat) :
    minAlternations (2 * n + 1) = 2 * n + 1 - maxAlternations (n + 1) ∧
      maxAlternations (2 * n + 1) = 2 * n + 1 - minAlternations n := by
  have hb := extrema_bounds n
  have hb' := extrema_bounds (n + 1)
  have hstep := extrema_step n
  have bounds (s : Nat) :
      2 * n + 1 - maxAlternations (n + 1) ≤ alternations (2 * n + 1) s ∧
        alternations (2 * n + 1) s ≤ 2 * n + 1 - minAlternations n := by
    obtain ⟨q, rfl | rfl⟩ := s.even_or_odd'
    · rw [alt_odd_even]
      have h1 := min_le_alt n q
      have h2 := alt_le_max n q
      constructor <;> omega
    · rw [alt_odd_odd]
      have h1 := min_le_alt (n + 1) q
      have h2 := alt_le_max (n + 1) q
      constructor <;> omega
  obtain ⟨s, hs⟩ := min_attained (2 * n + 1)
  obtain ⟨t, ht⟩ := max_attained (2 * n + 1)
  obtain ⟨u, hu⟩ := max_attained (n + 1)
  obtain ⟨v, hv⟩ := min_attained n
  have h1 := (bounds s).1
  have h2 := (bounds t).2
  have h3 := min_le_alt (2 * n + 1) (2 * u + 1)
  have h4 := alt_le_max (2 * n + 1) (2 * v)
  rw [alt_odd_odd, hu] at h3
  rw [alt_odd_even, hv] at h4
  constructor <;> omega

private theorem thueMorse_triple_boundary (n : Nat) :
    (thueMorse (n + 1) = thueMorse (3 * (n + 1))) ↔
      (thueMorse n = thueMorse (3 * n + 2)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
      · rw [show 3 * (2 * k + 1) = 2 * (3 * k + 1) + 1 by omega,
          show 3 * (2 * k) + 2 = 2 * (3 * k + 1) by omega]
        simp
      · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
          show 3 * (2 * (k + 1)) = 2 * (3 * (k + 1)) by omega,
          show 3 * (2 * k + 1) + 2 = 2 * (3 * k + 2) + 1 by omega]
        simpa using ih k (by omega)

/-- The parity of the all-start transition spectrum width is a triple-index comparison. -/
theorem alternation_extrema_parity (n : Nat) :
    (minAlternations n + maxAlternations n) % 2 =
      if thueMorse n = thueMorse (3 * n) then 0 else 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        have hb := extrema_bounds 0
        simp only [Nat.mul_zero, ↓reduceIte]
        omega
      obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
      · have hi := ih k (by omega)
        have he := extrema_even k
        have hb := extrema_bounds k
        rw [show 3 * (2 * k) = 2 * (3 * k) by omega]
        simp only [thueMorse_two_mul]
        omega
      · obtain ⟨j, rfl | rfl⟩ := k.even_or_odd'
        · have hi := ih j (by omega)
          have he := extrema_even j
          have ho := extrema_odd j
          have hbig := extrema_odd (2 * j)
          have hb := extrema_bounds j
          rw [show 3 * (2 * (2 * j) + 1) = 2 * (2 * (3 * j) + 1) + 1 by omega]
          simp only [thueMorse_two_mul, thueMorse_two_mul_add_one]
          cases h0 : thueMorse j <;> cases h1 : thueMorse (3 * j) <;>
            simp [h0, h1] at hi ⊢ <;> omega
        · have hi := ih (j + 1) (by omega)
          have he := extrema_even (j + 1)
          have ho := extrema_odd j
          have hbig := extrema_odd (2 * j + 1)
          have hb := extrema_bounds (j + 1)
          have ht := thueMorse_triple_boundary j
          rw [show 3 * (2 * (2 * j + 1) + 1) = 2 * (2 * (3 * j + 2)) + 1 by omega]
          simp only [thueMorse_two_mul, thueMorse_two_mul_add_one, Bool.not_not]
          simp only [ht] at hi
          have heq : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
          rw [heq] at hbig
          cases h0 : thueMorse j <;> cases h1 : thueMorse (3 * j + 2) <;>
            simp [h0, h1] at hi ⊢ <;> omega

private theorem discrete_walk_hits (f : Nat → Nat)
    (hstep : ∀ s, f (s + 1) ≤ f s + 1 ∧ f s ≤ f (s + 1) + 1)
    (m k : Nat) (hlo : min (f 0) (f m) ≤ k) (hhi : k ≤ max (f 0) (f m)) :
    ∃ s, f s = k := by
  induction m with
  | zero => exact ⟨0, by simpa using le_antisymm hlo hhi⟩
  | succ m ih =>
      by_cases h : min (f 0) (f m) ≤ k ∧ k ≤ max (f 0) (f m)
      · exact ih h.1 h.2
      · have hs := hstep m
        exact ⟨m + 1, by omega⟩

private theorem alt_interval (n k : Nat) :
    (∃ s, alternations n s = k) ↔ minAlternations n ≤ k ∧ k ≤ maxAlternations n := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨min_le_alt n s, alt_le_max n s⟩
  · rintro ⟨hlo, hhi⟩
    have step (s : Nat) :
        alternations n (s + 1) ≤ alternations n s + 1 ∧
          alternations n s ≤ alternations n (s + 1) + 1 := by
      have h := alt_snoc n s
      have h1 := transition_le_one s
      have h2 := transition_le_one (s + n)
      rw [alternations] at h
      constructor <;> omega
    obtain ⟨s, hs⟩ := min_attained n
    obtain ⟨t, ht⟩ := max_attained n
    by_cases h0 : alternations n 0 ≤ k
    · exact discrete_walk_hits (alternations n) step t k (by omega) (by omega)
    · exact discrete_walk_hits (alternations n) step s k (by omega) (by omega)

private def runCodeInterval (a b : Nat) : Finset (Nat × Bool) :=
  ((Finset.Icc a b).product Finset.univ).filter fun c => c.1 % 2 = 1 ∨ c.2 = false

private def weightedInterval (a b : Nat) : Nat :=
  ∑ r ∈ Finset.Icc a b, (1 + r % 2)

private theorem runCodeInterval_card (a b : Nat) :
    (runCodeInterval a b).card = weightedInterval a b := by
  rw [runCodeInterval, Finset.product_eq_sprod, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r _
  have hr := Nat.mod_lt r (by decide : 0 < 2)
  by_cases h : r % 2 = 1
  · simp [h]
  · have h0 : r % 2 = 0 := by omega
    simp [h, h0]

private theorem code_spectrum (n : Nat) :
    reducedAbelianCodes (n + 1) =
      runCodeInterval (minAlternations n + 1) (maxAlternations n + 1) := by
  classical
  ext c
  rw [mem_reducedAbelianCodes_iff (by omega : 0 < n + 1)]
  simp only [runCodeInterval, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨s, rfl⟩
    have hmin := min_le_alt n s
    have hmax := alt_le_max n s
    simp only [reducedAbelianCode, runs, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel, Nat.odd_iff]
    constructor
    · constructor <;> omega
    · split <;> simp_all
  · rintro ⟨⟨hmin, hmax⟩, hb⟩
    obtain ⟨s, hs⟩ := (alt_interval n (c.1 - 1)).mpr ⟨by omega, by omega⟩
    have hrs : runs (n + 1) s = c.1 := by
      simp only [runs, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      omega
    by_cases ho : Odd c.1
    · by_cases ht : thueMorse s = c.2
      · exact ⟨s, by simp [reducedAbelianCode, hrs, ho, ht]⟩
      · obtain ⟨t, htr, htt⟩ := exists_complement_factor (n + 1) s
        have htc : thueMorse t = c.2 := by
          rw [htt]
          exact Bool.not_eq_iff.mpr ht
        exact ⟨t, by simp [reducedAbelianCode, htr, hrs, ho, htc]⟩
    · have hc : c.2 = false := hb.resolve_left (by simpa [Nat.odd_iff] using ho)
      refine ⟨s, ?_⟩
      simp only [reducedAbelianCode, hrs, ho, ↓reduceIte]
      exact Prod.ext rfl hc.symm

private theorem complexity_weighted (n : Nat) :
    R (n + 1) = weightedInterval (minAlternations n + 1) (maxAlternations n + 1) := by
  rw [R, ← reducedAbelianCodes_card_eq_classes (n + 1) (by omega),
    code_spectrum, runCodeInterval_card]

private theorem weightedInterval_shift (a b : Nat) (h : a ≤ b + 1) :
    weightedInterval (a + 1) (b + 1) + (1 + a % 2) =
      weightedInterval a b + (1 + (b + 1) % 2) := by
  have hi : Finset.Icc a (b + 1) = insert a (Finset.Icc (a + 1) (b + 1)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hn : a ∉ Finset.Icc (a + 1) (b + 1) := by simp
  have ht := Finset.sum_Icc_succ_top h (fun r => 1 + r % 2)
  rw [hi, Finset.sum_insert hn] at ht
  unfold weightedInterval
  omega

private theorem even_complexity_intervals (n : Nat) (hn : 0 < n) :
    R (4 * n) = weightedInterval (2 * n + minAlternations n)
      (2 * n + 1 + maxAlternations n) ∧
    R (4 * n + 2) = weightedInterval (2 * n + minAlternations n + 1)
      (2 * n + 1 + maxAlternations n + 1) := by
  have he := extrema_even n
  have ho := extrema_odd n
  have hp := extrema_odd (n - 1)
  have hbig := extrema_odd (2 * n - 1)
  have hbig' := extrema_odd (2 * n)
  have hb := extrema_bounds n
  rw [show n - 1 + 1 = n by omega, show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at hp
  rw [show 2 * n - 1 + 1 = 2 * n by omega,
    show 2 * (2 * n - 1) + 1 = 4 * n - 1 by omega] at hbig
  rw [show 2 * (2 * n) + 1 = 4 * n + 1 by omega] at hbig'
  have h1 : minAlternations (4 * n - 1) + 1 = 2 * n + minAlternations n := by omega
  have h2 : maxAlternations (4 * n - 1) + 1 = 2 * n + 1 + maxAlternations n := by omega
  have h3 : minAlternations (4 * n + 1) + 1 = 2 * n + minAlternations n + 1 := by omega
  have h4 : maxAlternations (4 * n + 1) + 1 = 2 * n + 1 + maxAlternations n + 1 := by
    omega
  constructor
  · have hh := complexity_weighted (4 * n - 1)
    rwa [show 4 * n - 1 + 1 = 4 * n by omega, h1, h2] at hh
  · simpa only [h3, h4] using complexity_weighted (4 * n + 1)

/-- Equation (11) of Campbell-Currie-Rampersad, with zero-indexed Thue-Morse letters. -/
theorem reducedAbelianComplexity_even_difference (n : Nat) (hn : 0 < n) :
    ((R (4 * n + 2) : Int) - R (4 * n)).natAbs =
      if thueMorse n = thueMorse (3 * n) then 0 else 1 := by
  obtain ⟨h0, h1⟩ := even_complexity_intervals n hn
  have hb := extrema_bounds n
  have hshift := weightedInterval_shift (2 * n + minAlternations n)
    (2 * n + 1 + maxAlternations n) (by omega)
  rw [← h0, ← h1] at hshift
  have ha := Nat.mod_lt (minAlternations n) (by decide : 0 < 2)
  have hb' := Nat.mod_lt (maxAlternations n) (by decide : 0 < 2)
  have hp := alternation_extrema_parity n
  have hd : (R (4 * n + 2) : Int) - R (4 * n) =
      ((maxAlternations n % 2 : Nat) : Int) - ((minAlternations n % 2 : Nat) : Int) := by
    omega
  rw [hd]
  by_cases ht : thueMorse n = thueMorse (3 * n)
  · simp only [ht, ↓reduceIte] at hp ⊢
    have he : minAlternations n % 2 = maxAlternations n % 2 := by omega
    simp [he]
  · simp only [ht, ↓reduceIte] at hp ⊢
    have he : (minAlternations n % 2 = 0 ∧ maxAlternations n % 2 = 1) ∨
        (minAlternations n % 2 = 1 ∧ maxAlternations n % 2 = 0) := by omega
    rcases he with ⟨he0, he1⟩ | ⟨he0, he1⟩ <;> simp [he0, he1]

#print axioms alternation_extrema_parity
#print axioms reducedAbelianComplexity_even_difference

end D5.S1.Words.Complexity
