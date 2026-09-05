/- GID: D5/S1/Words/BarkerEvenLengthModFourObstruction
   generality: I
   mirror-B: D5/B/S1/Words/BarkerEvenLengthModFourObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A mod-four boundary congruence forces every even Barker sequence longer than two to have length divisible by four, with explicit Barker and non-Barker witnesses. -/

import Mathlib

open scoped BigOperators

namespace D5.S1.Words.BarkerEvenLengthModFourObstruction

/-- The `k`th aperiodic autocorrelation of the first `n` entries of `a`. -/
def aperiodicCorrelation (a : Nat -> Int) (n k : Nat) : Int :=
  ∑ i ∈ Finset.range (n - k), a i * a (i + k)

/-- The Barker condition on the first `n` entries of an integer sequence. -/
def IsBarker (a : Nat -> Int) (n : Nat) : Prop :=
  (∀ i < n, a i = 1 ∨ a i = -1) ∧
    ∀ k, 0 < k -> k < n -> |aperiodicCorrelation a n k| <= 1

private theorem sign_product_mod_four {x y : Int}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y ≡ x - y + 1 [ZMOD 4] := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [Int.ModEq]

private theorem correlation_mod_two {a : Nat -> Int} {n k : Nat}
    (ha : ∀ i < n, a i = 1 ∨ a i = -1) (hk : k <= n) :
    aperiodicCorrelation a n k ≡ (n - k : Nat) [ZMOD 2] := by
  unfold aperiodicCorrelation
  have hsum :
      (∑ i ∈ Finset.range (n - k), a i * a (i + k)) ≡
        ∑ _i ∈ Finset.range (n - k), (1 : Int) [ZMOD 2] := by
    apply Int.ModEq.sum
    intro i hi
    simp only [Finset.mem_range] at hi
    have hi0 : a i ≡ 1 [ZMOD 2] := by
      rcases ha i (by omega) with h | h
      · rw [h]
      · rw [h]
        norm_num [Int.ModEq]
    have hik : a (i + k) ≡ 1 [ZMOD 2] := by
      rcases ha (i + k) (by omega) with h | h
      · rw [h]
      · rw [h]
        norm_num [Int.ModEq]
    exact hi0.mul hik
  simpa using hsum

private theorem two_step_telescoping (f : Nat -> Int) (m : Nat) :
    (∑ i ∈ Finset.range m, (f i - f (i + 2))) =
      f 0 + f 1 - f m - f (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem correlation_two_pair_mod_four {a : Nat -> Int} {n : Nat}
    (ha : ∀ i < n, a i = 1 ∨ a i = -1) (hn : 2 <= n) :
    aperiodicCorrelation a n 2 + aperiodicCorrelation a n (n - 2) ≡
      (n : Int) [ZMOD 4] := by
  have hfirst :
      aperiodicCorrelation a n 2 ≡
        ∑ i ∈ Finset.range (n - 2), (a i - a (i + 2) + 1) [ZMOD 4] := by
    unfold aperiodicCorrelation
    apply Int.ModEq.sum
    intro i hi
    simp only [Finset.mem_range] at hi
    exact sign_product_mod_four (ha i (by omega)) (ha (i + 2) (by omega))
  have hfirstSum :
      (∑ i ∈ Finset.range (n - 2), (a i - a (i + 2) + 1)) =
        a 0 + a 1 - a (n - 2) - a (n - 1) + (n - 2 : Nat) := by
    rw [Finset.sum_add_distrib, two_step_telescoping]
    simp
    congr 1
    · omega
  have htail :
      aperiodicCorrelation a n (n - 2) ≡
        (a (n - 2) - a 0 + 1) + (a (n - 1) - a 1 + 1) [ZMOD 4] := by
    have hnsub : n - (n - 2) = 2 := by omega
    have hidx : 1 + (n - 2) = n - 1 := by omega
    rw [aperiodicCorrelation, hnsub]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hidx]
    have h0 := sign_product_mod_four (ha (n - 2) (by omega)) (ha 0 (by omega))
    have h1 := sign_product_mod_four (ha (n - 1) (by omega)) (ha 1 (by omega))
    simpa [mul_comm] using h0.add h1
  rw [hfirstSum] at hfirst
  have h := hfirst.add htail
  convert h using 1
  ring_nf
  omega

/-- Binary signs determine both the parity of every autocorrelation and the special mod-four
boundary sum at shift two. -/
theorem barker_correlation_congruences {a : Nat -> Int} {n : Nat}
    (ha : ∀ i < n, a i = 1 ∨ a i = -1) :
    (∀ k, k <= n ->
      aperiodicCorrelation a n k ≡ (n - k : Nat) [ZMOD 2]) ∧
      (2 <= n ->
        aperiodicCorrelation a n 2 + aperiodicCorrelation a n (n - 2) ≡
          (n : Int) [ZMOD 4]) := by
  exact ⟨fun _k hk => correlation_mod_two ha hk, correlation_two_pair_mod_four ha⟩

private theorem even_shift_correlation_zero {a : Nat -> Int} {n k : Nat}
    (hb : IsBarker a n) (hn : Even n) (hkpos : 0 < k) (hk : k < n)
    (hkeven : Even k) :
    aperiodicCorrelation a n k = 0 := by
  have hmod := correlation_mod_two hb.1 (Nat.le_of_lt hk)
  have hnk : Even (n - k) :=
    (Nat.even_sub (Nat.le_of_lt hk)).2 (by simp [hn, hkeven])
  rcases Int.abs_le_one_iff.mp (hb.2 k hkpos hk) with hzero | hone | hneg
  · exact hzero
  · exfalso
    rw [hone, Int.ModEq] at hmod
    obtain ⟨r, hr⟩ := hnk
    omega
  · exfalso
    rw [hneg, Int.ModEq] at hmod
    obtain ⟨r, hr⟩ := hnk
    omega

private theorem even_barker_length_mod_four_of_isBarker {a : Nat -> Int} {n : Nat}
    (hb : IsBarker a n) (hn : Even n) (hnlarge : 2 < n) :
    n % 4 = 0 := by
  have hc2 : aperiodicCorrelation a n 2 = 0 :=
    even_shift_correlation_zero hb hn (by omega) hnlarge even_two
  have hcn2 : aperiodicCorrelation a n (n - 2) = 0 := by
    apply even_shift_correlation_zero hb hn
    · omega
    · omega
    · exact (Nat.even_sub (by omega)).2 (by simp [hn])
  have hmod := correlation_two_pair_mod_four hb.1 (by omega : 2 <= n)
  rw [hc2, hcn2, zero_add] at hmod
  rw [Int.ModEq] at hmod
  norm_num at hmod
  exact_mod_cast hmod.symm

/-- Every even Barker sequence longer than two has length divisible by four; consequently no
length congruent to two modulo four supports such a sequence. -/
theorem even_barker_length_mod_four {a : Nat -> Int} {n : Nat}
    (hn : Even n) (hnlarge : 2 < n) :
    (IsBarker a n -> n % 4 = 0) ∧
      (n % 4 = 2 -> ¬IsBarker a n) := by
  constructor
  · exact fun hb => even_barker_length_mod_four_of_isBarker hb hn hnlarge
  · intro hnmod hb
    have hzero := even_barker_length_mod_four_of_isBarker hb hn hnlarge
    omega

/-- The classical length-thirteen Barker sequence `+++++--++-+-+`. -/
def barker13 : Nat -> Int
  | 0 | 1 | 2 | 3 | 4 | 7 | 8 | 10 | 12 => 1
  | _ => -1

/-- The classical length-four Barker sequence `+++-`. -/
def barker4 : Nat -> Int
  | 0 | 1 | 2 => 1
  | _ => -1

/-- A length-eight sign sequence with first and third autocorrelations both equal to three. -/
def oddEqualEight : Nat -> Int
  | 6 => -1
  | _ => 1

private theorem barker13_is_barker : IsBarker barker13 13 := by
  constructor
  · intro i hi
    interval_cases i <;> simp [barker13]
  · intro k hkpos hk
    interval_cases k <;>
      norm_num [aperiodicCorrelation, barker13, Finset.sum_range_succ]

private theorem barker4_is_barker : IsBarker barker4 4 := by
  constructor
  · intro i hi
    interval_cases i <;> simp [barker4]
  · intro k hkpos hk
    interval_cases k <;>
      norm_num [aperiodicCorrelation, barker4, Finset.sum_range_succ]

private theorem oddEqualEight_nonbarker :
    aperiodicCorrelation oddEqualEight 8 1 = 3 ∧
      aperiodicCorrelation oddEqualEight 8 3 = 3 ∧
      ¬IsBarker oddEqualEight 8 := by
  refine ⟨by norm_num [aperiodicCorrelation, oddEqualEight, Finset.sum_range_succ],
    by norm_num [aperiodicCorrelation, oddEqualEight, Finset.sum_range_succ], ?_⟩
  intro hb
  have h := hb.2 1 (by norm_num) (by norm_num)
  norm_num [aperiodicCorrelation, oddEqualEight, Finset.sum_range_succ] at h

/-- Explicit witnesses show that the obstruction is nonvacuous and that equal odd correlations
alone do not imply the Barker bound. -/
theorem barker_obstruction_witnesses :
    IsBarker barker13 13 ∧
      IsBarker barker4 4 ∧
      (aperiodicCorrelation oddEqualEight 8 1 = 3 ∧
        aperiodicCorrelation oddEqualEight 8 3 = 3 ∧
        ¬IsBarker oddEqualEight 8) := by
  exact ⟨barker13_is_barker, barker4_is_barker, oddEqualEight_nonbarker⟩

-- Fidelity witnesses: the quantified domains are inhabited and the hypotheses occur.
example : Nat -> Int := barker4

example :
    IsBarker barker4 4 ∧ Even 4 ∧ 2 < 4 := by
  exact ⟨barker4_is_barker, by norm_num, by norm_num⟩

example :
    (∀ i < 4, barker4 i = 1 ∨ barker4 i = -1) ∧
      Even 6 ∧ 2 < 6 ∧ 6 % 4 = 2 := by
  exact ⟨barker4_is_barker.1, by norm_num, by norm_num, by norm_num⟩

#print axioms barker_correlation_congruences
#print axioms even_barker_length_mod_four
#print axioms barker_obstruction_witnesses

end D5.S1.Words.BarkerEvenLengthModFourObstruction
