/- GID: D5/S1/Words/ZeckendorfBeattyBridge
   generality: I
   mirror-B: D5/B/S1/Words/ZeckendorfBeattyBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The least Zeckendorf digit is equivalent to the shifted golden mechanical letter. -/

import D5.S0.Tower.GoldenGapZeckendorf
import D5.S1.Words.GoldenMechanicalWord

namespace D5.S1.Words

open D5.S0.Conventions
open D5.S0.Tower.GoldenGapWord
open D5.S0.Tower.GoldenGapZeckendorf
open D5.S1.Dynamics

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem inv_golden_sq_add_inv_golden :
    Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem pow_add_pow_succ {r : ℝ} (hr : r ^ 2 + r = 1) {a : ℕ} (ha : 1 ≤ a) :
    r ^ a + r ^ (a + 1) = r ^ (a - 1) := by
  conv_lhs =>
    lhs
    rw [show a = a - 1 + 1 by omega, pow_succ]
  conv_lhs =>
    rhs
    rw [show a + 1 = (a - 1) + 2 by omega, pow_add]
  calc
    r ^ (a - 1) * r + r ^ (a - 1) * r ^ 2 =
        r ^ (a - 1) * (r ^ 2 + r) := by ring
    _ = r ^ (a - 1) := by rw [hr, mul_one]

private theorem sum_powers_le_sub_head {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d a : ℕ} {l : List ℕ}
    (hgap : (a :: l).Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ k ∈ a :: l, d + 1 ≤ k) :
    ((a :: l).map fun k => r ^ k).sum ≤ r ^ d - r ^ (a + 1) := by
  induction l generalizing a with
  | nil =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [le_sub_iff_add_le, pow_add_pow_succ hr (by have := hmin a (by simp); omega)]
      rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
      have := hmin a (by simp)
      omega
  | cons b l ih =>
      rw [List.pairwise_cons] at hgap
      have hab : b + 2 ≤ a := hgap.1 b (by simp)
      have htail : (b :: l).Pairwise fun x y => y + 2 ≤ x := hgap.2
      have hmin_tail : ∀ k ∈ b :: l, d + 1 ≤ k := by
        intro k hk
        exact hmin k (by simp [hk])
      have hih := ih htail hmin_tail
      simp only [List.map_cons, List.sum_cons]
      calc
        r ^ a + (r ^ b + (l.map fun k => r ^ k).sum) ≤
            r ^ a + (r ^ d - r ^ (b + 1)) := by
              gcongr
              simpa only [List.map_cons, List.sum_cons] using hih
        _ ≤ r ^ d - r ^ (a + 1) := by
          have hpowers : r ^ a + r ^ (a + 1) ≤ r ^ (b + 1) := by
            rw [pow_add_pow_succ hr (by omega)]
            rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
            omega
          linarith

private theorem sum_powers_lt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d : ℕ} {l : List ℕ}
    (hgap : l.Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ k ∈ l, d + 1 ≤ k) :
    (l.map fun k => r ^ k).sum < r ^ d := by
  cases l with
  | nil => simpa using pow_pos hr0 d
  | cons a l =>
      refine (sum_powers_le_sub_head hr0 hr1 hr hgap hmin).trans_lt ?_
      exact sub_lt_self _ (pow_pos hr0 (a + 1))

private theorem sum_neg_powers_le_sum_powers {r : ℝ} (hr0 : 0 < r) :
    ∀ l : List ℕ,
      (l.map fun k => (-r) ^ k).sum ≤ (l.map fun k => r ^ k).sum := by
  intro l
  induction l with
  | nil => simp
  | cons k l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hkpow : (-r) ^ k ≤ r ^ k := by
        simpa [abs_pow, abs_of_pos hr0] using le_abs_self ((-r) ^ k)
      exact add_le_add hkpow ih

private theorem neg_sum_odd_powers_le_sum_neg_powers {r : ℝ} (hr0 : 0 < r) :
    ∀ l : List ℕ,
      -((l.filter fun k => decide (Odd k)).map fun k => r ^ k).sum ≤
        (l.map fun k => (-r) ^ k).sum := by
  intro l
  induction l with
  | nil => simp
  | cons k l ih =>
      by_cases hk : Odd k
      · rw [List.filter_cons_of_pos (by simp [hk])]
        simp only [List.map_cons, List.sum_cons]
        rw [Odd.neg_pow hk]
        linarith
      · have heven : Even k := Nat.not_odd_iff_even.mp hk
        rw [List.filter_cons_of_neg (by simp [hk])]
        simp only [List.map_cons, List.sum_cons]
        rw [Even.neg_pow heven]
        have hpow : 0 ≤ r ^ k := (pow_pos hr0 k).le
        linarith

private theorem sum_neg_powers_eq_even_sub_odd (r : ℝ) : ∀ l : List ℕ,
    (l.map fun k => (-r) ^ k).sum =
      ((l.filter fun k => decide (Even k)).map fun k => r ^ k).sum -
        ((l.filter fun k => decide (Odd k)).map fun k => r ^ k).sum := by
  intro l
  induction l with
  | nil => simp
  | cons k l ih =>
      by_cases hk : Even k
      · have hnotOdd : ¬Odd k := Nat.not_odd_iff_even.mpr hk
        rw [List.filter_cons_of_pos (by simp [hk]),
          List.filter_cons_of_neg (by simp [hnotOdd])]
        simp only [List.map_cons, List.sum_cons]
        rw [Even.neg_pow hk, ih]
        ring
      · have hodd : Odd k := Nat.not_even_iff_odd.mp hk
        rw [List.filter_cons_of_neg (by simp [hk]),
          List.filter_cons_of_pos (by simp [hodd])]
        simp only [List.map_cons, List.sum_cons]
        rw [Odd.neg_pow hodd, ih]
        ring

private theorem canonical_pairwise {l : List ℕ} (hl : l.IsZeckendorfRep) :
    l.Pairwise fun x y => y + 2 ≤ x := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hl
  exact (List.pairwise_append.mp hl).1

private theorem canonical_two_le {l : List ℕ} (hl : l.IsZeckendorfRep) :
    ∀ k ∈ l, 2 ≤ k := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hl
  intro k hk
  exact (List.pairwise_append.mp hl).2.2 k hk 0 (by simp)

private theorem conjugate_error_bounds {l : List ℕ} (hl : l.IsZeckendorfRep) :
    -(Real.goldenRatio⁻¹ ^ 2) < (l.map fun k => Real.goldenConj ^ k).sum ∧
      (l.map fun k => Real.goldenConj ^ k).sum < Real.goldenRatio⁻¹ := by
  let r : ℝ := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hconj : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have hpair := canonical_pairwise hl
  have hmin := canonical_two_le hl
  have hupperPowers : (l.map fun k => r ^ k).sum < r := by
    simpa using sum_powers_lt hr0 hr1 hr hpair hmin
  have hupper : (l.map fun k => Real.goldenConj ^ k).sum < r := by
    rw [hconj]
    exact (sum_neg_powers_le_sum_powers hr0 l).trans_lt hupperPowers
  have hoddPair : (l.filter fun k => decide (Odd k)).Pairwise fun x y => y + 2 ≤ x :=
    hpair.filter _
  have hoddMin : ∀ k ∈ l.filter (fun k => decide (Odd k)), 3 ≤ k := by
    intro k hk
    have hk' := List.mem_filter.mp hk
    have htwo := hmin k hk'.1
    have hoddK : Odd k := by simpa using hk'.2
    have hne : k ≠ 2 := by
      intro heq
      subst k
      exact (by norm_num : ¬Odd 2) hoddK
    omega
  have hodd : (((l.filter fun k => decide (Odd k)).map fun k => r ^ k).sum) < r ^ 2 :=
    sum_powers_lt hr0 hr1 hr hoddPair hoddMin
  have hlower : -(r ^ 2) < (l.map fun k => Real.goldenConj ^ k).sum := by
    rw [hconj]
    exact lt_of_lt_of_le (neg_lt_neg hodd)
      (neg_sum_odd_powers_le_sum_neg_powers hr0 l)
  exact ⟨hlower, hupper⟩

private theorem conjugate_error_lt_cube_of_two_not_mem {l : List ℕ}
    (hl : l.IsZeckendorfRep) (htwo : 2 ∉ l) :
    (l.map fun k => Real.goldenConj ^ k).sum < Real.goldenRatio⁻¹ ^ 3 := by
  let r : ℝ := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hconj : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have hpair := canonical_pairwise hl
  have hmin := canonical_two_le hl
  let evens := l.filter fun k => decide (Even k)
  have hevenPair : evens.Pairwise fun x y => y + 2 ≤ x := hpair.filter _
  have hevenMin : ∀ k ∈ evens, 4 ≤ k := by
    intro k hk
    have hk' := List.mem_filter.mp hk
    have htwoLe := hmin k hk'.1
    have heven : Even k := by simpa using hk'.2
    have hne : k ≠ 2 := by
      intro heq
      exact htwo (heq ▸ hk'.1)
    rcases heven with ⟨a, ha⟩
    omega
  have hevenUpper : (evens.map fun k => r ^ k).sum < r ^ 3 :=
    sum_powers_lt hr0 hr1 hr hevenPair hevenMin
  have hoddNonneg :
      0 ≤ ((l.filter fun k => decide (Odd k)).map fun k => r ^ k).sum := by
    apply List.sum_nonneg
    intro x hx
    rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
    exact (pow_pos hr0 k).le
  rw [hconj, sum_neg_powers_eq_even_sub_odd]
  exact (sub_le_self _ hoddNonneg).trans_lt hevenUpper

private theorem cube_lt_conjugate_error_of_two_mem {l : List ℕ}
    (hl : l.IsZeckendorfRep) (htwo : 2 ∈ l) :
    Real.goldenRatio⁻¹ ^ 3 < (l.map fun k => Real.goldenConj ^ k).sum := by
  let r : ℝ := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hconj : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have hpair := canonical_pairwise hl
  have hmin := canonical_two_le hl
  letI : Std.Symm (fun x y : ℕ => x + 2 ≤ y ∨ y + 2 ≤ x) :=
    ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  have hseparated : l.Pairwise (fun x y => x + 2 ≤ y ∨ y + 2 ≤ x) :=
    hpair.imp fun h => Or.inr h
  let odds := l.filter fun k => decide (Odd k)
  have hoddPair : odds.Pairwise fun x y => y + 2 ≤ x := hpair.filter _
  have hoddMin : ∀ k ∈ odds, 5 ≤ k := by
    intro k hk
    have hk' := List.mem_filter.mp hk
    have htwoLe := hmin k hk'.1
    have hodd : Odd k := by simpa using hk'.2
    have hneTwo : k ≠ 2 := by
      intro heq
      subst k
      exact (by norm_num : ¬Odd 2) hodd
    have hneThree : k ≠ 3 := by
      intro heq
      subst k
      have hrel := hseparated.forall hk'.1 htwo (by omega)
      omega
    rcases hodd with ⟨a, ha⟩
    omega
  have hoddUpper : (odds.map fun k => r ^ k).sum < r ^ 4 :=
    sum_powers_lt hr0 hr1 hr hoddPair hoddMin
  let evens := l.filter fun k => decide (Even k)
  have htwoEven : 2 ∈ evens := by simp [evens, htwo]
  have hevenLower : r ^ 2 ≤ (evens.map fun k => r ^ k).sum := by
    apply List.single_le_sum
    · intro x hx
      rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
      exact (pow_pos hr0 k).le
    · exact List.mem_map.mpr ⟨2, htwoEven, rfl⟩
  have hpow : r ^ 2 - r ^ 4 = r ^ 3 := by
    calc
      r ^ 2 - r ^ 4 = r ^ 2 * (1 - r ^ 2) := by ring
      _ = r ^ 2 * r := by rw [show 1 - r ^ 2 = r by linarith]
      _ = r ^ 3 := by ring
  rw [hconj, sum_neg_powers_eq_even_sub_odd]
  rw [← hpow]
  linarith

private def shiftedFibValue (n : ℕ) : ℕ :=
  ((wdigits n).map fun k => Nat.fib (k - 1)).sum

private theorem fib_mul_inv_golden {k : ℕ} (hk : 2 ≤ k) :
    (Nat.fib k : ℝ) * Real.goldenRatio⁻¹ =
      (Nat.fib (k - 1) : ℝ) - Real.goldenConj ^ k := by
  have h := Real.goldenConj_mul_fib_succ_add_fib (k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
  rw [Real.inv_goldenRatio]
  linarith

private theorem sum_fib_mul_inv_golden {l : List ℕ} (hmin : ∀ k ∈ l, 2 ≤ k) :
    (l.map fun k => (Nat.fib k : ℝ) * Real.goldenRatio⁻¹).sum =
      (l.map fun k => (Nat.fib (k - 1) : ℝ)).sum -
        (l.map fun k => Real.goldenConj ^ k).sum := by
  induction l with
  | nil => simp
  | cons k l ih =>
      have hk : 2 ≤ k := hmin k (by simp)
      have hmin_tail : ∀ j ∈ l, 2 ≤ j := by
        intro j hj
        exact hmin j (by simp [hj])
      simp only [List.map_cons, List.sum_cons]
      rw [fib_mul_inv_golden hk, ih hmin_tail]
      ring

private theorem mul_inv_golden_eq_shift_sub_error (n : ℕ) :
    (n : ℝ) * Real.goldenRatio⁻¹ =
      (shiftedFibValue n : ℝ) -
        ((wdigits n).map fun k => Real.goldenConj ^ k).sum := by
  let l := wdigits n
  have hmin : ∀ k ∈ l, 2 ≤ k := canonical_two_le (wdigits_isCanonical n)
  have hterms :
      (l.map fun k => (Nat.fib k : ℝ) * Real.goldenRatio⁻¹).sum =
        (l.map fun k => (Nat.fib (k - 1) : ℝ)).sum -
          (l.map fun k => Real.goldenConj ^ k).sum := by
    exact sum_fib_mul_inv_golden hmin
  have hdecode :
      (n : ℝ) = ((wdigits n).map fun k => (Nat.fib k : ℝ)).sum := by
    have hcast :
        (((wdigits n).map Nat.fib).sum : ℝ) =
          ((wdigits n).map fun k => (Nat.fib k : ℝ)).sum := by
      induction wdigits n with
      | nil => simp
      | cons k l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    rw [← hcast]
    exact_mod_cast (decode_wdigits n).symm
  have hmul :
      ((l.map fun k => (Nat.fib k : ℝ)).sum) * Real.goldenRatio⁻¹ =
        (l.map fun k => (Nat.fib k : ℝ) * Real.goldenRatio⁻¹).sum := by
    induction l with
    | nil => simp
    | cons k l ih => simp only [List.map_cons, List.sum_cons, add_mul, ih]
  calc
    (n : ℝ) * Real.goldenRatio⁻¹ =
        ((wdigits n).map fun k => (Nat.fib k : ℝ)).sum * Real.goldenRatio⁻¹ := by
          rw [hdecode]
    _ = ((l.map fun k => (Nat.fib k : ℝ)).sum) * Real.goldenRatio⁻¹ := by
          simp [l]
    _ = (l.map fun k => (Nat.fib k : ℝ) * Real.goldenRatio⁻¹).sum := by
          exact hmul
    _ = (l.map fun k => (Nat.fib (k - 1) : ℝ)).sum -
        (l.map fun k => Real.goldenConj ^ k).sum := hterms
    _ = (shiftedFibValue n : ℝ) -
        ((wdigits n).map fun k => Real.goldenConj ^ k).sum := by
          have hcast :
              (((wdigits n).map fun k => Nat.fib (k - 1)).sum : ℝ) =
                ((wdigits n).map fun k => (Nat.fib (k - 1) : ℝ)).sum := by
            induction wdigits n with
            | nil => simp
            | cons k l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
          rw [show l = wdigits n by rfl]
          rw [show (shiftedFibValue n : ℝ) =
              (((wdigits n).map fun k => Nat.fib (k - 1)).sum : ℝ) by rfl]
          rw [hcast]

private theorem goldenFractionalPart_succ_eq (n : ℕ) :
    goldenFractionalPart (n + 1) = Real.goldenRatio⁻¹ -
      ((wdigits n).map fun k => Real.goldenConj ^ k).sum := by
  let r : ℝ := Real.goldenRatio⁻¹
  let error := ((wdigits n).map fun k => Real.goldenConj ^ k).sum
  have herr := conjugate_error_bounds (wdigits_isCanonical n)
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hslope : r = Real.goldenRatio - 1 := by
    dsimp [r]
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
    ring
  have hfract :
      Int.fract (((n + 1 : ℕ) : ℝ) * r) = goldenFractionalPart (n + 1) := by
    dsimp [goldenFractionalPart]
    rw [hslope, mul_sub, mul_one]
    exact Int.fract_sub_natCast
      (((n + 1 : ℕ) : ℝ) * Real.goldenRatio) (n + 1)
  have hdecomp :
      (((n + 1 : ℕ) : ℝ) * r) = (shiftedFibValue n : ℝ) + (r - error) := by
    dsimp [r]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      mul_inv_golden_eq_shift_sub_error]
    dsimp [error]
    ring
  have hunit : 0 ≤ r - error ∧ r - error < 1 := by
    dsimp [r, error] at herr ⊢
    constructor <;> linarith
  calc
    goldenFractionalPart (n + 1) = Int.fract (((n + 1 : ℕ) : ℝ) * r) := hfract.symm
    _ = Int.fract ((shiftedFibValue n : ℝ) + (r - error)) := by rw [hdecomp]
    _ = Int.fract (r - error) := Int.fract_natCast_add _ _
    _ = r - error := Int.fract_eq_self.mpr hunit
    _ = Real.goldenRatio⁻¹ -
        ((wdigits n).map fun k => Real.goldenConj ^ k).sum := rfl

/-- The least Zeckendorf digit is absent exactly at a shifted large mechanical letter. -/
theorem zeckendorf_beatty_bridge (i : ℕ) :
    2 ∉ wdigits i ↔ goldenMechanicalLetter (i + 1) = 1 := by
  rw [golden_mechanical_letter_eq_one_iff, goldenFractionalPart_succ_eq]
  let r : ℝ := Real.goldenRatio⁻¹
  let error := ((wdigits i).map fun k => Real.goldenConj ^ k).sum
  have hr : r ^ 2 + r = 1 := inv_golden_sq_add_inv_golden
  have hcube : r ^ 3 = 2 * r - 1 := by
    calc
      r ^ 3 = r * r ^ 2 := by ring
      _ = r * (1 - r) := by rw [show r ^ 2 = 1 - r by linarith]
      _ = 2 * r - 1 := by nlinarith [hr]
  change 2 ∉ wdigits i ↔ 1 - r ≤ r - error ∧ r - error < 1
  constructor
  · intro htwo
    have hsmall := conjugate_error_lt_cube_of_two_not_mem (wdigits_isCanonical i) htwo
    have herr := conjugate_error_bounds (wdigits_isCanonical i)
    dsimp [r, error] at hsmall herr hcube ⊢
    constructor <;> linarith
  · rintro ⟨hlower, _⟩
    by_contra htwo
    have hmem : 2 ∈ wdigits i := by simpa using htwo
    have hlarge := cube_lt_conjugate_error_of_two_mem (wdigits_isCanonical i) hmem
    dsimp [r, error] at hlarge hcube hlower
    linarith

/-- Every finite Fibonacci word is given explicitly by shifted golden Beatty floor differences. -/
theorem fibWord_eq_beatty_floor (Q : ℕ) :
    fibWord Q = List.ofFn fun i : Fin (Nat.fib (Q + 2)) =>
      if ⌊(((i.1 + 1 + 1 : ℕ) : ℝ) * Real.goldenRatio⁻¹)⌋ -
          ⌊(((i.1 + 1 : ℕ) : ℝ) * Real.goldenRatio⁻¹)⌋ = 1 then true else false := by
  rw [fibWord_eq_zeckendorf_word, List.ofFn_inj]
  funext i
  have hiff : 2 ∉ wdigits i.1 ↔
      ⌊(((i.1 + 1 + 1 : ℕ) : ℝ) * Real.goldenRatio⁻¹)⌋ -
        ⌊(((i.1 + 1 : ℕ) : ℝ) * Real.goldenRatio⁻¹)⌋ = 1 := by
    simpa [goldenMechanicalLetter, goldenMechanicalSlope] using
      zeckendorf_beatty_bridge i.1
  by_cases htwo : 2 ∈ wdigits i.1
  · have hfloor : ¬(⌊(((i.1 + 1 + 1 : ℕ) : ℝ) * Real.goldenRatio⁻¹)⌋ -
        ⌊(((i.1 + 1 : ℕ) : ℝ) * Real.goldenRatio⁻¹)⌋ = 1) := by
      exact fun h => (hiff.mpr h) htwo
    rw [if_pos htwo, if_neg hfloor]
  · have hfloor := hiff.mp htwo
    rw [if_neg htwo, if_pos hfloor]

end D5.S1.Words
