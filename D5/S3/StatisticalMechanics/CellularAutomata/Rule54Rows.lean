/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Rule54Rows
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Colin Barker's recurrence and generating-function conjectures for OEIS A259661, A118109 and A265225, Karl V. Keller's floor formula for A118109 and Barker's and Wesley Ivan Hurt's closed forms for A265225: the centre column, the rows and the running total of ON cells of the Rule 54 elementary cellular automaton started from a single ON cell. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the row
  invariant `row` (the cell at x of row n is ON exactly when |x| <= n and x = n mod 4 for even n,
  x /= n + 1 mod 4 for odd n, by induction through the rule table) and the row shift `shift`
  (digit j + 4 of row n + 2 is digit j of row n, and the first four digits of row n + 2 are
  1, 0, 0, 0 or 1, 1, 1, 0); the centre column, the Keller and Hurt closed forms, the recurrences
  and the coefficient comparisons for the generating functions are derived from these two new
  propositions
admission_basis: open-problem-resolution (issue #11145)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Set.Card
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.Rule54Rows

open Finset PowerSeries

/-!
OEIS A259661, A118109 and A265225 (2015): the centre column, the rows and the running total of
ON cells of the "Rule 54" elementary cellular automaton started from a single ON (black) cell. The
centre cells and the cells `-n, ..., n` of row `n` are read as strings of decimal digits (A259661,
A118109). Colin Barker conjectured the recurrences and generating functions (2015, 2019), Karl V.
Keller, Jr. the floor formula of A118109 (2021) and Wesley Ivan Hurt the closed form of A265225
(2016). Rule 54 is the elementary rule behind the interacting integrable reversible cellular
automaton of Bobenko, Bordemann, Gunn and Pinkall; here it is applied synchronously to every cell.
-/

/-- Wolfram rule 54: the new state of a cell with neighbourhood `(l, c, r)` is bit `4l + 2c + r`
of 54. -/
def rule54 (l c r : Bool) : Bool :=
  Nat.testBit 54 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of the automaton started from a single ON cell at the origin; every cell of `ℤ` is
updated at every step. -/
def cell : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | n + 1, x => rule54 (cell n (x - 1)) (cell n x) (cell n (x + 1))

/-- OEIS A259661: the centre cells of rows `0, ..., n` as decimal digits, row 0 first. -/
def centreColumn (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (cell k 0).toNat * 10 ^ (n - k)

/-- OEIS A118109: the cells `-n, ..., n` of row `n` as decimal digits, the cell at `-n` first. -/
def binaryRow (n : ℕ) : ℕ := ∑ j ∈ range (2 * n + 1), (cell n ((n : ℤ) - j)).toNat * 10 ^ j

/-- OEIS A265225: the number of ON cells of rows `0, ..., n` together. -/
noncomputable def totalOn (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), Set.ncard {x : ℤ | cell k x = true}

/-- Barker's recurrences and generating functions for the three sequences, Keller's floor formula
for A118109, and Barker's and Hurt's closed forms for A265225. Each denominator has constant term
1, so each generating function is stated as the product of the series with its denominator. -/
def claim : Prop :=
  (∀ n : ℕ, 3 < n → (centreColumn n : ℤ) = 11 * centreColumn (n - 1) - 11 * centreColumn (n - 2)
      + 11 * centreColumn (n - 3) - 10 * centreColumn (n - 4)) ∧
  (PowerSeries.mk (fun n => (centreColumn n : ℤ)) * ((1 - X) * (1 - 10 * X) * (1 + X ^ 2)) = 1) ∧
  (∀ n : ℕ, 3 < n → (binaryRow n : ℤ) = 10001 * binaryRow (n - 2) - 10000 * binaryRow (n - 4)) ∧
  (PowerSeries.mk (fun n => (binaryRow n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 111 * X) ∧
  (∀ n : ℕ, binaryRow n = (10000 + 1100 * (n % 2)) * 100 ^ n / 9999) ∧
  (∀ n : ℕ, (totalOn n : ℚ) = (n + 1) * (2 * n - (-1) ^ n + 5) / 4) ∧
  (∀ n : ℕ, 4 < n → (totalOn n : ℤ) = totalOn (n - 1) + 2 * totalOn (n - 2)
      - 2 * totalOn (n - 3) - totalOn (n - 4) + totalOn (n - 5)) ∧
  (PowerSeries.mk (fun n => (totalOn n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) = 1 + 3 * X) ∧
  (∀ n : ℕ, totalOn n = n + 1 + (n + 1) * ((n + 1) / 2))

theorem result : claim := by
  have table : ∀ a b c : Bool, rule54 a b c = true ↔ (a = true ∧ ¬ b = true) ∨
      (¬ a = true ∧ b = true ∧ ¬ c = true) ∨ (¬ a = true ∧ ¬ b = true ∧ c = true) := by decide
  have row : ∀ n : ℕ, ∀ x : ℤ, cell n x = true ↔ (-(n : ℤ) ≤ x ∧ x ≤ n ∧
      ((n % 2 = 0 ∧ x % 4 = (n : ℤ) % 4) ∨ (n % 2 = 1 ∧ x % 4 ≠ ((n : ℤ) + 1) % 4))) := by
    intro n
    induction n with
    | zero => intro x; simp [cell]; omega
    | succ n ih =>
      intro x
      rw [cell, table]
      simp only [ih]
      push_cast
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have hn' : (n + 1) % 2 = 1 := by omega
        simp only [hn, hn', true_and, false_and, false_or, or_false, Nat.zero_ne_one,
          Nat.one_ne_zero]
        constructor
        · intro h; omega
        · intro h; omega
      · have hn' : (n + 1) % 2 = 0 := by omega
        simp only [hn, hn', true_and, false_and, false_or, or_false, Nat.zero_ne_one,
          Nat.one_ne_zero]
        constructor
        · intro h; omega
        · intro h; omega
  -- centre column
  have centre : ∀ k : ℕ, ((cell k 0).toNat : ℤ) = if k % 4 = 0 ∨ k % 4 = 1 then 1 else 0 := by
    intro k
    cases hc : cell k 0
    · have h : ¬ (k % 4 = 0 ∨ k % 4 = 1) := by
        intro h
        have := (row k 0).mpr (by omega)
        simp [hc] at this
      simp [h]
    · have := (row k 0).mp hc
      have h : k % 4 = 0 ∨ k % 4 = 1 := by omega
      simp [h]
  have cstep : ∀ n : ℕ, centreColumn (n + 1) = 10 * centreColumn n + (cell (n + 1) 0).toNat := by
    intro n
    simp only [centreColumn]
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  -- row shift
  have shift : ∀ b n : ℕ,
      ∑ j ∈ range (2 * (n + 2) + 1), (cell (n + 2) (((n + 2 : ℕ) : ℤ) - j)).toNat * b ^ j =
        (if n % 2 = 0 then 1 else 1 + b + b ^ 2) +
          b ^ 4 * ∑ j ∈ range (2 * n + 1), (cell n ((n : ℤ) - j)).toNat * b ^ j := by
    intro b n
    rw [show 2 * (n + 2) + 1 = 4 + (2 * n + 1) by ring, Finset.sum_range_add, Finset.mul_sum]
    congr 1
    · have d : ∀ j : ℕ, j < 4 → (cell (n + 2) (((n + 2 : ℕ) : ℤ) - j)).toNat =
          if j = 0 ∨ (n % 2 = 1 ∧ j < 3) then 1 else 0 := by
        intro j hj
        cases hc : cell (n + 2) (((n + 2 : ℕ) : ℤ) - j)
        · have h : ¬ (j = 0 ∨ (n % 2 = 1 ∧ j < 3)) := by
            intro h
            have := (row (n + 2) (((n + 2 : ℕ) : ℤ) - j)).mpr (by push_cast; omega)
            rw [hc] at this; exact Bool.false_ne_true this
          simp [h]
        · have := (row (n + 2) (((n + 2 : ℕ) : ℤ) - j)).mp hc
          push_cast at this
          have h : j = 0 ∨ (n % 2 = 1 ∧ j < 3) := by omega
          simp [h]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, d 0 (by norm_num), d 1 (by norm_num),
        d 2 (by norm_num), d 3 (by norm_num)]
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have e : cell (n + 2) (((n + 2 : ℕ) : ℤ) - ((4 + j : ℕ) : ℤ)) = cell n ((n : ℤ) - j) := by
        rw [Bool.eq_iff_iff, row, row]
        push_cast
        constructor <;> intro h <;> omega
      rw [e, pow_add]
      ring
  -- A118109
  have bstep : ∀ n : ℕ,
      binaryRow (n + 2) = (if n % 2 = 0 then 1 else 111) + 10000 * binaryRow n := by
    intro n
    have h := shift 10 n
    simp only [binaryRow] at h ⊢
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn]
  have b0 : binaryRow 0 = 1 := by simp [binaryRow, cell]
  have b1 : binaryRow 1 = 111 := by decide
  have brec : ∀ k : ℕ,
      (binaryRow (k + 4) : ℤ) = 10001 * binaryRow (k + 2) - 10000 * binaryRow k := by
    intro k
    have h2 := bstep (k + 2)
    have h0 := bstep k
    rw [show (k + 2) % 2 = k % 2 by omega] at h2
    push_cast [h2, h0]
    split_ifs <;> ring
  have keller : ∀ n : ℕ, (9999 : ℤ) * binaryRow n + (if n % 2 = 0 then 1 else 111) =
      (10000 + 1100 * (n % 2 : ℕ)) * 100 ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | n
      · simp [b0]
      · simp [b1]
      · have h := ih n (by omega)
        rw [bstep n, show (n + 2) % 2 = n % 2 by omega]
        rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp only [hn] at h ⊢ <;>
          push_cast at h ⊢ <;> linear_combination 10000 * h
  -- centre-column values and recurrence
  have c0 : centreColumn 0 = 1 := by simp [centreColumn, cell]
  have cnat : ∀ k : ℕ, ((cell k 0).toNat : ℤ) = if k % 4 = 0 ∨ k % 4 = 1 then 1 else 0 := centre
  have crec : ∀ k : ℕ,
      (centreColumn (k + 4) : ℤ) = 11 * centreColumn (k + 3) - 11 * centreColumn (k + 2)
      + 11 * centreColumn (k + 1) - 10 * centreColumn k := by
    intro k
    have s4 := cstep (k + 3)
    have s3 := cstep (k + 2)
    have s2 := cstep (k + 1)
    have s1 := cstep k
    have per : ((cell (k + 4) 0).toNat : ℤ) - (cell (k + 3) 0).toNat + (cell (k + 2) 0).toNat
        - (cell (k + 1) 0).toNat = 0 := by
      rw [cnat, cnat, cnat, cnat]
      split_ifs <;> omega
    have s4' : (centreColumn (k + 4) : ℤ) = 10 * centreColumn (k + 3) + (cell (k + 4) 0).toNat := by
      exact_mod_cast s4
    have s3' : (centreColumn (k + 3) : ℤ) = 10 * centreColumn (k + 2) + (cell (k + 3) 0).toNat := by
      exact_mod_cast s3
    have s2' : (centreColumn (k + 2) : ℤ) = 10 * centreColumn (k + 1) + (cell (k + 2) 0).toNat := by
      exact_mod_cast s2
    have s1' : (centreColumn (k + 1) : ℤ) = 10 * centreColumn k + (cell (k + 1) 0).toNat := by
      exact_mod_cast s1
    linear_combination s4' - s3' + s2' - s1' + per
  -- row counts
  have ncardRow : ∀ k : ℕ, Set.ncard {x : ℤ | cell k x = true} =
      ∑ j ∈ range (2 * k + 1), (cell k ((k : ℤ) - j)).toNat * 1 ^ j := by
    intro k
    have hset : {x : ℤ | cell k x = true} =
        ↑(((range (2 * k + 1)).filter (fun j : ℕ => cell k ((k : ℤ) - j) = true)).image
          (fun j : ℕ => (k : ℤ) - j)) := by
      ext x
      simp only [Set.mem_ofPred_eq, coe_image, coe_filter, mem_range, Set.mem_image]
      constructor
      · intro hx
        have hb := (row k x).mp hx
        refine ⟨(k - x).toNat, ⟨by omega, ?_⟩, by omega⟩
        rwa [show (k : ℤ) - ((k - x).toNat : ℕ) = x by omega]
      · rintro ⟨j, ⟨_, hj⟩, rfl⟩
        exact hj
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun a b h => by
      simpa using h), Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases cell k ((k : ℤ) - j) <;> simp
  have rc0 : Set.ncard {x : ℤ | cell 0 x = true} = 1 := by
    rw [ncardRow]; simp [cell]
  have rc1 : Set.ncard {x : ℤ | cell 1 x = true} = 3 := by
    rw [ncardRow]; simp +decide
  have rcstep : ∀ k : ℕ, Set.ncard {x : ℤ | cell (k + 2) x = true} =
      (if k % 2 = 0 then 1 else 3) + Set.ncard {x : ℤ | cell k x = true} := by
    intro k
    rw [ncardRow, ncardRow, show ((k + 2 : ℕ) : ℤ) = ((k + 2 : ℕ) : ℤ) from rfl, shift 1 k]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk]
  have rcform : ∀ m : ℕ, Set.ncard {x : ℤ | cell (2 * m) x = true} = m + 1 ∧
      Set.ncard {x : ℤ | cell (2 * m + 1) x = true} = 3 * m + 3 := by
    intro m
    induction m with
    | zero => exact ⟨rc0, rc1⟩
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [show 2 * (m + 1) = 2 * m + 2 by ring, rcstep, ih.1]
        simp [show (2 * m) % 2 = 0 by omega]; ring
      · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, rcstep, ih.2]
        simp [show (2 * m + 1) % 2 = 1 by omega]; ring
  have tstep : ∀ n : ℕ,
      totalOn (n + 1) = totalOn n + Set.ncard {x : ℤ | cell (n + 1) x = true} := by
    intro n; simp only [totalOn]; rw [Finset.sum_range_succ]
  have hurtPair : ∀ m : ℕ, totalOn (2 * m) = 2 * m + 1 + (2 * m + 1) * m ∧
      totalOn (2 * m + 1) = 2 * m + 2 + (2 * m + 2) * (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [totalOn, rc0]
      · rw [tstep, show (0 + 1 : ℕ) = 2 * 0 + 1 from rfl, (rcform 0).2]; simp [totalOn, rc0]
    | succ m ih =>
      have e1 : totalOn (2 * (m + 1)) = 2 * (m + 1) + 1 + (2 * (m + 1) + 1) * (m + 1) := by
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, tstep, ih.2,
          show 2 * m + 1 + 1 = 2 * (m + 1) by ring, (rcform (m + 1)).1]
        ring
      refine ⟨e1, ?_⟩
      rw [tstep, e1, (rcform (m + 1)).2]
      ring
  have hurt : ∀ n : ℕ, totalOn n = n + 1 + (n + 1) * ((n + 1) / 2) := by
    intro n
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [(hurtPair m).1, show (2 * m + 1) / 2 = m by omega]
    · rw [(hurtPair m).2, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
  have barkerZ : ∀ n : ℕ, 4 * (totalOn n : ℤ) = (n + 1) * (2 * n - (-1) ^ n + 5) := by
    intro n
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [(hurtPair m).1, pow_mul]; push_cast; ring
    · rw [(hurtPair m).2, pow_succ, pow_mul]; push_cast; ring
  -- coefficient comparison
  have gf : ∀ (f : ℕ → ℤ) (d1 d2 d3 d4 d5 : ℤ),
      (∀ k, f (k + 5) + d1 * f (k + 4) + d2 * f (k + 3) + d3 * f (k + 2) + d4 * f (k + 1)
        + d5 * f k = 0) →
      mk f * (1 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5) =
        C (f 0) + C (f 1 + d1 * f 0) * X + C (f 2 + d1 * f 1 + d2 * f 0) * X ^ 2
          + C (f 3 + d1 * f 2 + d2 * f 1 + d3 * f 0) * X ^ 3
          + C (f 4 + d1 * f 3 + d2 * f 2 + d3 * f 1 + d4 * f 0) * X ^ 4 := by
    intro f d1 d2 d3 d4 d5 hr
    have e : mk f * (1 + C d1 * X + C d2 * X ^ 2 + C d3 * X ^ 3 + C d4 * X ^ 4 + C d5 * X ^ 5) =
        mk f + C d1 * (mk f * X ^ 1) + C d2 * (mk f * X ^ 2) + C d3 * (mk f * X ^ 3)
          + C d4 * (mk f * X ^ 4) + C d5 * (mk f * X ^ 5) := by ring
    rw [e]
    ext k
    simp only [LinearMap.map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X, coeff_C]
    rcases k with _ | _ | _ | _ | _ | k
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right,
        Nat.reduceSubDiff, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, Nat.add_eq_right,
        mul_zero, add_zero, OfNat.ofNat_ne_zero]
      linear_combination hr k
  -- values
  have tnat : ∀ k : ℕ, (cell k 0).toNat = if k % 4 = 0 ∨ k % 4 = 1 then 1 else 0 := by
    intro k
    have := centre k
    split_ifs at this ⊢ <;> exact_mod_cast this
  have c1 : centreColumn 1 = 11 := by rw [cstep, c0, tnat]; norm_num
  have c2 : centreColumn 2 = 110 := by rw [cstep, c1, tnat]; norm_num
  have c3 : centreColumn 3 = 1100 := by rw [cstep, c2, tnat]; norm_num
  have c4 : centreColumn 4 = 11001 := by rw [cstep, c3, tnat]; norm_num
  have b2 : binaryRow 2 = 10001 := by rw [bstep, b0]; norm_num
  have b3 : binaryRow 3 = 1110111 := by rw [bstep, b1]; norm_num
  have b4 : binaryRow 4 = 100010001 := by rw [bstep, b2]; norm_num
  have tv : ∀ n : ℕ, n < 5 → totalOn n = n + 1 + (n + 1) * ((n + 1) / 2) := fun n _ => hurt n
  have trec : ∀ k : ℕ, (totalOn (k + 5) : ℤ) = totalOn (k + 4) + 2 * totalOn (k + 3)
      - 2 * totalOn (k + 2) - totalOn (k + 1) + totalOn k := by
    intro k
    have e5 := barkerZ (k + 5)
    have e4 := barkerZ (k + 4)
    have e3 := barkerZ (k + 3)
    have e2 := barkerZ (k + 2)
    have e1 := barkerZ (k + 1)
    have e0 := barkerZ k
    push_cast at e5 e4 e3 e2 e1 e0
    have h : 4 * (totalOn (k + 5) : ℤ) = 4 * (totalOn (k + 4) + 2 * totalOn (k + 3)
        - 2 * totalOn (k + 2) - totalOn (k + 1) + totalOn k) := by
      linear_combination e5 - e4 - 2 * e3 + 2 * e2 + e1 - e0
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hurt⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simpa using crec k
  · rw [show ((1 - X) * (1 - 10 * X) * (1 + X ^ 2) : ℤ⟦X⟧) = 1 + C (-11) * X + C 11 * X ^ 2
        + C (-11) * X ^ 3 + C 10 * X ^ 4 + C 0 * X ^ 5 by
          simp only [map_neg, map_ofNat, map_zero]; ring]
    rw [gf _ (-11) 11 (-11) 10 0 (fun k => by
      have h := crec (k + 1)
      ring_nf at h ⊢
      linarith)]
    simp only [c0, c1, c2, c3, c4]
    norm_num
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simpa using brec k
  · rw [show ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) : ℤ⟦X⟧) = 1 + C 0 * X
        + C (-10001) * X ^ 2 + C 0 * X ^ 3 + C 10000 * X ^ 4 + C 0 * X ^ 5 by
          simp only [map_neg, map_ofNat, map_zero]; ring]
    rw [gf _ 0 (-10001) 0 10000 0 (fun k => by
      have h := brec (k + 1)
      ring_nf at h ⊢
      linarith)]
    simp only [b0, b1, b2, b3, b4]
    norm_num
  · intro n
    have h : 9999 * binaryRow n + (if n % 2 = 0 then 1 else 111) =
        (10000 + 1100 * (n % 2)) * 100 ^ n := by
      have := keller n
      split_ifs at this ⊢ <;> exact_mod_cast this
    rw [← h]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn] <;> omega
  · intro n
    have h := barkerZ n
    have hq : (4 : ℚ) * totalOn n = (n + 1) * (2 * n - (-1) ^ n + 5) := by exact_mod_cast h
    rw [eq_div_iff (by norm_num)]
    linarith
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    simpa using trec k
  · rw [show ((1 - X) ^ 3 * (1 + X) ^ 2 : ℤ⟦X⟧) = 1 + C (-1) * X + C (-2) * X ^ 2
        + C 2 * X ^ 3 + C 1 * X ^ 4 + C (-1) * X ^ 5 by
          simp only [map_neg, map_ofNat, map_one]; ring]
    rw [gf _ (-1) (-2) 2 1 (-1) (fun k => by
      have h := trec k
      ring_nf at h ⊢
      linarith)]
    simp only [tv 0 (by norm_num), tv 1 (by norm_num), tv 2 (by norm_num), tv 3 (by norm_num),
      tv 4 (by norm_num)]
    norm_num

end D5.S3.StatisticalMechanics.CellularAutomata.Rule54Rows
