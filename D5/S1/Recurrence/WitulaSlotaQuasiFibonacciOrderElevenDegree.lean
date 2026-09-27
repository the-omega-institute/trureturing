/- GID: D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree
   generality: G
   mirror-B: D5/B/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Order-eleven quasi-Fibonacci polynomials have degree n from n=5 onward. -/

/- proof_shape: result: content
   escape_witness: (W) leading-coefficient positivity invariant (have-chain inside result)
   admission_basis: open-problem-resolution (issue #9270)
   Direct frozen dependencies: none (pinned Mathlib only) -/

import Mathlib.Tactic.ComputeDegree

set_option autoImplicit false

namespace D5.S1.Recurrence.WitulaSlotaQuasiFibonacciOrderElevenDegree

/-- The quasi-Fibonacci polynomials of order `(11, δ)` (page 5, system (3.12) with its
initial values): the tuple `(A_n, B_n, C_n, D_n, E_n)` over `ℤ[X]`, `X` standing for `δ`. -/
noncomputable def quasi :
    ℕ → Polynomial ℤ × Polynomial ℤ × Polynomial ℤ × Polynomial ℤ × Polynomial ℤ
  | 0 => (1, 0, 0, 0, 0)
  | n + 1 =>
    let q := quasi n
    let A := q.1; let B := q.2.1; let C := q.2.2.1
    let D := q.2.2.2.1; let E := q.2.2.2.2
    (A + 2 * Polynomial.X * B - Polynomial.X * E,
      Polynomial.X * A + B + Polynomial.X * C - Polynomial.X * E,
      Polynomial.X * B + C + Polynomial.X * D - Polynomial.X * E,
      Polynomial.X * C + D,
      Polynomial.X * D + (1 - Polynomial.X) * E)

/-- `A_n(δ)`. -/
noncomputable def A (n : ℕ) : Polynomial ℤ := (quasi n).1

/-- `B_n(δ)`. -/
noncomputable def B (n : ℕ) : Polynomial ℤ := (quasi n).2.1

/-- `C_n(δ)`. -/
noncomputable def C (n : ℕ) : Polynomial ℤ := (quasi n).2.2.1

/-- `D_n(δ)`. -/
noncomputable def D (n : ℕ) : Polynomial ℤ := (quasi n).2.2.2.1

/-- `E_n(δ)`. -/
noncomputable def E (n : ℕ) : Polynomial ℤ := (quasi n).2.2.2.2

/-- The page-19 Problem as printed: all five degrees equal `n` for every `n ≥ 5`. -/
def claim : Prop := ∀ n : ℕ, 5 ≤ n →
  (A n).degree = n ∧ (B n).degree = n ∧ (C n).degree = n ∧
    (D n).degree = n ∧ (E n).degree = n

example : (A 4).degree = 4 ∧ (B 4).degree = 3 := by
  norm_num [A, B, quasi]
  ring_nf
  constructor <;> (compute_degree <;> norm_num)

example : (E 3).degree = ⊥ := by
  norm_num [E, quasi]

example : (A 5).coeff 5 = -1 ∧ (B 5).coeff 5 = 9 ∧ (C 5).coeff 5 = -1 ∧
    (D 5).coeff 5 = 4 ∧ (E 5).coeff 5 = -1 := by
  norm_num [A, B, C, D, E, quasi]
  ring_nf
  simp [Polynomial.coeff_X, Polynomial.coeff_one]

/-- The Problem's answer is yes. -/
theorem result : claim := by
  have hA (n : ℕ) :
      A (n + 1) = A n + 2 * Polynomial.X * B n - Polynomial.X * E n := by
    simp [A, B, E, quasi]
  have hB (n : ℕ) :
      B (n + 1) = Polynomial.X * A n + B n + Polynomial.X * C n - Polynomial.X * E n := by
    simp [A, B, C, E, quasi]
  have hC (n : ℕ) :
      C (n + 1) = Polynomial.X * B n + C n + Polynomial.X * D n - Polynomial.X * E n := by
    simp [B, C, D, E, quasi]
  have hD (n : ℕ) : D (n + 1) = Polynomial.X * C n + D n := by
    simp [C, D, quasi]
  have hE (n : ℕ) :
      E (n + 1) = Polynomial.X * D n + (1 - Polynomial.X) * E n := by
    simp [D, E, quasi]
  have hdeg : ∀ n : ℕ,
      (A n).natDegree ≤ n ∧ (B n).natDegree ≤ n ∧ (C n).natDegree ≤ n ∧
        (D n).natDegree ≤ n ∧ (E n).natDegree ≤ n := by
    intro n
    induction n with
    | zero => norm_num [A, B, C, D, E, quasi]
    | succ n ih =>
      rcases ih with ⟨ha, hb, hc, hd, he⟩
      rw [hA, hB, hC, hD, hE]
      constructor
      · calc
          (A n + 2 * Polynomial.X * B n - Polynomial.X * E n).natDegree
              ≤ max (A n + 2 * Polynomial.X * B n).natDegree
                (Polynomial.X * E n).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ n + 1 := by
            apply max_le
            · calc
                (A n + 2 * Polynomial.X * B n).natDegree
                    ≤ max (A n).natDegree
                      (2 * Polynomial.X * B n).natDegree := Polynomial.natDegree_add_le _ _
                _ ≤ n + 1 := by
                  apply max_le
                  · omega
                  · calc
                      (2 * Polynomial.X * B n).natDegree
                          ≤ (2 * Polynomial.X : Polynomial ℤ).natDegree +
                            (B n).natDegree := Polynomial.natDegree_mul_le
                      _ ≤ n + 1 := by norm_num; omega
            · calc
                (Polynomial.X * E n).natDegree
                    ≤ (Polynomial.X : Polynomial ℤ).natDegree +
                      (E n).natDegree := Polynomial.natDegree_mul_le
                _ ≤ n + 1 := by norm_num; omega
      · constructor
        · calc
            (Polynomial.X * A n + B n + Polynomial.X * C n - Polynomial.X * E n).natDegree
                ≤ max (Polynomial.X * A n + B n + Polynomial.X * C n).natDegree
                  (Polynomial.X * E n).natDegree := Polynomial.natDegree_sub_le _ _
            _ ≤ n + 1 := by
              apply max_le
              · refine (Polynomial.natDegree_add_le _ _).trans ?_
                apply max_le
                · refine (Polynomial.natDegree_add_le _ _).trans ?_
                  apply max_le
                  · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
                  · omega
                · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
              · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
        · constructor
          · calc
              (Polynomial.X * B n + C n + Polynomial.X * D n - Polynomial.X * E n).natDegree
                  ≤ max (Polynomial.X * B n + C n + Polynomial.X * D n).natDegree
                    (Polynomial.X * E n).natDegree := Polynomial.natDegree_sub_le _ _
              _ ≤ n + 1 := by
                apply max_le
                · refine (Polynomial.natDegree_add_le _ _).trans ?_
                  apply max_le
                  · refine (Polynomial.natDegree_add_le _ _).trans ?_
                    apply max_le
                    · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
                    · omega
                  · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
                · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
          · constructor
            · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
              · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
              · omega
            · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
              · exact Polynomial.natDegree_mul_le.trans (by norm_num; omega)
              · refine Polynomial.natDegree_mul_le.trans ?_
                have hsub : (1 - Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := by
                  compute_degree
                omega
  have hcoeff : ∀ n : ℕ,
      (A (n + 1)).coeff (n + 1) = 2 * (B n).coeff n - (E n).coeff n ∧
      (B (n + 1)).coeff (n + 1) = (A n).coeff n + (C n).coeff n - (E n).coeff n ∧
      (C (n + 1)).coeff (n + 1) = (B n).coeff n + (D n).coeff n - (E n).coeff n ∧
      (D (n + 1)).coeff (n + 1) = (C n).coeff n ∧
      (E (n + 1)).coeff (n + 1) = (D n).coeff n - (E n).coeff n := by
    intro n
    rcases hdeg n with ⟨ha, hb, hc, hd, he⟩
    have za : (A n).coeff (n + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (ha.trans_lt (Nat.lt_succ_self n))
    have zb : (B n).coeff (n + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hb.trans_lt (Nat.lt_succ_self n))
    have zc : (C n).coeff (n + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hc.trans_lt (Nat.lt_succ_self n))
    have zd : (D n).coeff (n + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (Nat.lt_succ_self n))
    have ze : (E n).coeff (n + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (he.trans_lt (Nat.lt_succ_self n))
    rw [hA, hB, hC, hD, hE]
    rw [show (1 - Polynomial.X) * E n = E n - Polynomial.X * E n by ring]
    simp [za, zb, zc, zd, ze, Polynomial.coeff_X_mul, mul_assoc, sub_eq_add_neg]
  let wa : ℕ → ℤ := fun n => (-1 : ℤ) ^ n * (A n).coeff n
  let wb : ℕ → ℤ := fun n => (-1 : ℤ) ^ (n + 1) * (B n).coeff n
  let wc : ℕ → ℤ := fun n => (-1 : ℤ) ^ (n + 2) * (C n).coeff n
  let wd : ℕ → ℤ := fun n => (-1 : ℤ) ^ (n + 3) * (D n).coeff n
  let we : ℕ → ℤ := fun n => (-1 : ℤ) ^ (n + 4) * (E n).coeff n
  have hwstep : ∀ n : ℕ,
      wa (n + 1) = 2 * wb n + we n ∧
      wb (n + 1) = wa n + wc n - we n ∧
      wc (n + 1) = wb n + wd n + we n ∧
      wd (n + 1) = wc n ∧
      we (n + 1) = wd n + we n := by
    intro n
    rcases hcoeff n with ⟨ha, hb, hc, hd, he⟩
    dsimp [wa, wb, wc, wd, we]
    rw [ha, hb, hc, hd, he]
    simp only [pow_succ]
    constructor
    · ring
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring
  let P : ℕ → Prop := fun n =>
    0 < wa n ∧ 0 < wb n ∧ 0 < wc n ∧ 0 < wd n ∧ 0 < we n ∧ we n < wa n + wc n
  have hbase : wa 5 = 1 ∧ wb 5 = 9 ∧ wc 5 = 1 ∧ wd 5 = 4 ∧ we 5 = 1 := by
    dsimp [wa, wb, wc, wd, we]
    norm_num [A, B, C, D, E, quasi]
    ring_nf
    simp [Polynomial.coeff_X, Polynomial.coeff_one]
  have hinv : ∀ k : ℕ, P (5 + k) := by
    intro k
    induction k with
    | zero =>
      dsimp [P]
      rcases hbase with ⟨ha, hb, hc, hd, he⟩
      simp [ha, hb, hc, hd, he]
    | succ k ih =>
      rcases hwstep (5 + k) with ⟨ha, hb, hc, hd, he⟩
      rw [Nat.add_succ]
      dsimp [P] at ih ⊢
      rw [ha, hb, hc, hd, he]
      omega
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases hdeg (5 + k) with ⟨ha, hb, hc, hd, he⟩
  have hp := hinv k
  dsimp [P] at hp
  rcases hp with ⟨pa, pb, pc, pd, pe, _⟩
  have hca : (A (5 + k)).coeff (5 + k) ≠ 0 := by
    intro h
    dsimp [wa] at pa
    rw [h, mul_zero] at pa
    omega
  have hcb : (B (5 + k)).coeff (5 + k) ≠ 0 := by
    intro h
    dsimp [wb] at pb
    rw [h, mul_zero] at pb
    omega
  have hcc : (C (5 + k)).coeff (5 + k) ≠ 0 := by
    intro h
    dsimp [wc] at pc
    rw [h, mul_zero] at pc
    omega
  have hcd : (D (5 + k)).coeff (5 + k) ≠ 0 := by
    intro h
    dsimp [wd] at pd
    rw [h, mul_zero] at pd
    omega
  have hce : (E (5 + k)).coeff (5 + k) ≠ 0 := by
    intro h
    dsimp [we] at pe
    rw [h, mul_zero] at pe
    omega
  exact ⟨Polynomial.degree_eq_of_le_of_coeff_ne_zero
      (Polynomial.degree_le_of_natDegree_le ha) hca,
    Polynomial.degree_eq_of_le_of_coeff_ne_zero
      (Polynomial.degree_le_of_natDegree_le hb) hcb,
    Polynomial.degree_eq_of_le_of_coeff_ne_zero
      (Polynomial.degree_le_of_natDegree_le hc) hcc,
    Polynomial.degree_eq_of_le_of_coeff_ne_zero
      (Polynomial.degree_le_of_natDegree_le hd) hcd,
    Polynomial.degree_eq_of_le_of_coeff_ne_zero
      (Polynomial.degree_le_of_natDegree_le he) hce⟩

end D5.S1.Recurrence.WitulaSlotaQuasiFibonacciOrderElevenDegree
