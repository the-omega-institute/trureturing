/- GID: D5/S3/Combinatorics/Zigzag/LaurentCoefficients
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/LaurentCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.NatAntidiagonal]
   utility: none
   digest: Finite Laurent formula and the two balanced coefficients. -/

import D5.S3.Combinatorics.Zigzag.WeightedPaths
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

open scoped BigOperators LaurentPolynomial

/-- One summand in the finite solution of the scalar recurrence.  The first
coordinate counts available slots and the second counts two-step moves. -/
noncomputable def closedTerm (p : Nat × Nat) : Laurent :=
  LaurentPolynomial.C
      (2 * Nat.choose p.1 p.2 * 2 ^ (p.1 - p.2) * 3 ^ p.2) *
    z ((p.1 : Int) - 2 * (p.2 : Int))

/-- The finite antidiagonal Laurent formula. -/
noncomputable def closedPolynomial (m : Nat) : Laurent :=
  ∑ p ∈ Finset.antidiagonal m, closedTerm p

private theorem closedTerm_step (a b : Nat) :
    closedTerm (a + 1, b + 1) =
      2 * z 1 * closedTerm (a, b + 1) + 3 * z (-1) * closedTerm (a, b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have h₁ : a + 1 < b + 1 := by omega
    have h₂ : a < b + 1 := by omega
    simp [closedTerm, Nat.choose_eq_zero_of_lt hab,
      Nat.choose_eq_zero_of_lt h₁, Nat.choose_eq_zero_of_lt h₂]
  · subst b
    simp [closedTerm, pow_succ, z]
    have ht : (LaurentPolynomial.T
        ((a : Int) + 1 - 2 * ((a : Int) + 1)) : Laurent) =
        LaurentPolynomial.T (-1) *
          LaurentPolynomial.T ((a : Int) - 2 * (a : Int)) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      ring
    rw [ht]
    ring
  · have hba : b ≤ a := by omega
    have hba1 : b + 1 ≤ a := by omega
    have hsub₁ : a + 1 - (b + 1) = a - b := by omega
    have hsub₂ : a - (b + 1) + 1 = a - b := by omega
    simp [closedTerm, Nat.choose_succ_succ, hsub₁, pow_succ, z]
    ring_nf
    have htneg : (LaurentPolynomial.T (-1) : Laurent) *
        LaurentPolynomial.T ((a : Int) - (b : Int) * 2) =
          LaurentPolynomial.T (-1 + (a : Int) - (b : Int) * 2) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      ring
    have htpos : (LaurentPolynomial.T 1 : Laurent) *
        LaurentPolynomial.T (-2 + (a : Int) - (b : Int) * 2) =
          LaurentPolynomial.T (-1 + (a : Int) - (b : Int) * 2) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      ring
    have hpow12L : ((2 : Laurent) ^ (a - (1 + b))) * 12 =
        (2 : Laurent) ^ (a - b) * 6 := by
      rw [show a - (1 + b) = a - (b + 1) by omega]
      calc
        (2 : Laurent) ^ (a - (b + 1)) * 12 =
            ((2 : Laurent) ^ (a - (b + 1)) * 2) * 6 := by ring
        _ = (2 : Laurent) ^ (a - b) * 6 := by rw [← pow_succ, hsub₂]
    have hneg_scaled :
        (Nat.choose a b : Laurent) * LaurentPolynomial.T (-1) *
              LaurentPolynomial.T ((a : Int) - (b : Int) * 2) *
              2 ^ (a - b) * 3 ^ b * 6 =
          (Nat.choose a b : Laurent) *
              LaurentPolynomial.T (-1 + (a : Int) - (b : Int) * 2) *
              2 ^ (a - b) * 3 ^ b * 6 := by
      calc
        _ = (Nat.choose a b : Laurent) *
              (LaurentPolynomial.T (-1) *
                LaurentPolynomial.T ((a : Int) - (b : Int) * 2)) *
              2 ^ (a - b) * 3 ^ b * 6 := by ring
        _ = _ := by rw [htneg]
    have hpos_scaled :
        (Nat.choose a (1 + b) : Laurent) * LaurentPolynomial.T 1 *
              LaurentPolynomial.T (-2 + (a : Int) - (b : Int) * 2) *
              2 ^ (a - (1 + b)) * 3 ^ b * 12 =
          (Nat.choose a (1 + b) : Laurent) *
              LaurentPolynomial.T (-1 + (a : Int) - (b : Int) * 2) *
              2 ^ (a - b) * 3 ^ b * 6 := by
      calc
        _ = (Nat.choose a (1 + b) : Laurent) *
              (LaurentPolynomial.T 1 *
                LaurentPolynomial.T (-2 + (a : Int) - (b : Int) * 2)) *
              2 ^ (a - (1 + b)) * 3 ^ b * 12 := by ring
        _ = (Nat.choose a (1 + b) : Laurent) *
              LaurentPolynomial.T (-1 + (a : Int) - (b : Int) * 2) *
              3 ^ b * (2 ^ (a - (1 + b)) * 12) := by rw [htpos]; ring
        _ = (Nat.choose a (1 + b) : Laurent) *
              LaurentPolynomial.T (-1 + (a : Int) - (b : Int) * 2) *
              3 ^ b * (2 ^ (a - b) * 6) := by rw [hpow12L]
        _ = _ := by ring
    rw [hneg_scaled, hpos_scaled]

private theorem closedPolynomial_recurrence (m : Nat) :
    closedPolynomial (m + 2) =
      2 * z 1 * closedPolynomial (m + 1) + 3 * z (-1) * closedPolynomial m := by
  have hleft : closedTerm (0, m + 2) = 0 := by
    have h : 0 < m + 2 := by omega
    simp [closedTerm, Nat.choose_eq_zero_of_lt h]
  have hright :
      closedTerm (m + 2, 0) = 2 * z 1 * closedTerm (m + 1, 0) := by
    simp [closedTerm, z, pow_succ]
    have ht : (LaurentPolynomial.T ((m : Int) + 2) : Laurent) =
        LaurentPolynomial.T 1 * LaurentPolynomial.T ((m : Int) + 1) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      ring
    rw [ht]
    ring
  simp only [closedPolynomial, Finset.Nat.antidiagonal_succ_succ',
    Finset.Nat.antidiagonal_succ', Finset.sum_cons, Finset.sum_map,
    Function.Embedding.coeFn_mk, Function.comp_apply]
  rw [hleft, zero_add, hright]
  change 2 * z 1 * closedTerm (m + 1, 0) +
        (∑ x ∈ Finset.antidiagonal m, closedTerm (x.1 + 1, x.2 + 1)) =
      2 * z 1 * (closedTerm (m + 1, 0) +
        ∑ x ∈ Finset.antidiagonal m, closedTerm (x.1, x.2 + 1)) +
      3 * z (-1) * ∑ x ∈ Finset.antidiagonal m, closedTerm x
  simp_rw [closedTerm_step]
  rw [Finset.sum_add_distrib]
  conv_lhs =>
    rhs
    lhs
    rw [← Finset.mul_sum]
  conv_lhs =>
    rhs
    rhs
    rw [← Finset.mul_sum]
  ring

/-- The source-derived transfer polynomial has the finite antidiagonal formula. -/
theorem pathPolynomial_closed_formula (m : Nat) :
    pathPolynomial m = closedPolynomial m := by
  induction m using Nat.twoStepInduction with
  | zero =>
      have hpath : pathPolynomial 0 = 2 := by
        have hzadd (p q : Int) : z p * z q = z (p + q) := by
          exact (LaurentPolynomial.T_add p q).symm
        have hzzero : z 0 = (1 : Laurent) := by simp [z]
        simp [pathPolynomial, terminalWeight, evenTerminalWeight,
          hzadd, hzzero, State.A, State.D]
        norm_num
      have hclosed : closedPolynomial 0 = 2 := by
        simp [closedPolynomial, closedTerm, z]
      rw [hpath, hclosed]
  | one =>
      have hpath : pathPolynomial 1 = 4 * z 1 := by
        have hzadd (p q : Int) : z p * z q = z (p + q) := by
          exact (LaurentPolynomial.T_add p q).symm
        have hzzero : z 0 = (1 : Laurent) := by simp [z]
        simp [pathPolynomial, terminalWeight, advance, evenTerminalWeight,
          hzadd, hzzero, State.A, State.D, State.E, State.H, State.I]
        ring
      have hclosed : closedPolynomial 1 = 4 * z 1 := by
        norm_num [closedPolynomial, closedTerm, Finset.Nat.antidiagonal_succ', z]
      rw [hpath, hclosed]
  | more m hm hm1 =>
      rw [pathPolynomial_recurrence, closedPolynomial_recurrence, hm, hm1]

/-- The coefficient used by the even boundary. -/
theorem pathPolynomial_coeff_three_mul (s : Nat) :
    (pathPolynomial (3 * s)).coeff 0 =
      2 * 6 ^ s * Nat.choose (2 * s) s := by
  have hcoeff (p : Nat × Nat) (q : Int) :
      (closedTerm p).coeff q =
        if (p.1 : Int) - 2 * (p.2 : Int) = q then
          2 * Nat.choose p.1 p.2 * 2 ^ (p.1 - p.2) * 3 ^ p.2
        else 0 := by
    change (LaurentPolynomial.C
        (2 * Nat.choose p.1 p.2 * 2 ^ (p.1 - p.2) * 3 ^ p.2) *
          LaurentPolynomial.T ((p.1 : Int) - 2 * (p.2 : Int))).coeff q = _
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    rw [AddMonoidAlgebra.coeff_single_apply]
  rw [pathPolynomial_closed_formula]
  unfold closedPolynomial
  rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp_rw [hcoeff]
  rw [Finset.sum_eq_single (2 * s, s)]
  · norm_num
    rw [show 2 * s - s = s by omega]
    calc
      2 * Nat.choose (2 * s) s * 2 ^ s * 3 ^ s =
          2 * (2 ^ s * 3 ^ s) * Nat.choose (2 * s) s := by ring
      _ = 2 * 6 ^ s * Nat.choose (2 * s) s := by rw [← mul_pow]; norm_num
  · intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    split_ifs with he
    · exfalso
      apply hne
      apply Prod.ext <;> dsimp
      · omega
      · omega
    · rfl
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_antidiagonal]
    omega

/-- The coefficient used by the odd singleton boundary. -/
theorem pathPolynomial_coeff_three_mul_add_two (s : Nat) :
    (pathPolynomial (3 * s + 2)).coeff (-1) =
      6 ^ (s + 1) * Nat.choose (2 * s + 1) (s + 1) := by
  have hcoeff (p : Nat × Nat) (q : Int) :
      (closedTerm p).coeff q =
        if (p.1 : Int) - 2 * (p.2 : Int) = q then
          2 * Nat.choose p.1 p.2 * 2 ^ (p.1 - p.2) * 3 ^ p.2
        else 0 := by
    change (LaurentPolynomial.C
        (2 * Nat.choose p.1 p.2 * 2 ^ (p.1 - p.2) * 3 ^ p.2) *
          LaurentPolynomial.T ((p.1 : Int) - 2 * (p.2 : Int))).coeff q = _
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    rw [AddMonoidAlgebra.coeff_single_apply]
  rw [pathPolynomial_closed_formula]
  unfold closedPolynomial
  rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp_rw [hcoeff]
  rw [Finset.sum_eq_single (2 * s + 1, s + 1)]
  · rw [if_pos (by push_cast; ring)]
    rw [show 2 * s + 1 - (s + 1) = s by omega, pow_succ]
    calc
      2 * Nat.choose (2 * s + 1) (s + 1) * 2 ^ s * (3 ^ s * 3) =
          6 * (2 ^ s * 3 ^ s) * Nat.choose (2 * s + 1) (s + 1) := by ring
      _ = 6 * 6 ^ s * Nat.choose (2 * s + 1) (s + 1) := by
        rw [← mul_pow]
        norm_num
      _ = 6 ^ (s + 1) * Nat.choose (2 * s + 1) (s + 1) := by
        rw [pow_succ]
        ring
  · intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    split_ifs with he
    · exfalso
      apply hne
      apply Prod.ext <;> dsimp
      · omega
      · omega
    · rfl
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_antidiagonal]
    omega

end D5.S3.Combinatorics.Zigzag
