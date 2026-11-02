/- GID: D5/S3/FiniteGroups/BajnokBeattyFirstCharacteristicDefect
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyFirstCharacteristicDefect
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: The first characteristic coefficient defect of the actual same-group Cayley graphs. -/

import D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments
import D5.S0.Observation.MatrixFirstMomentCoefficientBridge
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
proof_shape: first_characteristic_defect: content.
admission_basis: escape-witness.
escape_witness: the actual q19/q33 graphs supply every trace equality and the
trace defect. Their Hermitian property follows from their adjacency matrices.
The first-coefficient bridge then gives the negative defect divided by the
first return length; integer parameter factorization identifies this quotient.
No trace, kernel, return-count, spectral, or separation premise is added.
The range includes every odd p >= 3, including composite p.
-/

set_option autoImplicit false

noncomputable section

open scoped Classical

namespace D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect

open D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments (q19 q33 graph)
open D5.S0.Observation.MatrixFirstMomentCoefficientBridge

private theorem discriminant_factor (t : ℤ) :
    ((6 * t - 1) ^ 2 - 9) / 2 = (3 * t + 1) * (6 * t - 4) := by
  have hnum : (6 * t - 1) ^ 2 - 9 = 2 * ((3 * t + 1) * (6 * t - 4)) := by
    ring
  rw [hnum]
  omega

-- A local witness avoids referring to the supplier's private finiteness helper.
-- Finite is a proposition; its proof does not change the actual vertex type.
private theorem vertices_finite (p t : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t) :
    Finite (ZMod p.natAbs × ZMod (p * (((6 * t - 1) ^ 2 - 9) / 2)).natAbs) := by
  have hp : 0 < p := by omega
  have hD : 0 < ((6 * t - 1) ^ 2 - 9) / 2 := by
    rw [discriminant_factor]
    exact mul_pos (by omega) (by omega)
  letI : NeZero p.natAbs := ⟨Int.natAbs_ne_zero.mpr hp.ne'⟩
  letI : NeZero (p * (((6 * t - 1) ^ 2 - 9) / 2)).natAbs :=
    ⟨Int.natAbs_ne_zero.mpr (mul_pos hp hD).ne'⟩
  infer_instance

/-- The actual `(1,9)` and `(3,3)` Cayley graphs on the same residue-group product
have equal descending characteristic coefficients before the first return
length. At that length the second minus the first coefficient is exactly
`-2 * p * (3*t+1)`, cast from the integers into the complex numbers.

Descending index zero is the leading coefficient; the first differing
polynomial degree is `Fintype.card H - n`. No matrix or trace data is an input. -/
theorem first_characteristic_defect (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6 * t - 1
    let D : ℤ := (m ^ 2 - 9) / 2
    let H := ZMod p.natAbs × ZMod (p * D).natAbs
    let N : ℤ := p ^ 2 * D
    let n : ℕ := (p * (m - 3)).toNat
    letI : Finite H := vertices_finite p t hp3 ht
    letI : Fintype H := Fintype.ofFinite H
    let C19 : SimpleGraph H := graph (q19 p D t)
    let C33 : SimpleGraph H := graph (q33 p D t)
    let A19 : Matrix H H ℂ := C19.adjMatrix ℂ
    let A33 : Matrix H H ℂ := C33.adjMatrix ℂ
    (Nat.card H : ℤ) = N ∧
    0 < n ∧ n ≤ Fintype.card H ∧
    (∀ j : ℕ, j < n →
      A19.charpoly.coeff (Fintype.card H - j) =
        A33.charpoly.coeff (Fintype.card H - j)) ∧
    (A33.charpoly.coeff (Fintype.card H - n) -
      A19.charpoly.coeff (Fintype.card H - n) =
        ((-2 * p * (3 * t + 1) : ℤ) : ℂ)) ∧
    A19.charpoly ≠ A33.charpoly := by
  classical
  let m : ℤ := 6 * t - 1
  let D : ℤ := (m ^ 2 - 9) / 2
  let H := ZMod p.natAbs × ZMod (p * D).natAbs
  let N : ℤ := p ^ 2 * D
  let n : ℕ := (p * (m - 3)).toNat
  letI : Finite H := vertices_finite p t hp3 ht
  letI : Fintype H := Fintype.ofFinite H
  let C19 : SimpleGraph H := graph (q19 p D t)
  let C33 : SimpleGraph H := graph (q33 p D t)
  let A19 : Matrix H H ℂ := C19.adjMatrix ℂ
  let A33 : Matrix H H ℂ := C33.adjMatrix ℂ
  change (Nat.card H : ℤ) = N ∧
    0 < n ∧ n ≤ Fintype.card H ∧
    (∀ j : ℕ, j < n →
      A19.charpoly.coeff (Fintype.card H - j) =
        A33.charpoly.coeff (Fintype.card H - j)) ∧
    (A33.charpoly.coeff (Fintype.card H - n) -
      A19.charpoly.coeff (Fintype.card H - n) =
        ((-2 * p * (3 * t + 1) : ℤ) : ℂ)) ∧
    A19.charpoly ≠ A33.charpoly
  have hmom := BajnokBeattyCayleyReturnMoments.first_return_moment_defect
    p t hp3 hpo ht
  have hcardH : (Nat.card H : ℤ) = N := hmom.1
  have htrace : ∀ k : ℕ, k < n →
      Matrix.trace (A19 ^ k) = Matrix.trace (A33 ^ k) := hmom.2.2.2.1
  have hgap : Matrix.trace (A33 ^ n) - Matrix.trace (A19 ^ n) =
      2 * (N : ℂ) := hmom.2.2.2.2
  have h19 : A19.IsHermitian := (C19.isAdjMatrix_adjMatrix ℂ).isHermitian
  have h33 : A33.IsHermitian := (C33.isAdjMatrix_adjMatrix ℂ).isHermitian
  have hp : 0 < p := by omega
  have hm3 : 0 < m - 3 := by dsimp [m]; omega
  have hDfactor : D = (3 * t + 1) * (m - 3) := by
    dsimp [D, m]
    rw [discriminant_factor]
    ring
  have hnZ : (n : ℤ) = p * (m - 3) := by
    dsimp [n]
    exact Int.toNat_of_nonneg (le_of_lt (mul_pos hp hm3))
  have hn : 0 < n := by
    have h : (0 : ℤ) < (n : ℤ) := by rw [hnZ]; exact mul_pos hp hm3
    exact_mod_cast h
  have hNfactor : N = (n : ℤ) * (p * (3 * t + 1)) := by
    dsimp only [N]
    rw [hnZ, hDfactor]
    ring
  have hcardZ : (Fintype.card H : ℤ) = N := by
    simpa only [Nat.card_eq_fintype_card] using hcardH
  have hnCardZ : (n : ℤ) ≤ (Fintype.card H : ℤ) := by
    rw [hcardZ, hNfactor]
    have hqpos : 0 < p * (3 * t + 1) := mul_pos hp (by omega)
    have hq : 1 ≤ p * (3 * t + 1) := by omega
    have hnnonneg : (0 : ℤ) ≤ (n : ℤ) := by positivity
    calc
      (n : ℤ) = (n : ℤ) * 1 := (mul_one _).symm
      _ ≤ (n : ℤ) * (p * (3 * t + 1)) := mul_le_mul_of_nonneg_left hq hnnonneg
  have hnCard : n ≤ Fintype.card H := by exact_mod_cast hnCardZ
  have hbridge := matrix_first_moment_coefficient_bridge
    A19 A33 h19 h33 n hn hnCard (fun k _ hk => htrace k hk)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hNfactorC : (N : ℂ) = (n : ℂ) * ((p * (3 * t + 1) : ℤ) : ℂ) := by
    exact_mod_cast hNfactor
  have hcoeff : A33.charpoly.coeff (Fintype.card H - n) -
      A19.charpoly.coeff (Fintype.card H - n) =
        ((-2 * p * (3 * t + 1) : ℤ) : ℂ) := by
    apply mul_left_cancel₀ hnC
    rw [hbridge.2, hgap, hNfactorC]
    push_cast
    ring
  have hdistinct : A19.charpoly ≠ A33.charpoly := by
    intro hequal
    have hzero := hbridge.2
    rw [hequal, sub_self, mul_zero, hgap] at hzero
    have hNZ : 0 < N := by
      rw [hNfactor]
      exact mul_pos (by exact_mod_cast hn) (mul_pos hp (by omega))
    have hNC : (N : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hNZ)
    exact (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hNC))
      hzero.symm
  exact ⟨hcardH, hn, hnCard, hbridge.1, hcoeff, hdistinct⟩

#print axioms first_characteristic_defect

end D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect
