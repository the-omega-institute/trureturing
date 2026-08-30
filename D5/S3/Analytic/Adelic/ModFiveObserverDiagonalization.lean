/- GID: D5/S3/Analytic/Adelic/ModFiveObserverDiagonalization
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ModFiveObserverDiagonalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflected mod-five Hurwitz sectors split into trivial and quadratic channels. -/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * Repository searches for mod-five observer channels, Hadamard channel sums,
     ramified-prime restoration, and a quadratic-character Hurwitz split found
     no whole-statement D5 owner or canonical channel definition.
   * `ZMod.LFunction` is the canonical Hurwitz-zeta decomposition used below.
     `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta` supplies the
     deleted Euler factor, and `quadraticChar (ZMod 5)` supplies the canonical
     golden-symbol character. These Mathlib hits are applied directly.
   * Body-shape searches for all three definitions below found no D5 hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.ModFiveObserverDiagonalization

open Complex HurwitzZeta Matrix

noncomputable section

/-- The reflected Hurwitz sector supported on residues one and four modulo five. -/
noncomputable def modFiveFirstChannel (s : ℂ) : ℂ :=
  hurwitzZeta (ZMod.toAddCircle (1 : ZMod 5)) s +
    hurwitzZeta (ZMod.toAddCircle (4 : ZMod 5)) s

/-- The reflected Hurwitz sector supported on residues two and three modulo five. -/
noncomputable def modFiveSecondChannel (s : ℂ) : ℂ :=
  hurwitzZeta (ZMod.toAddCircle (2 : ZMod 5)) s +
    hurwitzZeta (ZMod.toAddCircle (3 : ZMod 5)) s

/-- The quadratic Dirichlet character modulo five, transported from integer to complex values. -/
noncomputable def modFiveQuadraticCharacter : DirichletCharacter ℂ 5 :=
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

/-- The unnormalized Hadamard matrix separating the sum and difference channels. -/
def modFiveObserverHadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 1; 1, -1]

private lemma two_not_square_mod_five : ¬IsSquare (2 : ZMod 5) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [ZMod.euler_criterion (p := 5) (a := 2) (by decide)]
  decide

private lemma three_not_square_mod_five : ¬IsSquare (3 : ZMod 5) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [ZMod.euler_criterion (p := 5) (a := 3) (by decide)]
  decide

private lemma four_square_mod_five : IsSquare (4 : ZMod 5) := by
  exact ⟨2, by decide⟩

private lemma quadratic_character_zero : modFiveQuadraticCharacter 0 = 0 := by
  simp only [modFiveQuadraticCharacter, MulChar.ringHomComp_apply, quadraticChar_apply,
    quadraticCharFun, if_true]
  norm_num

private lemma quadratic_character_one : modFiveQuadraticCharacter 1 = 1 := by
  simp only [modFiveQuadraticCharacter, MulChar.ringHomComp_apply, quadraticChar_apply,
    quadraticCharFun]
  rw [if_neg (by decide), if_pos IsSquare.one]
  norm_num

private lemma quadratic_character_two : modFiveQuadraticCharacter 2 = -1 := by
  simp only [modFiveQuadraticCharacter, MulChar.ringHomComp_apply, quadraticChar_apply,
    quadraticCharFun]
  rw [if_neg (by decide), if_neg two_not_square_mod_five]
  norm_num

private lemma quadratic_character_three : modFiveQuadraticCharacter 3 = -1 := by
  simp only [modFiveQuadraticCharacter, MulChar.ringHomComp_apply, quadraticChar_apply,
    quadraticCharFun]
  rw [if_neg (by decide), if_neg three_not_square_mod_five]
  norm_num

private lemma quadratic_character_four : modFiveQuadraticCharacter 4 = 1 := by
  simp only [modFiveQuadraticCharacter, MulChar.ringHomComp_apply, quadraticChar_apply,
    quadraticCharFun]
  rw [if_neg (by decide), if_pos four_square_mod_five]
  norm_num

private lemma trivial_channel_hurwitz_expansion (s : ℂ) :
    (5 : ℂ) ^ (-s) * (modFiveFirstChannel s + modFiveSecondChannel s) =
      DirichletCharacter.LFunctionTrivChar 5 s := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  change _ = ZMod.LFunction (1 : DirichletCharacter ℂ 5) s
  rw [ZMod.LFunction]
  congr 1
  rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} by decide]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [MulChar.map_zero]
  rw [MulChar.one_apply (by exact (by decide : (1 : ZMod 5) ≠ 0).isUnit)]
  rw [MulChar.one_apply (by exact (by decide : (2 : ZMod 5) ≠ 0).isUnit)]
  rw [MulChar.one_apply (by exact (by decide : (3 : ZMod 5) ≠ 0).isUnit)]
  rw [MulChar.one_apply (by exact (by decide : (4 : ZMod 5) ≠ 0).isUnit)]
  simp only [modFiveFirstChannel, modFiveSecondChannel, zero_mul, one_mul]
  ring

private lemma quadratic_channel_hurwitz_expansion (s : ℂ) :
    (5 : ℂ) ^ (-s) * (modFiveFirstChannel s - modFiveSecondChannel s) =
      ZMod.LFunction modFiveQuadraticCharacter s := by
  classical
  rw [ZMod.LFunction]
  congr 1
  rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} by decide]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [quadratic_character_zero, quadratic_character_one, quadratic_character_two,
    quadratic_character_three, quadratic_character_four]
  simp only [modFiveFirstChannel, modFiveSecondChannel, zero_mul, one_mul, neg_one_mul]
  ring

/-- The two reflected mod-five Hurwitz sectors diagonalize into the trivial and
quadratic Dirichlet channels. The final two clauses expose the trivial-channel
Euler factor and the quadratic character values that give the channel roles. -/
theorem mod_five_observer_diagonalization (s : ℂ) (hs : s ≠ 1) :
    ((5 : ℂ) ^ (-s) * (modFiveFirstChannel s + modFiveSecondChannel s) =
      (1 - (5 : ℂ) ^ (-s)) * riemannZeta s) ∧
    ((5 : ℂ) ^ (-s) * (modFiveFirstChannel s - modFiveSecondChannel s) =
      ZMod.LFunction modFiveQuadraticCharacter s) ∧
    (![((1 - (5 : ℂ) ^ (-s)) * riemannZeta s),
        ZMod.LFunction modFiveQuadraticCharacter s] =
      (5 : ℂ) ^ (-s) •
        (modFiveObserverHadamard *ᵥ
          ![modFiveFirstChannel s, modFiveSecondChannel s])) ∧
    ((5 : ℂ) ^ (-s) * (modFiveFirstChannel s + modFiveSecondChannel s) =
      DirichletCharacter.LFunctionTrivChar 5 s) ∧
    (DirichletCharacter.LFunctionTrivChar 5 s =
      (1 - (5 : ℂ) ^ (-s)) * riemannZeta s) ∧
    (modFiveQuadraticCharacter 0 = 0 ∧
      modFiveQuadraticCharacter 1 = 1 ∧
      modFiveQuadraticCharacter 2 = -1 ∧
      modFiveQuadraticCharacter 3 = -1 ∧
      modFiveQuadraticCharacter 4 = 1) := by
  have hTrivial := trivial_channel_hurwitz_expansion s
  have hEuler :=
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 5) hs
  rw [Nat.prime_five.primeFactors] at hEuler
  simp only [Finset.prod_singleton] at hEuler
  have hSum := hTrivial.trans hEuler
  have hDifference := quadratic_channel_hurwitz_expansion s
  have hMatrix :
      ![((1 - (5 : ℂ) ^ (-s)) * riemannZeta s),
          ZMod.LFunction modFiveQuadraticCharacter s] =
        (5 : ℂ) ^ (-s) •
          (modFiveObserverHadamard *ᵥ
            ![modFiveFirstChannel s, modFiveSecondChannel s]) := by
    ext index
    fin_cases index
    · simpa [modFiveObserverHadamard, Matrix.mulVec, dotProduct] using hSum.symm
    · simpa [modFiveObserverHadamard, Matrix.mulVec, dotProduct, sub_eq_add_neg] using
        hDifference.symm
  exact ⟨hSum, hDifference, hMatrix, hTrivial, hEuler, quadratic_character_zero,
    quadratic_character_one, quadratic_character_two, quadratic_character_three,
    quadratic_character_four⟩

#print axioms mod_five_observer_diagonalization

end

end D5.S3.Analytic.Adelic.ModFiveObserverDiagonalization
