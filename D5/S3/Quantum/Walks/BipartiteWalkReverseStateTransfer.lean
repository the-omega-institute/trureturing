/- GID: D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Neither seven-state bipartite walk transfers the sixth coordinate state to the first. -/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer

open Matrix

noncomputable section

def P : Matrix (Fin 7) (Fin 7) ℂ :=
  !![1/3, 0, 1/3, 1/3, 0, 0, 0;
     0, 1/2, 0, 0, 0, 1/2, 0;
     1/3, 0, 1/3, 1/3, 0, 0, 0;
     1/3, 0, 1/3, 1/3, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 1/2, 0, 0, 0, 1/2, 0;
     0, 0, 0, 0, 0, 0, 1]

def Q : Matrix (Fin 7) (Fin 7) ℂ :=
  !![1/2, 1/2, 0, 0, 0, 0, 0;
     1/2, 1/2, 0, 0, 0, 0, 0;
     0, 0, 1/2, 0, 1/2, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 1/2, 0, 1/2, 0, 0;
     0, 0, 0, 0, 0, 1/2, 1/2;
     0, 0, 0, 0, 0, 1/2, 1/2]

def Udisp : Matrix (Fin 7) (Fin 7) ℂ :=
  !![0, -1/3, 0, 2/3, 2/3, 0, 0;
     0, 0, 0, 0, 0, 0, 1;
     0, 2/3, 0, 2/3, 1/3, 0, 0;
     0, 2/3, 0, -1/3, 2/3, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0]

def Udef : Matrix (Fin 7) (Fin 7) ℂ := (2 • P - 1) * (2 • Q - 1)

def PerfectStateTransfer {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n) : Prop :=
  ∃ k : ℕ, ∃ γ : ℂ, ‖γ‖ = 1 ∧
    (U ^ k).mulVec (Pi.single a 1) = γ • Pi.single b 1

def claim : Prop :=
  ¬ PerfectStateTransfer Udef 5 0 ∧ ¬ PerfectStateTransfer Udisp 5 0

private def M (s : ℤ) : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, -1, 0, 2, 2, 0, 0;
     0, 0, 0, 0, 0, 0, 3;
     0, 2, 0, 2, s, 0, 0;
     0, 2, 0, -1, 2, 0, 0;
     0, 0, 3, 0, 0, 0, 0;
     3, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 3, 0]

private def v : Fin 7 → ℤ := ![-1, 0, 2, 2, 0, 0, 0]

private def w : Fin 7 → ℤ := ![2, 0, 0, -2, 2, -1, 0]

private lemma integer_form_def :
    (3 : ℂ) • Udef = (M (-1)).map (Int.castRingHom ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Udef, P, Q, M, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

private lemma integer_form_disp :
    (3 : ℂ) • Udisp = (M 1).map (Int.castRingHom ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Udisp, M]

private lemma scaled_matrix (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) :
    U = (1/3 : ℂ) • (M s).map (Int.castRingHom ℂ) := by
  rw [← h, smul_smul]
  norm_num

private lemma integer_first_column (s : ℤ) :
    (M s).mulVec (Pi.single 1 1) = v := by
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> norm_num [M, v, Matrix.col_apply]

private lemma integer_invariant (s : ℤ) :
    (M s).mulVec v = (2 : ℤ) • v + (3 : ℤ) • w := by
  ext i
  fin_cases i <;> norm_num [M, v, w, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private lemma first_steps (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) :
    U.mulVec (Pi.single 5 1) = Pi.single 6 1 ∧
    U.mulVec (Pi.single 6 1) = Pi.single 1 1 := by
  rw [scaled_matrix s U h]
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [M, Matrix.smul_mulVec, Matrix.mulVec_single_one,
      Matrix.col_apply, Pi.single_apply]

private lemma orbit_mod (s : ℤ) (n : ℕ) :
    (Int.castRingHom (ZMod 3)) ∘ ((M s ^ n).mulVec v) =
      (2 : ZMod 3) ^ n • ((Int.castRingHom (ZMod 3)) ∘ v) := by
  have heigen : (M s).map (Int.castRingHom (ZMod 3)) *ᵥ
      ((Int.castRingHom (ZMod 3)) ∘ v) =
      (2 : ZMod 3) • ((Int.castRingHom (ZMod 3)) ∘ v) := by
    ext i
    rw [← RingHom.map_mulVec, integer_invariant]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      show (3 : ZMod 3) = 0 by decide]
  have hpow : ((M s).map (Int.castRingHom (ZMod 3)) ^ n) *ᵥ
      ((Int.castRingHom (ZMod 3)) ∘ v) =
      (2 : ZMod 3) ^ n • ((Int.castRingHom (ZMod 3)) ∘ v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, heigen,
        smul_smul, pow_succ]
  simpa only [Function.comp_def, RingHom.map_mulVec, Matrix.map_pow] using hpow

private lemma amplitude_formula (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) (n : ℕ) :
    ((U ^ (n + 3)).mulVec (Pi.single 5 1)) 0 =
      (((M s ^ n).mulVec v) 0 : ℂ) / (3 : ℂ) ^ (n + 1) := by
  sorry

private lemma amplitude_ne_one (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) (k : ℕ) :
    ‖((U ^ k).mulVec (Pi.single 5 1)) 0‖ ≠ 1 := by
  sorry

private lemma no_transfer (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) :
    ¬ PerfectStateTransfer U 5 0 := by
  rintro ⟨k, γ, hγ, htransfer⟩
  have hentry := congrFun htransfer 0
  have heq : ((U ^ k).mulVec (Pi.single 5 1)) 0 = γ := by
    simpa using hentry
  exact amplitude_ne_one s U h k (heq ▸ hγ)

theorem result : claim :=
  ⟨no_transfer (-1) Udef integer_form_def, no_transfer 1 Udisp integer_form_disp⟩

end

end D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer
