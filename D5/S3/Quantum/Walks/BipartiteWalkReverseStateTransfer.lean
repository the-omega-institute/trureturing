/- GID: D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Neither seven-state bipartite walk transfers the sixth coordinate state to the first. -/

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.ZMod.Basic

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
  rw [Udef.eq_1, P.eq_1, Q.eq_1, M.eq_1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

private lemma integer_form_disp :
    (3 : ℂ) • Udisp = (M 1).map (Int.castRingHom ℂ) := by
  rw [Udisp.eq_1, M.eq_1]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private lemma scaled_matrix (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) :
    U = (1/3 : ℂ) • (M s).map (Int.castRingHom ℂ) := by
  simpa only [one_div] using (eq_inv_smul_iff₀ (by norm_num : (3 : ℂ) ≠ 0)).mpr h

private lemma integer_first_column (s : ℤ) :
    (M s).mulVec (Pi.single 1 1) = v := by
  rw [Matrix.mulVec_single_one, M.eq_1, v.eq_1]
  ext i
  fin_cases i <;> norm_num [Matrix.col_apply]

private lemma integer_invariant (s : ℤ) :
    (M s).mulVec v = (2 : ℤ) • v + (3 : ℤ) • w := by
  rw [M.eq_1, v.eq_1, w.eq_1]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

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
    have hv : Module.End.HasEigenvector ((M s).map (Int.castRingHom (ZMod 3))).toLin'
        (2 : ZMod 3) ((Int.castRingHom (ZMod 3)) ∘ v) := by
      constructor
      · exact Module.End.mem_eigenspace_iff.mpr heigen
      · intro hz
        have hzero := congrFun hz 0
        norm_num [Function.comp_apply, v] at hzero
    simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using hv.pow_apply n
  simpa only [Function.comp_def, RingHom.map_mulVec, Matrix.map_pow] using hpow

private lemma amplitude_formula (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) (n : ℕ) :
    ((U ^ (n + 3)).mulVec (Pi.single 5 1)) 0 =
      (((M s ^ n).mulVec v) 0 : ℂ) / (3 : ℂ) ^ (n + 1) := by
  let f := Int.castRingHom ℂ
  have hcol : (M s).map f *ᵥ (Pi.single 1 1) = f ∘ v := by
    ext i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply,
      Function.comp_apply] using
      congrArg f (congrFun (integer_first_column s) i)
  have he1 : U *ᵥ Pi.single 1 1 = (1/3 : ℂ) • (f ∘ v) := by
    rw [scaled_matrix s U h, Matrix.smul_mulVec, hcol]
  have hbase : (U ^ 3) *ᵥ Pi.single 5 1 = (1/3 : ℂ) • (f ∘ v) := by
    rw [pow_succ', pow_succ', pow_one, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, (first_steps s U h).1, (first_steps s U h).2, he1]
  have hpower : (U ^ n) *ᵥ (f ∘ v) =
      (1/3 : ℂ) ^ n • (f ∘ ((M s ^ n).mulVec v)) := by
    rw [scaled_matrix s U h, smul_pow, Matrix.smul_mulVec, ← Matrix.map_pow]
    congr 1
    ext i
    exact (RingHom.map_mulVec f (M s ^ n) v i).symm
  have hvec : (U ^ (n + 3)) *ᵥ Pi.single 5 1 =
      (1/3 : ℂ) ^ (n + 1) • (f ∘ ((M s ^ n).mulVec v)) := by
    rw [pow_add, ← Matrix.mulVec_mulVec, hbase, Matrix.mulVec_smul,
      hpower, smul_smul, ← pow_succ']
  have hentry := congrFun hvec 0
  change ((U ^ (n + 3)).mulVec (Pi.single 5 1)) 0 =
    (1/3 : ℂ) ^ (n + 1) * (((M s ^ n).mulVec v) 0 : ℂ) at hentry
  rw [one_div, inv_pow, mul_comm] at hentry
  simpa only [div_eq_mul_inv] using hentry

private lemma fraction_ne_one (a : ℤ) (n : ℕ) (hmod : (a : ZMod 3) ≠ 0) :
    ‖(a : ℂ) / (3 : ℂ) ^ (n + 1)‖ ≠ 1 := by
  intro heq
  have habs : |(a : ℝ)| = (3 : ℝ) ^ (n + 1) := by
    rw [Complex.norm_div, Complex.norm_intCast, Complex.norm_pow,
      Complex.norm_ofNat] at heq
    exact (div_eq_one_iff_eq (pow_ne_zero _ (by norm_num))).mp heq
  have habsInt : |a| = (3 : ℤ) ^ (n + 1) := by
    exact_mod_cast habs
  have hdvd : (3 : ℤ) ∣ a := by
    apply (dvd_abs 3 a).mp
    rw [habsInt]
    exact dvd_pow_self 3 (Nat.succ_ne_zero n)
  exact hmod ((ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mpr hdvd)

private lemma amplitude_ne_one (s : ℤ) (U : Matrix (Fin 7) (Fin 7) ℂ)
    (h : (3 : ℂ) • U = (M s).map (Int.castRingHom ℂ)) (k : ℕ) :
    ‖((U ^ k).mulVec (Pi.single 5 1)) 0‖ ≠ 1 := by
  rcases k with (_ | _ | _ | n)
  · norm_num [Pi.single_apply]
  · rw [pow_one, (first_steps s U h).1]
    norm_num [Pi.single_apply]
  · rw [pow_two, ← Matrix.mulVec_mulVec,
      (first_steps s U h).1, (first_steps s U h).2]
    norm_num [Pi.single_apply]
  · change ‖((U ^ (n + 3)).mulVec (Pi.single 5 1)) 0‖ ≠ 1
    rw [amplitude_formula s U h n]
    apply fraction_ne_one
    have hc : (((M s ^ n).mulVec v) 0 : ZMod 3) = -(2 : ZMod 3) ^ n := by
      simpa [Function.comp_apply, Pi.smul_apply, smul_eq_mul, v] using
        congrFun (orbit_mod s n) 0
    rw [hc, show (2 : ZMod 3) = -1 by decide]
    exact neg_ne_zero.mpr (isUnit_neg_one.pow n).ne_zero

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
