/- GID: D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenMoments
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CatalanPowerHankel/CiglerElevenMoments
   mirror-E: none(waiver:algebraic-moment-dictionary)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The Jacobi recurrence identifies odd Catalan powers as normalized polynomial moments. -/

import D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenDefs
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal
import Mathlib.Tactic

set_option maxRecDepth 2000
set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option quotPrecheck false

noncomputable section

namespace D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenMoments

open Polynomial
open CiglerElevenDefs

open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

local notation "P" => (fun n : ℕ => Polynomial.map
  (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun i : Fin 2 => if i = 0 then 2 else 1))
  (orthogonal n))

/-- The Jacobi polynomial action produces basis vectors, is normalized orthogonal,
and has the exact Catalan-power moment dictionary, including negative coefficient indices. -/
theorem moment_dictionary :
    ∃ moment : ℚ[X] →ₗ[ℚ] ℚ,
    (∀ a b : ℕ, moment (P a * P b) = if a = b then 1 else 0) ∧
    (∀ t k : ℕ, moment (X ^ t * P k) =
      catalanPowerCoeff (2 * k + 1) ((t : ℤ) - k)) := by
  let jacobi : Module.End ℚ (ℕ → ℚ) := {
    toFun := fun v => fun
      | 0 => v 0 + v 1
      | k + 1 => v k + 2 * v (k + 1) + v (k + 2)
    map_add' := by
      intro v w
      ext k
      cases k <;> simp <;> ring
    map_smul' := by
      intro c v
      ext k
      cases k <;> simp <;> ring }
  let moment : ℚ[X] →ₗ[ℚ] ℚ := {
    toFun := fun f => (aeval jacobi f) (Pi.single 0 1) 0
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  have pzero : P 0 = 1 := by simp [orthogonal]
  have pone : P 1 = X - 1 := by simp [orthogonal, sVar]
  have prec (n : ℕ) : P (n + 2) = (X - 2) * P (n + 1) - P n := by
    simp [orthogonal, tVar, Polynomial.map_sub, Polynomial.map_mul, Polynomial.C_ofNat]
  have row (n : ℕ) (v : ℕ → ℚ) : (aeval jacobi (P n)) v 0 = v n := by
    induction n using Nat.twoStepInduction generalizing v with
    | zero => simp [pzero]
    | one => simp [pone, jacobi, Pi.sub_apply]
    | more n ih₀ ih₁ =>
      rw [prec]
      have hc : aeval jacobi ((X - 2) * P (n + 1)) =
          aeval jacobi (P (n + 1)) * (jacobi - 2) := by
        rw [mul_comm, map_mul]
        rw [map_sub, aeval_X]
        congr 2
        exact aeval_natCast jacobi 2
      rw [map_sub, hc]
      change (aeval jacobi (P (n + 1))) ((jacobi - 2) v) 0 -
        (aeval jacobi (P n)) v 0 = v (n + 2)
      rw [ih₁, ih₀]
      simp [jacobi, LinearMap.sub_apply, Pi.sub_apply]
      ring
  have jzero : jacobi (Pi.single 0 1) = Pi.single 0 1 + Pi.single 1 1 := by
    ext l
    cases l with
    | zero => simp [jacobi]
    | succ l =>
      simp [jacobi, Pi.single_apply]
  have jsucc (n : ℕ) : jacobi (Pi.single (n + 1) 1) =
      Pi.single n 1 + 2 • Pi.single (n + 1) 1 + Pi.single (n + 2) 1 := by
    ext l
    cases l with
    | zero =>
      simp [jacobi, Pi.single_apply, eq_comm]
    | succ l =>
      simp only [jacobi, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
        Pi.single_apply]
      split_ifs <;> simp_all
      all_goals omega
  have column (n : ℕ) : (aeval jacobi (P n)) (Pi.single 0 1) = Pi.single n 1 := by
    induction n using Nat.twoStepInduction with
    | zero => simp [pzero]
    | one =>
      simp only [pone, map_sub, aeval_X, map_one, LinearMap.sub_apply,
        Module.End.one_apply, jzero]
      abel
    | more n ih₀ ih₁ =>
      rw [prec]
      simp only [map_sub, map_mul, aeval_X, map_ofNat, LinearMap.sub_apply,
        Module.End.mul_apply, ih₀, ih₁]
      rw [jsucc, Module.End.ofNat_apply]
      change Pi.single n 1 + 2 • Pi.single (n + 1) 1 + Pi.single (n + 2) 1 -
        2 • Pi.single (n + 1) 1 - Pi.single n 1 = _
      abel
  have binomial (t k : ℕ) : catalanPowerCoeff (2 * k + 1) ((t : ℤ) - k) =
      ((2 * t).choose (t + k) : ℚ) - ((2 * t).choose (t + k + 1) : ℚ) := by
    by_cases hkt : k ≤ t
    · have ht : 0 ≤ (t : ℤ) - k := by omega
      have hj : ((t : ℤ) - k).toNat = t - k := by omega
      have hden : (2 * (t - k : ℕ) : ℚ) + (2 * k + 1 : ℕ) = 2 * t + 1 := by
        have hh : t - k + k = t := Nat.sub_add_cancel hkt
        exact_mod_cast (show 2 * (t - k) + (2 * k + 1) = 2 * t + 1 by omega)
      have htop : 2 * (t - k) + (2 * k + 1) = 2 * t + 1 := by omega
      have hsym : (2 * t).choose (t + k) = (2 * t).choose (t - k) := by
        have hs := Nat.choose_symm (n := 2 * t) (k := t - k) (by omega)
        convert hs using 1; congr 1; omega
      have hscale := Nat.choose_mul_succ_eq (2 * t) (t - k)
      have hidx : 2 * t + 1 - (t - k) = t + k + 1 := by omega
      rw [hidx] at hscale
      have hs₁ : ((2 * t).choose (t - k) : ℚ) * (2 * t + 1) =
          ((2 * t + 1).choose (t - k) : ℚ) * (t + k + 1) := by
        exact_mod_cast hscale
      have hs₂ : ((2 * t).choose (t + k + 1) : ℚ) * (2 * t + 1) =
          ((2 * t + 1).choose (t - k) : ℚ) * (t - k : ℕ) := by
        by_cases heq : t = k
        · subst t
          simp [Nat.choose_eq_zero_of_lt (show 2 * k < k + k + 1 by omega)]
        · have hjp : 0 < t - k := by omega
          have hs := Nat.add_one_mul_choose_eq (2 * t) (t - k - 1)
          have hi : t - k - 1 + 1 = t - k := by omega
          rw [hi] at hs
          have hb : (2 * t).choose (t + k + 1) =
              (2 * t).choose (t - k - 1) := by
            have hh := Nat.choose_symm (n := 2 * t) (k := t - k - 1) (by omega)
            convert hh using 1; congr 1; omega
          rw [hb]
          simpa [mul_comm] using (show (2 * t + 1 : ℚ) *
            ((2 * t).choose (t - k - 1) : ℚ) =
            ((2 * t + 1).choose (t - k) : ℚ) * (t - k : ℕ) by exact_mod_cast hs)
      unfold catalanPowerCoeff
      rw [if_pos ht, hj, hden, htop, hsym]
      have hne : (2 * (t : ℚ) + 1) ≠ 0 := by positivity
      field_simp
      have hq : ((t - k : ℕ) : ℚ) = (t : ℚ) - k := by
        push_cast [Nat.cast_sub hkt]
        rfl
      push_cast at hs₁ hs₂ ⊢
      rw [hq] at hs₂
      nlinarith [hs₁, hs₂]
    · have ht : ¬ 0 ≤ (t : ℤ) - k := by omega
      rw [catalanPowerCoeff, if_neg ht]
      simp only [ Nat.choose_eq_zero_of_lt (show 2 * t < t + k by omega),
        Nat.choose_eq_zero_of_lt (show 2 * t < t + k + 1 by omega), Nat.cast_zero, sub_zero]
  let A (t k : ℕ) : ℚ :=
    ((2 * t).choose (t + k) : ℚ) - ((2 * t).choose (t + k + 1) : ℚ)
  have pascal₂ (a b : ℕ) : ((a + 2).choose (b + 2) : ℚ) =
      (a.choose b : ℚ) + 2 * (a.choose (b + 1) : ℚ) + (a.choose (b + 2) : ℚ) := by
    rw [show a + 2 = (a + 1) + 1 by omega,
      show b + 2 = (b + 1) + 1 by omega, Nat.choose_succ_succ',
      Nat.choose_succ_succ', Nat.choose_succ_succ']
    push_cast
    ring
  have azero (k : ℕ) : A 0 k = if k = 0 then 1 else 0 := by
    cases k <;> simp [A]
  have asucc (t k : ℕ) : A (t + 1) (k + 1) =
      A t k + 2 * A t (k + 1) + A t (k + 2) := by
    dsimp [A]
    rw [show 2 * (t + 1) = 2 * t + 2 by omega,
      show t + 1 + (k + 1) = t + k + 2 by omega,
      show t + k + 2 + 1 = (t + k + 1) + 2 by omega,
      pascal₂, pascal₂]
    simp only [show t + (k + 1) = t + k + 1 by omega,
      show t + (k + 2) = t + k + 2 by omega]
    ring
  have aboundary (t : ℕ) : A (t + 1) 0 = A t 0 + A t 1 := by
    cases t with
    | zero => norm_num [A]
    | succ t =>
      have hs : (2 * (t + 1)).choose t = (2 * (t + 1)).choose (t + 2) := by
        have hh := Nat.choose_symm (n := 2 * (t + 1)) (k := t + 2) (by omega)
        simpa only [show 2 * (t + 1) - (t + 2) = t by omega] using hh
      dsimp [A]
      rw [show 2 * (t + 1 + 1) = 2 * (t + 1) + 2 by omega,
        show t + 1 + 1 = t + 2 by omega,
        show t + 2 + 1 = (t + 1) + 2 by omega, pascal₂, pascal₂]
      rw [hs]
      ring
  have powers (t k : ℕ) : (jacobi ^ t) (Pi.single 0 1) k = A t k := by
    induction t generalizing k with
    | zero => simp [azero, Pi.single_apply]
    | succ t ih =>
      rw [pow_succ']
      change jacobi ((jacobi ^ t) (Pi.single 0 1)) k = _
      cases k with
      | zero =>
        change (jacobi ^ t) (Pi.single 0 1) 0 +
          (jacobi ^ t) (Pi.single 0 1) 1 = _
        rw [ih, ih]
        exact (aboundary t).symm
      | succ k =>
        change (jacobi ^ t) (Pi.single 0 1) k +
          2 * (jacobi ^ t) (Pi.single 0 1) (k + 1) +
          (jacobi ^ t) (Pi.single 0 1) (k + 2) = _
        rw [ih, ih, ih]
        exact (asucc t k).symm
  refine ⟨moment, ?_, ?_⟩
  · intro a b
    change (aeval jacobi (P a * P b)) (Pi.single 0 1) 0 = _
    rw [map_mul, Module.End.mul_apply, row, column]
    simp [Pi.single_apply]
  · intro t k
    change (aeval jacobi (X ^ t * P k)) (Pi.single 0 1) 0 = _
    rw [mul_comm, map_mul, Module.End.mul_apply, row, map_pow, aeval_X, powers, binomial]

end D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenMoments
