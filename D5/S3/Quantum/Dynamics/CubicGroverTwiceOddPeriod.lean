/- GID: D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: No connected cubic graph has period 2l for odd l. -/

/-
proof_shape: result: content
escape_witness: under cubic regularity, Odd l and grover G ^ (2 * l) = 1 imply
numerator G ^ 2 = 9; the local heq uses the odd determinant of the difference-of-powers
factor, and its diagonal evaluation is live in the contradiction.
Delivered declarations: grover, IsPeriodOf, claim, private numerator, and result.
admission_basis: open-problem-resolution (#12338; Proved)
Direct frozen dependencies: none (Mathlib only).
Utility: none; the result is a general negative answer for connected cubic graphs and odd l.
Escape-audit registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum

open scoped BigOperators
open Matrix

namespace D5.S3.Quantum.Dynamics.CubicGroverTwiceOddPeriod

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact matrix of §2.2, with the reversed-arc indicator inside the transition case. -/
def grover (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix G.Dart G.Dart ℂ :=
  fun a b => if b.snd = a.fst then
    2 / (G.degree b.snd : ℂ) - (if a = b.symm then 1 else 0) else 0

/-- A positive return time which is minimal among positive return times. -/
def IsPeriodOf {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (τ : ℕ) : Prop :=
  0 < τ ∧ U ^ τ = 1 ∧ ∀ σ, 0 < σ → σ < τ → U ^ σ ≠ 1

/-- Exactly the quantified claim in the preregistration. -/
def claim : Prop := ∀ l : ℕ, Odd l → 3 ∣ l →
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (∀ v, G.degree v = 3) → ¬ IsPeriodOf (grover G) (2 * l)

/-- The integer numerator `3U` for cubic graphs. -/
private def numerator (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix G.Dart G.Dart ℤ :=
  fun a b => if b.snd = a.fst then 2 - (if a = b.symm then 3 else 0) else 0

/-- Negative answer to Question 4.11, with its precise preregistered quantifiers. -/
theorem result : claim := by
  have stronger {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
      (hdegree : ∀ v, G.degree v = 3) (l : ℕ) (hl : Odd l) :
      grover G ^ (2 * l) ≠ 1 := by
    intro hret
    have hmodW : (Int.castRingHom (ZMod 2)).mapMatrix (numerator G) = ((1 : Matrix G.Dart G.Dart (ZMod 2)).submatrix SimpleGraph.Dart.symm id) := by
      ext a b
      change ((numerator G a b : ℤ) : ZMod 2) = ((1 : Matrix G.Dart G.Dart (ZMod 2)).submatrix SimpleGraph.Dart.symm id) a b
      have hm : (-1 : ZMod 2) = 1 := by decide
      have ht : (2 : ZMod 2) = 0 := by decide
      by_cases hr : a = b.symm
      · subst a
        norm_num [numerator, Matrix.submatrix, Matrix.one_apply]
        exact hm
      · have hr' : a.symm ≠ b := by
          intro he
          apply hr
          simpa using congrArg SimpleGraph.Dart.symm he
        by_cases hc : b.snd = a.fst
        · norm_num [numerator, Matrix.submatrix, Matrix.one_apply, hr, hr', hc]
          exact ht
        · simp [numerator, Matrix.submatrix, Matrix.one_apply, hr', hc]
    have hrev : ((1 : Matrix G.Dart G.Dart (ZMod 2)).submatrix SimpleGraph.Dart.symm id) ^ 2 = 1 := by
      ext a b
      rw [pow_two, Matrix.mul_apply]
      rw [Finset.sum_eq_single a.symm]
      · simp [Matrix.submatrix, Matrix.one_apply]
      · intro c _ hc
        have hh : a.symm ≠ c := Ne.symm hc
        simp [Matrix.submatrix, Matrix.one_apply, hh]
      · simp
    have hcast : (Int.castRingHom ℂ).mapMatrix (numerator G) = (3 : ℂ) • grover G := by
      ext a b
      change ((numerator G a b : ℤ) : ℂ) = 3 * grover G a b
      by_cases hc : b.snd = a.fst
      · dsimp only [numerator, grover]
        simp only [if_pos hc]
        rw [hdegree b.snd]
        split_ifs <;> norm_num
      · simp [numerator, grover, hc]
    have hdiag (a : G.Dart) : (numerator G ^ 2) a a = 1 := by
      rw [pow_two, Matrix.mul_apply]
      rw [Finset.sum_eq_single a.symm]
      · norm_num [numerator]
      · intro c _ hc
        by_cases hca : c.snd = a.fst
        · by_cases hac : a.snd = c.fst
          · have he : c = a.symm := SimpleGraph.Dart.ext _ _ (Prod.ext hac.symm hca)
            exact (hc he).elim
          · simp [numerator, hac]
        · simp [numerator, hca]
      · simp
    have hmod : (Int.castRingHom (ZMod 2)).mapMatrix (numerator G ^ 2) = 1 := by
      rw [map_pow, hmodW, hrev]
    have hpow : (numerator G ^ 2) ^ l = (9 : Matrix G.Dart G.Dart ℤ) ^ l := by
      apply Matrix.map_injective (Int.cast_injective (α := ℂ))
      change (Int.castRingHom ℂ).mapMatrix ((numerator G ^ 2) ^ l) =
        (Int.castRingHom ℂ).mapMatrix ((9 : Matrix G.Dart G.Dart ℤ) ^ l)
      simp only [map_pow, map_ofNat]
      rw [← pow_mul, hcast, smul_pow, hret]
      have hnine : (9 : Matrix G.Dart G.Dart ℂ) = (9 : ℂ) • 1 := by
        ext a b
        by_cases hab : a = b <;> simp [Matrix.ofNat_apply, hab]
      rw [hnine, smul_pow, one_pow, pow_mul]
      norm_num
    have heq : numerator G ^ 2 = 9 := by
      let X : Matrix G.Dart G.Dart ℤ := numerator G ^ 2
      let Q : Matrix G.Dart G.Dart ℤ :=
        ∑ i ∈ Finset.range l, X ^ i *
          (9 : Matrix G.Dart G.Dart ℤ) ^ (l - 1 - i)
      let red : Matrix G.Dart G.Dart ℤ →+* Matrix G.Dart G.Dart (ZMod 2) :=
        (Int.castRingHom (ZMod 2)).mapMatrix
      have nine : (9 : Matrix G.Dart G.Dart (ZMod 2)) = 1 := by
        have hn : (9 : ZMod 2) = 1 := by decide
        ext i j
        by_cases hij : i = j <;> simp [Matrix.ofNat_apply, Matrix.one_apply, hij, hn]
      have hodd : (l : ZMod 2) = 1 := by
        obtain ⟨k, hk⟩ := hl
        have ht : (2 : ZMod 2) = 0 := by decide
        rw [hk]
        simp [Nat.cast_add, Nat.cast_mul, ht]
      have hQ : red Q = 1 := by
        have hx : red X = 1 := hmod
        dsimp [Q]
        simp only [map_sum, map_mul, map_pow, map_ofNat, hx, nine, one_pow, one_mul]
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Matrix.sum_apply, hodd]
        · simp [Matrix.sum_apply, hij]
      have hdet : Q.det ≠ 0 := by
        intro hz
        have hd := (Int.castRingHom (ZMod 2)).map_det Q
        change (Q.det : ZMod 2) = (red Q).det at hd
        rw [hz, Int.cast_zero, hQ, Matrix.det_one] at hd
        exact zero_ne_one hd
      have hfac : (X - 9) * Q = 0 := by
        have hc : Commute X (9 : Matrix G.Dart G.Dart ℤ) := (Nat.cast_commute 9 X).symm
        have hxpow : X ^ l = (9 : Matrix G.Dart G.Dart ℤ) ^ l := hpow
        simpa only [Q, hxpow, sub_self] using hc.mul_geom_sum₂ l
      have hz : X - 9 = 0 := by
        have hh := congrArg (fun B : Matrix G.Dart G.Dart ℤ => B * Q.adjugate) hfac
        rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
          Matrix.zero_mul] at hh
        ext i j
        have hi := congrArg (fun B : Matrix G.Dart G.Dart ℤ => B i j) hh
        exact (mul_eq_zero.mp hi).resolve_left hdet
      exact sub_eq_zero.mp hz
    let : Nonempty V := hconn.nonempty
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp (by rw [hdegree v]; norm_num)
    let a : G.Dart := ⟨(v, w), hw⟩
    have hbad := congrArg (fun B : Matrix G.Dart G.Dart ℤ => B a a)
      heq
    rw [hdiag] at hbad
    norm_num [Matrix.ofNat_apply] at hbad
  intro l hl _ V _ _ G _ hconn hdegree hperiod
  exact stronger G hconn hdegree l hl hperiod.2.1


end
end D5.S3.Quantum.Dynamics.CubicGroverTwiceOddPeriod

#print axioms D5.S3.Quantum.Dynamics.CubicGroverTwiceOddPeriod.result
