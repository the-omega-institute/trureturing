/- GID: D5/S3/Observer/Dynamics/ToralReturnPrimeTwoCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/ToralReturnPrimeTwoCriterion
   mirror-E: none(waiver:explicit-inverses-at-all-moduli)
   anchors: []
   utility: none
   digest: Every intertwiner has a quadratic norm determinant and the actual reduced matrices are conjugate exactly at odd moduli. -/

import D5.S3.Observer.Dynamics.ToralReturnModuleStructure
import Mathlib.Algebra.Ring.Parity

/-!
The original integer companion and balanced matrices are transported by the
canonical integer ring homomorphism. Conjugacy is stated by actual two-sided
inverse matrices and an intertwining equation, not by an assumed equivalence.
The modulus is arbitrary, including 0 (integer coefficients) and 1 (the zero
ring). The parameter k is arbitrary, including 0.

The normal form works over every commutative ring and needs no division by 2.
Its determinant is twice a Pell-type quadratic norm. Over ZMod m the odd case
constructs an explicit inverse to 2, whereas every even modulus maps to ZMod 2
and obstructs invertibility. This closes the concrete local-detection question
left by ToralReturnModuleStructure; it is not a general profinite-rigidity or
mapping-class congruence-subgroup theorem.

Source search: reuse the two preceding actual-return owners; pinned mathlib
ZMod.castHom, ZMod.natCast_self, Nat.odd_iff and determinant multiplicativity.
Classical context: Bakker--Rodrigues, arXiv:2207.00922.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped Matrix

namespace D5.S3.Observer.Dynamics.ToralReturnPrimeTwoCriterion

open D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum

/-- Canonical coefficient transport of the original integer matrix. -/
def castMatrix (A : BinaryMatrix) (R : Type*) [CommRing R] :
    Matrix (Fin 2) (Fin 2) R := A.map (Int.castRingHom R)

/-- A division-free normal form, parametrized by the top row. -/
def normalForm {R : Type*} [CommRing R] (k a b : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![a, b; 2 * k * ((k + 1) * b - a), 2 * (a - k * b)]

private theorem cast_companion (k : ℕ) (R : Type*) [CommRing R] :
    castMatrix (companion k) R =
      !![4 * (k : R) + 1, 1; 4 * (k : R), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [castMatrix, companion]

private theorem cast_balanced (k : ℕ) (R : Type*) [CommRing R] :
    castMatrix (balanced k) R =
      !![2 * (k : R) + 1, 2; 2 * (k : R) * ((k : R) + 1), 2 * (k : R) + 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [castMatrix, balanced]

private theorem normalForm_intertwines {R : Type*} [CommRing R]
    (k : ℕ) (a b : R) :
    castMatrix (companion k) R * normalForm (k : R) a b =
      normalForm (k : R) a b * castMatrix (balanced k) R := by
  rw [cast_companion, cast_balanced]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalForm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Complete parametrization of all intertwiners over an arbitrary commutative
ring. It includes characteristic two and therefore can be reduced modulo 2. -/
theorem intertwiner_normal_form {R : Type*} [CommRing R]
    (k : ℕ) (U : Matrix (Fin 2) (Fin 2) R) :
    castMatrix (companion k) R * U = U * castMatrix (balanced k) R ↔
      U = normalForm (k : R) (U 0 0) (U 0 1) := by
  constructor
  · intro h
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h
    rw [cast_companion, cast_balanced] at h0 h1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
    have hc : U 1 0 = 2 * (k : R) * (((k : R) + 1) * U 0 1 - U 0 0) := by
      linear_combination h0
    have hd : U 1 1 = 2 * (U 0 0 - (k : R) * U 0 1) := by
      linear_combination h1
    ext i j
    fin_cases i <;> fin_cases j
    · simp [normalForm]
    · simp [normalForm]
    · simpa [normalForm] using hc
    · simpa [normalForm] using hd
  · intro hU
    calc
      castMatrix (companion k) R * U =
          castMatrix (companion k) R * normalForm (k : R) (U 0 0) (U 0 1) := by rw [← hU]
      _ = normalForm (k : R) (U 0 0) (U 0 1) * castMatrix (balanced k) R :=
        normalForm_intertwines k (U 0 0) (U 0 1)
      _ = U * castMatrix (balanced k) R := by rw [← hU]

/-- The determinant of every actual intertwiner is twice the explicit
quadratic norm. In the integer ring this records the exact index obstruction. -/
theorem intertwiner_quadratic_norm {R : Type*} [CommRing R]
    (k : ℕ) (U : Matrix (Fin 2) (Fin 2) R)
    (h : castMatrix (companion k) R * U = U * castMatrix (balanced k) R) :
    U.det = 2 * ((U 0 0) ^ 2 - (k : R) * ((k : R) + 1) * (U 0 1) ^ 2) := by
  calc
    U.det = (normalForm (k : R) (U 0 0) (U 0 1)).det :=
      congrArg Matrix.det ((intertwiner_normal_form k U).mp h)
    _ = _ := by simp [normalForm, Matrix.det_fin_two] <;> ring

/-- Actual invertible linear conjugacy on the original matrices reduced modulo m. -/
def ModularConjugacy (k m : ℕ) : Prop :=
  ∃ P Q : Matrix (Fin 2) (Fin 2) (ZMod m),
    P * Q = 1 ∧ Q * P = 1 ∧
      castMatrix (companion k) (ZMod m) * P =
        P * castMatrix (balanced k) (ZMod m)

private theorem no_conjugacy_at_even_modulus (k m : ℕ) (hm : 2 ∣ m) :
    ¬ ModularConjugacy k m := by
  rintro ⟨P, Q, hPQ, _hQP, hP⟩
  have hd : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  rw [intertwiner_quadratic_norm k P hP] at hd
  let reduction : ZMod m →+* ZMod 2 := ZMod.castHom hm (ZMod 2)
  have hbad := congrArg reduction hd
  norm_num [map_mul] at hbad

private theorem conjugacy_from_half (k m : ℕ) (u : ZMod m)
    (hu : (2 : ZMod m) * u = 1) : ModularConjugacy k m := by
  let P : Matrix (Fin 2) (Fin 2) (ZMod m) :=
    !![1, 0; -2 * (k : ZMod m), 2]
  let Q : Matrix (Fin 2) (Fin 2) (ZMod m) :=
    !![1, 0; (k : ZMod m), u]
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two, hu] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two]
    · change (Q * P) 1 0 = 0
      simp only [Q, P, Matrix.mul_apply, Fin.sum_univ_two]
      change (k : ZMod m) * 1 + u * (-2 * (k : ZMod m)) = 0
      calc
        _ = (1 - 2 * u) * (k : ZMod m) := by ring
        _ = 0 := by rw [hu]; ring
    · change (Q * P) 1 1 = 1
      simpa [P, Q, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using hu
  · rw [cast_companion, cast_balanced]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A sharp all-modulus criterion. Every odd modulus admits an explicit inverse
intertwiner; every even modulus fails already after the map to ZMod 2. -/
theorem modular_conjugacy_iff_odd (k m : ℕ) :
    ModularConjugacy k m ↔ Odd m := by
  constructor
  · intro h
    apply Nat.odd_iff.mpr
    by_contra hm
    have heven : 2 ∣ m := by omega
    exact no_conjugacy_at_even_modulus k m heven h
  · intro hm
    obtain ⟨r, hr⟩ := hm
    have htime : m = 2 * r + 1 := by omega
    have hzero : (2 : ZMod m) * (r : ZMod m) + 1 = 0 := by
      have hcast : (m : ZMod m) = ((2 * r + 1 : ℕ) : ZMod m) :=
        congrArg (fun t : ℕ => (t : ZMod m)) htime
      have hself := hcast.symm.trans (ZMod.natCast_self m)
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hself
    apply conjugacy_from_half k m (-(r : ZMod m))
    linear_combination -hzero

#print axioms intertwiner_normal_form
#print axioms intertwiner_quadratic_norm
#print axioms modular_conjugacy_iff_odd

end D5.S3.Observer.Dynamics.ToralReturnPrimeTwoCriterion
