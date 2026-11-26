/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/SpectralDeterminantReflection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/SpectralDeterminantReflection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Polynomial determinant reflection identifies the finite coefficient certificate. -/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace SpectralDeterminantReflection

/-- Dense coefficients in ascending order. Trailing zeroes are permitted. -/
structure Dense (A : Type) where
  coeffs : List A

namespace Dense

variable {A R : Type}

private def addCoeffs [Add A] : List A → List A → List A
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addCoeffs as bs

private def mulCoeffs [Zero A] [Add A] [Mul A] : List A → List A → List A
  | [], _ => []
  | a :: as, bs => addCoeffs (bs.map (a * ·)) (0 :: mulCoeffs as bs)

instance : Zero (Dense A) := ⟨⟨[]⟩⟩
instance [Add A] : Add (Dense A) := ⟨fun a b => ⟨addCoeffs a.coeffs b.coeffs⟩⟩
instance [Neg A] : Neg (Dense A) := ⟨fun a => ⟨a.coeffs.map Neg.neg⟩⟩
instance [Zero A] [Add A] [Mul A] : Mul (Dense A) :=
  ⟨fun a b => ⟨mulCoeffs a.coeffs b.coeffs⟩⟩

private def horner [Semiring R] (f : A → R) (x : R) : List A → R
  | [] => 0
  | a :: as => f a + x * horner f x as

/-- Evaluate coefficients through `f` and substitute `x` for the variable. -/
def eval [Semiring R] (f : A → R) (x : R) (p : Dense A) : R := horner f x p.coeffs

@[simp] theorem eval_nil [Semiring R] (f : A → R) (x : R) : eval f x ⟨[]⟩ = 0 := rfl

@[simp] theorem eval_cons [Semiring R] (f : A → R) (x : R) (a : A) (as : List A) :
    eval f x ⟨a :: as⟩ = f a + x * eval f x ⟨as⟩ := rfl

@[simp] theorem eval_zero [Semiring R] (f : A → R) (x : R) : eval f x 0 = 0 := rfl

private theorem horner_add [Add A] [Semiring R] (f : A → R) (x : R)
    (hf : ∀ a b, f (a + b) = f a + f b) (as bs : List A) :
    horner f x (addCoeffs as bs) = horner f x as + horner f x bs := by
  induction as generalizing bs with
  | nil => simp [horner, addCoeffs]
  | cons a as ih =>
    cases bs with
    | nil => simp [horner, addCoeffs]
    | cons b bs =>
      simp only [horner, addCoeffs, hf, ih, mul_add]
      ac_rfl

theorem eval_add [Add A] [Semiring R] (f : A → R) (x : R)
    (hf : ∀ a b, f (a + b) = f a + f b) (a b : Dense A) :
    eval f x (a + b) = eval f x a + eval f x b := horner_add f x hf _ _

theorem eval_neg [Neg A] [Ring R] (f : A → R) (x : R)
    (hf : ∀ a, f (-a) = -f a) (a : Dense A) :
    eval f x (-a) = -eval f x a := by
  change horner f x (a.coeffs.map Neg.neg) = -horner f x a.coeffs
  induction a.coeffs with
  | nil => simp [horner]
  | cons a as ih => simp [horner, hf, ih, add_comm]

private theorem horner_scale [Mul A] [CommSemiring R] (f : A → R) (x : R)
    (hf : ∀ a b, f (a * b) = f a * f b) (a : A) (bs : List A) :
    horner f x (bs.map (a * ·)) = f a * horner f x bs := by
  induction bs with
  | nil => simp [horner]
  | cons b bs ih =>
    simp only [List.map_cons, horner, hf, ih]
    ring

theorem eval_mul [Zero A] [Add A] [Mul A] [CommSemiring R] (f : A → R) (x : R)
    (hzero : f 0 = 0) (hadd : ∀ a b, f (a + b) = f a + f b)
    (hmul : ∀ a b, f (a * b) = f a * f b) (a b : Dense A) :
    eval f x (a * b) = eval f x a * eval f x b := by
  change horner f x (mulCoeffs a.coeffs b.coeffs) = horner f x a.coeffs * horner f x b.coeffs
  induction a.coeffs with
  | nil => simp [mulCoeffs, horner]
  | cons a as ih =>
    simp only [mulCoeffs, horner_add f x hadd, horner_scale f x hmul, horner, hzero,
      zero_add, ih]
    ring

def allZero (isZero : A → Bool) (a : Dense A) : Bool := a.coeffs.all isZero

theorem eval_eq_zero_of_allZero [Semiring R] (f : A → R) (x : R) (isZero : A → Bool)
    (sound : ∀ a, isZero a = true → f a = 0) (a : Dense A)
    (h : a.allZero isZero = true) : eval f x a = 0 := by
  obtain ⟨cs⟩ := a
  change horner f x cs = 0
  change cs.all isZero = true at h
  induction cs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [horner, sound a h.1, ih h.2]

theorem map_eval {S : Type} [Semiring R] [Semiring S] (g : R →+* S)
    (f : A → R) (x : R) (a : Dense A) :
    g (eval f x a) = eval (fun c => g (f c)) (g x) a := by
  obtain ⟨as⟩ := a
  induction as with
  | nil => simp only [eval_nil, map_zero]
  | cons a as ih => simp [ih]

end Dense

/-- The outer list holds powers of `q` and the inner lists hold powers of `m`. -/
abbrev Bi := Dense (Dense ℤ)

def bi (coeffs : List (List ℤ)) : Bi := ⟨coeffs.map Dense.mk⟩

def value {R : Type} [CommRing R] (m q : R) (a : Bi) : R :=
  Dense.eval (Dense.eval (fun c : ℤ => (c : R)) m) q a

theorem map_value {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m q : R) (a : Bi) :
    f (value m q a) = value (f m) (f q) a := by
  simp only [value, Dense.map_eval, map_intCast]

theorem value_add {R : Type} [CommRing R] (m q : R) (a b : Bi) :
    value m q (a + b) = value m q a + value m q b :=
  Dense.eval_add _ _ (Dense.eval_add _ _ Int.cast_add) _ _

theorem value_neg {R : Type} [CommRing R] (m q : R) (a : Bi) :
    value m q (-a) = -value m q a :=
  Dense.eval_neg _ _ (Dense.eval_neg _ _ Int.cast_neg) _

theorem value_mul {R : Type} [CommRing R] (m q : R) (a b : Bi) :
    value m q (a * b) = value m q a * value m q b :=
  Dense.eval_mul _ _ rfl (Dense.eval_add _ _ Int.cast_add)
    (Dense.eval_mul _ _ Int.cast_zero Int.cast_add Int.cast_mul) _ _

/-- Check the dense coefficients of the difference, allowing trailing zeroes. -/
def equal (a b : Bi) : Bool :=
  (a + -b).allZero (Dense.allZero fun c : ℤ => decide (c = 0))

theorem value_eq {R : Type} [CommRing R] (m q : R) {a b : Bi}
    (h : equal a b = true) : value m q a = value m q b := by
  have hz := Dense.eval_eq_zero_of_allZero (Dense.eval (fun c : ℤ => (c : R)) m) q _
    (Dense.eval_eq_zero_of_allZero _ _ _ (fun c hc => by rw [of_decide_eq_true hc, Int.cast_zero]))
    (a + -b) h
  change value m q (a + -b) = 0 at hz
  rwa [value_add, value_neg, ← sub_eq_add_neg, sub_eq_zero] at hz

abbrev IP := Polynomial (Polynomial ℤ)

noncomputable def asPolynomial (a : Bi) : IP := value (Polynomial.C Polynomial.X) Polynomial.X a

open Polynomial in
noncomputable def specialize {R : Type} [CommRing R] (f : ℤ →+* R) (m q : R) : IP →+* R :=
  eval₂RingHom (eval₂RingHom f m) q

open Polynomial in
theorem specialize_asPolynomial {R : Type} [CommRing R] (f : ℤ →+* R) (m q : R) (a : Bi) :
    specialize f m q (asPolynomial a) = value m q a := by
  rw [asPolynomial, map_value]
  simp [specialize, eval₂_X]

section Determinant
open Matrix

variable {R : Type} [CommRing R]

/-- The fraction-free elimination numerator below and to the right of the first pivot. -/
def cross {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => M 0 0 * M i.succ j.succ - M i.succ 0 * M 0 j.succ

private theorem det_mul_pivot {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    M 0 0 ^ n * M.det = M 0 0 * (cross M).det := by
  let d : Fin (n + 1) → R := Fin.cases 1 fun _ => M 0 0
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    diagonal d
  let V : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun i j => if j = 0 ∧ i ≠ 0 then M i 0 else 0
  let E := D - V
  have hdiag (i) : E i i = d i := by
    change (D - V) i i = d i
    rw [Matrix.sub_apply]
    by_cases hi : i = 0 <;> simp [D, V, hi]
  have hE : E.det = M 0 0 ^ n := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp only [hdiag, d, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ, one_mul,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · intro i j hij
      change i < j at hij
      have hj : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
      change (D - V) i j = 0
      rw [Matrix.sub_apply]
      simp [D, V, ne_of_lt hij, hj]
  have hmul (i j : Fin (n + 1)) :
      (E * M) i j = d i * M i j -
        if i = 0 then 0 else M i 0 * M 0 j := by
    rw [show E * M = D * M - V * M by simp only [E, sub_mul]]
    rw [Matrix.sub_apply, show (D * M) i j = _ by
      simpa only [D] using Matrix.diagonal_mul d M i j]
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    by_cases hi : i = 0 <;> simp [V, hi]
  have hcol (i : Fin n) : (E * M) i.succ 0 = 0 := by
    rw [hmul]
    simp [d, mul_comm]
  have hsub : (E * M).submatrix Fin.succ Fin.succ = cross M := by
    apply Matrix.ext
    intro i j
    simp [hmul, d, cross]
  calc
    M 0 0 ^ n * M.det = (E * M).det := by rw [Matrix.det_mul, hE]
    _ = M 0 0 * (cross M).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      simp [hmul, d, hsub]

/-- Each Bareiss step supplies a polynomial identity for the scaled trailing matrix. -/
theorem det_step {n : ℕ} [IsDomain R] (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (previous result : R)
    (hp : M 0 0 ≠ 0) (hcross : previous • B = cross M)
    (hB : B.det = M 0 0 ^ n * result) :
    M.det = previous ^ (n + 1) * result := by
  have h := det_mul_pivot M
  rw [← hcross, Matrix.det_smul, Fintype.card_fin, hB] at h
  apply mul_left_cancel₀ (pow_ne_zero (n + 1) hp)
  calc
    M 0 0 ^ (n + 1) * M.det = M 0 0 * (previous ^ (n + 1) * (M 0 0 ^ n * result)) := h
    _ = M 0 0 ^ (n + 1) * (previous ^ (n + 1) * result) := by rw [pow_succ]; ring

end Determinant

open Matrix

/-- Check each entry of the scaled trailing matrix by exact integer coefficient arithmetic. -/
def crossCheck {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Bi)
    (B : Matrix (Fin n) (Fin n) Bi) (previous : Bi) (i j : Fin n) : Bool :=
  equal (previous * B i j) (A 0 0 * A i.succ j.succ + -(A i.succ 0 * A 0 j.succ))

theorem crossCheck_sound {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Bi)
    (B : Matrix (Fin n) (Fin n) Bi) (previous : Bi)
    (check : ∀ i j, crossCheck A B previous i j = true) :
    asPolynomial previous • B.map asPolynomial = cross (A.map asPolynomial) := by
  apply Matrix.ext
  intro i j
  have h := value_eq (Polynomial.C Polynomial.X : IP) Polynomial.X (check i j)
  simpa only [Matrix.smul_apply, Matrix.map_apply, cross, asPolynomial, smul_eq_mul,
    value_mul, value_add, value_neg, sub_eq_add_neg] using h

theorem pivot_ne_zero (a : Bi) (h : value (R := ℤ) 2 1 a ≠ 0) : asPolynomial a ≠ 0 := by
  intro hz
  apply h
  rw [← specialize_asPolynomial (RingHom.id ℤ), hz, map_zero]

end SpectralDeterminantReflection
