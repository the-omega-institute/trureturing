/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreNormalizedJet
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreNormalizedJet
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreHigherJet, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetElimination]
   utility: none
   digest: Exact trace normalization preserves the opposite branch's first nonzero difference in the forbidden population at degree four. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreHigherJet
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetElimination

/-!
# Exact trace normalization for the hard-core transfer jet
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreNormalizedJet

open PeriodicMPSUniformHardCoreJetElimination
open PeriodicMPSUniformHardCoreQuarticSign
open PeriodicMPSUniformHardCoreTransferRecurrence
open PeriodicMPSUniformHardCoreHigherJet
open PeriodicMPSUniformHardCoreFirstJet
  (entry rawJet chartJet rawJet_coeff_zero rawJet_coeff_one baseWeights firstWeights
    polyWeight direction)
open Polynomial
open scoped Matrix Kronecker

noncomputable section

/-- The Fibonacci ratio used to divide the raw coefficients by a common factor. -/
def ratio (n : ℕ) : ℝ := F n / G n

/-- The full thirteen-slot input to the certified raw jet, in its original order. -/
def parameters (n : ℕ) (x : Path) : Parameters :=
  ![x.t, (3 - 2 * ratio n)*x.t, x.a₂, x.b₂, x.c₂, x.d₂, x.b₃, x.c₃, x.d₃,
    x.a₄, x.b₄, x.c₄, x.d₄]

def numerator (n : ℕ) (x : Path) (row : Fin 8) : Polynomial ℂ :=
  pathRaw (parameters n x) row n

private theorem map_raw {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) R) (p q : TwoBits) (m : ℕ) :
    f (binaryInsertion A B p q * binaryTransfer A B ^ m).trace =
      (binaryInsertion (fun i => f.mapMatrix (A i)) (fun i => f.mapMatrix (B i)) p q *
        binaryTransfer (fun i => f.mapMatrix (A i)) (fun i => f.mapMatrix (B i)) ^ m).trace := by
  change (f : R →+ S) (Matrix.trace _) = _
  rw [AddMonoidHom.map_trace (f : R →+ S)]
  have hk (U V : Matrix (Fin 2) (Fin 2) R) :
      f.mapMatrix (U ⊗ₖ V) = f.mapMatrix U ⊗ₖ f.mapMatrix V :=
    Matrix.ext fun i j => f.map_mul _ _
  change (f.mapMatrix (_ * _ ^ m)).trace = _
  simp only [map_mul, map_pow, binaryInsertion, binaryTransfer, map_add, hk]

private def coeffJet : Polynomial ℂ →+* TrivSqZeroExt ℂ ℂ where
  toFun p := (p.coeff 0, p.coeff 1)
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_one' := TrivSqZeroExt.ext (by simp) (by simp [Polynomial.coeff_one])
  map_add' p q := TrivSqZeroExt.ext (Polynomial.coeff_add _ _ _) (Polynomial.coeff_add _ _ _)
  map_mul' p q := TrivSqZeroExt.ext (Polynomial.mul_coeff_zero _ _) (Polynomial.mul_coeff_one _ _)

private theorem pathRaw_firstTwo (y : Parameters) (row : Fin 8) (n : ℕ) :
    coeffJet (pathRaw y row n) =
      coeffJet (rawJet (Complex.I * (y 0 : ℂ)) (Complex.I * (y 1 : ℂ)) Complex.I 0 row n) := by
  let A := pathChart y
  let B := chartJet (Complex.I * (y 0 : ℂ)) (Complex.I * (y 1 : ℂ)) Complex.I 0
  have hcoef (i : Fin 2) (j k : Fin 2) :
      (A i j k).coeff 0 = (B i j k).coeff 0 ∧
      (A i j k).coeff 1 = (B i j k).coeff 1 := by
    have h0 (a : Fin 4) := coeff_pathCoordinate y a 0
    have h1 (a : Fin 4) := coeff_pathCoordinate y a 1
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul] at h0 h1
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [A, B, pathChart, chartJet, hardCoreChart, h0, h1, pathTerms, coeff_one]
  have he (i : Fin 2) : coeffJet.mapMatrix (A i) = coeffJet.mapMatrix (B i) :=
    Matrix.ext fun j k => TrivSqZeroExt.ext (hcoef i j k).1 (hcoef i j k).2
  have he' (i : Fin 2) : coeffJet.mapMatrix (conjugateJet A i) =
      coeffJet.mapMatrix (conjugateJet B i) := by
    apply Matrix.ext
    intro j k
    apply TrivSqZeroExt.ext
    · change ((A i j k).map (starRingEnd ℂ)).coeff 0 =
        ((B i j k).map (starRingEnd ℂ)).coeff 0
      simpa only [conjugateJet, RingHom.mapMatrix_apply, Matrix.map_apply, coeff_map, coeffJet,
        RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_mk] using
        congrArg (starRingEnd ℂ) (hcoef i j k).1
    · change ((A i j k).map (starRingEnd ℂ)).coeff 1 =
        ((B i j k).map (starRingEnd ℂ)).coeff 1
      simpa only [conjugateJet, RingHom.mapMatrix_apply, Matrix.map_apply, coeff_map, coeffJet,
        RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_mk] using
        congrArg (starRingEnd ℂ) (hcoef i j k).2
  change coeffJet (binaryRawTransfer A (entry row).1 (entry row).2 n) =
    coeffJet (binaryRawTransfer B (entry row).1 (entry row).2 n)
  simp only [binaryRawTransfer, map_raw, he, he']

/-- Cyclicity makes the two single-excitation diagonal entries coincide. -/
private theorem numerator_diag_swap (n : ℕ) (x : Path) :
    numerator n x 7 = numerator n x 1 := by
  let A := pathChart (parameters n x)
  let B := conjugateJet A
  let U := A 0 ⊗ₖ B 0
  let V := A 1 ⊗ₖ B 1
  have hc : Commute (U + V) ((U + V) ^ (n-2)) :=
    (Commute.refl _).pow_right _
  have ht : Matrix.trace (((U+V)*U) * (U+V)^(n-2)) =
      Matrix.trace ((U*(U+V)) * (U+V)^(n-2)) := by
    rw [Matrix.trace_mul_cycle (U+V) U _, ← hc.eq, Matrix.mul_assoc U]
    exact Matrix.trace_mul_comm _ _
  rw [add_mul, mul_add, add_mul, add_mul, Matrix.trace_add, Matrix.trace_add] at ht
  change Matrix.trace (binaryInsertion A B (1,0) (1,0) * (U+V)^(n-2)) =
    Matrix.trace (binaryInsertion A B (0,1) (0,1) * (U+V)^(n-2))
  simp only [binaryInsertion, Matrix.mul_kronecker_mul]
  exact add_left_cancel ht

/-- Trace of the raw two-site matrix along the jet. -/
def mass (n : ℕ) (x : Path) : Polynomial ℂ :=
  numerator n x 0 + numerator n x 1 + numerator n x 7 + numerator n x 6

private theorem mass_eq_three (n : ℕ) (x : Path) :
    mass n x = numerator n x 0 + 2 * numerator n x 1 + numerator n x 6 := by
  rw [mass, numerator_diag_swap]
  ring

/-- Row component as a sequence of real Taylor coefficients. -/
def rawCoeff (imag : Bool) (n : ℕ) (x : Path) (row : Fin 8) (r : ℕ) : ℝ :=
  let c := (numerator n x row).coeff r
  if imag then c.im else c.re

def massCoeff (n : ℕ) (x : Path) (r : ℕ) : ℝ :=
  ((mass n x).coeff r).re

/-- Formal division by the real trace. The index is the Taylor order. -/
def normalizedCoeff (imag : Bool) (n : ℕ) (x : Path) (row : Fin 8) : ℕ → ℝ
  | r => (rawCoeff imag n x row r -
      ∑ k : Fin r, massCoeff n x (r - k.val) * normalizedCoeff imag n x row k.val) /
        massCoeff n x 0
termination_by r => r
decreasing_by exact k.isLt

private def coefficientWeight (specialize : Sparse → ℂ) (second : Bool) :
    List (Sparse × Sparse) → Polynomial ℂ
  | [] => 0
  | (p, q) :: rest =>
    C (specialize (if second then q else p)) + X * coefficientWeight specialize second rest

private theorem pathWeight_eq (y : Parameters) (r : Fin 5) (row : Fin 7) (second : Bool) :
    pathWeight y r.val row.val second =
      coefficientWeight (fun p => (Complex.I ^ r.val / (denominator r.val : ℂ)) *
        (Sparse.value y p : ℂ)) second (weights r.val row.val) := by
  fin_cases r <;> fin_cases row <;> rfl

def realWeight (y : Parameters) (n : ℝ) (second : Bool) :
    List (Sparse × Sparse) → ℝ
  | [] => 0
  | (p, q) :: rest =>
    Sparse.value y (if second then q else p) + n * realWeight y n second rest

private theorem eval_coefficientWeight (y : Parameters) (a : ℂ) (n : ℝ) (second : Bool)
    (ws : List (Sparse × Sparse)) :
    (coefficientWeight (fun p => a * (Sparse.value y p : ℂ)) second ws).eval (n : ℂ) =
      a * (realWeight y n second ws : ℂ) := by
  induction ws with
  | nil => simp [coefficientWeight, realWeight]
  | cons hd tl ih =>
    rcases hd with ⟨p, q⟩
    simp only [coefficientWeight, realWeight, eval_add, eval_C, eval_mul, eval_X, ih,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring

def weightValue (n : ℕ) (x : Path) (r row : ℕ) : ℝ :=
  let y := parameters n x
  let ws := weights r row
  (ratio n * realWeight y n false ws + realWeight y n true ws) / (denominator r : ℝ)

theorem F_eq_ratio_mul (n : ℕ) (hn : 7 ≤ n) : F n = ratio n * G n := by
  unfold ratio
  field_simp [(G_pos hn).ne']

private theorem numerator_higher (n : ℕ) (hn : 7 ≤ n) (x : Path)
    (r : Fin 5) (hr : 2 ≤ r.val) (row : Fin 7) :
    (numerator n x row.castSucc).coeff r.val =
      Complex.I ^ r.val * ((G n * weightValue n x r.val row.val : ℝ) : ℂ) := by
  rw [numerator, pathRaw_coeff_eq _ r hr row n hn, fibonacciCandidate,
    pathWeight_eq, pathWeight_eq, ← Complex.ofReal_natCast, eval_coefficientWeight,
    eval_coefficientWeight]
  have hF : (Nat.fib n : ℂ) = ((ratio n * G n : ℝ) : ℂ) := by
    rw [← F_eq_ratio_mul n hn]
    simp [F]
  have hG : (Nat.fib (n-1) : ℂ) = (G n : ℂ) := by simp [G]
  rw [hF, hG]
  push_cast [weightValue, div_eq_mul_inv]
  ring

private theorem numerator_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    (numerator n x row).coeff 0 =
      ((![F n, G n, F n-G n, G n, 0, 0, 0, G n] : Fin 8 → ℝ) row : ℂ) := by
  unfold numerator
  rw [show (pathRaw (parameters n x) row n).coeff 0 = _ from
    congrArg TrivSqZeroExt.fst (pathRaw_firstTwo (parameters n x) row n)]
  change (rawJet ..).coeff 0 = _
  rw [rawJet_coeff_zero _ _ _ _ _ _ hn]
  fin_cases row <;> simp [fibonacciCandidate, baseWeights, F, G, sub_eq_add_neg]

private theorem polyWeight_eq (y : Fin 8 → ℂ) (row : Fin 8) (i j : Fin 4) :
    polyWeight y row i j =
      C ((∑ k, (firstWeights row i k : ℂ) * y k) / 5) +
        C ((∑ k, (firstWeights row j k : ℂ) * y k) / 5) * X := rfl

private theorem numerator_first (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    (numerator n x row).coeff 1 = Complex.I *
      ((![0, 0, 0, G n-F n, 3*G n-F n, G n, 0, 0] : Fin 8 → ℝ) row : ℂ) := by
  unfold numerator
  rw [show (pathRaw (parameters n x) row n).coeff 1 = _ from
    congrArg TrivSqZeroExt.snd (pathRaw_firstTwo (parameters n x) row n)]
  change (rawJet ..).coeff 1 = _
  rw [rawJet_coeff_one _ _ _ _ _ _ hn, polyWeight_eq, polyWeight_eq]
  have hFG := F_eq_ratio_mul n hn
  fin_cases row <;> apply Complex.ext <;>
    simp [fibonacciCandidate, direction, Fin.sum_univ_succ, firstWeights, parameters,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im,
      ← show (Nat.fib n : ℝ) = F n from rfl, ← show (Nat.fib (n-1) : ℝ) = G n from rfl] <;>
    try ring
  all_goals
    change x.t * ratio n * G n * 2 - x.t * F n * 2 - F n + G n = -F n + G n
    rw [hFG]
    ring

@[local simp] private theorem monomial_2 (y : Parameters) :
    Sparse.monomialValue y 2 = y 0 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_3 (y : Parameters) :
    Sparse.monomialValue y 3 = y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_4 (y : Parameters) :
    Sparse.monomialValue y 4 = y 0 * y 0 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_5 (y : Parameters) :
    Sparse.monomialValue y 5 = y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 2) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_6 (y : Parameters) :
    Sparse.monomialValue y 6 = y 0 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_7 (y : Parameters) :
    Sparse.monomialValue y 7 = y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 3) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_8 (y : Parameters) :
    Sparse.monomialValue y 8 = y 0 * y 0 * y 0 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 0) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_9 (y : Parameters) :
    Sparse.monomialValue y 9 = y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_10 (y : Parameters) :
    Sparse.monomialValue y 10 = y 0 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 2) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_11 (y : Parameters) :
    Sparse.monomialValue y 11 = y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 4) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_12 (y : Parameters) :
    Sparse.monomialValue y 12 = y 0 * y 0 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 0 * primeCode 1) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_13 (y : Parameters) :
    Sparse.monomialValue y 13 = y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 5) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_14 (y : Parameters) :
    Sparse.monomialValue y 14 = y 0 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 3) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_15 (y : Parameters) :
    Sparse.monomialValue y 15 = y 1 * y 2 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 2) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_17 (y : Parameters) :
    Sparse.monomialValue y 17 = y 6 := by
  calc
    _ = Sparse.monomialValue y (primeCode 6) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_18 (y : Parameters) :
    Sparse.monomialValue y 18 = y 0 * y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 1 * primeCode 1) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_19 (y : Parameters) :
    Sparse.monomialValue y 19 = y 7 := by
  calc
    _ = Sparse.monomialValue y (primeCode 7) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_21 (y : Parameters) :
    Sparse.monomialValue y 21 = y 1 * y 3 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 3) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_22 (y : Parameters) :
    Sparse.monomialValue y 22 = y 0 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 4) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_23 (y : Parameters) :
    Sparse.monomialValue y 23 = y 8 := by
  calc
    _ = Sparse.monomialValue y (primeCode 8) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_26 (y : Parameters) :
    Sparse.monomialValue y 26 = y 0 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 0 * primeCode 5) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_27 (y : Parameters) :
    Sparse.monomialValue y 27 = y 1 * y 1 * y 1 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 1 * primeCode 1) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_33 (y : Parameters) :
    Sparse.monomialValue y 33 = y 1 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 4) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_39 (y : Parameters) :
    Sparse.monomialValue y 39 = y 1 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 1 * primeCode 5) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_121 (y : Parameters) :
    Sparse.monomialValue y 121 = y 4 * y 4 := by
  calc
    _ = Sparse.monomialValue y (primeCode 4 * primeCode 4) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_143 (y : Parameters) :
    Sparse.monomialValue y 143 = y 4 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 4 * primeCode 5) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

@[local simp] private theorem monomial_169 (y : Parameters) :
    Sparse.monomialValue y 169 = y 5 * y 5 := by
  calc
    _ = Sparse.monomialValue y (primeCode 5 * primeCode 5) :=
      congrArg (Sparse.monomialValue y) (by decide)
    _ = _ := by simp only [Sparse.monomialValue_mul, Sparse.monomialValue_primeCode]

private theorem mass_weight_two (n : ℕ) (x : Path) :
    -(weightValue n x 2 0 + 2 * weightValue n x 2 1 + weightValue n x 2 6) =
      mass₂ n (ratio n) x := by
  norm_num [weightValue, weights, realWeight, Sparse.value, denominator, parameters, mass₂]
  ring

private theorem raw_weight_two (n : ℕ) (x : Path) :
    -weightValue n x 2 1 = p₂ n (ratio n) x ∧
    -weightValue n x 2 2 = q₂ n (ratio n) x ∧
    -weightValue n x 2 3 = h₂ n (ratio n) x ∧
    -weightValue n x 2 4 = w₂ (ratio n) x ∧
    -weightValue n x 2 5 = v₂ (ratio n) x ∧
    -weightValue n x 2 6 = 3 - ratio n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [weightValue, weights, realWeight, Sparse.value, denominator, parameters,
      p₂, q₂, h₂, w₂, v₂] <;> ring

private theorem raw_weight_w_three (n : ℕ) (x : Path) :
    -weightValue n x 3 4 = w₃ n (ratio n) x := by
  norm_num [weightValue, weights, realWeight, Sparse.value, denominator, parameters, w₃]
  ring

private theorem raw_weight_j_four (n : ℕ) (x : Path) :
    weightValue n x 4 6 = j₄ n (ratio n) x := by
  norm_num [weightValue, weights, realWeight, Sparse.value, denominator, parameters, j₄]
  ring

theorem raw_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    rawCoeff false n x row 0 =
      (![F n, G n, F n-G n, G n, 0, 0, 0, G n] : Fin 8 → ℝ) row ∧
    rawCoeff true n x row 0 = 0 := by
  simp [rawCoeff, numerator_zero n hn]

theorem raw_first (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    rawCoeff false n x row 1 = 0 ∧
    rawCoeff true n x row 1 =
      (![0, 0, 0, G n-F n, 3*G n-F n, G n, 0, 0] : Fin 8 → ℝ) row := by
  simp [rawCoeff, numerator_first n hn, Complex.mul_re, Complex.mul_im]

theorem raw_two (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) (hr : row.val < 7 := by decide) :
    rawCoeff false n x row 2 = G n * -weightValue n x 2 row.val ∧
    rawCoeff true n x row 2 = 0 := by
  let rr : Fin 7 := ⟨row.val, hr⟩
  have hh := numerator_higher n hn x 2 (by decide) rr
  change (numerator n x row).coeff 2 = Complex.I ^ 2 *
    ((G n * weightValue n x 2 row.val : ℝ) : ℂ) at hh
  simp [rawCoeff, hh, Complex.I_sq, Complex.mul_re, Complex.mul_im]

theorem raw_three (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) (hr : row.val < 7 := by decide) :
    rawCoeff false n x row 3 = 0 ∧
    rawCoeff true n x row 3 = G n * -weightValue n x 3 row.val := by
  let rr : Fin 7 := ⟨row.val, hr⟩
  have hh := numerator_higher n hn x 3 (by decide) rr
  change (numerator n x row).coeff 3 = Complex.I ^ 3 *
    ((G n * weightValue n x 3 row.val : ℝ) : ℂ) at hh
  simp [rawCoeff, hh, Complex.mul_re, Complex.mul_im]

theorem raw_four (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) (hr : row.val < 7 := by decide) :
    rawCoeff false n x row 4 = G n * weightValue n x 4 row.val ∧
    rawCoeff true n x row 4 = 0 := by
  let rr : Fin 7 := ⟨row.val, hr⟩
  have hh := numerator_higher n hn x 4 (by decide) rr
  change (numerator n x row).coeff 4 = Complex.I ^ 4 *
    ((G n * weightValue n x 4 row.val : ℝ) : ℂ) at hh
  simp [rawCoeff, hh]

theorem mass_component (n : ℕ) (x : Path) (r : ℕ) :
    massCoeff n x r = rawCoeff false n x 0 r + 2*rawCoeff false n x 1 r +
      rawCoeff false n x 6 r := by
  rw [massCoeff, mass_eq_three]
  rw [show (2 : ℂ[X]) = 1 + 1 by norm_num, add_mul, one_mul]
  simp only [rawCoeff, Bool.false_eq_true, ite_false, coeff_add, Complex.add_re]
  ring

theorem mass_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    massCoeff n x 0 = G n * (ratio n + 2) := by
  rw [mass_component, (raw_zero n hn x 0).1, (raw_zero n hn x 1).1,
    (raw_zero n hn x 6).1]
  simp
  rw [F_eq_ratio_mul n hn]
  ring

theorem mass_one (n : ℕ) (hn : 7 ≤ n) (x : Path) : massCoeff n x 1 = 0 := by
  simp [mass_component, (raw_first n hn x _).1]

theorem mass_two (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    massCoeff n x 2 = G n * mass₂ n (ratio n) x := by
  rw [mass_component, (raw_two n hn x 0).1, (raw_two n hn x 1).1,
    (raw_two n hn x 6).1, ← mass_weight_two]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  ring

theorem mass_three (n : ℕ) (hn : 7 ≤ n) (x : Path) : massCoeff n x 3 = 0 := by
  rw [mass_component, (raw_three n hn x 0).1, (raw_three n hn x 1).1,
    (raw_three n hn x 6).1]
  ring

theorem ratio_add_two (n : ℕ) (hn : 7 ≤ n) : ratio n + 2 = Z n / G n := by
  unfold ratio Z
  field_simp [(G_pos hn).ne']

private theorem ratio_ne_one (n : ℕ) (hn : 7 ≤ n) : ratio n ≠ 1 := by
  have h := (fib_bounds hn).1
  have hg := G_pos hn
  intro he
  have he' := F_eq_ratio_mul n hn
  rw [he, one_mul] at he'
  linarith

private theorem ratio_ne_two (n : ℕ) (hn : 7 ≤ n) : ratio n ≠ 2 := by
  have h := (denominator_factors hn).1
  intro he
  have he' := F_eq_ratio_mul n hn
  rw [he] at he'
  linarith

theorem ratio_add_two_ne_zero (n : ℕ) (hn : 7 ≤ n) : ratio n + 2 ≠ 0 := by
  rw [ratio_add_two n hn]
  exact div_ne_zero (denominator_factors hn).2.1.ne' (G_pos hn).ne'

private theorem foldA_ratio (n : ℕ) (hn : 7 ≤ n) :
    foldA (ratio n) * G n ^ 2 = A n := by
  unfold foldA ratio A
  field_simp [(G_pos hn).ne']

private theorem determinantFactor_ratio (n : ℕ) (hn : 7 ≤ n) :
    determinantFactor n (ratio n) * G n ^ 3 = D n := by
  unfold determinantFactor deltaRatio ratio D delta Z
  field_simp [(G_pos hn).ne']

private theorem foldA_ratio_ne_zero (n : ℕ) (hn : 7 ≤ n) : foldA (ratio n) ≠ 0 := by
  intro he
  exact (denominator_factors hn).2.2.1.ne (by rw [← foldA_ratio n hn, he, zero_mul])

private theorem determinantFactor_ratio_ne_zero (n : ℕ) (hn : 7 ≤ n) :
    determinantFactor n (ratio n) ≠ 0 := by
  intro he
  exact (denominator_factors hn).2.2.2.ne (by
    rw [← determinantFactor_ratio n hn, he, zero_mul])

private theorem quartic_ratio (n : ℕ) (hn : 7 ≤ n) : quarticRatio n (ratio n) = quartic n := by
  unfold quarticRatio quartic
  apply (div_eq_div_iff _ (quartic_denominator_ne_zero hn)).mpr
  · unfold ratio determinantFactor foldA quadraticFactor quarticP quarticDenominator
    unfold D P A Z deltaRatio delta
    field_simp [(G_pos hn).ne']
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (ratio_ne_two n hn))
      (ratio_add_two_ne_zero n hn)) (pow_ne_zero _ (foldA_ratio_ne_zero n hn)))
      (determinantFactor_ratio_ne_zero n hn)

theorem normalized_zero (imag : Bool) (n : ℕ) (x : Path) (row : Fin 8) :
    normalizedCoeff imag n x row 0 = rawCoeff imag n x row 0 / massCoeff n x 0 := by
  rw [normalizedCoeff]
  simp

theorem normalized_one (imag : Bool) (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    normalizedCoeff imag n x row 1 = rawCoeff imag n x row 1 / massCoeff n x 0 := by
  rw [normalizedCoeff]
  simp [mass_one n hn]

theorem normalized_two (imag : Bool) (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    normalizedCoeff imag n x row 2 = (rawCoeff imag n x row 2 -
      massCoeff n x 2 * normalizedCoeff imag n x row 0) / massCoeff n x 0 := by
  rw [normalizedCoeff]
  simp [Fin.sum_univ_succ, mass_one n hn]

theorem normalized_three (imag : Bool) (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    normalizedCoeff imag n x row 3 = (rawCoeff imag n x row 3 -
      massCoeff n x 2 * normalizedCoeff imag n x row 1) / massCoeff n x 0 := by
  rw [normalizedCoeff]
  simp [Fin.sum_univ_succ, mass_three n hn, mass_one n hn]

theorem normalized_four (imag : Bool) (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    normalizedCoeff imag n x row 4 = (rawCoeff imag n x row 4 -
      (massCoeff n x 4 * normalizedCoeff imag n x row 0 +
        massCoeff n x 2 * normalizedCoeff imag n x row 2)) / massCoeff n x 0 := by
  rw [normalizedCoeff]
  simp [Fin.sum_univ_succ, mass_three n hn, mass_one n hn]

private theorem normalize_scaled (g z m r s : ℝ) (hg : g ≠ 0) (hz : z ≠ 0) :
    (g*s - g*m*(g*r/(g*z)))/(g*z) = (z*s - m*r)/z^2 := by
  field_simp

private theorem second_scaled (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8)
    (a b : ℝ) (h0 : rawCoeff false n x row 0 = G n*a)
    (h2 : rawCoeff false n x row 2 = G n*b) :
    normalizedCoeff false n x row 2 =
      ((ratio n+2)*b - mass₂ n (ratio n) x*a)/(ratio n+2)^2 := by
  rw [normalized_two _ n hn, normalized_zero, mass_zero n hn, mass_two n hn, h0, h2]
  exact normalize_scaled _ _ _ _ _ (G_pos hn).ne' (ratio_add_two_ne_zero n hn)

private theorem quadratic_readouts (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    let f := ratio n
    let z := f+2
    normalizedCoeff false n x 1 2 = (z * p₂ n f x - mass₂ n f x)/z^2 ∧
    normalizedCoeff false n x 2 2 = (z * q₂ n f x - (f-1)*mass₂ n f x)/z^2 ∧
    normalizedCoeff false n x 3 2 = (z * h₂ n f x - mass₂ n f x)/z^2 ∧
    normalizedCoeff false n x 4 2 = w₂ f x/z ∧
    normalizedCoeff false n x 5 2 = v₂ f x/z ∧
    normalizedCoeff false n x 6 2 = (3-f)/z := by
  obtain ⟨hp, hq, hh, hw, hv, hj⟩ := raw_weight_two n x
  have hz := ratio_add_two_ne_zero n hn
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [second_scaled n hn x 1 1 (p₂ n (ratio n) x)]
    · ring
    · simpa using (raw_zero n hn x 1).1
    · rw [(raw_two n hn x 1).1]
      exact congrArg (G n * ·) hp
  · rw [second_scaled n hn x 2 (ratio n-1) (q₂ n (ratio n) x)]
    · ring
    · rw [(raw_zero n hn x 2).1]
      change F n - G n = _
      rw [F_eq_ratio_mul n hn]
      ring
    · rw [(raw_two n hn x 2).1]
      exact congrArg (G n * ·) hq
  · rw [second_scaled n hn x 3 1 (h₂ n (ratio n) x)]
    · ring
    · simpa using (raw_zero n hn x 3).1
    · rw [(raw_two n hn x 3).1]
      exact congrArg (G n * ·) hh
  · rw [second_scaled n hn x 4 0 (w₂ (ratio n) x)]
    · field_simp
      simp
    · simpa using (raw_zero n hn x 4).1
    · rw [(raw_two n hn x 4).1]
      exact congrArg (G n * ·) hw
  · rw [second_scaled n hn x 5 0 (v₂ (ratio n) x)]
    · field_simp
      simp
    · simpa using (raw_zero n hn x 5).1
    · rw [(raw_two n hn x 5).1]
      exact congrArg (G n * ·) hv
  · rw [second_scaled n hn x 6 0 (3-ratio n)]
    · field_simp
      simp
    · simpa using (raw_zero n hn x 6).1
    · rw [(raw_two n hn x 6).1]
      exact congrArg (G n * ·) hj

private theorem cubic_w (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    let f := ratio n
    normalizedCoeff true n x 4 3 =
      ((f+2)*w₃ n f x - (3-f)*mass₂ n f x)/(f+2)^2 := by
  dsimp only
  rw [normalized_three _ n hn, normalized_one _ n hn, mass_zero n hn, mass_two n hn,
    (raw_three n hn x 4).2, (raw_first n hn x 4).2]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, raw_weight_w_three]
  change (G n*w₃ n (ratio n) x - G n*mass₂ n (ratio n) x *
    ((3*G n-F n)/(G n*(ratio n+2))))/(G n*(ratio n+2)) = _
  rw [F_eq_ratio_mul n hn, show 3*G n-ratio n*G n = G n*(3-ratio n) by ring]
  rw [normalize_scaled _ _ _ _ _ (G_pos hn).ne' (ratio_add_two_ne_zero n hn)]
  ring

private theorem quartic_j (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    let f := ratio n
    normalizedCoeff false n x 6 4 =
      ((f+2)*j₄ n f x - (3-f)*mass₂ n f x)/(f+2)^2 := by
  obtain ⟨_, _, _, _, _, hj⟩ := quadratic_readouts n hn x
  have hg := (G_pos hn).ne'
  have hz := ratio_add_two_ne_zero n hn
  dsimp only
  rw [normalized_four _ n hn, normalized_zero, (raw_zero n hn x 6).1,
    hj, (raw_four n hn x 6).1, mass_zero n hn, mass_two n hn]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, raw_weight_j_four]
  change (G n*j₄ n (ratio n) x -
    (massCoeff n x 4*(0/(G n*(ratio n+2))) +
      G n*mass₂ n (ratio n) x*((3-ratio n)/(ratio n+2))))/(G n*(ratio n+2)) = _
  field_simp
  ring

theorem forbidden_lower_coefficients (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    let j := normalizedCoeff false n x 6
    j 0 = 0 ∧ j 1 = 0 ∧ j 2 = (3-ratio n)/(ratio n+2) ∧ j 3 = 0 := by
  obtain ⟨_, _, _, _, _, hj⟩ := quadratic_readouts n hn x
  dsimp only
  refine ⟨?_, ?_, hj, ?_⟩
  · simp [normalized_zero, (raw_zero n hn x 6).1]
  · simp [normalized_one _ n hn, (raw_first n hn x 6).1]
  · simp [normalized_three _ n hn, normalized_one _ n hn, (raw_first n hn x 6).1,
      (raw_three n hn x 6).1]

/-- The seven regular rows, with the real block preceding the imaginary block. -/
def regularCoeff (n : ℕ) (x : Path) (r : ℕ) : Fin 7 → ℝ :=
  ![normalizedCoeff false n x 1 r, normalizedCoeff false n x 2 r,
    normalizedCoeff false n x 4 r, normalizedCoeff false n x 5 r,
    normalizedCoeff true n x 3 r, normalizedCoeff true n x 4 r, normalizedCoeff true n x 5 r]

private theorem toRealRegularEqual (n : ℕ) (hn : 7 ≤ n) (x : Path)
    (hr : regularCoeff n x 2 = regularCoeff n original 2) :
    RealRegularEqual n (ratio n) x := by
  obtain ⟨hp, hq, _, hw, hv, _⟩ := quadratic_readouts n hn x
  obtain ⟨hp₀, hq₀, _, hw₀, hv₀, _⟩ := quadratic_readouts n hn original
  have hz := ratio_add_two_ne_zero n hn
  have he (i : Fin 7) := congrFun hr i
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h₀ := he 0
    simp [regularCoeff, hp, hp₀] at h₀
    field_simp at h₀
    unfold pDiff
    linear_combination h₀
  · have h₁ := he 1
    simp [regularCoeff, hq, hq₀] at h₁
    field_simp at h₁
    unfold qDiff
    linear_combination h₁
  · have h₂ := he 2
    simp [regularCoeff, hw, hw₀] at h₂
    exact (div_left_inj' hz).mp h₂
  · have h₃ := he 3
    simp [regularCoeff, hv, hv₀] at h₃
    exact (div_left_inj' hz).mp h₃

/-- The normalized fold equation after imposing equality in the regular rows. -/
theorem normalized_fold_difference (n : ℕ) (hn : 7 ≤ n) (x : Path)
    (hr : regularCoeff n x 2 = regularCoeff n original 2) :
    let f := ratio n
    normalizedCoeff false n x 3 2 - normalizedCoeff false n original 3 2 =
      (x.t-1)*(foldA f*x.t+foldB f)/(2*(f+2)) := by
  obtain ⟨_, _, hh, _, _, _⟩ := quadratic_readouts n hn x
  obtain ⟨_, _, hh₀, _, _, _⟩ := quadratic_readouts n hn original
  have h := fold_difference (ratio_ne_one n hn) (toRealRegularEqual n hn x hr)
  have hz := ratio_add_two_ne_zero n hn
  dsimp only
  rw [hh, hh₀]
  unfold hDiff at h
  field_simp
  linear_combination h

/-- Opposite slope determined by the normalized fold equation. -/
def oppositeSlope (n : ℕ) : ℝ :=
  -foldB (ratio n) / foldA (ratio n)

theorem oppositeSlope_ne_one (n : ℕ) (hn : 7 ≤ n) : oppositeSlope n ≠ 1 := by
  intro he
  unfold oppositeSlope at he
  have h := (div_eq_iff (foldA_ratio_ne_zero n hn)).mp he
  unfold foldA foldB at h
  have hg := G_pos hn
  have hh := (fib_bounds hn).1
  have hu := (fib_bounds hn).2.1
  rw [F_eq_ratio_mul n hn] at hh hu
  have hl : 0 < ratio n := by
    by_contra! h
    nlinarith only [hh, mul_nonpos_of_nonpos_of_nonneg h hg.le, hg]
  have h5 : 3 * ratio n - 5 < 0 := by
    by_contra! h
    nlinarith only [hu, mul_nonneg h hg.le, hg]
  have hnon := mul_neg_of_pos_of_neg hl h5
  nlinarith only [h, hnon]

theorem slopes_of_equal_fold (n : ℕ) (hn : 7 ≤ n) (x : Path)
    (hr : regularCoeff n x 2 = regularCoeff n original 2)
    (hh : normalizedCoeff false n x 3 2 = normalizedCoeff false n original 3 2) :
    x.t = 1 ∨ x.t = oppositeSlope n := by
  have h := normalized_fold_difference n hn x hr
  have hz := ratio_add_two_ne_zero n hn
  have ha := foldA_ratio_ne_zero n hn
  rw [hh, sub_self, eq_comm, div_eq_zero_iff] at h
  obtain h | h := h
  · obtain h | h := mul_eq_zero.mp h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr ((eq_div_iff ha).mpr (by linear_combination h))
  · exact False.elim ((mul_ne_zero (by norm_num) hz) h)

/-- Uniform degree-four normalized forbidden difference, with optional cubic
change of parameter on the reference path. -/
theorem opposite_forbidden_quartic_reparam (n : ℕ) (hn : 7 ≤ n) (x : Path) (σ : ℝ)
    (ht : x.t = oppositeSlope n) (hr : regularCoeff n x 2 = regularCoeff n original 2)
    (hw : normalizedCoeff true n x 4 3 - normalizedCoeff true n original 4 3 =
      σ*(3-ratio n)/(ratio n+2)) :
    normalizedCoeff false n x 6 4 - normalizedCoeff false n original 6 4 -
      2*σ*((3-ratio n)/(ratio n+2)) = quartic n := by
  have hz := ratio_add_two_ne_zero n hn
  have ha := foldA_ratio_ne_zero n hn
  have hd := determinantFactor_ratio_ne_zero n hn
  rw [cubic_w n hn x, cubic_w n hn original] at hw
  have hw' : wDiff₃ n (ratio n) x = σ*(ratio n+2)*(3-ratio n) := by
    unfold wDiff₃
    field_simp at hw
    linear_combination hw
  have hq := quartic_difference (ratio_ne_one n hn) (ratio_ne_two n hn) hz ha hd
    (toRealRegularEqual n hn x hr) ht hw'
  rw [quartic_ratio n hn] at hq
  rw [quartic_j n hn x, quartic_j n hn original, ← hq]
  unfold jDiff₄
  field_simp
  ring

/-- When the regular readouts agree through cubic order, the opposite
slope's forbidden diagonal has first difference exactly at order four. -/
theorem opposite_forbidden_first_difference (n : ℕ) (hn : 7 ≤ n) (x : Path)
    (ht : x.t = oppositeSlope n)
    (hr : ∀ k ≤ 3, regularCoeff n x k = regularCoeff n original k) :
    (∀ k < 4, normalizedCoeff false n x 6 k = normalizedCoeff false n original 6 k) ∧
    normalizedCoeff false n x 6 4 - normalizedCoeff false n original 6 4 = quartic n ∧
    Real.sign (normalizedCoeff false n x 6 4 - normalizedCoeff false n original 6 4) =
      (-1 : ℝ)^(n-1) ∧
    normalizedCoeff false n x 6 4 ≠ normalizedCoeff false n original 6 4 := by
  have hw := congrFun (hr 3 (by decide)) (5 : Fin 7)
  change normalizedCoeff true n x 4 3 = normalizedCoeff true n original 4 3 at hw
  have hq := opposite_forbidden_quartic_reparam n hn x 0 ht (hr 2 (by decide)) (by simp [hw])
  simp only [mul_zero, zero_mul, sub_zero] at hq
  refine ⟨?_, hq, hq ▸ quartic_sign hn, ?_⟩
  · obtain ⟨h₀, h₁, h₂, h₃⟩ := forbidden_lower_coefficients n hn x
    obtain ⟨h₀', h₁', h₂', h₃'⟩ := forbidden_lower_coefficients n hn original
    intro k hk
    interval_cases k
    · exact h₀.trans h₀'.symm
    · exact h₁.trans h₁'.symm
    · exact h₂.trans h₂'.symm
    · exact h₃.trans h₃'.symm
  · intro he
    rw [he, sub_self] at hq
    exact quartic_ne_zero hn hq.symm

/-- Equality of the full formal readouts through order four excludes the
opposite fold root on the chosen reference path. -/
theorem no_equal_formal_readouts_on_opposite_branch (n : ℕ) (hn : 7 ≤ n) (x : Path)
    (hr : ∀ k ≤ 4, regularCoeff n x k = regularCoeff n original k)
    (hh : normalizedCoeff false n x 3 2 = normalizedCoeff false n original 3 2)
    (hj : normalizedCoeff false n x 6 4 = normalizedCoeff false n original 6 4) :
    x.t = 1 := by
  rcases slopes_of_equal_fold n hn x (hr 2 (by decide)) hh with h | h
  · exact h
  · exact False.elim ((opposite_forbidden_first_difference n hn x h
      (fun k hk => hr k (by omega))).2.2.2 hj)

end

#print axioms normalized_fold_difference
#print axioms opposite_forbidden_first_difference
#print axioms no_equal_formal_readouts_on_opposite_branch

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreNormalizedJet
