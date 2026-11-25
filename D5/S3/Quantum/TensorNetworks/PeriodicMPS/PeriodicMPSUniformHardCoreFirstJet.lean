/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreTransferRecurrence, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreQuarticSign]
   utility: none
   digest: The normalized two-site differential at the hard-core witness has seven independent regular rows and admits local reconstruction after fixing one extra coordinate. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreTransferRecurrence
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreQuarticSign
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The normalized first jet of the uniform hard-core two-site readout
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFirstJet

open PeriodicMPSUniformHardCoreTransferRecurrence
open PeriodicMPSUniformHardCoreQuarticSign
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSParentIntersection (Word twoFlattening)
open UniformMPSExpectedDimensionRefutation (traceWord)
open Polynomial
open scoped Matrix Kronecker BigOperators

/-- Rows of the raw transfer certificate in order `00, p, q, z, w, v, j, 10`. -/
def entry : Fin 8 → TwoBits × TwoBits :=
  ![((0, 0), (0, 0)), ((0, 1), (0, 1)), ((0, 1), (1, 0)), ((0, 0), (0, 1)),
    ((1, 1), (0, 0)), ((1, 1), (0, 1)), ((1, 1), (1, 1)), ((1, 0), (1, 0))]

/-- The coefficient of `F` and `G` in the constant raw terms. -/
def baseWeights : Fin 8 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![1, -1], ![0, 1], ![0, 0], ![0, 0], ![0, 0], ![0, 1]]

/-- Integer coefficients of five times the raw first jet in the basis
`F, G, nF, nG`. The direction variables are `a,b,c,d` followed by
their four conjugates. -/
def firstWeights : Fin 8 → Fin 4 → Fin 8 → ℤ :=
  ![![![6, -2, 0, 0, 6, -2, 0, 0], ![-10, 0, 0, 0, -10, 0, 0, 0],
       ![-1, 2, 0, 0, -1, 2, 0, 0], ![3, -1, 0, 0, 3, -1, 0, 0]],
    ![![-3, 1, 0, 0, -3, 1, 0, 0], ![5, 0, 0, 0, 5, 0, 0, 0],
       ![3, -1, 0, 0, 3, -1, 0, 0], ![-4, 3, 0, 0, -4, 3, 0, 0]],
    ![![19, -3, -5, -5, 19, -3, -5, -5], ![-30, 5, 10, 10, -30, 5, 10, 10],
       ![-4, 3, 0, 0, -4, 3, 0, 0], ![7, -4, 0, 0, 7, -4, 0, 0]],
    ![![-13, 1, 0, 0, -3, 1, 5, 5], ![20, -5, 0, 0, 5, 0, -5, -5],
       ![3, -1, 0, 0, 3, -1, 0, 0], ![-4, 3, 0, 0, -4, 3, 0, 0]],
    ![![0, 0, -5, 5, 0, 0, 0, 0], ![0, 0, 15, -5, 0, 0, 0, 0],
       0, 0],
    ![![0, 0, 0, 5, 0, 0, 0, 0], ![0, 0, 5, -5, 0, 0, 0, 0],
       0, 0],
    0,
    ![![-3, 1, 0, 0, -3, 1, 0, 0], ![5, 0, 0, 0, 5, 0, 0, 0],
       ![3, -1, 0, 0, 3, -1, 0, 0], ![-4, 3, 0, 0, -4, 3, 0, 0]]]

private abbrev SymbolicJet := TrivSqZeroExt ℤ (Fin 8 → ℤ)

private def variableJet (base : ℤ) (i : Fin 8) : SymbolicJet :=
  (base, fun j => if i = j then 1 else 0)

private def symbolicRaw (r : Fin 8) (n : ℕ) : SymbolicJet :=
  let A := hardCoreChart (variableJet 0 0) (variableJet 1 1) (variableJet 0 2)
    (variableJet 0 3)
  let B := hardCoreChart (variableJet 0 4) (variableJet 1 5) (variableJet 0 6)
    (variableJet 0 7)
  (binaryInsertion A B (entry r).1 (entry r).2 * binaryTransfer A B ^ (n - 2)).trace

private def baseInteger (r : Fin 8) (n : ℕ) : ℤ :=
  baseWeights r 0 * (Nat.fib n : ℤ) + baseWeights r 1 * (Nat.fib (n - 1) : ℤ)

private def firstInteger (r : Fin 8) (n : ℕ) (i : Fin 8) : ℤ :=
  (firstWeights r 0 i + (n : ℤ) * firstWeights r 2 i) * (Nat.fib n : ℤ) +
    (firstWeights r 1 i + (n : ℤ) * firstWeights r 3 i) * (Nat.fib (n - 1) : ℤ)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem baseSamples (r : Fin 8) (k : Fin 2) :
    (symbolicRaw r (7 + k)).fst = baseInteger r (7 + k) := by
  fin_cases r <;> fin_cases k <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem firstSamples (r : Fin 8) (k : Fin 4) (i : Fin 8) :
    5 * (symbolicRaw r (7 + k)).snd i = firstInteger r (7 + k) i := by
  fin_cases r <;> fin_cases k <;> fin_cases i <;> decide

noncomputable section

private def coeffJet : Polynomial ℂ →+* TrivSqZeroExt ℂ ℂ where
  toFun p := (p.coeff 0, p.coeff 1)
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_one' := TrivSqZeroExt.ext (by simp) (by simp [Polynomial.coeff_one])
  map_add' p q := TrivSqZeroExt.ext (Polynomial.coeff_add _ _ _) (Polynomial.coeff_add _ _ _)
  map_mul' p q := TrivSqZeroExt.ext (Polynomial.mul_coeff_zero _ _) (by
    change (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0
    exact Polynomial.mul_coeff_one _ _)

private def dot (x : Fin 8 → ℂ) (m : Fin 8 → ℤ) : ℂ :=
  ∑ i, (m i : ℂ) * x i

private def specialize (x : Fin 8 → ℂ) : SymbolicJet →+* TrivSqZeroExt ℂ ℂ where
  toFun u := ((u.fst : ℂ), dot x u.snd)
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp [dot])
  map_one' := TrivSqZeroExt.ext (by simp) (by simp [dot])
  map_add' u v := TrivSqZeroExt.ext (Int.cast_add _ _) (by
    change dot x (u.snd + v.snd) = dot x u.snd + dot x v.snd
    simp [dot, add_mul, Finset.sum_add_distrib])
  map_mul' u v := TrivSqZeroExt.ext (Int.cast_mul _ _) (by
    change (∑ i, (↑(u.fst * v.snd i + u.snd i * v.fst) : ℂ) * x i) =
      (u.fst : ℂ) * dot x v.snd + dot x u.snd * (v.fst : ℂ)
    simp only [dot, Int.cast_add, Int.cast_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring)

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

private theorem map_chart {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (a b c d : R) (i : Fin 2) :
    f.mapMatrix (hardCoreChart a b c d i) = hardCoreChart (f a) (f b) (f c) (f d) i := by
  ext u v
  fin_cases i <;> fin_cases u <;> fin_cases v <;> simp [hardCoreChart, RingHom.mapMatrix_apply]

/-- The affine hard-core path in any complex direction, using a real parameter. -/
def chartJet (a b c d : ℂ) : Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  hardCoreChart (C a * X) (1 + C b * X) (C c * X) (C d * X)

def rawJet (a b c d : ℂ) (r : Fin 8) (n : ℕ) : Polynomial ℂ :=
  binaryRawTransfer (chartJet a b c d) (entry r).1 (entry r).2 n

/-- The four chart directions followed by their complex conjugates. -/
def direction (a b c d : ℂ) : Fin 8 → ℂ :=
  ![a, b, c, d, star a, star b, star c, star d]

private theorem specialize_variable (x : Fin 8 → ℂ) (b : ℤ) (i : Fin 8) :
    specialize x (variableJet b i) = ((b : ℂ), x i) := by
  refine TrivSqZeroExt.ext rfl ?_
  change (∑ j : Fin 8, (↑(if i = j then (1 : ℤ) else 0) : ℂ) * x j) = x i
  simp [eq_comm (a := i), apply_ite ((↑) : ℤ → ℂ)]

private theorem specialize_raw (a b c d : ℂ) (r : Fin 8) (n : ℕ) :
    specialize (direction a b c d) (symbolicRaw r n) = coeffJet (rawJet a b c d r n) := by
  unfold symbolicRaw rawJet binaryRawTransfer
  rw [map_raw, map_raw]
  have hconj (i : Fin 2) :
      conjugateJet (chartJet a b c d) i = chartJet (star a) (star b) (star c) (star d) i := by
    ext u v
    fin_cases i <;> fin_cases u <;> fin_cases v <;>
      simp [conjugateJet, chartJet, hardCoreChart]
  simp only [hconj]
  have hcoeff (z : ℂ) : coeffJet (C z * X) = (0, z) := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> change (C z * X).coeff _ = _ <;> simp
  have hone (z : ℂ) : coeffJet (1 + C z * X) = (1, z) := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> change (1 + C z * X).coeff _ = _ <;>
      simp [coeff_one]
  simp only [chartJet, map_chart, specialize_variable, hcoeff, hone]
  simp [direction]

/-- Affine polynomial weight for one Fibonacci sequence in the first jet. -/
def polyWeight (x : Fin 8 → ℂ) (r : Fin 8) (i j : Fin 4) : Polynomial ℂ :=
  C (dot x (firstWeights r i) / 5) + C (dot x (firstWeights r j) / 5) * X

private theorem polyWeight_degree (x : Fin 8 → ℂ) (r : Fin 8) (i j : Fin 4) :
    (polyWeight x r i j).degree ≤ (1 : WithBot ℕ) := by
  unfold polyWeight
  apply degree_add_le_of_degree_le
  · exact degree_C_le.trans (by decide)
  · exact (degree_mul_le _ _).trans (by
      rw [degree_X]
      calc
        _ ≤ 0 + (1 : WithBot ℕ) := add_le_add degree_C_le le_rfl
        _ = _ := by rfl)

/-- Uniform constant term, including the vanishing `11` population. -/
theorem rawJet_coeff_zero (a b c d : ℂ) (r : Fin 8) (n : ℕ) (hn : 7 ≤ n) :
    (rawJet a b c d r n).coeff 0 =
      fibonacciCandidate (C (baseWeights r 0 : ℂ)) (C (baseWeights r 1 : ℂ)) n := by
  apply (hardCoreRaw_fibonacci_iff_initial (C a * X) (1 + C b * X) (C c * X) (C d * X)
    (by simp) (by simp) (by simp) (by simp) (entry r).1 (entry r).2 0 (by decide)
    _ _ degree_C_le degree_C_le).mpr _ n hn
  intro k hk
  have h := congrArg TrivSqZeroExt.fst (specialize_raw a b c d r (7 + k))
  change ((symbolicRaw r (7 + k)).fst : ℂ) = (rawJet a b c d r (7 + k)).coeff 0 at h
  change (rawJet a b c d r (7 + k)).coeff 0 = _
  rw [← h, baseSamples r ⟨k, by omega⟩]
  simp [baseInteger, fibonacciCandidate]

/-- Uniform first coefficient, with all four complex direction coordinates free. -/
theorem rawJet_coeff_one (a b c d : ℂ) (r : Fin 8) (n : ℕ) (hn : 7 ≤ n) :
    (rawJet a b c d r n).coeff 1 =
      fibonacciCandidate (polyWeight (direction a b c d) r 0 2)
        (polyWeight (direction a b c d) r 1 3) n := by
  apply (hardCoreRaw_fibonacci_iff_initial (C a * X) (1 + C b * X) (C c * X) (C d * X)
    (by simp) (by simp) (by simp) (by simp) (entry r).1 (entry r).2 1 (by decide)
    _ _ (polyWeight_degree ..) (polyWeight_degree ..)).mpr _ n hn
  intro k hk
  have h := congrArg TrivSqZeroExt.snd (specialize_raw a b c d r (7 + k))
  change dot (direction a b c d) (symbolicRaw r (7 + k)).snd =
    (rawJet a b c d r (7 + k)).coeff 1 at h
  change (rawJet a b c d r (7 + k)).coeff 1 = _
  rw [← h]
  apply (mul_left_cancel₀ (show (5 : ℂ) ≠ 0 by norm_num))
  calc
    5 * dot (direction a b c d) (symbolicRaw r (7 + k)).snd =
        dot (direction a b c d) (firstInteger r (7 + k)) := by
      rw [dot, dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ← Int.cast_ofNat (R := ℂ) 5, ← Int.cast_mul]
      exact congrArg (fun v : ℤ => (v : ℂ) * direction a b c d i)
        (firstSamples r ⟨k, by omega⟩ i)
    _ = _ := by
      simp [dot, firstInteger, fibonacciCandidate, polyWeight, Fin.sum_univ_succ]
      ring

abbrev Coord := Fin 4 → ℂ

def witness : Coord := ![0, 1, 0, 0]

def cores (x : Coord) := hardCoreChart (x 0) (x 1) (x 2) (x 3)

private def raw (u : Coord) (r : Fin 8) (n : ℕ) : Polynomial ℂ :=
  rawJet (u 0) (u 1) (u 2) (u 3) r n

private def twoMass (A : Fin 2 → PeriodicMPSParentIntersection.Bond) (s : ℕ) : ℝ :=
  (rawTwo A s).trace.re

private def normalizedTwo (A : Fin 2 → PeriodicMPSParentIntersection.Bond) (s : ℕ) :
    Matrix TwoBits TwoBits ℂ := (twoMass A s)⁻¹ • rawTwo A s

private def massJet (u : Coord) (n : ℕ) : Polynomial ℂ :=
  raw u 0 n + raw u 1 n + raw u 7 n + raw u 6 n

private theorem raw_eval (u : Coord) (r : Fin 8) (s : ℕ) (t : ℝ) :
    (raw u r (s + 4)).eval (t : ℂ) =
      rawTwo (cores (witness + t • u)) s (entry r).1 (entry r).2 := by
  unfold raw rawJet
  rw [eval_binaryRawTransfer]
  congr 1
  funext i
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [cores, witness, chartJet, hardCoreChart, RingHom.mapMatrix_apply,
      Complex.real_smul] <;> ring

private theorem mass_eval (u : Coord) (s : ℕ) (t : ℝ) :
    ((massJet u (s + 4)).eval (t : ℂ)).re = twoMass (cores (witness + t • u)) s := by
  simp only [massJet, eval_add, raw_eval, twoMass, Matrix.trace, Matrix.diag,
    Fintype.sum_prod_type, Fin.sum_univ_two, entry, Matrix.cons_val_zero]
  simp
  ring

private theorem raw_zero (u : Coord) (r : Fin 8) (n : ℕ) (hn : 7 ≤ n) :
    (raw u r n).coeff 0 = (↑(![F n, G n, F n - G n, G n, 0, 0, 0, G n] r) : ℂ) := by
  rw [raw, rawJet_coeff_zero _ _ _ _ _ _ hn]
  fin_cases r <;> simp [fibonacciCandidate, baseWeights, F, G, sub_eq_add_neg]

private theorem mass_zero (u : Coord) (n : ℕ) (hn : 7 ≤ n) :
    ((massJet u n).eval 0).re = Z n := by
  rw [← coeff_zero_eq_eval_zero]
  simp [massJet, raw_zero u _ n hn, Z]
  ring

private theorem polynomial_re (P : Polynomial ℂ) :
    HasDerivAt (fun t : ℝ => (P.eval (t : ℂ)).re) (P.coeff 1).re 0 := by
  simpa [← coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] using
    (P.hasDerivAt (0 : ℂ)).real_of_complex

private theorem polynomial_im (P : Polynomial ℂ) :
    HasDerivAt (fun t : ℝ => (P.eval (t : ℂ)).im) (P.coeff 1).im 0 := by
  have h : HasDerivAt (fun t : ℝ => P.eval (t : ℂ)) (P.derivative.eval 0) 0 :=
    HasDerivAt.comp_ofReal (by rw [Complex.ofReal_zero]; exact P.hasDerivAt 0)
  simpa [Function.comp_def, ← coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] using
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

/-- One real or imaginary component of the normalized physical two-site entry. -/
def component (imag : Bool) (s : ℕ) (r : Fin 8) (x : Coord) : ℝ :=
  let z := normalizedTwo (cores x) s (entry r).1 (entry r).2
  if imag then z.im else z.re

/-- Exact quotient differentiation of the trace-normalized marginal. -/
theorem hasDerivAt_component (imag : Bool) (s : ℕ) (hs : 3 ≤ s)
    (r : Fin 8) (u : Coord) :
    HasDerivAt (fun t : ℝ => component imag s r (witness + t • u))
      (let n := s + 4
       let N := fun z : ℂ => if imag then z.im else z.re
       (N ((raw u r n).coeff 1) * Z n -
        N ((raw u r n).coeff 0) * ((massJet u n).coeff 1).re) / Z n ^ 2) 0 := by
  let n := s + 4
  let N := fun z : ℂ => if imag then z.im else z.re
  have hn : 7 ≤ n := by dsimp [n]; omega
  have hm := mass_zero u n hn
  have hZ := (denominator_factors hn).2.1.ne'
  have hN : HasDerivAt (fun t : ℝ => N ((raw u r n).eval (t : ℂ)))
      (N ((raw u r n).coeff 1)) 0 := by
    cases imag
    · exact polynomial_re _
    · exact polynomial_im _
  have hd : ((massJet u n).eval ((0 : ℝ) : ℂ)).re ≠ 0 := by simpa [hm] using hZ
  have h := hN.div (polynomial_re (massJet u n)) hd
  have h0 : ((massJet u n).coeff 0).re = Z n := by rwa [coeff_zero_eq_eval_zero]
  simp only [Complex.ofReal_zero, ← coeff_zero_eq_eval_zero, h0] at h
  convert h using 1
  ext t
  change component imag s r (witness + t • u) =
    N ((raw u r n).eval (t : ℂ)) / ((massJet u n).eval (t : ℂ)).re
  rw [show n = s + 4 from rfl, raw_eval, mass_eval]
  cases imag <;>
    simp only [N, component, Bool.false_eq_true, ↓reduceIte, normalizedTwo,
      Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, div_eq_mul_inv] <;> ring

private def pA (n f g : ℝ) : ℝ := 2 * ((3 * n - 3) * f + (5 - 4 * n) * g) / 5
private def pB (n f g : ℝ) : ℝ := 2 * ((1 - n) * f + 3 * n * g) / 5
private def qA (n f g : ℝ) : ℝ := 2 * ((19 - 4 * n) * f + (7 * n - 30) * g) / 5

/-- Real block in row order `p,q,Re w,Re v` and column order `Re a,Re b,Re c,Re d`. -/
def realBlock (n : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let f := F n
  let g := G n
  let z := Z n
  let mA := 2 * (n : ℝ) * (f - g)
  let mB := 2 * (n : ℝ) * g
  !![(z * pA n f g - g * mA) / z^2, (z * pB n f g - g * mB) / z^2, 0, 0;
    (z * qA n f g - (f - g) * mA) / z^2, (z * pA n f g - (f - g) * mB) / z^2,
      2 * (2 * g - f) / z, 2 * (2 * g - f) / z;
    0, 0, (3 * g - f) / z, (f - g) / z;
    0, 0, g / z, (f - g) / z]

/-- Imaginary rows `Im z,Im w,Im v` on `Im b,Im c,Im d`. -/
def imagBlock (n : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let f := F n
  let g := G n
  let z := Z n
  !![-g / z, (g - f) / z, (g - f) / z;
    0, (3 * g - f) / z, (f - g) / z;
    0, g / z, (f - g) / z]

/-- The omitted `Im a` column of the imaginary block. -/
def imagA (n : ℕ) : Fin 3 → ℝ := ![(3 * G n - 2 * F n) / Z n, 0, 0]

private theorem det_block (a b c d e f g h i j : ℝ) :
    (!![a, b, 0, 0; c, d, e, f; 0, 0, g, h; 0, 0, i, j] :
      Matrix (Fin 4) (Fin 4) ℝ).det = (a * d - b * c) * (g * j - h * i) := by
  let M := Matrix.fromBlocks !![a,b;c,d] !![0,0;e,f] (0 : Matrix (Fin 2) (Fin 2) ℝ)
    !![g,h;i,j]
  have hm : Matrix.reindex finSumFinEquiv finSumFinEquiv M =
      (!![a, b, 0, 0; c, d, e, f; 0, 0, g, h; 0, 0, i, j] :
        Matrix (Fin 4) (Fin 4) ℝ) := by
    ext u v
    fin_cases u <;> fin_cases v <;> rfl
  rw [← hm, Matrix.det_reindex_self]
  unfold M
  rw [Matrix.det_fromBlocks_zero₂₁]
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  rfl

theorem realBlock_det (n : ℕ) (hn : 7 ≤ n) :
    (realBlock n).det * Z n ^ 6 =
      -4 * (F n - 2 * G n) * (F n - G n) * Z n * D n / 5 := by
  have hz := (denominator_factors hn).2.1.ne'
  rw [realBlock, det_block]
  unfold pA pB qA
  field_simp
  unfold D delta Z
  ring

theorem imagBlock_det (n : ℕ) (hn : 7 ≤ n) :
    (imagBlock n).det = G n * (F n - 2 * G n) * (F n - G n) / Z n ^ 3 := by
  have hz := (denominator_factors hn).2.1.ne'
  rw [imagBlock, Matrix.det_fin_three]
  simp
  field_simp
  ring

private theorem fg_ne (n : ℕ) (hn : 7 ≤ n) : F n - G n ≠ 0 := by
  have h := (fib_bounds hn).1
  have hg := G_pos hn
  linarith

theorem realBlock_det_ne_zero (n : ℕ) (hn : 7 ≤ n) : (realBlock n).det ≠ 0 := by
  obtain ⟨hf, hz, _, hd⟩ := denominator_factors hn
  have h : -4 * (F n - 2 * G n) * (F n - G n) * Z n * D n / 5 ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (by norm_num) hf.ne) (fg_ne n hn)) hz.ne') hd.ne) (by norm_num)
  intro he
  apply h
  rw [← realBlock_det n hn, he, zero_mul]

theorem imagBlock_det_ne_zero (n : ℕ) (hn : 7 ≤ n) : (imagBlock n).det ≠ 0 := by
  obtain ⟨hf, hz, _, _⟩ := denominator_factors hn
  rw [imagBlock_det n hn]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (G_pos hn).ne' hf.ne) (fg_ne n hn))
    (pow_ne_zero _ hz.ne')

private def rawReal (u : Coord) (n : ℕ) : Fin 8 → ℝ :=
  let f := F n
  let g := G n
  let a := (u 0).re
  let b := (u 1).re
  let c := (u 2).re
  let d := (u 3).re
  let p := pA n f g * a + pB n f g * b
  ![2 * (n : ℝ) * ((f - g) * a + g * b) - 2 * p,
    p,
    qA n f g * a + pA n f g * b + 2 * (2 * g - f) * (c + d),
    p + (3 * g - 2 * f) * a - g * b + (f - g) * (c + d),
    (3 * g - f) * c + (f - g) * d, g * c + (f - g) * d, 0, p]

private def rawImag (u : Coord) (n : ℕ) : Fin 8 → ℝ :=
  let f := F n
  let g := G n
  let a := (u 0).im
  let b := (u 1).im
  let c := (u 2).im
  let d := (u 3).im
  ![0, 0, 0, (3 * g - 2 * f) * a - g * b + (g - f) * (c + d),
    (3 * g - f) * c + (f - g) * d, g * c + (f - g) * d, 0, 0]

set_option maxHeartbeats 4000000 in
private theorem raw_one_parts (u : Coord) (n : ℕ) (hn : 7 ≤ n) (r : Fin 8) :
    ((raw u r n).coeff 1).re = rawReal u n r ∧
      ((raw u r n).coeff 1).im = rawImag u n r := by
  rw [raw, rawJet_coeff_one _ _ _ _ _ _ hn]
  fin_cases r <;> constructor <;>
    simp [fibonacciCandidate, polyWeight, dot, firstWeights, direction,
      Fin.sum_univ_succ, rawReal, rawImag, pA, pB, qA, F, G, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring

private theorem mass_one (u : Coord) (n : ℕ) (hn : 7 ≤ n) :
    ((massJet u n).coeff 1).re =
      2 * (n : ℝ) * ((F n - G n) * (u 0).re + G n * (u 1).re) := by
  simp only [massJet, coeff_add, Complex.add_re, (raw_one_parts u n hn _).1]
  simp [rawReal]
  ring

/-- The real and imaginary regular rows, in the orders used by the two blocks. -/
def regularReadout (s : ℕ) (x : Coord) : (Fin 4 → ℝ) × (Fin 3 → ℝ) :=
  (![(component false s 1 x), (component false s 2 x),
      (component false s 4 x), (component false s 5 x)],
   ![(component true s 3 x), (component true s 4 x), (component true s 5 x)])

/-- The normalized regular first jet, with the extra imaginary column retained. -/
def regularJet (n : ℕ) (u : Coord) : (Fin 4 → ℝ) × (Fin 3 → ℝ) :=
  (realBlock n *ᵥ (fun i => (u i).re),
    imagBlock n *ᵥ ![(u 1).im, (u 2).im, (u 3).im] + (u 0).im • imagA n)

set_option maxHeartbeats 2000000 in
/-- The displayed block entries are the exact derivatives of the physical readout. -/
theorem hasDerivAt_regularReadout (s : ℕ) (hs : 3 ≤ s) (u : Coord) :
    HasDerivAt (fun t : ℝ => regularReadout s (witness + t • u)) (regularJet (s + 4) u) 0 := by
  have hn : 7 ≤ s + 4 := by omega
  have hz := (denominator_factors hn).2.1.ne'
  have h (imag : Bool) (r : Fin 8) := hasDerivAt_component imag s hs r u
  apply HasDerivAt.prodMk
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;>
      refine (h false _).congr_deriv ?_ <;>
      simp [realBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        raw_zero u _ _ hn, (raw_one_parts u _ hn _).1, rawReal, pA, pB, qA, mass_one u _ hn] <;>
      field_simp <;> ring
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;>
      refine (h true _).congr_deriv ?_ <;>
      simp [imagBlock, imagA, raw_zero u _ _ hn, (raw_one_parts u _ hn _).2, rawImag] <;>
      field_simp
    ring

private lemma smooth_cores (i j k : Fin 2) :
    ContDiff ℝ 1 (fun x : Coord => cores x i j k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact contDiff_const | exact contDiff_apply ℝ (fun _ : Fin 4 => ℂ) _

private lemma smooth_word (w : List (Fin 2)) (i j : Fin 2) :
    ContDiff ℝ 1 (fun x : Coord => (w.map (cores x)).prod i j) := by
  induction w generalizing i j with
  | nil => exact contDiff_const
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    exact ContDiff.sum fun l _ => (smooth_cores k i l).mul (ih l j)

private lemma smooth_raw (s : ℕ) (p q : TwoBits) :
    ContDiff ℝ 1 (fun x : Coord => rawTwo (cores x) s p q) := by
  have hf (r : TwoBits) (w : Word (s + 2)) :
      ContDiff ℝ 1 (fun x : Coord => twoFlattening (cores x) s r w) := by
    simp only [twoFlattening, traceWord, Matrix.trace, Matrix.diag, List.ofFn_comp']
    exact ContDiff.sum fun i _ => smooth_word _ i i
  simp only [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiff.sum fun w _ => (hf p w).mul (Complex.conjCLE.contDiff.comp (hf q w))

private lemma smooth_component (imag : Bool) (s : ℕ) (hs : 3 ≤ s) (r : Fin 8) :
    ContDiffAt ℝ 1 (component imag s r) witness := by
  have hm : ContDiff ℝ 1 (fun x : Coord => twoMass (cores x) s) :=
    Complex.reCLM.contDiff.comp
      (ContDiff.sum (s := Finset.univ) fun p _ => smooth_raw s p p)
  have hmnz : twoMass (cores witness) s ≠ 0 := by
    have hn : 7 ≤ s + 4 := by omega
    have h := mass_eval (0 : Coord) s 0
    rw [Complex.ofReal_zero, mass_zero (0 : Coord) (s + 4) hn, zero_smul, add_zero] at h
    rw [← h]
    exact (denominator_factors hn).2.1.ne'
  have hz : ContDiffAt ℝ 1
      (fun x : Coord => normalizedTwo (cores x) s (entry r).1 (entry r).2) witness :=
    (hm.contDiffAt.inv hmnz).smul (smooth_raw s (entry r).1 (entry r).2).contDiffAt
  cases imag
  · exact Complex.reCLM.contDiff.contDiffAt.comp witness hz
  · exact Complex.imCLM.contDiff.contDiffAt.comp witness hz

theorem regularReadout_contDiffAt (s : ℕ) (hs : 3 ≤ s) :
    ContDiffAt ℝ 1 (regularReadout s) witness := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> exact smooth_component false s hs _
  · apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> exact smooth_component true s hs _

/-- Exact Fréchet derivative of the seven regular outputs in every chart direction. -/
theorem fderiv_regularReadout_apply (s : ℕ) (hs : 3 ≤ s) (u : Coord) :
    fderiv ℝ (regularReadout s) witness u = regularJet (s + 4) u := by
  have hpath : HasDerivAt (fun t : ℝ => witness + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add witness
  have hdiff := (regularReadout_contDiffAt s hs).differentiableAt (by decide)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  exact hd.unique (hasDerivAt_regularReadout s hs u)

/-- The seven outputs determine the seven remaining directions once `Im a` is specified. -/
theorem reconstruct_regularJet (n : ℕ) (hn : 7 ≤ n) (t : ℝ)
    (y : (Fin 4 → ℝ) × (Fin 3 → ℝ)) :
    ∃! u : Coord, (u 0).im = t ∧ regularJet n u = y := by
  have hR : IsUnit (realBlock n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realBlock_det_ne_zero n hn))
  have hI : IsUnit (imagBlock n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (imagBlock_det_ne_zero n hn))
  obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hR y.1
  obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hI (y.2 - t • imagA n)
  let u : Coord := fun i => ⟨v i, (![t, w 0, w 1, w 2] : Fin 4 → ℝ) i⟩
  have hw' : (![w 0, w 1, w 2] : Fin 3 → ℝ) = w := by
    funext i
    fin_cases i <;> rfl
  have hu : (u 0).im = t ∧ regularJet n u = y := by
    refine ⟨rfl, Prod.ext hv ?_⟩
    change (imagBlock n) *ᵥ ![w 0, w 1, w 2] + t • imagA n = y.2
    rw [hw', hw, sub_add_cancel]
  refine ⟨u, hu, ?_⟩
  intro u' hu'
  have hreal : (fun i => (u' i).re) = v :=
    Matrix.mulVec_injective_of_isUnit hR ((congrArg Prod.fst hu'.2).trans hv.symm)
  have hgoal : (imagBlock n) *ᵥ ![(u' 1).im, (u' 2).im, (u' 3).im] =
      y.2 - t • imagA n := by
    have he := congrArg Prod.snd hu'.2
    change (imagBlock n) *ᵥ ![(u' 1).im, (u' 2).im, (u' 3).im] +
      (u' 0).im • imagA n = y.2 at he
    rw [hu'.1] at he
    exact eq_sub_of_add_eq he
  have himag := Matrix.mulVec_injective_of_isUnit hI (hgoal.trans hw.symm)
  funext i
  apply Complex.ext
  · exact congrFun hreal i
  · fin_cases i
    · exact hu'.1
    · exact congrFun himag 0
    · exact congrFun himag 1
    · exact congrFun himag 2

theorem regularReadout_surjective_fderiv (s : ℕ) (hs : 3 ≤ s) :
    Function.Surjective (fderiv ℝ (regularReadout s) witness) := by
  intro y
  obtain ⟨u, hu, _⟩ := reconstruct_regularJet (s + 4) (by omega) 0 y
  exact ⟨u, (fderiv_regularReadout_apply s hs u).trans hu.2⟩

/-- The real rank of the normalized regular differential is seven. -/
theorem regularReadout_rank_seven (s : ℕ) (hs : 3 ≤ s) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (regularReadout s) witness).toLinearMap) = 7 := by
  rw [LinearMap.range_eq_top.mpr (regularReadout_surjective_fderiv s hs), finrank_top]
  simp [Module.finrank_prod]

/-- Fixing the free coordinate `Im a` alongside the seven regular readouts. -/
def regularCoordinates (s : ℕ) (x : Coord) : ℝ × ((Fin 4 → ℝ) × (Fin 3 → ℝ)) :=
  ((x 0).im, regularReadout s x)

/-- For every chain length at least seven, the augmented regular observations are
local coordinates on the hard-core chart. This supplies the local reconstruction
with `Im a` as the free parameter. -/
theorem local_regular_reconstruction (s : ℕ) (hs : 3 ≤ s) :
    ∃ e : OpenPartialHomeomorph Coord (ℝ × ((Fin 4 → ℝ) × (Fin 3 → ℝ))),
      witness ∈ e.source ∧ (e : Coord → _) = regularCoordinates s := by
  let π : Coord →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj 0)
  let L := π.prod (fderiv ℝ (regularReadout s) witness)
  have hL (u : Coord) : L u = ((u 0).im, regularJet (s + 4) u) := by
    exact Prod.ext rfl (fderiv_regularReadout_apply s hs u)
  have hB : Function.Bijective L := by
    constructor
    · intro u v hv
      rw [hL, hL] at hv
      obtain ⟨w, _, hw⟩ := reconstruct_regularJet (s + 4) (by omega) (u 0).im
        (regularJet (s + 4) u)
      exact (hw u ⟨rfl, rfl⟩).trans
        (hw v ⟨(congrArg Prod.fst hv).symm, (congrArg Prod.snd hv).symm⟩).symm
    · rintro ⟨t, y⟩
      obtain ⟨u, hu, _⟩ := reconstruct_regularJet (s + 4) (by omega) t y
      exact ⟨u, (hL u).trans (Prod.ext hu.1 hu.2)⟩
  let E := (LinearEquiv.ofBijective L.toLinearMap hB).toContinuousLinearEquiv
  have hl : (E : Coord →L[ℝ] _) = L := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hreg := regularReadout_contDiffAt s hs
  have hsm : ContDiffAt ℝ 1 (regularCoordinates s) witness :=
    π.contDiff.contDiffAt.prodMk hreg
  have hd : HasFDerivAt (regularCoordinates s) (E : Coord →L[ℝ] _) witness := by
    rw [hl]
    exact π.hasFDerivAt.prodMk (hreg.differentiableAt (by decide)).hasFDerivAt
  exact ⟨hsm.toOpenPartialHomeomorph (regularCoordinates s) hd (by decide),
    hsm.mem_toOpenPartialHomeomorph_source hd (by decide),
    hsm.toOpenPartialHomeomorph_coe hd (by decide)⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFirstJet

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFirstJet.rawJet_coeff_one
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFirstJet.regularReadout_rank_seven
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreFirstJet.local_regular_reconstruction
