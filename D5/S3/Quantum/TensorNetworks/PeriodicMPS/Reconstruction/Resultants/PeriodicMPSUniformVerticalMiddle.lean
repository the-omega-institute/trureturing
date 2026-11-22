/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Resultants/PeriodicMPSUniformVerticalMiddle
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Resultants/PeriodicMPSUniformVerticalMiddle
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Transfer expansion of the middle trace block. -/
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
The middle triplet columns of the reducible section, in the order of the
two rotations followed by the transverse column. The inputs of the trace
readout are the literal powers and the ordered finite cross sum.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalMiddle

open scoped BigOperators Matrix
open PowerSeries (C X coeff)
open D5.S0.Observation.MatrixTracePowerSum (pow_add_two)

noncomputable section

abbrev BondMatrix (R : Type*) := Matrix (Fin 2) (Fin 2) R

variable {R : Type*} [CommRing R]

private def quadratic (a d : R) : PowerSeries R :=
  1 - X ^ 1 * C a + X ^ 2 * C d

private def reciprocal (a d : R) : PowerSeries R :=
  PowerSeries.invOfUnit (quadratic a d) 1

private theorem quadratic_mul_reciprocal (a d : R) :
    quadratic a d * reciprocal a d = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp [quadratic]

/-- The reciprocal of the product of the two reversed quadratic characteristic
polynomials. On the section its coefficients are the complete homogeneous
functions of the four roots. -/
def completeSeries (B0 B1 : BondMatrix R) : PowerSeries R :=
  reciprocal B0.trace B0.det * reciprocal B1.trace B1.det

private theorem quadraticRight_mul_complete (B0 B1 : BondMatrix R) :
    quadratic B1.trace B1.det * completeSeries B0 B1 = reciprocal B0.trace B0.det := by
  rw [completeSeries, mul_left_comm, quadratic_mul_reciprocal, mul_one]

private theorem quadraticLeft_mul_complete (B0 B1 : BondMatrix R) :
    quadratic B0.trace B0.det * completeSeries B0 B1 = reciprocal B1.trace B1.det := by
  rw [completeSeries, ← mul_assoc, quadratic_mul_reciprocal, one_mul]

/-- The coefficient of degree `n-k`, extended by zero at negative degrees. -/
def shiftedCoeff (F : PowerSeries R) (n k : ℕ) : R :=
  if k ≤ n then coeff (n - k) F else 0

private theorem shiftedCoeff_zero (F : PowerSeries R) (n : ℕ) :
    shiftedCoeff F n 0 = coeff n F := by
  simp [shiftedCoeff]

private theorem shiftedCoeff_succ (F : PowerSeries R) (n k : ℕ) :
    shiftedCoeff F (n + 1) (k + 1) = shiftedCoeff F n k := by
  simp [shiftedCoeff, Nat.add_sub_add_right]

private theorem coeff_quadratic_mul (a d : R) (F : PowerSeries R) (n : ℕ) :
    coeff n (quadratic a d * F) =
      coeff n F - a * shiftedCoeff F n 1 + d * shiftedCoeff F n 2 := by
  rw [quadratic, add_mul, sub_mul, one_mul]
  simp only [LinearMap.map_add, LinearMap.map_sub, mul_assoc, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_C_mul]
  by_cases h₁ : 1 ≤ n <;> by_cases h₂ : 2 ≤ n <;> simp [shiftedCoeff, h₁, h₂]

/-- The literal ordered convolution, including the pure `B1^m` endpoint. -/
def literalCross (B0 B1 : BondMatrix R) (m : ℕ) : BondMatrix R :=
  ∑ i ∈ Finset.range m, B0 ^ i * B1 ^ (m - i)

private theorem literalCross_succ (B0 B1 : BondMatrix R) (m : ℕ) :
    literalCross B0 B1 (m + 1) = B1 ^ (m + 1) + B0 * literalCross B0 B1 m := by
  unfold literalCross
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  simp only [pow_zero, Nat.sub_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show m + 1 - (i + 1) = m - i by omega, pow_succ', mul_assoc]

/-- The mixed transfer at the reducible ket, in ket-block order. -/
def sectionTransfer (B0 B1 : BondMatrix R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks B0 B1 0 B1

/-- The finite ordered sum is the upper-right block of the literal transfer power. -/
theorem sectionTransfer_pow (B0 B1 : BondMatrix R) (m : ℕ) :
    sectionTransfer B0 B1 ^ m =
      Matrix.fromBlocks (B0 ^ m) (literalCross B0 B1 m) 0 (B1 ^ m) := by
  induction m with
  | zero => simp [literalCross, Matrix.fromBlocks_one]
  | succ m ih =>
    rw [pow_succ' (sectionTransfer B0 B1), ih, sectionTransfer, Matrix.fromBlocks_multiply,
      literalCross_succ]
    simp only [mul_zero, zero_mul, add_zero, pow_succ', add_comm]

private def liftSeries : PowerSeries R →+* PowerSeries (BondMatrix R) :=
  PowerSeries.map (algebraMap R (BondMatrix R))

private def powerTail (M : BondMatrix R) : PowerSeries (BondMatrix R) :=
  PowerSeries.mk fun n => M ^ (n + 1)

private def numerator (M : BondMatrix R) : PowerSeries (BondMatrix R) :=
  C M - X ^ 1 * C (M.det • (1 : BondMatrix R))

private theorem coeff_shiftedConst (n k : ℕ) (M : BondMatrix R)
    (F : PowerSeries (BondMatrix R)) :
    coeff n (X ^ k * C M * F) =
      if k ≤ n then M * coeff (n - k) F else 0 := by
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
  simp only [PowerSeries.coeff_C_mul]

private theorem lift_quadratic_mul_powerTail (M : BondMatrix R) :
    liftSeries (quadratic M.trace M.det) * powerTail M = numerator M := by
  apply PowerSeries.ext
  intro n
  simp only [quadratic, liftSeries, map_add, map_sub, map_mul, map_pow, map_one,
    PowerSeries.map_X, PowerSeries.map_C, Algebra.algebraMap_eq_smul_one,
    add_mul, sub_mul, one_mul,
    coeff_shiftedConst, powerTail, numerator, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C, Matrix.smul_mul]
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · have h := pow_add_two M 0
    simp only [Nat.zero_add, pow_one, pow_zero] at h
    norm_num [h]
  · have h := pow_add_two M (n + 1)
    have hidx : n + 1 + 1 - 1 = n + 1 := by omega
    have hidx' : n + 1 + 1 - 2 = n := by omega
    have hn : n + 1 + 1 ≠ 0 := by omega
    have hn' : n + 1 ≠ 0 := by omega
    have h₁ : 1 ≤ n + 1 + 1 := by omega
    have h₂ : 2 ≤ n + 1 + 1 := by omega
    simp only [hidx, hidx', hn, hn', h₁, h₂, ite_true, ite_false, sub_zero]
    rw [h]
    abel

private theorem lift_commute_const (F : PowerSeries R) (M : BondMatrix R) :
    Commute (liftSeries F) (C M) := by
  show liftSeries F * C M = C M * liftSeries F
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
    liftSeries, PowerSeries.coeff_map]
  exact Algebra.commutes _ _

private theorem lift_commute_numerator (F : PowerSeries R) (M : BondMatrix R) :
    Commute (liftSeries F) (numerator M) := by
  exact (lift_commute_const F M).sub_right
    ((PowerSeries.commute_X_pow (liftSeries F) 1).mul_right (lift_commute_const F _))

private theorem powerTail_eq (M : BondMatrix R) :
    powerTail M = numerator M * liftSeries (reciprocal M.trace M.det) := by
  let F := reciprocal M.trace M.det
  have h : liftSeries F * liftSeries (quadratic M.trace M.det) = 1 := by
    rw [← map_mul, mul_comm F, quadratic_mul_reciprocal, map_one]
  calc
    powerTail M = liftSeries F * (liftSeries (quadratic M.trace M.det) * powerTail M) := by
      rw [← mul_assoc, h, one_mul]
    _ = liftSeries F * numerator M := by rw [lift_quadratic_mul_powerTail]
    _ = _ := (lift_commute_numerator F M).eq

private theorem shiftedConst_mul (i j : ℕ) (A B : BondMatrix R) :
    (X ^ i * C A) * (X ^ j * C B) = X ^ (i + j) * C (A * B) := by
  calc
    _ = X ^ i * (C A * X ^ j) * C B := by simp only [mul_assoc]
    _ = X ^ i * (X ^ j * C A) * C B := by rw [(PowerSeries.commute_X_pow (C A) j).eq]
    _ = _ := by simp only [pow_add, map_mul, mul_assoc]

set_option maxHeartbeats 800000 in
private theorem numerator_mul (B0 B1 : BondMatrix R) :
    numerator B0 * numerator B1 =
      C (B0 * B1) - X ^ 1 * C (B1.det • B0 + B0.det • B1) +
        X ^ 2 * C ((B0.det * B1.det) • (1 : BondMatrix R)) := by
  have h (A : BondMatrix R) : (X : PowerSeries (BondMatrix R)) ^ 0 * C A = C A := by
    simp
  have expandSub (a b c d : PowerSeries (BondMatrix R)) :
      (a - b) * (c - d) = a * c - (a * d + b * c) + b * d := by
    simp only [sub_mul, mul_sub]
    abel
  unfold numerator
  rw [← h B0, ← h B1, expandSub]
  simp only [shiftedConst_mul, smul_mul_smul_comm]
  simp only [Nat.zero_add, Nat.add_zero, pow_zero, one_mul, Matrix.smul_mul, Matrix.mul_smul,
    mul_one, map_add, mul_add]

private theorem powerTail_mul (B0 B1 : BondMatrix R) :
    powerTail B0 * powerTail B1 =
      (numerator B0 * numerator B1) * liftSeries (completeSeries B0 B1) := by
  let F0 := liftSeries (reciprocal B0.trace B0.det)
  let F1 := liftSeries (reciprocal B1.trace B1.det)
  calc
    _ = (numerator B0 * F0) * (numerator B1 * F1) := by rw [powerTail_eq, powerTail_eq]
    _ = numerator B0 * ((F0 * numerator B1) * F1) := by simp only [mul_assoc]
    _ = numerator B0 * ((numerator B1 * F0) * F1) := by
      rw [(lift_commute_numerator (reciprocal B0.trace B0.det) B1).eq]
    _ = _ := by simp only [completeSeries, map_mul, F0, F1, mul_assoc]

private theorem coeff_const_mul_lift (n : ℕ) (A : BondMatrix R) (F : PowerSeries R) :
    coeff n (C A * liftSeries F) = coeff n F • A := by
  simp only [PowerSeries.coeff_C_mul, liftSeries, PowerSeries.coeff_map,
    Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one]

private theorem coeff_shiftedConst_mul_lift (n k : ℕ) (A : BondMatrix R)
    (F : PowerSeries R) :
    coeff n (X ^ k * C A * liftSeries F) = shiftedCoeff F n k • A := by
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', coeff_const_mul_lift, shiftedCoeff]
  split_ifs <;> simp

/-- Cayley–Hamilton applied to each side of the literal convolution.
Here `n = m-2`. The three coefficients come from a single scalar reciprocal. -/
theorem literalCross_eq (B0 B1 : BondMatrix R) (n : ℕ) :
    literalCross B0 B1 (n + 2) =
      B1 ^ (n + 2) + coeff n (completeSeries B0 B1) • (B0 * B1) -
        shiftedCoeff (completeSeries B0 B1) n 1 • (B1.det • B0 + B0.det • B1) +
        shiftedCoeff (completeSeries B0 B1) n 2 •
          ((B0.det * B1.det) • (1 : BondMatrix R)) := by
  have hsum : literalCross B0 B1 (n + 2) =
      coeff n (powerTail B0 * powerTail B1) + B1 ^ (n + 2) := by
    rw [literalCross, Finset.sum_range_succ', PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (powerTail B0) * coeff j (powerTail B1))]
    simp only [powerTail, PowerSeries.coeff_mk, pow_zero, Nat.sub_zero, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n + 2 - (i + 1) = n - i + 1 by omega]
  rw [hsum, powerTail_mul, numerator_mul, add_mul, sub_mul]
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_const_mul_lift,
    coeff_shiftedConst_mul_lift]
  abel

/-- The three bra features in the middle triplet row. The caller supplies the
scalar `half = 1/2` in its coefficient ring. -/
def tripletFeature (half : R) (B0 B1 : BondMatrix R) (i : Fin 3) : BondMatrix R :=
  ![B0 ^ 2, half • (B0 * B1 + B1 * B0), B1 ^ 2] i

/-- Trace readout on `(I, B0, B1)`. -/
def traceFeatures (half : R) (B0 B1 : BondMatrix R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => (tripletFeature half B0 B1 i * (![1, B0, B1] j)).trace

/-- The two rotation matrices and the literal transverse matrix, read on the
three bra features. -/
def middleTraceBlock (half : R) (B0 B1 : BondMatrix R) (m : ℕ) :
    Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j =>
    (tripletFeature half B0 B1 i * (![B0 ^ m, B1 ^ m, literalCross B0 B1 m] j)).trace

private theorem power_eq (M : BondMatrix R) (n : ℕ) :
    M ^ (n + 2) =
      coeff (n + 1) (reciprocal M.trace M.det) • M -
        (M.det * coeff n (reciprocal M.trace M.det)) • (1 : BondMatrix R) := by
  have h := congrArg (fun F : PowerSeries (BondMatrix R) => coeff (n + 1) F)
    (powerTail_eq M)
  simpa only [powerTail, PowerSeries.coeff_mk, numerator, sub_mul, LinearMap.map_sub,
    coeff_const_mul_lift, coeff_shiftedConst_mul_lift, shiftedCoeff_succ, shiftedCoeff_zero,
    smul_smul, mul_comm (M.det)] using h

private def middleCoordinates (B0 B1 : BondMatrix R) (n : ℕ) :
    Matrix (Fin 3) (Fin 3) R :=
  let F := completeSeries B0 B1
  let P := B0.det
  let Q := B1.det
  let a := reciprocal B0.trace P
  let b := reciprocal B1.trace Q
  !![-(P * coeff n a), -(Q * coeff n b),
       -(Q * coeff n b) + P * Q * shiftedCoeff F n 2;
     coeff (n + 1) a, 0, -(Q * shiftedCoeff F n 1);
     0, coeff (n + 1) b, coeff (n + 1) b - P * shiftedCoeff F n 1]

private theorem middleTraceBlock_eq_mul (half : R) (B0 B1 : BondMatrix R) (n : ℕ)
    (hzero : coeff n (completeSeries B0 B1) = 0) :
    middleTraceBlock half B0 B1 (n + 2) =
      traceFeatures half B0 B1 * middleCoordinates B0 B1 n := by
  have hcross : literalCross B0 B1 (n + 2) =
      (-(B1.det * coeff n (reciprocal B1.trace B1.det)) +
          B0.det * B1.det * shiftedCoeff (completeSeries B0 B1) n 2) • (1 : BondMatrix R) +
        (-(B1.det * shiftedCoeff (completeSeries B0 B1) n 1)) • B0 +
        (coeff (n + 1) (reciprocal B1.trace B1.det) -
          B0.det * shiftedCoeff (completeSeries B0 B1) n 1) • B1 := by
    rw [literalCross_eq, hzero, zero_smul, add_zero, power_eq B1]
    module
  ext i j
  revert j
  rw [Fin.forall_fin_succ, Fin.forall_fin_two]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, middleTraceBlock, traceFeatures,
      middleCoordinates, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hcross, power_eq B0 n, power_eq B1 n, mul_add, mul_sub,
      Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      mul_one, mul_zero, add_zero] <;> ring

/-- `J_m` from the middle witness, with `m = n+2` and the negative-index
complete homogeneous functions set to zero. -/
def middleFactor (B0 B1 : BondMatrix R) (n : ℕ) : R :=
  let F := completeSeries B0 B1
  shiftedCoeff F n 1 ^ 2 * coeff (n + 2) F +
    coeff (n + 1) F ^ 2 * shiftedCoeff F n 2

private theorem middleCoordinates_det (B0 B1 : BondMatrix R) (n : ℕ)
    (hzero : coeff n (completeSeries B0 B1) = 0) :
    (middleCoordinates B0 B1 n).det = (B0.det * B1.det) * middleFactor B0 B1 n := by
  let F := completeSeries B0 B1
  let a := B0.trace
  let b := B1.trace
  let P := B0.det
  let Q := B1.det
  change coeff n F = 0 at hzero
  have hrec : quadratic a P * (quadratic b Q * F) = 1 := by
    dsimp only [a, b, P, Q, F]
    rw [quadraticRight_mul_complete, quadratic_mul_reciprocal]
  have hnext : coeff (n + 2) F =
      (a + b) * coeff (n + 1) F + (P * b + Q * a) * shiftedCoeff F n 1 -
        P * Q * shiftedCoeff F n 2 := by
    have h := congrArg (fun G : PowerSeries R => coeff (n + 2) G) hrec
    have hn : n + 2 ≠ 0 := by omega
    simp only [coeff_quadratic_mul, shiftedCoeff_succ, shiftedCoeff_zero,
      PowerSeries.coeff_one, hn, ite_false, hzero] at h
    linear_combination h
  have ha := quadraticRight_mul_complete B0 B1
  have hb := quadraticLeft_mul_complete B0 B1
  change quadratic b Q * F = reciprocal a P at ha
  change quadratic a P * F = reciprocal b Q at hb
  unfold middleCoordinates middleFactor
  change Matrix.det !![-(P * coeff n (reciprocal a P)), -(Q * coeff n (reciprocal b Q)),
      -(Q * coeff n (reciprocal b Q)) + P * Q * shiftedCoeff F n 2;
      coeff (n + 1) (reciprocal a P), 0, -(Q * shiftedCoeff F n 1);
      0, coeff (n + 1) (reciprocal b Q),
        coeff (n + 1) (reciprocal b Q) - P * shiftedCoeff F n 1] =
    (P * Q) * (shiftedCoeff F n 1 ^ 2 * coeff (n + 2) F +
      coeff (n + 1) F ^ 2 * shiftedCoeff F n 2)
  rw [← ha, ← hb, Matrix.det_fin_three, hnext]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, coeff_quadratic_mul, shiftedCoeff_succ,
    shiftedCoeff_zero, hzero]
  ring

/-- The middle trace determinant on the zero locus of `H_(m-2)`.
In a spectral quotient this is the determinant congruence of the literal
columns. All three columns are built from actual matrix powers. -/
theorem middleTraceBlock_det_of_h_zero (half : R) (B0 B1 : BondMatrix R) (n : ℕ)
    (hzero : coeff n (completeSeries B0 B1) = 0) :
    (middleTraceBlock half B0 B1 (n + 2)).det =
      (traceFeatures half B0 B1).det * (B0.det * B1.det) * middleFactor B0 B1 n := by
  rw [middleTraceBlock_eq_mul half B0 B1 n hzero, Matrix.det_mul,
    middleCoordinates_det B0 B1 n hzero]
  exact (mul_assoc (traceFeatures half B0 B1).det (B0.det * B1.det) (middleFactor B0 B1 n)).symm

private theorem coe_charpolyRev_eq_quadratic (B : BondMatrix R) :
    (B.charpolyRev : PowerSeries R) = quadratic B.trace B.det := by
  have h : B.charpolyRev =
      1 - Polynomial.X * Polynomial.C B.trace + Polynomial.X ^ 2 * Polynomial.C B.det := by
    rw [Matrix.charpolyRev, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, map_add, map_sub, map_mul]; ring
  rw [h]
  simp only [quadratic, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow, Polynomial.coe_one, pow_one]

private theorem sectionTransfer_charpolyRev (B0 B1 : BondMatrix R) :
    (sectionTransfer B0 B1).charpolyRev = B0.charpolyRev * B1.charpolyRev := by
  have h : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (Polynomial R)) -
        (Polynomial.X : Polynomial R) • (sectionTransfer B0 B1).map Polynomial.C =
      Matrix.fromBlocks (1 - (Polynomial.X : Polynomial R) • B0.map Polynomial.C)
        (-((Polynomial.X : Polynomial R) • B1.map Polynomial.C)) 0
        (1 - (Polynomial.X : Polynomial R) • B1.map Polynomial.C) := by
    ext (i | i) (j | j) <;>
      simp [sectionTransfer, Matrix.fromBlocks, Matrix.one_apply, Matrix.map_apply]
  unfold Matrix.charpolyRev
  rw [h, Matrix.det_fromBlocks_zero₂₁]

/-- This is the same characteristic reciprocal used in the antisymmetric
transfer readout, with the transfer indexed in ket blocks. -/
theorem completeSeries_eq_transferReciprocal (B0 B1 : BondMatrix R) :
    completeSeries B0 B1 =
      PowerSeries.invOfUnit ((sectionTransfer B0 B1).charpolyRev : PowerSeries R) 1 := by
  rw [sectionTransfer_charpolyRev, Polynomial.coe_mul, coe_charpolyRev_eq_quadratic,
    coe_charpolyRev_eq_quadratic]
  let D := quadratic B0.trace B0.det * quadratic B1.trace B1.det
  change completeSeries B0 B1 = PowerSeries.invOfUnit D 1
  have hD : PowerSeries.constantCoeff D = ((1 : Rˣ) : R) := by simp [D, quadratic]
  have h : D * completeSeries B0 B1 = 1 := by
    dsimp only [D]
    rw [mul_assoc, quadraticRight_mul_complete, quadratic_mul_reciprocal]
  calc
    completeSeries B0 B1 = 1 * completeSeries B0 B1 := (one_mul _).symm
    _ = (PowerSeries.invOfUnit D 1 * D) * completeSeries B0 B1 := by
      rw [PowerSeries.invOfUnit_mul D 1 hD]
    _ = PowerSeries.invOfUnit D 1 := by rw [mul_assoc, h, mul_one]

/-- The bra matrices on the paired spectral section. -/
def sectionB0 (r s : R) : BondMatrix R := !![r, 0; 0, s]

def sectionB1 (t u p : R) : BondMatrix R := !![p, 1; -((p - t) * (p - u)), t + u - p]

private theorem sectionB0_det (r s : R) : (sectionB0 r s).det = r * s := by
  simp [sectionB0]

private theorem sectionB1_det (t u p : R) : (sectionB1 t u p).det = t * u := by
  simp [sectionB1]; ring

private theorem quadratic_eq_rootFactors (r s : R) :
    quadratic (r + s) (r * s) =
      (1 - X * C r) * (1 - X * C s) := by
  simp only [quadratic, pow_one, map_add, map_mul]
  ring

/-- The four spectral factors identify the same series as the complete
homogeneous generating series in the four roots. -/
theorem section_rootFactors_mul_completeSeries (r s t u p : R) :
    ((1 - X * C r) * (1 - X * C s)) * ((1 - X * C t) * (1 - X * C u)) *
        completeSeries (sectionB0 r s) (sectionB1 t u p) = 1 := by
  have h0 : (sectionB0 r s).trace = r + s := by simp [sectionB0]
  have h1 : (sectionB1 t u p).trace = t + u := by simp [sectionB1]
  rw [← quadratic_eq_rootFactors, ← quadratic_eq_rootFactors,
    ← h0, ← h1, ← sectionB0_det r s, ← sectionB1_det t u p, mul_assoc,
    quadraticRight_mul_complete, quadratic_mul_reciprocal]

/-- The determinant of the literal middle columns at the paired section. -/
theorem section_middleTraceBlock_det (half r s t u p : R) (n : ℕ)
    (hzero : coeff n (completeSeries (sectionB0 r s) (sectionB1 t u p)) = 0) :
    let B0 := sectionB0 r s
    let B1 := sectionB1 t u p
    (middleTraceBlock half B0 B1 (n + 2)).det =
      (traceFeatures half B0 B1).det * (r * s * (t * u)) * middleFactor B0 B1 n := by
  dsimp only
  rw [middleTraceBlock_det_of_h_zero half _ _ n hzero, sectionB0_det, sectionB1_det]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalMiddle
