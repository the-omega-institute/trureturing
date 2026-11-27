/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Weighted and boundary formulas for the outer section. -/
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import D5.S3.Geometry.FlatlandImageAlgebra

/-!
The reducible section has spectral variables `r,s,t,u` and the free variable
`q = (p-u)/(t-u)`. On `t ≠ u` this change adds multiples of the `p` column
to the root columns and multiplies the `p` column by `t-u`.
The polynomial expressions below extend the resulting matrix to all roots.
The row and column orders follow `uniform-vertical-pairing-grading/replay.py`.
-/

noncomputable section

set_option autoImplicit false

open MvPolynomial
open scoped BigOperators Matrix

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSection

variable {R : Type*} [CommRing R]

local notation "P" => MvPolynomial (Fin 5) R
local notation "r" => (X (0 : Fin 5) : P)
local notation "s" => (X (1 : Fin 5) : P)
local notation "t" => (X (2 : Fin 5) : P)
local notation "u" => (X (3 : Fin 5) : P)
local notation "q" => (X (4 : Fin 5) : P)

private def sectionP : P := u + (t - u) * q
private def thetaT : P := r * q + s * (1 - q)
private def thetaU : P := r * (1 - q) + s * q

/-- The six outer observations of the reducible section with literal spectral weights. -/
def outerRows (m : ℕ) : Fin 6 → P :=
  ![r ^ m * r ^ 2 + s ^ m * s ^ 2,
    r ^ m * (r * sectionP) + s ^ m * (s * ((t + u) - sectionP)),
    r ^ m * ((t + u) * sectionP - t * u) +
      s ^ m * ((t + u) * ((t + u) - sectionP) - t * u),
    t ^ m * ((r + s) * thetaT - r * s) + u ^ m * ((r + s) * thetaU - r * s),
    t ^ m * (t * thetaT) + u ^ m * (u * thetaU),
    t ^ m * t ^ 2 + u ^ m * u ^ 2]

private def rotation : Fin 6 → ℤ := ![0, 2, 4, -4, -2, 0]

/-- The outer block with ordinary root derivatives at fixed `q`, the `q` derivative,
and the physical diagonal rotation. -/
def outerDividedMatrix (m : ℕ) : Matrix (Fin 6) (Fin 6) P :=
  Matrix.of fun i =>
    ![pderiv (0 : Fin 5) (outerRows m i), pderiv (1 : Fin 5) (outerRows m i),
      pderiv (2 : Fin 5) (outerRows m i), pderiv (3 : Fin 5) (outerRows m i),
      pderiv (4 : Fin 5) (outerRows m i), C (rotation i : R) * outerRows m i]

/-- The polynomial determinant after removing the four logarithmic root factors. -/
def outerDividedDet (m : ℕ) : P := (outerDividedMatrix m).det

private def rootColumnFactor : Fin 6 → P := ![r, s, t, u, 1, 1]

/-- The outer block with logarithmic root derivatives at fixed `q`. -/
def outerLogMatrix (m : ℕ) : Matrix (Fin 6) (Fin 6) P :=
  Matrix.of fun i j => rootColumnFactor j * outerDividedMatrix m i j

theorem outerLogMatrix_det (m : ℕ) :
    (outerLogMatrix m : Matrix (Fin 6) (Fin 6) P).det =
      (r * s * t * u) * outerDividedDet m := by
  rw [outerLogMatrix, Matrix.det_mul_row, outerDividedDet]
  simp [rootColumnFactor, Fin.prod_univ_succ, mul_assoc]

private def rootWeight (a b : ℕ) : Fin 5 → ℕ := ![a, a, b, b, 0]

/-- The indicators of the root pairs `(r,s)` and `(t,u)`, in that order. -/
def pairWeight : Fin 2 → Fin 5 → ℕ := ![rootWeight 1 0, rootWeight 0 1]

private def rowDegree (a b m : ℕ) : Fin 6 → ℕ :=
  ![m * a + (a + a), m * a + (a + b), m * a + (b + b),
    m * b + (a + a), m * b + (b + a), m * b + (b + b)]

private theorem outerRows_isWeightedHomogeneous (a b m : ℕ) (i : Fin 6) :
    (outerRows (R := R) m i).IsWeightedHomogeneous (rootWeight a b) (rowDegree a b m i) := by
  let w := rootWeight a b
  have hr : (r).IsWeightedHomogeneous w a := isWeightedHomogeneous_X R w _
  have hs : (s).IsWeightedHomogeneous w a := isWeightedHomogeneous_X R w _
  have ht : (t).IsWeightedHomogeneous w b := isWeightedHomogeneous_X R w _
  have hu : (u).IsWeightedHomogeneous w b := isWeightedHomogeneous_X R w _
  have hq : (q).IsWeightedHomogeneous w 0 := isWeightedHomogeneous_X R w _
  have hqc : (1 - q).IsWeightedHomogeneous w 0 := (isWeightedHomogeneous_one R w).sub hq
  have hshift : ((t - u) * q).IsWeightedHomogeneous w b := by
    simpa only [add_zero] using (ht.sub hu).mul hq
  have hp : (sectionP (R := R)).IsWeightedHomogeneous w b := hu.add hshift
  have hp' := (ht.add hu).sub hp
  have hθt : (thetaT (R := R)).IsWeightedHomogeneous w a := by
    have h₁ : (r * q).IsWeightedHomogeneous w a := by
      simpa only [add_zero] using hr.mul hq
    have h₂ : (s * (1 - q)).IsWeightedHomogeneous w a := by
      simpa only [add_zero] using hs.mul hqc
    exact h₁.add h₂
  have hθu : (thetaU (R := R)).IsWeightedHomogeneous w a := by
    have h₁ : (r * (1 - q)).IsWeightedHomogeneous w a := by
      simpa only [add_zero] using hr.mul hqc
    have h₂ : (s * q).IsWeightedHomogeneous w a := by
      simpa only [add_zero] using hs.mul hq
    exact h₁.add h₂
  have hrm : (r ^ m).IsWeightedHomogeneous w (m * a) := by
    simpa only [Nat.nsmul_eq_mul] using hr.pow m
  have hsm : (s ^ m).IsWeightedHomogeneous w (m * a) := by
    simpa only [Nat.nsmul_eq_mul] using hs.pow m
  have htm : (t ^ m).IsWeightedHomogeneous w (m * b) := by
    simpa only [Nat.nsmul_eq_mul] using ht.pow m
  have hum : (u ^ m).IsWeightedHomogeneous w (m * b) := by
    simpa only [Nat.nsmul_eq_mul] using hu.pow m
  fin_cases i
  · change (r ^ m * r ^ 2 + s ^ m * s ^ 2).IsWeightedHomogeneous w (m * a + (a + a))
    simpa only [pow_two] using (hrm.mul (hr.mul hr)).add (hsm.mul (hs.mul hs))
  · exact (hrm.mul (hr.mul hp)).add (hsm.mul (hs.mul hp'))
  · exact (hrm.mul (((ht.add hu).mul hp).sub (ht.mul hu))).add
      (hsm.mul (((ht.add hu).mul hp').sub (ht.mul hu)))
  · exact (htm.mul (((hr.add hs).mul hθt).sub (hr.mul hs))).add
      (hum.mul (((hr.add hs).mul hθu).sub (hr.mul hs)))
  · exact (htm.mul (ht.mul hθt)).add (hum.mul (hu.mul hθu))
  · change (t ^ m * t ^ 2 + u ^ m * u ^ 2).IsWeightedHomogeneous w (m * b + (b + b))
    simpa only [pow_two] using (htm.mul (ht.mul ht)).add (hum.mul (hu.mul hu))

private theorem weighted_logDerivative {w : Fin 5 → ℕ} {d : ℕ} {f : P}
    (h : f.IsWeightedHomogeneous w d) (i : Fin 5) :
    (X i * pderiv i f).IsWeightedHomogeneous w d := by
  by_cases hi : w i ≤ d
  · have hdeg : w i + (d - w i) = d := by omega
    simpa only [hdeg] using
      (isWeightedHomogeneous_X (R := R) w i).mul (h.pderiv (i := i) (Nat.sub_add_cancel hi))
  · have hzero : pderiv i f = 0 := by
      ext e
      rw [coeff_pderiv]
      have hweight : Finsupp.weight w (e + Finsupp.single i 1) =
          Finsupp.weight w e + w i := by
        simp [Finsupp.weight_single]
      have he : Finsupp.weight w (e + Finsupp.single i 1) ≠ d := by
        rw [hweight]
        omega
      simp [h.coeff_eq_zero _ he]
    rw [hzero, mul_zero]
    exact isWeightedHomogeneous_zero R w d

private theorem outerLogMatrix_isWeightedHomogeneous (a b m : ℕ) (i j : Fin 6) :
    (outerLogMatrix (R := R) m i j).IsWeightedHomogeneous (rootWeight a b)
      (rowDegree a b m i) := by
  have h := outerRows_isWeightedHomogeneous (R := R) a b m i
  fin_cases j
  · exact weighted_logDerivative h 0
  · exact weighted_logDerivative h 1
  · exact weighted_logDerivative h 2
  · exact weighted_logDerivative h 3
  · change (1 * pderiv (4 : Fin 5) (outerRows m i)).IsWeightedHomogeneous _ _
    rw [one_mul]
    exact h.pderiv (i := 4) (Nat.add_zero _)
  · change (1 * (C (rotation i : R) * outerRows m i)).IsWeightedHomogeneous _ _
    rw [one_mul]
    exact h.C_mul _

private theorem outerLogMatrix_det_isWeightedHomogeneous (m : ℕ) (pair : Fin 2) :
    (outerLogMatrix (R := R) m).det.IsWeightedHomogeneous (pairWeight pair) (3 * m + 6) := by
  fin_cases pair
  · have hsum : (∑ i : Fin 6, rowDegree 1 0 m i) = 3 * m + 6 := by
      simp [rowDegree, Fin.sum_univ_succ]; omega
    rw [← hsum]
    exact D5.S3.Geometry.FlatlandImageAlgebra.homogeneous_determinant
      (rootWeight 1 0) _ _ (outerLogMatrix_isWeightedHomogeneous 1 0 m)
  · have hsum : (∑ i : Fin 6, rowDegree 0 1 m i) = 3 * m + 6 := by
      simp [rowDegree, Fin.sum_univ_succ]; omega
    rw [← hsum]
    exact D5.S3.Geometry.FlatlandImageAlgebra.homogeneous_determinant
      (rootWeight 0 1) _ _ (outerLogMatrix_isWeightedHomogeneous 0 1 m)

private def rootExponent : Fin 5 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1

private theorem rootProduct_monomial :
    r * s * t * u = monomial rootExponent (1 : R) := by
  simp [X, rootExponent, monomial_mul_monomial]

/-- Each pairing indicator sees degree `3*m+4` in the divided determinant. -/
theorem outerDividedDet_isWeightedHomogeneous (m : ℕ) (pair : Fin 2) :
    (outerDividedDet (R := R) m).IsWeightedHomogeneous (pairWeight pair) (3 * m + 4) := by
  have h := outerLogMatrix_det_isWeightedHomogeneous (R := R) m pair
  rw [outerLogMatrix_det, rootProduct_monomial] at h
  intro e he
  have hp : (monomial rootExponent (1 : R) * outerDividedDet m).coeff
      (rootExponent + e) ≠ 0 := by
    simpa only [coeff_monomial_mul, one_mul] using he
  have hdeg := h hp
  have hroot : Finsupp.weight (pairWeight pair) rootExponent = 2 := by
    simp only [rootExponent, map_add, Finsupp.weight_single, one_nsmul]
    fin_cases pair <;> rfl
  rw [map_add, hroot] at hdeg
  omega

section Boundary

variable {A : Type*} [CommRing A]

-- At s = u = 0, remove r^(m-1) from each top row and t^(m-1) from each bottom row.
private def boundaryRowFactor (m : ℕ) (x y : A) : Fin 6 → A :=
  ![x ^ (m - 1), x ^ (m - 1), x ^ (m - 1), y ^ (m - 1), y ^ (m - 1), y ^ (m - 1)]

private def boundaryCore (n x y z : A) : Matrix (Fin 6) (Fin 6) A :=
  !![(n + 2) * x ^ 2, 0, 0, 0, 0, 0;
     (n + 1) * z * x * y, 0, z * x ^ 2, -(z - 1) * x ^ 2, x ^ 2 * y, 2 * z * x ^ 2 * y;
     n * z * y ^ 2, 0, 2 * z * x * y, 0, x * y ^ 2, 4 * z * x * y ^ 2;
     2 * z * x * y, 0, n * z * x ^ 2, 0, x ^ 2 * y, -4 * z * x ^ 2 * y;
     z * y ^ 2, -(z - 1) * y ^ 2, (n + 1) * z * x * y, 0, x * y ^ 2, -2 * z * x * y ^ 2;
     0, 0, (n + 2) * y ^ 2, 0, 0, 0]

set_option maxHeartbeats 600000 in
private theorem boundaryMatrix [Algebra R A] (m : ℕ) (hm : 3 ≤ m) (x y z : A) :
    (aeval ![x, 0, y, 0, z] : P →ₐ[R] A).mapMatrix (outerDividedMatrix m) =
      Matrix.of (fun i j => boundaryRowFactor m x y i * boundaryCore (m : A) x y z i j) := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  have hsplit : m = (m - 1) + 1 := by omega
  have hpow (v : A) : v ^ m = v ^ (m - 1) * v :=
    (congrArg (fun k : ℕ => v ^ k) hsplit).trans (pow_succ v _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, outerDividedMatrix, outerRows, sectionP,
      thetaT, thetaU, rotation, zero_pow hm0, zero_pow hm1, hpow x, hpow y, boundaryRowFactor, boundaryCore] <;>
    ring

private theorem boundaryCore_det (n x y z : A) :
    (boundaryCore n x y z).det = -8 * (n + 2) ^ 2 * x ^ 7 * y ^ 7 * z * (z - 1) ^ 2 := by
  let tail : Matrix (Fin 5) (Fin 5) A :=
    (boundaryCore n x y z).submatrix Fin.succ (0 : Fin 6).succAbove
  have hfirst : (boundaryCore n x y z).det = ((n + 2) * x ^ 2) * tail.det := by
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (0 : Fin 6)]
    · simp [boundaryCore, tail]
    · intro j _ hj
      have hz : boundaryCore n x y z 0 j = 0 := by
        fin_cases j <;> first | exact (hj rfl).elim | rfl
      rw [hz, mul_zero, zero_mul]
    · simp
  have hlast : tail.det =
      -((n + 2) * y ^ 2) * (tail.submatrix (4 : Fin 5).succAbove (1 : Fin 5).succAbove).det := by
    rw [Matrix.det_succ_row tail (4 : Fin 5), Finset.sum_eq_single (1 : Fin 5)]
    · have hentry : tail 4 1 = (n + 2) * y ^ 2 := rfl
      rw [hentry]
      have hsign : (-1 : A) ^ ((4 : Fin 5).val + (1 : Fin 5).val) = -1 := by norm_num
      rw [hsign, neg_one_mul]
    · intro j _ hj
      have hz : tail 4 j = 0 := by
        fin_cases j <;> first | exact (hj rfl).elim | rfl
      rw [hz, mul_zero, zero_mul]
    · simp
  have hminor : tail.submatrix (4 : Fin 5).succAbove (1 : Fin 5).succAbove =
      !![0, -(z - 1) * x ^ 2, x ^ 2 * y, 2 * z * x ^ 2 * y;
         0, 0, x * y ^ 2, 4 * z * x * y ^ 2;
         0, 0, x ^ 2 * y, -4 * z * x ^ 2 * y;
         -(z - 1) * y ^ 2, 0, x * y ^ 2, -2 * z * x * y ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hfirst, hlast, hminor]
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_succ, Fin.succAbove]; ring

/-- Specialization at `s=u=0`. Taking the remaining values as indeterminates
in an `R`-algebra gives the polynomial boundary identity. -/
theorem outerDividedDet_boundary [Algebra R A] (m : ℕ) (hm : 3 ≤ m) (x y z : A) :
    aeval ![x, 0, y, 0, z] (outerDividedDet (R := R) m) =
      -8 * ((m : A) + 2) ^ 2 * (x * y) ^ (3 * m + 4) * z * (z - 1) ^ 2 := by
  rw [outerDividedDet, AlgHom.map_det, boundaryMatrix m hm, Matrix.det_mul_column, boundaryCore_det]
  have hpow (v : A) : v ^ (m - 1) * v ^ (m - 1) * v ^ (m - 1) * v ^ 7 =
      v ^ (3 * m + 4) := by
    simp only [← pow_add]
    congr 1
    omega
  calc
    _ = (-8 * ((m : A) + 2) ^ 2 * z * (z - 1) ^ 2) *
        ((x ^ (m - 1) * x ^ (m - 1) * x ^ (m - 1) * x ^ 7) *
         (y ^ (m - 1) * y ^ (m - 1) * y ^ (m - 1) * y ^ 7)) := by
      simp [boundaryRowFactor, Fin.prod_univ_succ]; ring
    _ = _ := by rw [hpow x, hpow y, mul_pow]; ring

end Boundary

/-- Both pairing degrees are attained over a characteristic-zero field. -/
theorem outerDividedDet_weightedTotalDegree {K : Type*} [Field K] [CharZero K]
    (m : ℕ) (hm : 3 ≤ m) (pair : Fin 2) :
    (outerDividedDet (R := K) m).weightedTotalDegree (pairWeight pair) = 3 * m + 4 := by
  have hne : outerDividedDet (R := K) m ≠ 0 := by
    intro h
    have hboundary := outerDividedDet_boundary (R := K) m hm (1 : K) 1 2
    rw [h, map_zero] at hboundary
    have hmcast : (m : K) + 2 ≠ 0 := by
      exact_mod_cast (show m + 2 ≠ 0 by omega)
    have hvalue : (-8 : K) * ((m : K) + 2) ^ 2 * 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hmcast)) (by norm_num)
    apply hvalue
    simpa only [mul_one, one_pow, show (2 : K) - 1 = 1 by norm_num] using hboundary.symm
  have hdeg := (outerDividedDet_isWeightedHomogeneous (R := K) m pair).weighted_total_degree hne
  rw [weightedTotalDegree_coe _ _ hne] at hdeg
  exact WithBot.coe_inj.mp hdeg

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSection
