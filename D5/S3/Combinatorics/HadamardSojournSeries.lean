/- GID: D5/S3/Combinatorics/HadamardSojournSeries
   generality: G
   mirror-B: none(waiver:covered-by-hadamard-sojourn-rigidity-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The positive-sojourn recurrence for the Hadamard sign coin has a formal-series solution obtained from half-line Catalan transfers. -/

module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
Omega original.

The positive-sojourn recurrence for the Hadamard sign coin has a formal-series
solution obtained from half-line Catalan transfers. The series degree records
elapsed time and the coefficient polynomial records positive intervals.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Omega.HadamardSojournSeries

open scoped Matrix BigOperators

private abbrev Poly := Polynomial ℂ
private abbrev Series := PowerSeries Poly
private abbrev SeriesMatrix := Matrix (Fin 2) (Fin 2) Series

private def intervalMark (x : ℤ) (b : Bool) : Poly :=
  if 0 < x ∨ (x = 0 ∧ b = true) then Polynomial.X else 1

private def tvar : Series := PowerSeries.C Polynomial.X

private def zvar : Series := PowerSeries.X

private def uniformMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; -1, 1]

private def seriesHalf : Series :=
  PowerSeries.C (Polynomial.C (1 / 2 : ℂ))

-- The half-line excursions use the alternating Catalan series at degrees divisible by four.
private def catalanBase : Series :=
  PowerSeries.subst (PowerSeries.X ^ 4 : Series)
    (PowerSeries.rescale (-1) (PowerSeries.catalanSeries.map (Nat.castRingHom Poly)))

private def markedStep (a : Poly) : Series := PowerSeries.C a * PowerSeries.X

private def catalanAt (a : Poly) : Series := PowerSeries.rescale a catalanBase

private lemma catalanBase_eq :
    catalanBase + (PowerSeries.X : Series) ^ 4 * catalanBase ^ 2 = 1 := by
  let S := PowerSeries.catalanSeries.map (Nat.castRingHom Poly)
  have hS : S ^ 2 * PowerSeries.X + 1 = S := by
    simpa only [S, map_add, map_mul, map_one, map_pow, PowerSeries.map_X] using
      congrArg (PowerSeries.map (Nat.castRingHom Poly)) PowerSeries.catalanSeries_sq_mul_X_add_one
  have hR : (PowerSeries.rescale (-1) S) ^ 2 * (-PowerSeries.X) + 1 =
      PowerSeries.rescale (-1) S := by
    simpa only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_neg_one_X] using
      congrArg (PowerSeries.rescale (-1 : Poly)) hS
  have hs : PowerSeries.HasSubst ((PowerSeries.X : Series) ^ 4) :=
    PowerSeries.HasSubst.X_pow (by decide : 4 ≠ 0)
  let ev := PowerSeries.substAlgHom (R := Poly) hs
  have he := congrArg ev hR
  simp only [map_add, map_mul, map_one, map_pow, map_neg] at he
  have hev : ev PowerSeries.X = (PowerSeries.X : Series) ^ 4 := by
    exact PowerSeries.substAlgHom_X (R := Poly) hs
  rw [hev] at he
  simp only [ev, PowerSeries.coe_substAlgHom, S] at he
  have he' : catalanBase ^ 2 * (-(PowerSeries.X : Series) ^ 4) + 1 = catalanBase := he
  linear_combination -he'

private lemma catalanAt_eq (a : Poly) :
    catalanAt a + (markedStep a) ^ 4 * (catalanAt a) ^ 2 = 1 := by
  simpa only [catalanAt, markedStep, map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X] using
    congrArg (PowerSeries.rescale a) catalanBase_eq

private lemma coeff_catalanAt (a : Poly) (n : ℕ) :
    PowerSeries.coeff n (catalanAt a) =
      if 4 ∣ n then a ^ n * (-1 : Poly) ^ (n / 4) * (catalan (n / 4) : Poly) else 0 := by
  rw [catalanAt, PowerSeries.coeff_rescale, catalanBase, PowerSeries.coeff_subst_X_pow (by decide)]
  split <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff,
    mul_assoc]

private def leftStepSeries : SeriesMatrix := !![1, 1; 0, 0]
private def rightStepSeries : SeriesMatrix := !![0, 0; 1, -1]

private def positiveTransfer (x C : Series) : SeriesMatrix :=
  !![x + x ^ 3 * C, x - x ^ 3 * C; 0, 0]

private def negativeTransfer (x C : Series) : SeriesMatrix :=
  !![0, 0; x - x ^ 3 * C, -(x + x ^ 3 * C)]

private lemma positiveTransfer_eq (x C : Series) (h : C + x ^ 4 * C ^ 2 = 1) :
    positiveTransfer x C = x • (leftStepSeries + (positiveTransfer x C) ^ 2 * rightStepSeries) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveTransfer, leftStepSeries, rightStepSeries, pow_two] <;>
    first | linear_combination x ^ 3 * h | linear_combination -(x ^ 3) * h

private lemma negativeTransfer_eq (x C : Series) (h : C + x ^ 4 * C ^ 2 = 1) :
    negativeTransfer x C = x • (rightStepSeries + (negativeTransfer x C) ^ 2 * leftStepSeries) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [negativeTransfer, leftStepSeries, rightStepSeries, pow_two] <;>
    first | linear_combination x ^ 3 * h | linear_combination -(x ^ 3) * h

private def boundaryKernel (f g : Series) : SeriesMatrix := !![1-f, f; -g, 1-g]

private lemma boundaryKernel_eq (x y C D : Series) :
    boundaryKernel (x ^ 2 - x ^ 4 * C) (y ^ 2 - y ^ 4 * D) =
      1 - x • (positiveTransfer x C * rightStepSeries) -
        y • (negativeTransfer y D * leftStepSeries) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [boundaryKernel, positiveTransfer, negativeTransfer, leftStepSeries, rightStepSeries] <;> ring

private def boundaryInverse (h k J : Series) : SeriesMatrix :=
  J • !![1+k, h-1; 1-k, 1+h]

private lemma boundaryInverse_eq (h k J f g : Series)
    (hf : h = 1 - 2 * f) (hg : k = 1 - 2 * g) (hJ : (1 + h * k) * J = 1) :
    boundaryInverse h k J * boundaryKernel f g = 1 := by
  subst h
  subst k
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [boundaryInverse, boundaryKernel, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hJ | ring

private lemma rescale_boundary_algebra (h k H K J L b : Series)
    (hH : h * H = 1) (hK : k * K = 1)
    (hJ : (1 + h * k) * J = 1) (hL : (1 + H * K) * L = 1)
    (hb : k * (1 - h ^ 2) = b * h * (1 - k ^ 2)) :
    (1 - b) • (boundaryInverse h k J + boundaryInverse H K L - (2 : SeriesMatrix)) =
      (h - b * k - (1 - b)) • (uniformMatrix.map (PowerSeries.C.comp Polynomial.C)) := by
  have hKJ : L = h * k * J := by
    have hproduct : (1 + H * K) * (h * k) = 1 + h * k := by
      calc
        _ = h * k + (h * H) * (k * K) := by ring
        _ = _ := by rw [hH, hK]; ring
    calc
      L = L * ((1 + h * k) * J) := by rw [hJ, mul_one]
      _ = L * ((1 + H * K) * (h * k)) * J := by rw [hproduct]; ring
      _ = h * k * J := by rw [← mul_assoc L, mul_comm L, hL, one_mul]
  have hratio : (1 - b) * (h + k) * J = h - b * k := by
    have hp : (1 - b) * (h + k) = (h - b * k) * (1 + h * k) := by
      linear_combination hb
    rw [hp, mul_assoc, hJ, mul_one]
  have hs (h k H K J L : Series) (hH : h * H = 1) (hK : k * K = 1)
      (hJ : (1 + h * k) * J = 1) (hL : L = h * k * J) :
      boundaryInverse h k J + boundaryInverse H K L - (2 : SeriesMatrix) =
      ((h + k) * J - 1) • (uniformMatrix.map (PowerSeries.C.comp Polynomial.C)) := by
    subst L
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [boundaryInverse, uniformMatrix, Matrix.ofNat_apply]
    · linear_combination hJ + J * h * hK
    · linear_combination J * k * hH - hJ
    · linear_combination hJ - J * h * hK
    · linear_combination hJ + J * k * hH

  rw [hs h k H K J L hH hK hJ hKJ, smul_smul]
  have H : (1 - b) * ((h + k) * J - 1) = h - b * k - (1 - b) := by
    linear_combination hratio
  rw [H]

private def scalarH (a : Poly) : Series :=
  1 - 2 * ((markedStep a) ^ 2 - (markedStep a) ^ 4 * catalanAt a)

private lemma scalarH_unit (a : Poly) :
    scalarH a * (scalarH a + 4 * (markedStep a) ^ 2) = 1 := by
  unfold scalarH
  linear_combination 4 * (markedStep a) ^ 4 * (catalanAt_eq a)

private def boundaryDet (a b : Poly) : Series := (1 + scalarH a * scalarH b) * seriesHalf

private lemma constantCoeff_half : seriesHalf.constantCoeff = Polynomial.C (1 / 2 : ℂ) := by
  simp [seriesHalf]

private lemma constantCoeff_det (a b : Poly) :
    (boundaryDet a b).constantCoeff = 1 := by
  simp only [boundaryDet, scalarH, map_mul, map_add, map_sub, map_pow, map_one, map_ofNat,
    markedStep, PowerSeries.constantCoeff_X, mul_zero,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    zero_mul, sub_zero, mul_one, constantCoeff_half]
  have h : (2 : Poly) * Polynomial.C (1 / 2 : ℂ) = 1 := by
    rw [← map_ofNat Polynomial.C, ← map_mul]
    norm_num
  simpa only [one_add_one_eq_two] using h

private def boundaryScalar (a b : Poly) : Series :=
  seriesHalf * PowerSeries.invOfUnit (boundaryDet a b) 1

private lemma boundaryScalar_eq (a b : Poly) :
    (1 + scalarH a * scalarH b) * boundaryScalar a b = 1 := by
  rw [boundaryScalar, ← mul_assoc]
  exact PowerSeries.mul_invOfUnit (boundaryDet a b) 1 (constantCoeff_det a b)

private def positiveStepVar : Series := markedStep Polynomial.X

private lemma positiveStepVar_eq : positiveStepVar = zvar * tvar := by
  exact mul_comm _ _

private lemma markedStep_one : markedStep 1 = zvar := by simp [markedStep, zvar]

private def minusTransfer : SeriesMatrix := negativeTransfer zvar (catalanAt 1)
private def plusTransfer : SeriesMatrix := positiveTransfer positiveStepVar (catalanAt Polynomial.X)

private def boundary : SeriesMatrix :=
  boundaryInverse (scalarH Polynomial.X) (scalarH 1) (boundaryScalar Polynomial.X 1)

private lemma transportPower (D P Q : SeriesMatrix) (z : Series)
    (h : D = z • (P + D ^ 2 * Q)) (n : ℕ) :
    D ^ (n + 1) = z • (D ^ n * P + D ^ (n + 2) * Q) := by
  calc
    D ^ (n + 1) = D ^ n * D := pow_succ _ _
    _ = D ^ n * (z • (P + D ^ 2 * Q)) := congrArg (D ^ n * ·) h
    _ = _ := by rw [mul_smul_comm, mul_add, ← mul_assoc, ← pow_add]

private def halfLineExtension (B L R : SeriesMatrix) (x : ℤ) : SeriesMatrix :=
  match x with
  | .ofNat n => B * L ^ n
  | .negSucc n => B * R ^ (n + 1)

@[simp] private lemma halfLineExtension_zero (B L R : SeriesMatrix) :
    halfLineExtension B L R 0 = B := by
  change B * L ^ 0 = B
  rw [pow_zero, mul_one]

private lemma halfLineExtension_ofNat (B L R : SeriesMatrix) (n : ℕ) :
    halfLineExtension B L R (.ofNat n) = B * L ^ n := rfl

private lemma halfLineExtension_negSucc (B L R : SeriesMatrix) (n : ℕ) :
    halfLineExtension B L R (.negSucc n) = B * R ^ (n + 1) := rfl

private lemma model_origin :
    boundary = 1 + zvar • ((boundary * minusTransfer) * leftStepSeries) +
      positiveStepVar • ((boundary * plusTransfer) * rightStepSeries) := by
  have h := boundaryInverse_eq (scalarH Polynomial.X) (scalarH 1)
    (boundaryScalar Polynomial.X 1)
    (positiveStepVar ^ 2 - positiveStepVar ^ 4 * catalanAt Polynomial.X)
    (markedStep 1 ^ 2 - markedStep 1 ^ 4 * catalanAt 1) rfl rfl
    (boundaryScalar_eq _ _)
  have hh : boundary * boundaryKernel (positiveStepVar ^ 2 - positiveStepVar ^ 4 * catalanAt Polynomial.X)
      (markedStep 1 ^ 2 - markedStep 1 ^ 4 * catalanAt 1) = 1 := h
  rw [boundaryKernel_eq, markedStep_one, mul_sub, mul_sub, mul_one,
    mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc] at hh
  have hp : boundary - positiveStepVar • ((boundary * plusTransfer) * rightStepSeries) -
      zvar • ((boundary * minusTransfer) * leftStepSeries) = 1 := hh
  exact (sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp hp))

private lemma halfLineExtension_recursion (B L R P Q : SeriesMatrix) (Z : Series)
    (hL : L = (Z * PowerSeries.C Polynomial.X) • (P + L ^ 2 * Q))
    (hR : R = Z • (Q + R ^ 2 * P))
    (hB : B = 1 + Z • ((B * R) * P) +
      (Z * PowerSeries.C Polynomial.X) • ((B * L) * Q))
    (x : ℤ) :
    halfLineExtension B L R x = (if x = 0 then 1 else 0) +
      (Z * PowerSeries.C (intervalMark x false)) • (halfLineExtension B L R (x - 1) * P) +
      (Z * PowerSeries.C (intervalMark x true)) • (halfLineExtension B L R (x + 1) * Q) := by
  rcases x with n | n
  · cases n with
    | zero =>
      have hnat : Int.ofNat 0 = 0 := rfl
      rw [hnat, halfLineExtension_zero, show (0 : ℤ) - 1 = Int.negSucc 0 by decide,
        show (0 : ℤ) + 1 = Int.ofNat 1 by decide, halfLineExtension_negSucc, halfLineExtension_ofNat]
      rw [show intervalMark 0 false = 1 by rfl, show intervalMark 0 true = Polynomial.X by rfl]
      simpa only [↓reduceIte, map_one, mul_one, pow_one, Nat.zero_add] using hB
    | succ n =>
      have hl : (Int.ofNat (n + 1)) - 1 = Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hr : (Int.ofNat (n + 1)) + 1 = Int.ofNat (n + 2) := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hp : 0 < Int.ofNat (n + 1) := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hi (b : Bool) : intervalMark (Int.ofNat (n + 1)) b = Polynomial.X :=
        ite_eq_left (Or.inl hp)
      rw [hl, hr, halfLineExtension_ofNat, halfLineExtension_ofNat, halfLineExtension_ofNat,
        ite_eq_right hp.ne', hi false, hi true, zero_add]
      have h := congrArg (B * ·) (transportPower _ _ _ _ hL n)
      rw [mul_smul_comm, mul_add, smul_add, ← mul_assoc, ← mul_assoc] at h
      exact h
  · have hlt : Int.negSucc n < 0 := by omega
    have hl : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    have hi (b : Bool) : intervalMark (Int.negSucc n) b = 1 :=
      ite_eq_right (fun h => h.elim hlt.not_gt (fun he => hlt.ne he.1))
    have hr : halfLineExtension B L R (Int.negSucc n + 1) = B * R ^ n := by
      cases n with
      | zero =>
        rw [show Int.negSucc 0 + 1 = 0 by decide, halfLineExtension_zero, pow_zero, mul_one]
      | succ n =>
        rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by omega, halfLineExtension_negSucc]
    rw [halfLineExtension_negSucc, hl, halfLineExtension_negSucc, hr, hi false, hi true,
      ite_eq_right hlt.ne, zero_add, map_one, mul_one]
    have h := congrArg (B * ·) (transportPower _ _ _ _ hR n)
    rw [mul_smul_comm, mul_add, smul_add, ← mul_assoc, ← mul_assoc] at h
    exact h.trans (add_comm _ _)

private def imaginaryMark : Poly := Polynomial.C Complex.I

private lemma imaginaryMark_sq : imaginaryMark ^ 2 = -1 := by
  rw [imaginaryMark, ← map_pow, Complex.I_sq, map_neg, map_one]

private lemma imaginaryMark_fourth : imaginaryMark ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, imaginaryMark_sq]
  simp

private lemma rescale_catalanAt (a : Poly) :
    PowerSeries.rescale imaginaryMark (catalanAt a) = catalanAt a := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_rescale, coeff_catalanAt]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [pow_mul, imaginaryMark_fourth, one_pow, one_mul]
  · simp

private lemma rescale_markedStep_pow (a : Poly) (n : ℕ) :
    PowerSeries.rescale imaginaryMark (markedStep a ^ n) =
      PowerSeries.C (imaginaryMark ^ n) * markedStep a ^ n := by
  have hc : PowerSeries.rescale imaginaryMark (PowerSeries.C a) = PowerSeries.C a := by
    apply PowerSeries.ext
    intro k
    by_cases hk : k = 0 <;> simp [PowerSeries.coeff_C, hk]
  simp [markedStep, PowerSeries.rescale_X, hc, mul_pow, mul_left_comm]

private lemma rescale_scalarH (a : Poly) :
    PowerSeries.rescale imaginaryMark (scalarH a) =
      scalarH a + 4 * markedStep a ^ 2 := by
  unfold scalarH
  simp only [map_sub, map_mul, map_one, map_ofNat, rescale_markedStep_pow,
    imaginaryMark_sq, imaginaryMark_fourth, map_neg, map_one, one_mul, neg_one_mul,
    rescale_catalanAt]
  ring

-- Divide out the sojourn marker only after taking coefficients in the time variable.
private lemma boundary_even :
    (1 - tvar ^ 2) •
      (boundary + boundary.map (PowerSeries.rescale imaginaryMark) - (2 : SeriesMatrix)) =
      (2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
        tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1)) •
        uniformMatrix.map (PowerSeries.C.comp Polynomial.C) := by
  let h := scalarH Polynomial.X
  let k := scalarH 1
  let H := h + 4 * positiveStepVar ^ 2
  let K := k + 4 * markedStep 1 ^ 2
  let J := boundaryScalar Polynomial.X 1
  let L := PowerSeries.rescale imaginaryMark J
  have hmap : boundary.map (PowerSeries.rescale imaginaryMark) = boundaryInverse H K L := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [boundary, boundaryInverse, h, k, H, K, J, L, rescale_scalarH, positiveStepVar]
  have hL : (1 + H * K) * L = 1 := by
    simpa only [h, k, H, K, J, L, positiveStepVar, map_mul, map_add, map_one, rescale_scalarH]
      using congrArg (PowerSeries.rescale imaginaryMark) (boundaryScalar_eq Polynomial.X 1)
  have hpos : h * H = 1 := scalarH_unit Polynomial.X
  have hneg : k * K = 1 := scalarH_unit 1
  have hb : k * (1 - h ^ 2) = tvar ^ 2 * h * (1 - k ^ 2) := by
    change h * (h + 4 * positiveStepVar ^ 2) = 1 at hpos
    change k * (k + 4 * markedStep 1 ^ 2) = 1 at hneg
    rw [positiveStepVar_eq] at hpos
    rw [markedStep_one] at hneg
    linear_combination -(k * hpos) + tvar ^ 2 * h * hneg
  rw [hmap]
  have heven := rescale_boundary_algebra h k H K J L (tvar ^ 2) hpos hneg
    (boundaryScalar_eq Polynomial.X 1) hL hb
  change (1 - tvar ^ 2) • (boundary + boundaryInverse H K L - (2 : SeriesMatrix)) = _ at heven
  rw [heven]
  have hs : h - tvar ^ 2 * k - (1 - tvar ^ 2) =
      2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
        tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1) := by
    unfold h k scalarH
    rw [markedStep_one]
    change 1 - 2 * (positiveStepVar ^ 2 - positiveStepVar ^ 4 * catalanAt Polynomial.X) -
      tvar ^ 2 * (1 - 2 * (zvar ^ 2 - zvar ^ 4 * catalanAt 1)) - (1 - tvar ^ 2) = _
    rw [positiveStepVar_eq]
    ring
  rw [hs]

private def alternatingCatalan (m : ℕ) : ℂ := (-1 : ℂ) ^ m * (catalan m : ℂ)

private lemma coeff_step_catalan (a : Poly) (m : ℕ) :
    PowerSeries.coeff (4 * (m + 1)) (markedStep a ^ 4 * catalanAt a) =
      Polynomial.C (alternatingCatalan m) * a ^ (4 * (m + 1)) := by
  have hm : 4 * (m + 1) = 4 * m + 4 := by omega
  rw [hm]
  simp only [markedStep, mul_pow, ← map_pow, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul, coeff_catalanAt, dvd_mul_right, ite_true]
  rw [show 4 * m / 4 = m by omega, pow_add]
  simp [alternatingCatalan, mul_assoc]
  ring

private def supportPolynomial (m : ℕ) : Poly :=
  ∑ j ∈ Finset.range (2 * m + 1), Polynomial.X ^ (2 * (j + 1))

private lemma supportPolynomial_mul (m : ℕ) :
    (1 - (Polynomial.X : Poly) ^ 2) * supportPolynomial m =
      Polynomial.X ^ 2 - Polynomial.X ^ (4 * (m + 1)) := by
  have he (l : ℕ) :
      (1 - (Polynomial.X : Poly) ^ 2) *
          (∑ j ∈ Finset.range l, Polynomial.X ^ (2 * (j + 1))) =
        Polynomial.X ^ 2 - Polynomial.X ^ (2 * (l + 1)) := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ, mul_add, ih, show 2 * (l + 1 + 1) = 2 * (l + 1) + 2 by omega,
        pow_add]
      ring
  simpa [supportPolynomial, show 2 * (2 * m + 1 + 1) = 4 * (m + 1) by omega] using he (2 * m + 1)

private lemma coeff_supportPolynomial (m k : ℕ) :
    (supportPolynomial m).coeff k =
      if 0 < k ∧ k < 4 * (m + 1) ∧ Even k then 1 else 0 := by
  classical
  unfold supportPolynomial
  rw [Polynomial.finsetSum_coeff]
  split_ifs with hk
  · obtain ⟨hp, ht, j, hj⟩ := hk
    rw [Finset.sum_eq_single (j - 1)]
    · rw [Polynomial.coeff_X_pow, ite_eq_left (by omega)]
    · intro l hl hne
      rw [Polynomial.coeff_X_pow, ite_eq_right (by omega)]
    · intro hn
      simp only [Finset.mem_range] at hn
      omega
  · apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_X_pow, ite_eq_right]
    intro h
    apply hk
    simp only [Finset.mem_range] at hj
    exact ⟨by omega, by omega, j + 1, by omega⟩

private lemma boundary_coeff (m : ℕ) (i j : Fin 2) :
    PowerSeries.coeff (4 * (m + 1)) (boundary i j) =
      Polynomial.C (-alternatingCatalan m * uniformMatrix i j) * supportPolynomial m := by
  let n := 4 * (m + 1)
  have hn : n ≠ 0 := by dsimp [n]; omega
  have h := congrArg (fun A : SeriesMatrix => PowerSeries.coeff n (A i j)) boundary_even
  have hrescale : imaginaryMark ^ n = 1 := by
    dsimp [n]
    rw [pow_mul, imaginaryMark_fourth, one_pow]
  have hconstant : PowerSeries.coeff n ((2 : SeriesMatrix) i j) = 0 := by
    by_cases hij : i = j <;> simp [Matrix.ofNat_apply, hij, ← map_ofNat (PowerSeries.C (R := Poly)), PowerSeries.coeff_C, hn]
  have hleft :
      PowerSeries.coeff n ((1 - tvar ^ 2) *
        (boundary i j + PowerSeries.rescale imaginaryMark (boundary i j) - (2 : SeriesMatrix) i j)) =
      (1 - Polynomial.X ^ 2) * (2 * PowerSeries.coeff n (boundary i j)) := by
    rw [show (1 - tvar ^ 2 : Series) = PowerSeries.C (1 - (Polynomial.X : Poly) ^ 2) by
      simp [tvar]]
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_rescale, hrescale, hconstant, two_mul]
  have hright : PowerSeries.coeff n
      ((2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
        tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1)) *
        PowerSeries.C (Polynomial.C (uniformMatrix i j))) =
      2 * (Polynomial.X ^ n - Polynomial.X ^ 2) *
        Polynomial.C (alternatingCatalan m * uniformMatrix i j) := by
    have htwo : (2 : Series) = PowerSeries.C (2 : Poly) := (map_ofNat PowerSeries.C _).symm
    have hvar : tvar ^ 2 = PowerSeries.C (Polynomial.X ^ 2 : Poly) := by
      simp only [tvar, map_pow]
    rw [PowerSeries.coeff_mul_C, map_sub, ← markedStep_one, htwo, hvar]
    simp only [mul_assoc, PowerSeries.coeff_C_mul, positiveStepVar, n, coeff_step_catalan,
      one_pow, mul_one, map_mul]
    ring
  change PowerSeries.coeff n ((1 - tvar ^ 2) *
    (boundary i j + PowerSeries.rescale imaginaryMark (boundary i j) - (2 : SeriesMatrix) i j)) =
    PowerSeries.coeff n ((2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
      tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1)) *
        PowerSeries.C (Polynomial.C (uniformMatrix i j))) at h
  rw [hleft, hright] at h
  have hx : (1 - (Polynomial.X : Poly) ^ 2) ≠ 0 := by
    intro he
    have hc := congrArg (fun p : Poly => p.coeff 0) he
    norm_num [Polynomial.coeff_X_pow] at hc
  apply mul_left_cancel₀ (mul_ne_zero (show (2 : Poly) ≠ 0 by norm_num) hx)
  calc
    _ = 2 * (Polynomial.X ^ n - Polynomial.X ^ 2) *
        Polynomial.C (alternatingCatalan m * uniformMatrix i j) := by
          rw [← h]
          ring
    _ = _ := by
      let C := Polynomial.C (alternatingCatalan m * uniformMatrix i j)
      have hneg : Polynomial.C (-alternatingCatalan m * uniformMatrix i j) = -C := by
        rw [neg_mul, map_neg]
      rw [hneg]
      have hh : (1 - (Polynomial.X : Poly) ^ 2) * supportPolynomial m =
          Polynomial.X ^ 2 - Polynomial.X ^ n := supportPolynomial_mul m
      change 2 * (Polynomial.X ^ n - Polynomial.X ^ 2) * C =
        2 * (1 - Polynomial.X ^ 2) * (-C * supportPolynomial m)
      linear_combination 2 * C * hh

/-- The fixed-direction Hadamard recurrence has a solution whose origin coefficients
at times `4 * (m + 1)` are supported on strictly interior even sojourn counts. -/
public theorem exists_solution :
    let mark (x : ℤ) (b : Bool) :=
      if 0 < x ∨ (x = 0 ∧ b = true) then (Polynomial.X : Polynomial ℂ) else 1
    ∃ F : ℤ → Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℂ)),
      (∀ x : ℤ, F x = (if x = 0 then 1 else 0) +
        (PowerSeries.X * PowerSeries.C (mark x false)) • (F (x - 1) * !![1, 1; 0, 0]) +
        (PowerSeries.X * PowerSeries.C (mark x true)) • (F (x + 1) * !![0, 0; 1, -1])) ∧
      ∀ (m k : ℕ) (i j : Fin 2),
        (PowerSeries.coeff (4 * (m + 1)) (F 0 i j)).coeff k =
          if 0 < k ∧ k < 4 * (m + 1) ∧ Even k then
            -((-1 : ℂ) ^ m * (catalan m : ℂ)) * (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ) i j
          else 0 := by
  refine ⟨halfLineExtension boundary plusTransfer minusTransfer, ?_, ?_⟩
  · have hplus : plusTransfer =
        positiveStepVar • (leftStepSeries + plusTransfer ^ 2 * rightStepSeries) :=
      positiveTransfer_eq positiveStepVar _ (catalanAt_eq Polynomial.X)
    have hminus : minusTransfer = zvar • (rightStepSeries + minusTransfer ^ 2 * leftStepSeries) := by
      unfold minusTransfer
      apply negativeTransfer_eq
      simpa only [markedStep_one] using catalanAt_eq 1
    exact halfLineExtension_recursion _ _ _ _ _ _ (positiveStepVar_eq ▸ hplus) hminus
      (positiveStepVar_eq ▸ model_origin)
  · intro m k i j
    change (PowerSeries.coeff (4 * (m + 1))
      (halfLineExtension boundary plusTransfer minusTransfer 0 i j)).coeff k = _
    rw [halfLineExtension_zero, boundary_coeff, Polynomial.coeff_C_mul, coeff_supportPolynomial]
    split <;> simp [alternatingCatalan, uniformMatrix]

end Omega.HadamardSojournSeries
