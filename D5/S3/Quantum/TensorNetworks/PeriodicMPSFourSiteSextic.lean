/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Critch–Morton equation on actual four-site periodic MPS. -/

import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity
import Mathlib.Algebra.DualNumber

/-! Theorem 3 of Critch and Morton, https://arxiv.org/html/1210.2812v4,
in the necklace order `0000, 1000, 1100, 1010, 1110, 1111`.
Only vanishing on the actual image is needed for two-site recovery. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteSextic

open D5.S0.Observation.MatrixTracePowerSum (pow_add_two trace_pow_add_two)
open PeriodicMPSParentIntersection (Bond Word twoFlattening)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped DualNumber Matrix

noncomputable section

/-- The determinant of the triplet block when its singlet coordinate vanishes. -/
def hankelDet {R : Type*} [CommRing R] (a b c e f : R) : R :=
  a * c * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 3

/-- The homogeneous equation in the six four-site necklace amplitudes.
It is written in powers of the singlet coordinate `d - c`. -/
def sextic {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  let q := d - c
  let hankel := hankelDet a b c e f
  0 - hankel ^ 2 - 2 * (a * f - 2 * b * e + c ^ 2) * hankel * q +
    (-a ^ 2 * f ^ 2 + 4 * a * b * e * f - 4 * a * c ^ 2 * f + 2 * a * c * e ^ 2 +
      2 * b ^ 2 * c * f - 4 * b ^ 2 * e ^ 2 + c ^ 4) * q ^ 2 -
    2 * (2 * a * c * f - a * e ^ 2 - b ^ 2 * f) * q ^ 3 - a * f * q ^ 4

/-- The sextic is the negative square of a cubic, corrected by the triplet
determinant times the cube of the singlet coordinate. -/
theorem sextic_square_and_triplet {R : Type*} [CommRing R] (a b c d e f : R) :
    let k := d - c
    let h := hankelDet a b c e f
    let theta := h + k * (a * f - 2 * b * e + c ^ 2) + c * k ^ 2
    sextic a b c d e f = -theta ^ 2 - k ^ 3 * (2 * h + k * (a * f - c ^ 2)) := by
  simp only [sextic, hankelDet]
  ring

private lemma trace_sq (X : Bond) : (X ^ 2).trace = X.trace ^ 2 - 2 * X.det := by
  rw [trace_pow_add_two X 0]
  norm_num [Matrix.trace_one, pow_two]
  ring

private lemma trace_fourth (X : Bond) :
    (X ^ 4).trace = X.trace ^ 4 - 4 * X.trace ^ 2 * X.det + 2 * X.det ^ 2 := by
  rw [trace_pow_add_two X 2, trace_pow_add_two X 1, trace_sq, pow_one]
  ring

private lemma trace_cube_mul (X Y : Bond) :
    (X ^ 3 * Y).trace = (X.trace ^ 2 - X.det) * (X * Y).trace -
      X.trace * X.det * Y.trace := by
  rw [pow_add_two X 1, pow_add_two X 0]
  simp only [pow_zero, pow_one, Matrix.sub_mul, Matrix.smul_mul, one_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  ring_nf

private lemma trace_sq_mul_sq (X Y : Bond) :
    (X ^ 2 * Y ^ 2).trace = X.trace * Y.trace * (X * Y).trace -
      X.trace ^ 2 * Y.det - Y.trace ^ 2 * X.det + 2 * X.det * Y.det := by
  rw [pow_add_two X 0, pow_add_two Y 0]
  simp only [pow_zero, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, one_mul, mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  norm_num [Matrix.trace_one]
  ring

private lemma sextic_trace_coordinates (t s u v k : ℂ) :
    sextic (t ^ 4 - 4 * t ^ 2 * u + 2 * u ^ 2) ((t ^ 2 - u) * k - t * u * s)
      (t * s * k - t ^ 2 * v - s ^ 2 * u + 2 * u * v) (k ^ 2 - 2 * (u * v))
      ((s ^ 2 - v) * k - s * v * t) (s ^ 4 - 4 * s ^ 2 * v + 2 * v ^ 2) = 0 := by
  unfold sextic hankelDet
  ring

/-- Every actual four-site uniform binary bond-two MPS satisfies the sextic relation. -/
theorem sextic_actual (A : Fin 2 → Bond) :
    sextic (traceWord 2 2 4 A ![0, 0, 0, 0]) (traceWord 2 2 4 A ![1, 0, 0, 0])
      (traceWord 2 2 4 A ![1, 1, 0, 0]) (traceWord 2 2 4 A ![1, 0, 1, 0])
      (traceWord 2 2 4 A ![1, 1, 1, 0]) (traceWord 2 2 4 A ![1, 1, 1, 1]) = 0 := by
  let X := A 0
  let Y := A 1
  change sextic (X * (X * (X * (X * 1)))).trace
    (Y * (X * (X * (X * 1)))).trace (Y * (Y * (X * (X * 1)))).trace
    (Y * (X * (Y * (X * 1)))).trace (Y * (Y * (Y * (X * 1)))).trace
    (Y * (Y * (Y * (Y * 1)))).trace = 0
  have hxy := Matrix.trace_mul_comm Y X
  have hb : (Y * (X * (X * (X * 1)))).trace = (X ^ 3 * Y).trace := by
    simp only [mul_one, Matrix.trace_mul_comm Y, pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
  have hc : (Y * (Y * (X * (X * 1)))).trace = (X ^ 2 * Y ^ 2).trace := by
    rw [mul_one, ← Matrix.mul_assoc Y Y, ← pow_two, ← pow_two,
      Matrix.trace_mul_comm (Y ^ 2)]
  have hd : (Y * (X * (Y * (X * 1)))).trace = ((Y * X) ^ 2).trace := by
    simp only [mul_one, pow_two, Matrix.mul_assoc]
  have he : (Y * (Y * (Y * (X * 1)))).trace = (Y ^ 3 * X).trace := by
    simp only [mul_one, pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
  rw [hb, hc, hd, he, trace_cube_mul, trace_sq_mul_sq, trace_sq, Matrix.det_mul,
    trace_cube_mul, hxy]
  have ha (M : Bond) : M * (M * (M * (M * 1))) = M ^ 4 := by
    simp only [mul_one, pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
  rw [ha, ha, trace_fourth, trace_fourth, mul_comm Y.det X.det]
  exact sextic_trace_coordinates X.trace Y.trace X.det Y.det (X * Y).trace

private def pairBits : Fin 4 ≃ Fin 2 × Fin 2 :=
  (finProdFinEquiv (m := 2) (n := 2)).symm

private def pairWord : (Fin 2 × Fin 2) ≃ Word 2 where
  toFun x := ![x.1, x.2]
  invFun w := (w 0, w 1)
  left_inv _ := rfl
  right_inv w := by ext i; fin_cases i <;> rfl

/-- The actual four-site amplitude flattening in binary order on both sides. -/
def fourFlattening (A : Fin 2 → Bond) : Matrix (Fin 4) (Fin 4) ℂ :=
  (twoFlattening A 0).submatrix pairBits (pairBits.trans pairWord)

private lemma fourFlattening_apply (A : Fin 2 → Bond) (i j : Fin 4) :
    fourFlattening A i j =
      traceWord 2 2 4 A ![(pairBits i).1, (pairBits i).2, (pairBits j).1, (pairBits j).2] := by
  change traceWord 2 2 4 A (Fin.append ![(pairBits i).1, (pairBits i).2]
    ![(pairBits j).1, (pairBits j).2]) = _
  congr 1
  ext k
  fin_cases k <;> rfl

private lemma traceWord_rotate (A : Fin 2 → Bond) (a b c d : Fin 2) :
    traceWord 2 2 4 A ![a, b, c, d] = traceWord 2 2 4 A ![b, c, d, a] := by
  change (A a * (A b * (A c * (A d * 1)))).trace =
    (A b * (A c * (A d * (A a * 1)))).trace
  simpa only [mul_one, Matrix.mul_assoc] using
    Matrix.trace_mul_comm (A a) (A b * (A c * A d))

/-- In binary order, the four-site flattening is specified by six necklace amplitudes. -/
theorem fourFlattening_entries (A : Fin 2 → Bond) :
    fourFlattening A =
      let a := traceWord 2 2 4 A ![0, 0, 0, 0]
      let b := traceWord 2 2 4 A ![1, 0, 0, 0]
      let c := traceWord 2 2 4 A ![1, 1, 0, 0]
      let d := traceWord 2 2 4 A ![1, 0, 1, 0]
      let e := traceWord 2 2 4 A ![1, 1, 1, 0]
      let f := traceWord 2 2 4 A ![1, 1, 1, 1]
      !![a, b, b, c; b, d, c, e; b, c, d, e; c, e, e, f] := by
  ext i j
  rw [fourFlattening_apply]
  fin_cases i <;> fin_cases j
  · rfl
  · exact (traceWord_rotate A 1 0 0 0).symm
  · exact (traceWord_rotate A 0 0 1 0).trans (traceWord_rotate A 0 1 0 0)
  · exact (traceWord_rotate A 0 0 1 1).trans (traceWord_rotate A 0 1 1 0)
  · exact traceWord_rotate A 0 1 0 0
  · exact traceWord_rotate A 0 1 0 1
  · exact traceWord_rotate A 0 1 1 0
  · exact traceWord_rotate A 0 1 1 1
  · rfl
  · exact (traceWord_rotate A 1 1 0 0).symm
  · rfl
  · exact (traceWord_rotate A 1 0 1 1).trans (traceWord_rotate A 0 1 1 1)
  · rfl
  · exact (traceWord_rotate A 1 1 1 0).symm
  · rfl
  · rfl

/-- The square Gram product gives precisely the actual four-site two-site marginal. -/
theorem fourFlattening_gram (A : Fin 2 → Bond) :
    fourFlattening A * (fourFlattening A).conjTranspose =
      (rawTwo A 0).submatrix pairBits pairBits := by
  let e := pairBits.trans pairWord
  have h : ((twoFlattening A 0).submatrix pairBits e).conjTranspose =
      (twoFlattening A 0).conjTranspose.submatrix e pairBits := rfl
  change (twoFlattening A 0).submatrix pairBits e *
    ((twoFlattening A 0).submatrix pairBits e).conjTranspose = _
  rw [h, Matrix.submatrix_mul_equiv]
  rfl

/-- A proportional square flattening with the same nonzero two-site marginal
recovers the whole four-site state up to unit phase. -/
theorem phase_of_proportional_flattening (A B : Fin 2 → Bond) (c : ℂ)
    (hF : fourFlattening B = c • fourFlattening A)
    (hG : rawTwo B 0 = rawTwo A 0) (hG₀ : rawTwo A 0 ≠ 0) :
    ‖c‖ = 1 ∧ traceWord 2 2 4 B = c • traceWord 2 2 4 A := by
  let F := fourFlattening A
  have hGram : fourFlattening B * (fourFlattening B).conjTranspose = F * F.conjTranspose := by
    rw [fourFlattening_gram B, hG]
    exact (fourFlattening_gram A).symm
  have hGram₀ : F * F.conjTranspose ≠ 0 := by
    intro hz
    apply hG₀
    have hz' := (fourFlattening_gram A).symm.trans hz
    apply Matrix.ext
    intro i j
    simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply, Matrix.zero_apply] using
      congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M (pairBits.symm i) (pairBits.symm j)) hz'
  have hs : (c * star c) • (F * F.conjTranspose) = (1 : ℂ) • (F * F.conjTranspose) := by
    simpa only [hF, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      one_smul, mul_comm (star c) c, F] using hGram
  have hunit : c * star c = 1 := (smul_left_injective ℂ hGram₀) hs
  have hnorm : ‖c‖ ^ 2 = 1 := by
    have hre := congrArg Complex.re hunit
    simpa [Complex.mul_conj', ← Complex.ofReal_pow] using hre
  refine ⟨by nlinarith [norm_nonneg c], ?_⟩
  funext w
  have hw : (![w 0, w 1, w 2, w 3] : Word 4) = w := by
    funext i
    fin_cases i <;> rfl
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ =>
    M (pairBits.symm (w 0, w 1)) (pairBits.symm (w 2, w 3))) hF
  simpa only [Matrix.smul_apply, fourFlattening_apply, Equiv.apply_symm_apply,
    hw, Pi.smul_apply] using hc

section Boundary

open TrivSqZeroExt

variable {R : Type*} [CommRing R]

@[simp] private lemma dualFstTwo : (2 : R[ε]).fst = (2 : R) := rfl

@[simp] private lemma dualSndTwo : (2 : R[ε]).snd = (0 : R) := rfl

@[simp] private lemma dualFstFour : (4 : R[ε]).fst = (4 : R) := rfl

@[simp] private lemma dualSndFour : (4 : R[ε]).snd = (0 : R) := rfl

/-- At a rank-one triplet, the sextic vanishes to first order in every direction.
The dual-number equation includes both the value and the linear term. -/
theorem sextic_rank_one_triplet (u v w a b c d e f : R) :
    sextic (inl (u ^ 2) + inr a : R[ε]) (inl (u * v) + inr b)
      (inl (u * w) + inr c) (inl (2 * v ^ 2 - u * w) + inr d)
      (inl (v * w) + inr e) (inl (w ^ 2) + inr f) = 0 := by
  apply TrivSqZeroExt.ext
  · simp [sextic, hankelDet]
    ring
  · simp [sextic, hankelDet, TrivSqZeroExt.snd_pow, smul_eq_mul]
    ring

private lemma mul_eq_zero_of_fst_eq_zero (x y : R[ε])
    (hx : x.fst = 0) (hy : y.fst = 0) : x * y = 0 := by
  apply TrivSqZeroExt.ext
  · simp [hx, hy]
  · simp [hx, hy]

/-- A singular triplet with zero singlet also makes the sextic vanish to first order. -/
theorem sextic_singular_triplet_zero_singlet (a b c d e f : R[ε])
    (hs : d.fst = c.fst) (ht : hankelDet a.fst b.fst c.fst e.fst f.fst = 0) :
    sextic a b c d e f = 0 := by
  have hq : (d - c).fst = 0 := by simp [hs]
  have hh : (hankelDet a b c e f).fst = 0 := by
    simpa [hankelDet] using ht
  have hhh : hankelDet a b c e f ^ 2 = 0 := by
    simpa only [pow_two] using mul_eq_zero_of_fst_eq_zero _ _ hh hh
  have hq2 : (d - c) ^ 2 = 0 := by
    simpa only [pow_two] using mul_eq_zero_of_fst_eq_zero _ _ hq hq
  have hhq : hankelDet a b c e f * (d - c) = 0 :=
    mul_eq_zero_of_fst_eq_zero _ _ hh hq
  simp [sextic, hhh, hq2, pow_succ' (d - c) 2, pow_succ' (d - c) 3, mul_assoc, hhq]

end Boundary

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteSextic
