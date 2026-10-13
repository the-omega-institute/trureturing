/- GID: D5/S3/Quantum/Hiai/TildeSpectralNonconcavity
   generality: I
   mirror-B: D5/B/S3/Quantum/Hiai/TildeSpectralNonconcavity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: First-variable nonconcavity of the tilde spectral trace away from the midpoint. -/

import D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

noncomputable section
namespace D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder NNReal Topology
open Matrix Set Filter

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- The first argument is the base of the weighted geometric mean. -/
def geometricMean (α : ℝ) (X Y : Matrix d d ℂ) : Matrix d d ℂ :=
  X ^ (1 / 2 : ℝ) * (X ^ (-1 / 2 : ℝ) * Y * X ^ (-1 / 2 : ℝ)) ^ α *
    X ^ (1 / 2 : ℝ)

/-- Hiai's tilde spectral trace; every power is matrix continuous functional calculus. -/
def tildeTrace (α p : ℝ) (A B : Matrix d d ℂ) : ℝ :=
  let K := geometricMean α (A ^ (-p)) (B ^ p)
  (Matrix.trace ((K ^ (1 / 2 : ℝ) * A ^ (2 * p * (1 - α)) *
    K ^ (1 / 2 : ℝ)) ^ (1 / p))).re

private def diagonal (x : ℝ) : Mat := Matrix.diagonal ![(x : ℂ), 1]
private def projection (w : ℝ) : Mat :=
  !![(w : ℂ), (Real.sqrt (w * (1 - w)) : ℂ);
     (Real.sqrt (w * (1 - w)) : ℂ), (1 - w : ℝ)]

private lemma diagonal_posDef {x : ℝ} (hx : 0 < x) : (diagonal x).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i
  · simpa [diagonal] using hx
  · norm_num [diagonal]

private lemma projection_posSemidef {w : ℝ} (hw : 0 < w) (hw1 : w < 1) :
    (projection w).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star
    (![(Real.sqrt w : ℂ), (Real.sqrt (1 - w) : ℂ)] : Fin 2 → ℂ)
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projection, Matrix.vecMulVec, Pi.star_apply, Complex.conj_ofReal,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hw.le,
      Real.mul_self_sqrt (by linarith : 0 ≤ 1 - w), Real.sqrt_mul hw.le] <;> ring

private lemma projection_sq {w : ℝ} (hw : 0 < w) (hw1 : w < 1) :
    projection w * projection w = projection w := by
  have hs : Real.sqrt (w * (1 - w)) * Real.sqrt (w * (1 - w)) = w * (1 - w) :=
    Real.mul_self_sqrt (mul_nonneg hw.le (by linarith))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projection, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, hs] <;>
    norm_cast <;> nlinarith

private lemma diagonal_rpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (diagonal x) ^ t = diagonal (x ^ t) := by
  let H : Mat := Matrix.diagonal ![(1 : ℂ), -1]
  have hH : IsSelfAdjoint H := by
    change Hᴴ = H
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [H, Matrix.conjTranspose_apply]
  have hHH : H * H = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [H, Matrix.mul_apply, Fin.sum_univ_two]
  have harg : ((x + 1) / 2) • (1 : Mat) + ((x - 1) / 2) • H = diagonal x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, diagonal, Matrix.smul_apply, Complex.real_smul] <;> ring
  rw [CFC.rpow_eq_cfc_real (diagonal_posDef hx).posSemidef.nonneg, ← harg,
    D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc _ _ _ _ hH hHH]
  rw [show (x + 1) / 2 + (x - 1) / 2 = x by ring,
    show (x + 1) / 2 - (x - 1) / 2 = 1 by ring]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, diagonal, Matrix.smul_apply, Complex.real_smul] <;> ring

private lemma scaled_projection_rpow (Q : Mat) (hQ : Q.PosSemidef)
    (hQQ : Q * Q = Q) {s q : ℝ} (hs : 0 ≤ s) (hq : 0 < q) :
    (s • Q) ^ q = (s ^ q) • Q := by
  let H : Mat := (2 : ℝ) • Q - 1
  have hH : IsSelfAdjoint H :=
    (hQ.isHermitian.smul (IsSelfAdjoint.of_nonneg (show (0 : ℝ) ≤ 2 by norm_num))).sub
      Matrix.isHermitian_one
  have hHH : H * H = 1 := by
    dsimp [H]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul,
      hQQ, smul_smul]
    module
  have harg : (s / 2) • (1 : Mat) + (s / 2) • H = s • Q := by
    dsimp [H]
    module
  rw [CFC.rpow_eq_cfc_real (hQ.smul hs).nonneg, ← harg,
    D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc _ _ _ _ hH hHH]
  rw [show s / 2 + s / 2 = s by ring, sub_self, Real.zero_rpow hq.ne', add_zero,
    sub_zero]
  dsimp [H]
  module

private lemma projection_rpow {w q : ℝ} (hw : 0 < w) (hw1 : w < 1) (hq : 0 < q) :
    (projection w) ^ q = projection w := by
  simpa using scaled_projection_rpow (projection w) (projection_posSemidef hw hw1)
    (projection_sq hw hw1) (show (0 : ℝ) ≤ 1 by norm_num) hq

private lemma projection_diagonal_projection {w : ℝ} (hw : 0 < w) (hw1 : w < 1)
    (x : ℝ) :
    projection w * diagonal x * projection w = (1 - w + w * x) • projection w := by
  have hs : Real.sqrt (w * (1 - w)) * Real.sqrt (w * (1 - w)) = w * (1 - w) :=
    Real.mul_self_sqrt (mul_nonneg hw.le (by linarith))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projection, diagonal, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.smul_apply, Complex.real_smul,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub, hs] <;>
    norm_cast <;> nlinarith [congrArg (fun z : ℝ => z * x) hs]

private lemma geometricMean_power {A : Matrix d d ℂ} (hA : A.PosDef) {p : ℝ} (hp : 0 < p)
    (α : ℝ) (B : Matrix d d ℂ) :
    geometricMean α (A ^ (-p)) (B ^ p) =
      A ^ (-p / 2) * (A ^ (p / 2) * B ^ p * A ^ (p / 2)) ^ α * A ^ (-p / 2) := by
  unfold geometricMean
  rw [CFC.rpow_rpow A (-p) (1 / 2) (neg_ne_zero.mpr hp.ne') hA.isStrictlyPositive,
    CFC.rpow_rpow A (-p) (-1 / 2) (neg_ne_zero.mpr hp.ne') hA.isStrictlyPositive]
  congr 3 <;> ring


private lemma geometricMean_projection {w α p x : ℝ} (hw : 0 < w) (hw1 : w < 1) (hα : 0 < α) (hp : 0 < p)
    (hx : 0 < x) :
    geometricMean α ((diagonal x) ^ (-p)) ((projection w) ^ p) =
      ((1 - w + w * x ^ p) ^ (α - 1)) • (projection w) := by
  let D := diagonal x
  let S := D ^ (p / 2)
  let R := S * (projection w) * S
  let μ : ℝ := 1 - w + w * x ^ p
  have hD : D.PosDef := diagonal_posDef hx
  have hμ : 0 < μ := by dsimp [μ]; exact add_pos (by linarith) (mul_pos hw (Real.rpow_pos_of_pos hx _))
  have hS : S.IsHermitian := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hR : R.PosSemidef := by
    simpa [R, hS.eq] using (projection_posSemidef hw hw1).mul_mul_conjTranspose_same S
  have hSS : S * S = D ^ p := by
    dsimp [S]
    rw [← CFC.rpow_add hD.isUnit]
    congr 1
    ring
  have hPDP : (projection w) * D ^ p * (projection w) = μ • (projection w) := by
    rw [diagonal_rpow hx p]
    exact projection_diagonal_projection hw hw1 _
  have hRR : R * R = μ • R := by
    calc
      R * R = S * ((projection w) * (S * S) * (projection w)) * S := by simp [R, mul_assoc]
      _ = μ • R := by rw [hSS, hPDP]; simp [R]
  let Q := μ⁻¹ • R
  have hQ : Q.PosSemidef := hR.smul (inv_nonneg.mpr hμ.le)
  have hQQ : Q * Q = Q := by
    dsimp [Q]
    rw [Matrix.smul_mul, Matrix.mul_smul, hRR]
    simp only [smul_smul]
    congr 1
    field_simp
  have hscale : μ • Q = R := by simp [Q, smul_smul, hμ.ne']
  have hpow : R ^ α = μ ^ (α - 1) • R := by
    have hcoeff : μ ^ α = μ ^ (α - 1) * μ := by
      rw [← Real.rpow_add_one hμ.ne']
      congr 1
      ring
    calc
      R ^ α = (μ • Q) ^ α := congrArg (fun X : Mat => X ^ α) hscale.symm
      _ = μ ^ α • Q := scaled_projection_rpow Q hQ hQQ hμ.le hα
      _ = μ ^ (α - 1) • (μ • Q) :=
        (congrArg (fun t : ℝ => t • Q) hcoeff).trans (mul_smul _ _ _)
      _ = μ ^ (α - 1) • R := by rw [hscale]
  have hleft : D ^ (-p / 2) * S = 1 := by
    convert CFC.rpow_neg_mul_rpow (p / 2) hD.isStrictlyPositive using 1 <;> congr 1 <;> ring
  have hright : S * D ^ (-p / 2) = 1 := by
    convert CFC.rpow_mul_rpow_neg (p / 2) hD.isStrictlyPositive using 1 <;> congr 1 <;> ring
  have hcancel : D ^ (-p / 2) * R * D ^ (-p / 2) = (projection w) := by
    calc
      _ = (D ^ (-p / 2) * S) * (projection w) * (S * D ^ (-p / 2)) := by
        simp [R, mul_assoc]
      _ = (projection w) := by rw [hleft, hright, one_mul, mul_one]
  rw [geometricMean_power hD hp, projection_rpow hw hw1 hp]
  change D ^ (-p / 2) * R ^ α * D ^ (-p / 2) = μ ^ (α - 1) • (projection w)
  rw [hpow, Matrix.mul_smul, Matrix.smul_mul, hcancel]

private def scalarCore (w α p x : ℝ) : ℝ :=
  ((1 - w + w * x ^ p) ^ (α - 1)) * (1 - w + w * x ^ (2 * p * (1 - α)))

private def scalarTrace (w α p x : ℝ) : ℝ := (scalarCore w α p x) ^ (1 / p)

private lemma scalarCore_pos (w α p : ℝ) {x : ℝ} (hw : 0 < w) (hw1 : w < 1) (hx : 0 < x) : 0 < scalarCore w α p x := by
  unfold scalarCore
  have hv : 0 < 1 - w := by linarith
  positivity

private lemma scalarTrace_pos (w α p : ℝ) {x : ℝ} (hw : 0 < w) (hw1 : w < 1) (hx : 0 < x) : 0 < scalarTrace w α p x :=
  Real.rpow_pos_of_pos (scalarCore_pos w α p hw hw1 hx) _

private lemma trace_projection {w α p x : ℝ} (hw : 0 < w) (hw1 : w < 1) (hα : 0 < α) (hp : 0 < p) (hx : 0 < x) :
    tildeTrace α p (diagonal x) (projection w) = scalarTrace w α p x := by
  let s : ℝ := (1 - w + w * x ^ p) ^ (α - 1)
  let ν : ℝ := 1 - w + w * x ^ (2 * p * (1 - α))
  have hs : 0 < s := by
    have hv : 0 < 1 - w := by linarith
    dsimp [s]
    positivity
  have hν : 0 < ν := by
    have hv : 0 < 1 - w := by linarith
    dsimp [ν]
    positivity
  have hsquare : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
    rw [← Real.rpow_add hs]
    norm_num
  have hinner : (s ^ (1 / 2 : ℝ) • (projection w)) *
      (diagonal x) ^ (2 * p * (1 - α)) * (s ^ (1 / 2 : ℝ) • (projection w)) =
      (s * ν) • (projection w) := by
    rw [diagonal_rpow hx]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [projection_diagonal_projection hw hw1]
    simp only [smul_smul]
    congr 1
    change (s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ)) * ν = s * ν
    rw [hsquare]
  unfold tildeTrace
  rw [geometricMean_projection hw hw1 hα hp hx]
  dsimp only
  change (Matrix.trace (((s • (projection w)) ^ (1 / 2 : ℝ) *
    (diagonal x) ^ (2 * p * (1 - α)) * (s • (projection w)) ^ (1 / 2 : ℝ)) ^
    (1 / p))).re = scalarTrace w α p x
  rw [scaled_projection_rpow (projection w) (projection_posSemidef hw hw1) (projection_sq hw hw1) hs.le
      (show (0 : ℝ) < 1 / 2 by norm_num), hinner]
  rw [scaled_projection_rpow (projection w) (projection_posSemidef hw hw1) (projection_sq hw hw1)
    (mul_nonneg hs.le hν.le) (one_div_pos.mpr hp)]
  simp [Matrix.trace, projection, Fin.sum_univ_two, Complex.real_smul,
    scalarTrace, scalarCore, s, ν]
  ring

private lemma scalarCore_at_root {w α p q k : ℝ} (hw1 : w < 1)
    (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) (hwq : w * q = 1 - w) :
    scalarCore w α p ((k * q) ^ (1 / p)) =
      ((1 - w) ^ α / (1 + k) ^ (1 - α)) *
        (1 + k ^ (2 * (1 - α)) * q ^ (1 - 2 * α)) := by
  have hv : 0 < 1 - w := by linarith
  have hx : ((k * q) ^ (1 / p)) ^ p = k * q := by
    rw [← Real.rpow_mul (mul_pos hk hq).le]
    rw [show 1 / p * p = 1 by field_simp]
    exact Real.rpow_one _
  have hx2 : ((k * q) ^ (1 / p)) ^ (2 * p * (1 - α)) =
      k ^ (2 * (1 - α)) * (q * q ^ (1 - 2 * α)) := by
    rw [← Real.rpow_mul (mul_pos hk hq).le,
      show 1 / p * (2 * p * (1 - α)) = 2 * (1 - α) by field_simp,
      Real.mul_rpow hk.le hq.le]
    congr 1
    calc
      q ^ (2 * (1 - α)) = q ^ (1 + (1 - 2 * α)) := by congr 1; ring
      _ = q * q ^ (1 - 2 * α) := by rw [Real.rpow_add hq, Real.rpow_one]
  have hμ : 1 - w + w * (k * q) = (1 - w) * (1 + k) := by
    calc
      _ = (1 - w) + k * (w * q) := by ring
      _ = _ := by rw [hwq]; ring
  have hν : 1 - w + w * (k ^ (2 * (1 - α)) * (q * q ^ (1 - 2 * α))) =
      (1 - w) * (1 + k ^ (2 * (1 - α)) * q ^ (1 - 2 * α)) := by
    calc
      _ = 1 - w + (w * q) * k ^ (2 * (1 - α)) * q ^ (1 - 2 * α) := by ring
      _ = _ := by rw [hwq]; ring
  have hvpow : (1 - w) ^ (α - 1) * (1 - w) = (1 - w) ^ α := by
    rw [← Real.rpow_add_one hv.ne']
    congr 1
    ring
  unfold scalarCore
  rw [hx, hx2, hμ, hν, Real.mul_rpow hv.le (by linarith : 0 ≤ 1 + k)]
  rw [show α - 1 = -(1 - α) by ring,
    Real.rpow_neg (by linarith : 0 ≤ 1 + k)]
  rw [show -(1 - α) = α - 1 by ring]
  calc
    _ = ((1 - w) ^ (α - 1) * (1 - w)) / (1 + k) ^ (1 - α) *
        (1 + k ^ (2 * (1 - α)) * q ^ (1 - 2 * α)) := by ring
    _ = _ := by rw [hvpow]

private lemma scalarCore_decreases {α p : ℝ} (hα1 : α < 1) (hαne : α ≠ 1 / 2)
    (hp : 0 < p) :
    ∃ w a b : ℝ, 0 < w ∧ w < 1 ∧ 0 < a ∧ a < b ∧
      scalarTrace w α p b < scalarTrace w α p a := by
  let r := 1 - α
  have hr : 0 < r := by dsimp [r]; linarith
  let γ : ℝ := (3 / 2 : ℝ) ^ r
  let η : ℝ := (4 : ℝ) ^ r
  have hγ : 1 < γ := Real.one_lt_rpow (by norm_num) hr
  have hγη : γ < η := Real.rpow_lt_rpow (by norm_num) (by norm_num) hr
  let δ := (γ - 1) / (2 * (η - γ))
  have hδ : 0 < δ := div_pos (by linarith) (mul_pos (by norm_num) (by linarith))
  have hβ : 1 - 2 * α ≠ 0 := by intro he; apply hαne; linarith
  let q := δ ^ (1 / (1 - 2 * α))
  have hq : 0 < q := Real.rpow_pos_of_pos hδ _
  have hqβ : q ^ (1 - 2 * α) = δ := by
    dsimp [q]
    rw [← Real.rpow_mul hδ.le, show 1 / (1 - 2 * α) * (1 - 2 * α) = 1 by field_simp [hβ]]
    exact Real.rpow_one _
  let w := 1 / (1 + q)
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : w < 1 := by dsimp [w]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
  have hv : 0 < 1 - w := by linarith
  have hwq : w * q = 1 - w := by dsimp [w]; field_simp; ring
  let a := q ^ (1 / p)
  let b := (2 * q) ^ (1 / p)
  have ha : 0 < a := Real.rpow_pos_of_pos hq _
  have hb : 0 < b := Real.rpow_pos_of_pos (by positivity) _
  have hab : a < b := Real.rpow_lt_rpow hq.le (by linarith) (one_div_pos.mpr hp)
  have heqa : scalarCore w α p a = (1 - w) ^ α / (2 : ℝ) ^ r * (1 + δ) := by
    simpa [a, r, hqβ, show (1 + 1 : ℝ) = 2 by norm_num] using scalarCore_at_root (α := α) hw1 hp hq (show (0 : ℝ) < 1 by norm_num) hwq
  have heqb : scalarCore w α p b = (1 - w) ^ α / (3 : ℝ) ^ r * (1 + η * δ) := by
    have h2 : (2 : ℝ) ^ (2 * (1 - α)) = η := by
      dsimp [η, r]
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    simpa [b, r, hqβ, h2, show (1 + 2 : ℝ) = 3 by norm_num] using scalarCore_at_root (α := α) hw1 hp hq (show (0 : ℝ) < 2 by norm_num) hwq
  have h2 : 0 < (2 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : 0 < (3 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) _
  have hγeq : γ = (3 : ℝ) ^ r / (2 : ℝ) ^ r := Real.div_rpow (by norm_num) (by norm_num) r
  have hδeq : δ * (η - γ) = (γ - 1) / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt (sub_pos.mpr hγη)] <;> ring
  have hgap : scalarCore w α p a - scalarCore w α p b =
      (1 - w) ^ α * (γ - 1) / (2 * (3 : ℝ) ^ r) := by
    rw [heqa, heqb]
    have hsmall : γ * (1 + δ) - (1 + η * δ) = (γ - 1) / 2 := by
      nlinarith [hδeq]
    calc
      _ = ((1 - w) ^ α / (3 : ℝ) ^ r) * (γ * (1 + δ) - (1 + η * δ)) := by
        rw [hγeq]
        field_simp [h2.ne', h3.ne']
      _ = _ := by rw [hsmall]; ring
  have hdrop : scalarCore w α p b < scalarCore w α p a := by
    have hg : 0 < (1 - w) ^ α * (γ - 1) / (2 * (3 : ℝ) ^ r) := by
      exact div_pos (mul_pos (Real.rpow_pos_of_pos hv _) (by linarith)) (by positivity)
    linarith [hgap]
  refine ⟨w, a, b, hw, hw1, ha, hab, ?_⟩
  exact Real.rpow_lt_rpow (scalarCore_pos w α p hw hw1 hb).le hdrop (one_div_pos.mpr hp)

private lemma scalar_jensen {α p : ℝ} (hα1 : α < 1) (hαne : α ≠ 1 / 2)
    (hp : 0 < p) :
    ∃ w a b c θ : ℝ, 0 < w ∧ w < 1 ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < θ ∧ θ < 1 ∧
      b = (1 - θ) * a + θ * c ∧
      scalarTrace w α p b < (1 - θ) * scalarTrace w α p a + θ * scalarTrace w α p c := by
  obtain ⟨w, a, b, hw, hw1, ha, hab, hdrop⟩ := scalarCore_decreases hα1 hαne hp
  have hb : 0 < b := ha.trans hab
  have hha := scalarTrace_pos w α p hw hw1 ha
  have hhb := scalarTrace_pos w α p hw hw1 hb
  let θ := (scalarTrace w α p a - scalarTrace w α p b) / (2 * scalarTrace w α p a)
  have hθ : 0 < θ := div_pos (sub_pos.mpr hdrop) (by positivity)
  have hθhalf : θ < 1 / 2 := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  let c := a + (b - a) / θ
  have hc : 0 < c := add_pos ha (div_pos (sub_pos.mpr hab) hθ)
  have haffine : b = (1 - θ) * a + θ * c := by
    dsimp [c]
    field_simp [hθ.ne']
    ring
  have hmid : (1 - θ) * scalarTrace w α p a =
      (scalarTrace w α p a + scalarTrace w α p b) / 2 := by
    dsimp [θ]
    field_simp [hha.ne']
    ring
  refine ⟨w, a, b, c, θ, hw, hw1, ha, hb, hc, hθ, by linarith, haffine, ?_⟩
  have hhc := scalarTrace_pos w α p hw hw1 hc
  rw [hmid]
  nlinarith [mul_pos hθ hhc]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
set_option backward.isDefEq.respectTransparency false in
private lemma positive_power_continuousOn {q : ℝ} (hq : 0 < q) :
    ContinuousOn (fun B : Mat => CFC.rpow B q) {B | B.PosSemidef} := by
  let qn : ℝ≥0 := ⟨q, hq.le⟩
  have hqn : 0 < qn := hq
  have h := CFC.continuousOn_nnrpow (A := Mat) qn
  simp only [Matrix.nonneg_iff_posSemidef] at h
  convert! h using 1
  funext B
  exact (CFC.nnrpow_eq_rpow (a := B) hqn).symm

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
set_option backward.isDefEq.respectTransparency false in
private lemma tildeTrace_continuousOn {α p : ℝ} (hα : 0 < α) (hp : 0 < p) (A : Mat) :
    ContinuousOn (tildeTrace α p A) {B | B.PosSemidef} := by
  let F := (A ^ (-p)) ^ (1 / 2 : ℝ)
  let N := (A ^ (-p)) ^ (-1 / 2 : ℝ)
  let C := fun B : Mat => N * B ^ p * N
  let K := fun B : Mat => F * (C B) ^ α * F
  let L := fun B : Mat => (K B) ^ (1 / 2 : ℝ)
  let M := fun B : Mat => L B * A ^ (2 * p * (1 - α)) * L B
  have hF : F.IsHermitian := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hN : N.IsHermitian := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hCpos : ∀ B : Mat, (C B).PosSemidef := by
    intro B
    simpa [C, hN.eq] using
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg (a := B) (y := p))).mul_mul_conjTranspose_same N
  have hKpos : ∀ B : Mat, (K B).PosSemidef := by
    intro B
    simpa [K, hF.eq] using
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg (a := C B) (y := α))).mul_mul_conjTranspose_same F
  have hL : ∀ B : Mat, (L B).IsHermitian := fun B => IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hMpos : ∀ B : Mat, (M B).PosSemidef := by
    intro B
    simpa [M, (hL B).eq] using
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg (a := A) (y := 2 * p * (1 - α)))).mul_mul_conjTranspose_same (L B)
  have hC : ContinuousOn C {B | B.PosSemidef} :=
    (continuousOn_const.mul (positive_power_continuousOn hp)).mul continuousOn_const
  have hK : ContinuousOn K {B | B.PosSemidef} :=
    (continuousOn_const.mul ((positive_power_continuousOn hα).comp hC
      (fun B _ => hCpos B))).mul continuousOn_const
  have hLcont : ContinuousOn L {B | B.PosSemidef} :=
    (positive_power_continuousOn (show (0 : ℝ) < 1 / 2 by norm_num)).comp hK
      (fun B _ => hKpos B)
  have hM : ContinuousOn M {B | B.PosSemidef} :=
    (hLcont.mul continuousOn_const).mul hLcont
  have houter := (positive_power_continuousOn (one_div_pos.mpr hp)).comp hM
    (fun B _ => hMpos B)
  have htrace : Continuous (fun B : Mat => (Matrix.trace B).re) :=
    Complex.continuous_re.comp (Matrix.traceLinearMap (Fin 2) ℂ ℂ).continuous_of_finiteDimensional
  exact htrace.comp_continuousOn houter

private lemma diagonal_affine (a c θ : ℝ) :
    diagonal ((1 - θ) * a + θ * c) = (1 - θ) • diagonal a + θ • diagonal c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, Matrix.smul_apply, Complex.real_smul] <;> ring

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
set_option backward.isDefEq.respectTransparency false in
/-- For every weight strictly between zero and one, away from one half and every positive power,
positive definite complex 2 by 2 matrices violate first-variable concavity of the
exact tilde spectral trace. -/
theorem strict_first_variable_jensen_violation {α p : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hαne : α ≠ 1 / 2) (hp : 0 < p) :
    ∃ A₀ A₁ B : Mat, A₀.PosDef ∧ A₁.PosDef ∧ B.PosDef ∧
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        tildeTrace α p ((1 - θ) • A₀ + θ • A₁) B <
          (1 - θ) * tildeTrace α p A₀ B + θ * tildeTrace α p A₁ B := by
  obtain ⟨w, a, b, c, θ, hw, hw1, ha, hb, hc, hθ, hθ1, habc, hgap⟩ := scalar_jensen hα1 hαne hp
  have hboundary : tildeTrace α p (diagonal b) (projection w) <
      (1 - θ) * tildeTrace α p (diagonal a) (projection w) +
        θ * tildeTrace α p (diagonal c) (projection w) := by
    simpa [trace_projection hw hw1 hα hp ha, trace_projection hw hw1 hα hp hb,
      trace_projection hw hw1 hα hp hc] using hgap
  let Bε := fun e : ℝ => (projection w) + e • (1 : Mat)
  have hBpos : ∀ e ∈ Ici (0 : ℝ), (Bε e).PosSemidef := fun e he =>
    (projection_posSemidef hw hw1).add (Matrix.PosSemidef.one.smul he)
  have hBcont : Continuous Bε := by fun_prop
  let gap := fun e : ℝ => (1 - θ) * tildeTrace α p (diagonal a) (Bε e) +
    θ * tildeTrace α p (diagonal c) (Bε e) - tildeTrace α p (diagonal b) (Bε e)
  have hcont (x : ℝ) : ContinuousOn (fun e : ℝ => tildeTrace α p (diagonal x) (Bε e)) (Ici 0) :=
    (tildeTrace_continuousOn hα hp (diagonal x)).comp hBcont.continuousOn hBpos
  have hgapCont : ContinuousWithinAt gap (Ici 0) 0 :=
    ((((hcont a).const_mul (1 - θ)).add ((hcont c).const_mul θ)).sub
      (hcont b)).continuousWithinAt (by simp : (0 : ℝ) ∈ Ici 0)
  have hgap0 : 0 < gap 0 := by simpa [gap, Bε] using sub_pos.mpr hboundary
  have hev : ∀ᶠ e in 𝓝[Ici 0] (0 : ℝ), 0 < gap e :=
    hgapCont.eventually (IsOpen.mem_nhds isOpen_Ioi hgap0)
  have hev' : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < gap e :=
    hev.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  obtain ⟨e, hegap, he⟩ := (hev'.and self_mem_nhdsWithin).exists
  have hBdef : (Bε e).PosDef := by
    simpa [Bε, add_comm] using (Matrix.PosDef.one.smul he).add_posSemidef (projection_posSemidef hw hw1)
  refine ⟨diagonal a, diagonal c, Bε e, diagonal_posDef ha, diagonal_posDef hc, hBdef,
    θ, hθ, hθ1, ?_⟩
  rw [← diagonal_affine, ← habc]
  exact sub_pos.mp hegap

#print axioms strict_first_variable_jensen_violation

end D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
