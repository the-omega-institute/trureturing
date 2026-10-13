/- GID: D5/S3/Quantum/Hiai/TildeSpectralNonconcavity
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/TildeSpectralNonconcavity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All-dimension SPD joint-concavity classification of the actual tilde spectral trace. -/

import D5.S3.Quantum.Matrix.TwoPointFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import D5.S3.Quantum.Hiai.PsiMeanTraceConcavity

noncomputable section
namespace D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder NNReal Topology
open Matrix Set Filter GeneralizedPerspectiveFunction

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
    QuantumTwoPointFunctionalCalculus.two_point_cfc _ _ _ _ hH hHH]
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
    QuantumTwoPointFunctionalCalculus.two_point_cfc _ _ _ _ hH hHH]
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

private def gramCore (p : ℝ) (A B : Matrix d d ℂ) : Matrix d d ℂ :=
  A ^ (p / 2) * B ^ p * A ^ (p / 2)

private def midpointTrace (p : ℝ) (A B : Matrix d d ℂ) : ℝ :=
  InverseMeanVariational.tracePower (1 / (2 * p)) (gramCore p A B)

private lemma gramCore_posDef {p : ℝ} {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (gramCore p A B).PosDef := by
  have hS := hA.isStrictlyPositive.rpow A (p / 2)
  have h := (hB.isStrictlyPositive.rpow B p).posDef.mul_mul_conjTranspose_same
    (B := A ^ (p / 2)) (Matrix.vecMul_injective_iff_isUnit.mpr hS.isUnit)
  simpa only [gramCore, hS.posDef.isHermitian.eq] using h

private lemma power_half_square {A : Matrix d d ℂ} (hA : A.PosDef) (q : ℝ) :
    A ^ (q / 2) * A ^ (q / 2) = A ^ q := by
  rw [← CFC.rpow_add hA.isUnit]
  congr 1
  ring

private lemma power_half_cancel {A : Matrix d d ℂ} (hA : A.PosDef) (q : ℝ) :
    A ^ (q / 2) * A ^ (-q / 2) = 1 ∧ A ^ (-q / 2) * A ^ (q / 2) = 1 := by
  constructor
  · convert CFC.rpow_mul_rpow_neg (q / 2) hA.isStrictlyPositive using 1 <;> congr 2 <;> ring
  · convert CFC.rpow_neg_mul_rpow (q / 2) hA.isStrictlyPositive using 1 <;> congr 2 <;> ring

private lemma midpoint_riccati {p : ℝ} (hp : 0 < p) {A B : Matrix d d ℂ}
    (hA : A.PosDef) :
    A ^ (p / 2) * geometricMean (1 / 2) (A ^ (-p)) (B ^ p) * A ^ (p / 2) =
      (gramCore p A B) ^ (1 / 2 : ℝ) := by
  have hc := power_half_cancel hA p
  calc
    _ = (A ^ (p / 2) * A ^ (-p / 2)) * (gramCore p A B) ^ (1 / 2 : ℝ) *
        (A ^ (-p / 2) * A ^ (p / 2)) := by
      rw [geometricMean_power hA hp]
      simp only [gramCore, mul_assoc]
    _ = _ := by rw [hc.1, hc.2, one_mul, mul_one]

set_option maxHeartbeats 1000000 in
-- The Gram trace identification normalizes several dependent CFC powers.
private lemma tildeTrace_midpoint {p : ℝ} (hp : 0 < p) {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    tildeTrace (1 / 2) p A B = midpointTrace p A B := by
  let L := geometricMean (1 / 2) (A ^ (-p)) (B ^ p)
  let V := A ^ (p / 2) * L ^ (1 / 2 : ℝ)
  have hL : L.PosDef := by
    rw [show L = A ^ (-p / 2) * (gramCore p A B) ^ (1 / 2 : ℝ) * A ^ (-p / 2)
      from geometricMean_power hA hp _ _]
    have hN := hA.isStrictlyPositive.rpow A (-p / 2)
    simpa only [hN.posDef.isHermitian.eq] using
      ((gramCore_posDef hA hB).isStrictlyPositive.rpow _ (1 / 2)).posDef.mul_mul_conjTranspose_same
        (B := A ^ (-p / 2)) (Matrix.vecMul_injective_iff_isUnit.mpr hN.isUnit)
  have hS : (A ^ (p / 2))ᴴ = A ^ (p / 2) :=
    (hA.isStrictlyPositive.rpow A (p / 2)).isSelfAdjoint.star_eq
  have hR : (L ^ (1 / 2 : ℝ))ᴴ = L ^ (1 / 2 : ℝ) :=
    (hL.isStrictlyPositive.rpow L (1 / 2)).isSelfAdjoint.star_eq
  have hc : Vᴴ * V = L ^ (1 / 2 : ℝ) * A ^ p * L ^ (1 / 2 : ℝ) := by
    simp only [V, Matrix.conjTranspose_mul, hR, hS, mul_assoc]
    rw [← mul_assoc (A ^ _) (A ^ _), power_half_square hA p]
  have hr : V * Vᴴ = (gramCore p A B) ^ (1 / 2 : ℝ) := by
    simp only [V, Matrix.conjTranspose_mul, hR, hS, mul_assoc]
    rw [← mul_assoc (L ^ _) (L ^ _), power_half_square hL 1]
    rw [CFC.rpow_one L hL.posSemidef.nonneg]
    simpa only [mul_assoc] using midpoint_riccati hp hA
  have hg := InverseMeanVariational.norm_rpow_gram V (show 0 < 2 / p by positivity)
  have hh := InverseMeanVariational.norm_rpow_rowGram
    V (show 0 < 2 / p by positivity)
  rw [hc] at hg
  rw [hr] at hh
  have he : InverseMeanVariational.tracePower (1 / p)
      (L ^ (1 / 2 : ℝ) * A ^ p * L ^ (1 / 2 : ℝ)) =
      InverseMeanVariational.tracePower (1 / p) ((gramCore p A B) ^ (1 / 2 : ℝ)) := by
    simpa only [show 2 / p / 2 = 1 / p by ring] using hg.symm.trans hh
  unfold tildeTrace
  rw [show 2 * p * (1 - (1 / 2 : ℝ)) = p by ring]
  change InverseMeanVariational.tracePower (1 / p)
    (L ^ (1 / 2 : ℝ) * A ^ p * L ^ (1 / 2 : ℝ)) = _
  rw [he]
  unfold InverseMeanVariational.tracePower midpointTrace
  rw [CFC.rpow_rpow _ (1 / 2) (1 / p) (by norm_num)
    (gramCore_posDef hA hB).isStrictlyPositive]
  congr 2
  ring

private def epstein (p : ℝ) (Z A : Matrix d d ℂ) : ℝ :=
  InverseMeanVariational.tracePower (1 / p) (Zᴴ * A ^ p * Z)

private lemma epstein_concave {p t : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (Z : Matrix d d ℂ) (hZ : IsUnit Z) {A₀ A₁ : Matrix d d ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * epstein p Z A₀ + t * epstein p Z A₁ ≤
      epstein p Z ((1 - t) • A₀ + t • A₁) := by
  have hm {X Y : Matrix d d ℂ} (hX : X.PosDef) (hY : Y.PosDef) :
      PsiMeanTraceConcavity.geometricMean 0 (X ^ p) (Y ^ p) = X ^ p := by
    unfold PsiMeanTraceConcavity.geometricMean
    have hXp := hX.isStrictlyPositive.rpow X p
    have hN := hXp.rpow _ (-1 / 2)
    have hinner := (hN.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint
      (Y ^ p) ((X ^ p) ^ (-1 / 2 : ℝ)) hN.isSelfAdjoint).2
      (hY.isStrictlyPositive.rpow Y p)
    rw [CFC.rpow_zero _ hinner.nonneg, mul_one, power_half_square hXp.posDef 1]
    exact CFC.rpow_one _ hXp.nonneg
  have hAm : ((1 - t) • A₀ + t • A₁).PosDef :=
    (CStarAlgebra.convexOn_ringInverse (A := Matrix d d ℂ)).1 hA₀.isStrictlyPositive
      hA₁.isStrictlyPositive (sub_nonneg.mpr ht1) ht0 (by ring) |>.posDef
  have hh := (PsiMeanTraceConcavity.psi_jointly_concave hp hp1 (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    Z hZ) (A₁ := (1 : Matrix d d ℂ)) (A₂ := 1) (B₁ := A₀) (B₂ := A₁)
    (θ := t) Matrix.PosDef.one Matrix.PosDef.one hA₀ hA₁ ht0 ht1
  have hone : (1 - t) • (1 : Matrix d d ℂ) + t • 1 = 1 := by module
  simpa only [PsiMeanTraceConcavity.psi, hone, hm hA₀ Matrix.PosDef.one,
    hm hA₁ Matrix.PosDef.one, hm hAm Matrix.PosDef.one, epstein, smul_eq_mul] using hh

private lemma variational_upper {p : ℝ} (hp : 0 < p) {A B Z : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hZ : IsUnit Z) :
    midpointTrace p A B ≤ (epstein p Z A + epstein p Z⁻¹ᴴ B) / 2 := by
  letI := hZ.invertible
  let U := A ^ (p / 2) * Z
  let V := Z⁻¹ * B ^ (p / 2)
  have hS : (A ^ (p / 2))ᴴ = A ^ (p / 2) :=
    (hA.isStrictlyPositive.rpow A (p / 2)).isSelfAdjoint.star_eq
  have hR : (B ^ (p / 2))ᴴ = B ^ (p / 2) :=
    (hB.isStrictlyPositive.rpow B (p / 2)).isSelfAdjoint.star_eq
  have hUV : U * V = A ^ (p / 2) * B ^ (p / 2) := by simp [U, V, mul_assoc]
  have hM : (A ^ (p / 2) * B ^ (p / 2)) *
      (A ^ (p / 2) * B ^ (p / 2))ᴴ = gramCore p A B := by
    simp only [Matrix.conjTranspose_mul, hS, hR, gramCore, mul_assoc]
    rw [← mul_assoc (B ^ _) (B ^ _), power_half_square hB p]
  have hU : Uᴴ * U = Zᴴ * A ^ p * Z := by
    simp only [U, Matrix.conjTranspose_mul, hS, mul_assoc]
    rw [← mul_assoc (A ^ _) (A ^ _), power_half_square hA p]
  have hV : V * Vᴴ = Z⁻¹ * B ^ p * Z⁻¹ᴴ := by
    simp only [V, Matrix.conjTranspose_mul, hR, mul_assoc]
    rw [← mul_assoc (B ^ _) (B ^ _), power_half_square hB p]
  have hh := InverseMeanVariational.holder_two_young
    U V (one_div_pos.mpr hp)
  rw [hUV,
    InverseMeanVariational.norm_rpow_rowGram
      _ (one_div_pos.mpr hp), hM,
    InverseMeanVariational.norm_rpow_gram U (by positivity), hU,
    InverseMeanVariational.norm_rpow_rowGram
      V (by positivity), hV] at hh
  simp only [show 2 * (1 / p) / 2 = 1 / p by ring,
    show 1 / p / 2 = 1 / (2 * p) by ring] at hh
  have hstar : (Z⁻¹ᴴ)ᴴ = Z⁻¹ := Matrix.conjTranspose_conjTranspose _
  change 2 * midpointTrace p A B - InverseMeanVariational.tracePower (1 / p)
    (Z⁻¹ * B ^ p * Z⁻¹ᴴ) ≤ epstein p Z A at hh
  unfold epstein at hh ⊢
  rw [hstar]
  linarith

private lemma variational_attainment {p : ℝ} (hp : 0 < p) {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ Z : Matrix d d ℂ, IsUnit Z ∧ epstein p Z A = midpointTrace p A B ∧
      epstein p Z⁻¹ᴴ B = midpointTrace p A B := by
  let C := gramCore p A B
  have hC : C.PosDef := gramCore_posDef hA hB
  let S := A ^ (p / 2)
  let N := A ^ (-p / 2)
  let R := C ^ (1 / 4 : ℝ)
  let J := C ^ (-1 / 4 : ℝ)
  let Z := N * R
  have hN := hA.isStrictlyPositive.rpow A (-p / 2)
  have hR := hC.isStrictlyPositive.rpow C (1 / 4)
  have hSN : S * N = 1 := (power_half_cancel hA p).1
  have hNS : N * S = 1 := (power_half_cancel hA p).2
  have hJR : J * R = 1 := by
    simpa only [J, R, neg_div] using CFC.rpow_neg_mul_rpow (1 / 4 : ℝ) hC.isStrictlyPositive
  have hZI : Z⁻¹ = J * S := Matrix.inv_eq_left_inv (by
    calc
      (J * S) * Z = J * (S * N) * R := by simp [Z, mul_assoc]
      _ = 1 := by rw [hSN, mul_one, hJR])
  have hNAn : N * A ^ p * N = 1 := by
    rw [← power_half_square hA p]
    change N * (S * S) * N = 1
    calc
      _ = (N * S) * (S * N) := by simp [mul_assoc]
      _ = 1 := by rw [hNS, hSN, one_mul]
  have hNstar : Nᴴ = N := hN.posDef.isHermitian.eq
  have hRstar : Rᴴ = R := hR.posDef.isHermitian.eq
  have hEa : Zᴴ * A ^ p * Z = C ^ (1 / 2 : ℝ) := by
    calc
      _ = R * (N * A ^ p * N) * R := by
        change (N * R)ᴴ * A ^ p * (N * R) = _
        rw [Matrix.conjTranspose_mul, hNstar, hRstar]
        simp only [mul_assoc]
      _ = R * R := by rw [hNAn, mul_one]
      _ = C ^ (1 / 2 : ℝ) := by
        dsimp [R]
        rw [← CFC.rpow_add hC.isUnit]
        norm_num
  have hS : Sᴴ = S := (hA.isStrictlyPositive.rpow A (p / 2)).isSelfAdjoint.star_eq
  have hJ : Jᴴ = J := (hC.isStrictlyPositive.rpow C (-1 / 4)).isSelfAdjoint.star_eq
  have hEb : Z⁻¹ * B ^ p * Z⁻¹ᴴ = C ^ (1 / 2 : ℝ) := by
    calc
      _ = J * C * J := by rw [hZI]; simp [Matrix.conjTranspose_mul, hS, hJ, C, gramCore, S, mul_assoc]
      _ = C ^ (-1 / 4 : ℝ) * C ^ (1 : ℝ) * C ^ (-1 / 4 : ℝ) := by
        rw [CFC.rpow_one C hC.posSemidef.nonneg]
      _ = C ^ ((-1 / 4 : ℝ) + 1 + (-1 / 4 : ℝ)) := by
        rw [← CFC.rpow_add hC.isUnit, ← CFC.rpow_add hC.isUnit]
      _ = C ^ (1 / 2 : ℝ) := by norm_num
  have htrace : InverseMeanVariational.tracePower (1 / p) (C ^ (1 / 2 : ℝ)) =
      midpointTrace p A B := by
    unfold InverseMeanVariational.tracePower midpointTrace
    dsimp only [C]
    rw [CFC.rpow_rpow (gramCore p A B) (1 / 2) (1 / p) (by norm_num) hC.isStrictlyPositive]
    congr 2
    ring
  refine ⟨Z, hN.isUnit.mul hR.isUnit, ?_, ?_⟩
  · change InverseMeanVariational.tracePower (1 / p) (Zᴴ * A ^ p * Z) = _
    exact (congrArg (InverseMeanVariational.tracePower (1 / p)) hEa).trans htrace
  · simpa [epstein, Matrix.conjTranspose_conjTranspose] using
      (congrArg (InverseMeanVariational.tracePower (1 / p)) hEb).trans htrace

private lemma midpoint_concave {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    JointlyConcaveOn {A : Matrix d d ℂ | A.PosDef} {B : Matrix d d ℂ | B.PosDef}
      (tildeTrace (1 / 2) p) := by
  intro A₀ A₁ B₀ B₁ t hA₀ hA₁ hB₀ hB₁ ht0 ht1
  have hAm : ((1 - t) • A₀ + t • A₁).PosDef :=
    (CStarAlgebra.convexOn_ringInverse (A := Matrix d d ℂ)).1 hA₀.isStrictlyPositive
      hA₁.isStrictlyPositive (sub_nonneg.mpr ht1) ht0 (by ring) |>.posDef
  have hBm : ((1 - t) • B₀ + t • B₁).PosDef :=
    (CStarAlgebra.convexOn_ringInverse (A := Matrix d d ℂ)).1 hB₀.isStrictlyPositive
      hB₁.isStrictlyPositive (sub_nonneg.mpr ht1) ht0 (by ring) |>.posDef
  obtain ⟨Z, hZ, hEa, hEb⟩ := variational_attainment hp hAm hBm
  have hZI : IsUnit Z⁻¹ᴴ := by
    letI := hZ.invertible
    exact (isUnit_of_invertible Z⁻¹).star
  have hcA := epstein_concave hp hp1 Z hZ hA₀ hA₁ ht0 ht1
  have hcB := epstein_concave hp hp1 Z⁻¹ᴴ hZI hB₀ hB₁ ht0 ht1
  have hu0 := variational_upper hp hA₀ hB₀ hZ
  have hu1 := variational_upper hp hA₁ hB₁ hZ
  rw [hEa] at hcA
  rw [hEb] at hcB
  simp only [smul_eq_mul, tildeTrace_midpoint hp hA₀ hB₀,
    tildeTrace_midpoint hp hA₁ hB₁, tildeTrace_midpoint hp hAm hBm]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hu0),
    mul_nonneg ht0 (sub_nonneg.mpr hu1)]

private def axisProjection : Mat := Matrix.diagonal ![(1 : ℂ), 0]

private lemma axisProjection_posSemidef : axisProjection.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [axisProjection]

private lemma axisProjection_sq : axisProjection * axisProjection = axisProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisProjection, Matrix.mul_apply, Fin.sum_univ_two]

private lemma complement_axis_posSemidef : (1 - axisProjection).PosSemidef := by
  have he : (1 : Mat) - axisProjection = Matrix.diagonal ![(0 : ℂ), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [axisProjection]
  rw [he]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num

private lemma complement_axis_sq :
    (1 - axisProjection) * (1 - axisProjection) = 1 - axisProjection := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, axisProjection_sq]
  abel

private lemma balanced_projection :
    projection (1 / 2) = !![(1 / 2 : ℂ), 1 / 2; 1 / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [projection, Real.sqrt_div]

private lemma midpoint_boundary_axis {p : ℝ} (hp : 0 < p)
    (Q : Mat) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (htr : Matrix.trace Q = 1)
    (hQPQ : Q * projection (1 / 2) * Q = (1 / 2 : ℝ) • Q) :
    midpointTrace p Q (projection (1 / 2)) = (1 / 2 : ℝ) ^ (1 / (2 * p)) := by
  have hQpow : Q ^ (p / 2) = Q := by
    simpa using scaled_projection_rpow Q hQ hQQ (show (0 : ℝ) ≤ 1 by norm_num)
      (show 0 < p / 2 by positivity)
  unfold midpointTrace gramCore InverseMeanVariational.tracePower
  rw [hQpow, projection_rpow (by norm_num) (by norm_num) hp, hQPQ,
    scaled_projection_rpow Q hQ hQQ (by norm_num) (by positivity)]
  simp [Matrix.trace_smul, htr, Complex.smul_re, smul_eq_mul]

private lemma involution_trace_rpow (H : Mat) (hH : IsSelfAdjoint H) (hHH : H * H = 1)
    (htr : Matrix.trace H = 0) (a b q : ℝ) (hX : (a • (1 : Mat) + b • H).PosSemidef) :
    InverseMeanVariational.tracePower q (a • (1 : Mat) + b • H) =
      (a + b) ^ q + (a - b) ^ q := by
  unfold InverseMeanVariational.tracePower
  rw [CFC.rpow_eq_cfc_real hX.nonneg,
    QuantumTwoPointFunctionalCalculus.two_point_cfc _ _ _ _ hH hHH]
  simp [Matrix.trace_add, Matrix.trace_smul, htr, Matrix.trace_one]

private lemma midpoint_density_middle {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    midpointTrace p ((1 / 2 : ℝ) • (1 : Mat))
      ((1 - 2 * s) • projection (1 / 2) + s • (1 : Mat)) =
      (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * (Real.sqrt (1 - s) + Real.sqrt s) := by
  let P := projection (1 / 2)
  let H := (2 : ℝ) • P - 1
  let B := (1 - 2 * s) • P + s • (1 : Mat)
  have hP := projection_posSemidef (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  have hH : IsSelfAdjoint H :=
    (hP.isHermitian.smul (IsSelfAdjoint.of_nonneg (show (0 : ℝ) ≤ 2 by norm_num))).sub
      Matrix.isHermitian_one
  have hHH : H * H = 1 := by
    dsimp only [H]
    have hPP : P * P = P := projection_sq (w := 1 / 2) (by norm_num) (by norm_num)
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      hPP, mul_one, one_mul, smul_smul]
    module
  have htrH : Matrix.trace H = 0 := by
    simp [H, P, balanced_projection, Matrix.trace, Fin.sum_univ_two, Matrix.smul_apply]
    ring
  have hB : B.PosSemidef :=
    (hP.smul (by linarith)).add (Matrix.PosSemidef.one.smul hs)
  have hBform : B = (1 / 2 : ℝ) • (1 : Mat) + (1 / 2 - s) • H := by
    dsimp [B, H]
    module
  let a := ((1 - s) ^ p + s ^ p) / 2
  let b := ((1 - s) ^ p - s ^ p) / 2
  have hBpow : B ^ p = a • (1 : Mat) + b • H := by
    rw [CFC.rpow_eq_cfc_real hB.nonneg, hBform,
      QuantumTwoPointFunctionalCalculus.two_point_cfc _ _ _ _ hH hHH]
    rw [show (1 / 2 : ℝ) + (1 / 2 - s) = 1 - s by ring,
      show (1 / 2 : ℝ) - (1 / 2 - s) = s by ring]
  have hhalf : ((1 / 2 : ℝ) • (1 : Mat)) ^ (p / 2) =
      ((1 / 2 : ℝ) ^ (p / 2)) • (1 : Mat) :=
    scaled_projection_rpow 1 Matrix.PosSemidef.one (by simp) (by norm_num) (by positivity)
  have hsquare : ((1 / 2 : ℝ) ^ (p / 2)) * ((1 / 2 : ℝ) ^ (p / 2)) = (1 / 2 : ℝ) ^ p := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    congr 1
    ring
  let c := (1 / 2 : ℝ) ^ p
  have hC : gramCore p ((1 / 2 : ℝ) • (1 : Mat)) B =
      (c * a) • (1 : Mat) + (c * b) • H := by
    unfold gramCore
    rw [hhalf, hBpow]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    rw [hsquare]
    dsimp only [c]
    rw [smul_add, smul_smul, smul_smul]
  have hCpos : ((c * a) • (1 : Mat) + (c * b) • H).PosSemidef := by
    rw [← hC]
    have hS : (((1 / 2 : ℝ) • (1 : Mat)) ^ (p / 2)).IsHermitian :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    simpa only [gramCore, hS.eq] using
      (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := B) (y := p))).mul_mul_conjTranspose_same
        (((1 / 2 : ℝ) • (1 : Mat)) ^ (p / 2))
  change InverseMeanVariational.tracePower (1 / (2 * p))
    (gramCore p ((1 / 2 : ℝ) • (1 : Mat)) B) = _
  rw [hC, involution_trace_rpow H hH hHH htrH _ _ _ hCpos,
    show c * a + c * b = c * (1 - s) ^ p by dsimp [a,b]; ring,
    show c * a - c * b = c * s ^ p by dsimp [a,b]; ring,
    Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _),
    Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hs _)]
  have h1s : 0 ≤ 1 - s := by linarith
  have hexp : p * (1 / (2 * p)) = (1 / 2 : ℝ) := by field_simp
  simp only [c, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.rpow_mul h1s, ← Real.rpow_mul hs, hexp, ← Real.sqrt_eq_rpow]
  ring

private lemma midpoint_boundary_middle {p : ℝ} (hp : 0 < p) :
    midpointTrace p ((1 / 2 : ℝ) • (1 : Mat)) (projection (1 / 2)) =
      (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
  simpa using midpoint_density_middle hp (s := 0) (by norm_num) (by norm_num)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
set_option backward.isDefEq.respectTransparency false in
private lemma midpoint_parameter_continuity {p : ℝ} (hp : 0 < p)
    (A B : ℝ → Mat) (hAc : Continuous A) (hBc : Continuous B) (s : Set ℝ)
    (hA : ∀ x ∈ s, (A x).PosSemidef) (hB : ∀ x ∈ s, (B x).PosSemidef) :
    ContinuousOn (fun x => midpointTrace p (A x) (B x)) s := by
  have hAH := (positive_power_continuousOn (show 0 < p / 2 by positivity)).comp
    hAc.continuousOn hA
  have hBP := (positive_power_continuousOn hp).comp hBc.continuousOn hB
  have hC : ContinuousOn (fun x => gramCore p (A x) (B x)) s :=
    (hAH.mul hBP).mul hAH
  have hCpos (x : ℝ) : (gramCore p (A x) (B x)).PosSemidef := by
    have hS : (A x ^ (p / 2)).IsHermitian := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    simpa only [gramCore, hS.eq] using
      (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := B x) (y := p))).mul_mul_conjTranspose_same
        (A x ^ (p / 2))
  have houter := (positive_power_continuousOn (show 0 < 1 / (2 * p) by positivity)).comp
    hC (fun x _ => hCpos x)
  have htrace : Continuous (fun X : Mat => (Matrix.trace X).re) :=
    Complex.continuous_re.comp (Matrix.traceLinearMap (Fin 2) ℂ ℂ).continuous_of_finiteDimensional
  exact htrace.comp_continuousOn houter

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
set_option backward.isDefEq.respectTransparency false in
private lemma midpoint_strict_jensen {p : ℝ} (hp : 1 < p) :
    ∃ A₀ A₁ B : Mat, A₀.PosDef ∧ A₁.PosDef ∧ B.PosDef ∧
      tildeTrace (1 / 2) p ((1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A₁) B <
        (1 / 2 : ℝ) * tildeTrace (1 / 2) p A₀ B +
        (1 / 2 : ℝ) * tildeTrace (1 / 2) p A₁ B := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let Q := axisProjection
  let R := (1 : Mat) - Q
  let P := projection (1 / 2)
  let A₀ := fun s : ℝ => (1 - 2 * s) • Q + s • (1 : Mat)
  let A₁ := fun s : ℝ => (1 - 2 * s) • R + s • (1 : Mat)
  let B := fun s : ℝ => (1 - 2 * s) • P + s • (1 : Mat)
  have hQ : Q.PosSemidef := axisProjection_posSemidef
  have hR : R.PosSemidef := complement_axis_posSemidef
  have hP : P.PosSemidef := projection_posSemidef (by norm_num) (by norm_num)
  have hnonneg : ∀ s ∈ Icc (0 : ℝ) (1 / 2), 0 ≤ 1 - 2 * s := by intro s hs; linarith [hs.2]
  have hA₀ : ∀ s ∈ Icc (0 : ℝ) (1 / 2), (A₀ s).PosSemidef := fun s hs =>
    (hQ.smul (hnonneg s hs)).add (Matrix.PosSemidef.one.smul hs.1)
  have hA₁ : ∀ s ∈ Icc (0 : ℝ) (1 / 2), (A₁ s).PosSemidef := fun s hs =>
    (hR.smul (hnonneg s hs)).add (Matrix.PosSemidef.one.smul hs.1)
  have hB : ∀ s ∈ Icc (0 : ℝ) (1 / 2), (B s).PosSemidef := fun s hs =>
    (hP.smul (hnonneg s hs)).add (Matrix.PosSemidef.one.smul hs.1)
  have hmix (s : ℝ) : (1 / 2 : ℝ) • A₀ s + (1 / 2 : ℝ) • A₁ s = (1 / 2 : ℝ) • (1 : Mat) := by
    dsimp [A₀, A₁, R]
    module
  have hAc₀ : Continuous A₀ := by fun_prop
  have hAc₁ : Continuous A₁ := by fun_prop
  have hBc : Continuous B := by fun_prop
  let gap := fun s : ℝ => (1 / 2 : ℝ) * midpointTrace p (A₀ s) (B s) +
    (1 / 2 : ℝ) * midpointTrace p (A₁ s) (B s) -
    midpointTrace p ((1 / 2 : ℝ) • (1 : Mat)) (B s)
  have hcont : ContinuousWithinAt gap (Icc (0 : ℝ) (1 / 2)) 0 :=
    ((((midpoint_parameter_continuity hp0 A₀ B hAc₀ hBc _ hA₀ hB).const_mul (1 / 2)).add
      ((midpoint_parameter_continuity hp0 A₁ B hAc₁ hBc _ hA₁ hB).const_mul (1 / 2))).sub
      (midpoint_parameter_continuity hp0 (fun _ => (1 / 2 : ℝ) • (1 : Mat)) B
        continuous_const hBc _ (fun _ _ => Matrix.PosSemidef.one.smul (by norm_num)) hB)).continuousWithinAt
          (by norm_num)
  have htrQ : Matrix.trace Q = 1 := by norm_num [Q, axisProjection, Matrix.trace, Fin.sum_univ_two]
  have htrR : Matrix.trace R = 1 := by
    norm_num [R, Matrix.trace_sub, Matrix.trace_one, htrQ]
  have hQPP : Q * P * Q = (1 / 2 : ℝ) • Q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q, P, axisProjection, balanced_projection, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.smul_apply]
  have hRPP : R * P * R = (1 / 2 : ℝ) • R := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R, Q, P, axisProjection, balanced_projection, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.smul_apply]
  have hboundary : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) < (1 / 2 : ℝ) ^ (1 / (2 * p)) := by
    apply Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num)
    apply (div_lt_iff₀ (by positivity : 0 < 2 * p)).mpr
    linarith
  have hg0 : 0 < gap 0 := by
    dsimp only [gap]
    simp only [A₀, A₁, B, mul_zero, sub_zero, one_smul, zero_smul, add_zero]
    change 0 < (1 / 2 : ℝ) * midpointTrace p Q (projection (1 / 2)) +
      (1 / 2 : ℝ) * midpointTrace p R (projection (1 / 2)) -
        midpointTrace p ((1 / 2 : ℝ) • (1 : Mat)) (projection (1 / 2))
    rw [midpoint_boundary_axis hp0 Q hQ axisProjection_sq htrQ hQPP,
      midpoint_boundary_axis hp0 R hR complement_axis_sq htrR hRPP,
      midpoint_boundary_middle hp0]
    linarith
  have hev : ∀ᶠ s in 𝓝[Icc (0 : ℝ) (1 / 2)] 0, 0 < gap s :=
    hcont.eventually (IsOpen.mem_nhds isOpen_Ioi hg0)
  have heq : 𝓝[Icc (0 : ℝ) (1 / 2)] 0 = 𝓝[≥] (0 : ℝ) :=
    nhdsWithin_Icc_eq_nhdsGE (by norm_num)
  rw [heq] at hev
  have hev' : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < gap s :=
    hev.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, ⟨hgap, hs1⟩, hs⟩ := ((hev'.and hsmall).and self_mem_nhdsWithin).exists
  have hcoeff : 0 ≤ 1 - 2 * s := by linarith
  have hA₀d : (A₀ s).PosDef := by
    simpa [A₀, add_comm] using (Matrix.PosDef.one.smul hs).add_posSemidef (hQ.smul hcoeff)
  have hA₁d : (A₁ s).PosDef := by
    simpa [A₁, add_comm] using (Matrix.PosDef.one.smul hs).add_posSemidef (hR.smul hcoeff)
  have hBd : (B s).PosDef := by
    simpa [B, add_comm] using (Matrix.PosDef.one.smul hs).add_posSemidef (hP.smul hcoeff)
  refine ⟨A₀ s, A₁ s, B s, hA₀d, hA₁d, hBd, ?_⟩
  rw [hmix, tildeTrace_midpoint hp0 hA₀d hBd, tildeTrace_midpoint hp0 hA₁d hBd,
    tildeTrace_midpoint hp0 (Matrix.PosDef.one.smul (by norm_num)) hBd]
  exact sub_pos.mp hgap

/-- The full admissible-parameter classification of Hiai's actual tilde trace on SPD pairs. -/
theorem joint_concavity_classification {α p : ℝ} (hα : 0 < α) (hα1 : α < 1) (hp : 0 < p) :
    (∀ n : ℕ, JointlyConcaveOn {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef}
      {B : Matrix (Fin n) (Fin n) ℂ | B.PosDef} (tildeTrace α p)) ↔
        α = 1 / 2 ∧ p ≤ 1 := by
  constructor
  · intro hc
    have hαhalf : α = 1 / 2 := by
      by_contra hn
      obtain ⟨A₀, A₁, B, hA₀, hA₁, hB, t, ht0, ht1, hgap⟩ :=
        strict_first_variable_jensen_violation hα hα1 hn hp
      have hh := hc 2 hA₀ hA₁ hB hB ht0.le ht1.le
      have hm : (1 - t) • B + t • B = B := by module
      rw [hm] at hh
      exact (not_lt_of_ge hh) hgap
    refine ⟨hαhalf, ?_⟩
    by_contra hn
    obtain ⟨A₀, A₁, B, hA₀, hA₁, hB, hgap⟩ := midpoint_strict_jensen (lt_of_not_ge hn)
    rw [hαhalf] at hc
    have hh := hc 2 hA₀ hA₁ hB hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hm : (1 - (1 / 2 : ℝ)) • B + (1 / 2 : ℝ) • B = B := by module
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, smul_eq_mul] at hh
    rw [show (1 / 2 : ℝ) • B + (1 / 2 : ℝ) • B = B by module] at hh
    exact (not_lt_of_ge hh) hgap
  · rintro ⟨rfl, hp1⟩ n
    exact midpoint_concave hp hp1

#print axioms joint_concavity_classification

end D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
