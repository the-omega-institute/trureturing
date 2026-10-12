/- GID: D5/S3/Quantum/Hiai/TildeSpectralNonconcavity
   generality: I
   mirror-B: D5/B/S3/Quantum/Hiai/TildeSpectralNonconcavity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: First-variable nonconcavity of the tilde spectral trace below the midpoint. -/

import D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder NNReal Topology
open Matrix Set Filter

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
local instance : Pow Mat ℝ := ⟨CFC.rpow⟩

/-- The first argument is the base of the weighted geometric mean. -/
def geometricMean (α : ℝ) (X Y : Mat) : Mat :=
  X ^ (1 / 2 : ℝ) * (X ^ (-1 / 2 : ℝ) * Y * X ^ (-1 / 2 : ℝ)) ^ α *
    X ^ (1 / 2 : ℝ)

/-- Hiai's tilde spectral trace; every power is matrix continuous functional calculus. -/
def tildeTrace (α p : ℝ) (A B : Mat) : ℝ :=
  let K := geometricMean α (A ^ (-p)) (B ^ p)
  (Matrix.trace ((K ^ (1 / 2 : ℝ) * A ^ (2 * p * (1 - α)) *
    K ^ (1 / 2 : ℝ)) ^ (1 / p))).re

private def diagonal (x : ℝ) : Mat := Matrix.diagonal ![(x : ℂ), 1]
private def projection : Mat := !![(1 / 2 : ℂ), 1 / 2; 1 / 2, 1 / 2]

private lemma diagonal_posDef {x : ℝ} (hx : 0 < x) : (diagonal x).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i
  · simpa [diagonal] using hx
  · norm_num [diagonal]

private lemma projection_posSemidef : projection.PosSemidef := by
  have h := (Matrix.posSemidef_vecMulVec_self_star (![1, 1] : Fin 2 → ℂ)).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, Matrix.vecMulVec, Pi.star_apply, Matrix.smul_apply]

private lemma projection_sq : projection * projection = projection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, Matrix.mul_apply, Fin.sum_univ_two]

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

private lemma projection_rpow {q : ℝ} (hq : 0 < q) : projection ^ q = projection := by
  simpa using scaled_projection_rpow projection projection_posSemidef projection_sq
    (show (0 : ℝ) ≤ 1 by norm_num) hq

private lemma projection_diagonal_projection (x : ℝ) :
    projection * diagonal x * projection = ((1 + x) / 2) • projection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projection, diagonal, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.smul_apply, Complex.real_smul] <;> ring

private lemma geometricMean_power {A : Mat} (hA : A.PosDef) {p : ℝ} (hp : 0 < p)
    (α : ℝ) (B : Mat) :
    geometricMean α (A ^ (-p)) (B ^ p) =
      A ^ (-p / 2) * (A ^ (p / 2) * B ^ p * A ^ (p / 2)) ^ α * A ^ (-p / 2) := by
  unfold geometricMean
  rw [CFC.rpow_rpow A (-p) (1 / 2) (neg_ne_zero.mpr hp.ne') hA.isStrictlyPositive,
    CFC.rpow_rpow A (-p) (-1 / 2) (neg_ne_zero.mpr hp.ne') hA.isStrictlyPositive]
  congr 3 <;> ring


private lemma geometricMean_projection {α p x : ℝ} (hα : 0 < α) (hp : 0 < p)
    (hx : 0 < x) :
    geometricMean α ((diagonal x) ^ (-p)) (projection ^ p) =
      (((1 + x ^ p) / 2) ^ (α - 1)) • projection := by
  let D := diagonal x
  let S := D ^ (p / 2)
  let R := S * projection * S
  let μ : ℝ := (1 + x ^ p) / 2
  have hD : D.PosDef := diagonal_posDef hx
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hS : S.IsHermitian := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hR : R.PosSemidef := by
    simpa [R, hS.eq] using projection_posSemidef.mul_mul_conjTranspose_same S
  have hSS : S * S = D ^ p := by
    dsimp [S]
    rw [← CFC.rpow_add hD.isUnit]
    congr 1
    ring
  have hPDP : projection * D ^ p * projection = μ • projection := by
    rw [diagonal_rpow hx p]
    exact projection_diagonal_projection _
  have hRR : R * R = μ • R := by
    calc
      R * R = S * (projection * (S * S) * projection) * S := by simp [R, mul_assoc]
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
  have hcancel : D ^ (-p / 2) * R * D ^ (-p / 2) = projection := by
    calc
      _ = (D ^ (-p / 2) * S) * projection * (S * D ^ (-p / 2)) := by
        simp [R, mul_assoc]
      _ = projection := by rw [hleft, hright, one_mul, mul_one]
  rw [geometricMean_power hD hp, projection_rpow hp]
  change D ^ (-p / 2) * R ^ α * D ^ (-p / 2) = μ ^ (α - 1) • projection
  rw [hpow, Matrix.mul_smul, Matrix.smul_mul, hcancel]

private def scalarCore (α p x : ℝ) : ℝ :=
  (((1 + x ^ p) / 2) ^ (α - 1)) * ((1 + x ^ (2 * p * (1 - α))) / 2)

private def scalarTrace (α p x : ℝ) : ℝ := (scalarCore α p x) ^ (1 / p)

private lemma scalarCore_pos (α p : ℝ) {x : ℝ} (hx : 0 < x) : 0 < scalarCore α p x := by
  unfold scalarCore
  positivity

private lemma scalarTrace_pos (α p : ℝ) {x : ℝ} (hx : 0 < x) : 0 < scalarTrace α p x :=
  Real.rpow_pos_of_pos (scalarCore_pos α p hx) _

private lemma trace_projection {α p x : ℝ} (hα : 0 < α) (hp : 0 < p) (hx : 0 < x) :
    tildeTrace α p (diagonal x) projection = scalarTrace α p x := by
  let s : ℝ := ((1 + x ^ p) / 2) ^ (α - 1)
  let ν : ℝ := (1 + x ^ (2 * p * (1 - α))) / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hsquare : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
    rw [← Real.rpow_add hs]
    norm_num
  have hinner : (s ^ (1 / 2 : ℝ) • projection) *
      (diagonal x) ^ (2 * p * (1 - α)) * (s ^ (1 / 2 : ℝ) • projection) =
      (s * ν) • projection := by
    rw [diagonal_rpow hx]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [projection_diagonal_projection]
    simp only [smul_smul]
    congr 1
    change (s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ)) * ν = s * ν
    rw [hsquare]
  unfold tildeTrace
  rw [geometricMean_projection hα hp hx]
  dsimp only
  change (Matrix.trace (((s • projection) ^ (1 / 2 : ℝ) *
    (diagonal x) ^ (2 * p * (1 - α)) * (s • projection) ^ (1 / 2 : ℝ)) ^
    (1 / p))).re = scalarTrace α p x
  rw [scaled_projection_rpow projection projection_posSemidef projection_sq hs.le
      (show (0 : ℝ) < 1 / 2 by norm_num), hinner]
  rw [scaled_projection_rpow projection projection_posSemidef projection_sq
    (mul_nonneg hs.le hν.le) (one_div_pos.mpr hp)]
  simp [Matrix.trace, projection, Fin.sum_univ_two, Complex.real_smul,
    scalarTrace, scalarCore, s, ν]
  ring

private lemma scalarCore_derivative (α p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (scalarCore α p)
      ((p * (1 - α) / 2) * ((1 + x ^ p) / 2) ^ (α - 2) * x ^ (p - 1) *
        ((1 + x ^ p) * x ^ (p * (1 - 2 * α)) -
          (1 + x ^ (2 * p * (1 - α))) / 2)) x := by
  let μ : ℝ := (1 + x ^ p) / 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hdμ : HasDerivAt (fun y : ℝ => (1 + y ^ p) / 2) (p * x ^ (p - 1) / 2) x :=
    ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_add 1).div_const 2
  have hdν : HasDerivAt (fun y : ℝ => (1 + y ^ (2 * p * (1 - α))) / 2)
      ((2 * p * (1 - α)) * x ^ (2 * p * (1 - α) - 1) / 2) x :=
    ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_add 1).div_const 2
  have hsplit : x ^ (2 * p * (1 - α) - 1) =
      x ^ (p - 1) * x ^ (p * (1 - 2 * α)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hμsplit : μ ^ (α - 1) = μ ^ (α - 2) * μ := by
    rw [← Real.rpow_add_one hμ.ne']
    congr 1
    ring
  convert! (hdμ.rpow_const (p := α - 1) (Or.inl hμ.ne')).mul hdν using 1
  dsimp only [μ] at hμsplit
  rw [show α - 1 - 1 = α - 2 by ring, hsplit, hμsplit]
  ring

private lemma scalarCore_decreases {α p : ℝ} (hαhalf : α < 1 / 2)
    (hp : 0 < p) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ scalarTrace α p b < scalarTrace α p a := by
  let q : ℝ := p * (1 - 2 * α)
  have hq : 0 < q := mul_pos hp (by linarith)
  let x₀ : ℝ := (8 : ℝ) ^ (-1 / q)
  have hx₀ : 0 < x₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hx₀1 : x₀ < 1 := by
    dsimp [x₀]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (div_neg_of_neg_of_pos (by norm_num) hq)
  have hx₀q : x₀ ^ q = (1 / 8 : ℝ) := by
    dsimp only [x₀]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
    rw [show -1 / q * q = -1 by field_simp [hq.ne']]
    norm_num
  have hneg : ∀ x ∈ Icc (x₀ / 4) (x₀ / 2), deriv (scalarCore α p) x < 0 := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have hxx₀ : x ≤ x₀ := by linarith [hx.2]
    have hx1 : x < 1 := lt_of_le_of_lt hxx₀ hx₀1
    have hxp : x ^ p < 1 := Real.rpow_lt_one hxpos.le hx1 hp
    have hxq : x ^ q ≤ 1 / 8 := by
      simpa [hx₀q] using Real.rpow_le_rpow hxpos.le hxx₀ hq.le
    have hxpnonneg : 0 ≤ x ^ p := Real.rpow_nonneg hxpos.le _
    have hxqnonneg : 0 ≤ x ^ q := Real.rpow_nonneg hxpos.le _
    have hxtnonneg : 0 ≤ x ^ (2 * p * (1 - α)) := Real.rpow_nonneg hxpos.le _
    have hprod : (1 + x ^ p) * x ^ q ≤ 2 * (1 / 8 : ℝ) :=
      mul_le_mul (by linarith) hxq hxqnonneg (by norm_num)
    have hbracket : (1 + x ^ p) * x ^ q -
        (1 + x ^ (2 * p * (1 - α))) / 2 < 0 := by nlinarith
    rw [(scalarCore_derivative α p hxpos).deriv]
    apply mul_neg_of_pos_of_neg
    · have hr : 0 < 1 - α := by linarith
      positivity
    · exact hbracket
  have hcont : ContinuousOn (scalarCore α p) (Icc (x₀ / 4) (x₀ / 2)) := by
    intro x hx
    exact (scalarCore_derivative α p
      (lt_of_lt_of_le (by positivity : 0 < x₀ / 4) hx.1)).continuousAt.continuousWithinAt
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc (x₀ / 4) (x₀ / 2)) hcont
    (fun x hx => hneg x (interior_subset hx))
  have hab : x₀ / 4 < x₀ / 2 := by linarith
  have hcore := hanti (by constructor <;> linarith : x₀ / 4 ∈ Icc (x₀ / 4) (x₀ / 2))
    (by constructor <;> linarith : x₀ / 2 ∈ Icc (x₀ / 4) (x₀ / 2)) hab
  refine ⟨x₀ / 4, x₀ / 2, by positivity, hab, ?_⟩
  exact Real.rpow_lt_rpow (scalarCore_pos α p (by positivity)).le hcore (one_div_pos.mpr hp)

private lemma scalar_jensen {α p : ℝ} (hαhalf : α < 1 / 2)
    (hp : 0 < p) :
    ∃ a b c θ : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < θ ∧ θ < 1 ∧
      b = (1 - θ) * a + θ * c ∧
      scalarTrace α p b < (1 - θ) * scalarTrace α p a + θ * scalarTrace α p c := by
  obtain ⟨a, b, ha, hab, hdrop⟩ := scalarCore_decreases hαhalf hp
  have hb : 0 < b := ha.trans hab
  have hha := scalarTrace_pos α p ha
  have hhb := scalarTrace_pos α p hb
  let θ := (scalarTrace α p a - scalarTrace α p b) / (2 * scalarTrace α p a)
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
  have hmid : (1 - θ) * scalarTrace α p a =
      (scalarTrace α p a + scalarTrace α p b) / 2 := by
    dsimp [θ]
    field_simp [hha.ne']
    ring
  refine ⟨a, b, c, θ, ha, hb, hc, hθ, by linarith, haffine, ?_⟩
  have hhc := scalarTrace_pos α p hc
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
/-- For every weight strictly between zero and one half and every positive power,
positive definite complex 2 by 2 matrices violate first-variable concavity of the
exact tilde spectral trace. -/
theorem strict_first_variable_jensen_violation {α p : ℝ}
    (hα : 0 < α) (hαhalf : α < 1 / 2) (hp : 0 < p) :
    ∃ A₀ A₁ B : Mat, A₀.PosDef ∧ A₁.PosDef ∧ B.PosDef ∧
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        tildeTrace α p ((1 - θ) • A₀ + θ • A₁) B <
          (1 - θ) * tildeTrace α p A₀ B + θ * tildeTrace α p A₁ B := by
  obtain ⟨a, b, c, θ, ha, hb, hc, hθ, hθ1, habc, hgap⟩ := scalar_jensen hαhalf hp
  have hboundary : tildeTrace α p (diagonal b) projection <
      (1 - θ) * tildeTrace α p (diagonal a) projection +
        θ * tildeTrace α p (diagonal c) projection := by
    simpa [trace_projection hα hp ha, trace_projection hα hp hb,
      trace_projection hα hp hc] using hgap
  let Bε := fun e : ℝ => projection + e • (1 : Mat)
  have hBpos : ∀ e ∈ Ici (0 : ℝ), (Bε e).PosSemidef := fun e he =>
    projection_posSemidef.add (Matrix.PosSemidef.one.smul he)
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
    simpa [Bε, add_comm] using (Matrix.PosDef.one.smul he).add_posSemidef projection_posSemidef
  refine ⟨diagonal a, diagonal c, Bε e, diagonal_posDef ha, diagonal_posDef hc, hBdef,
    θ, hθ, hθ1, ?_⟩
  rw [← diagonal_affine, ← habc]
  exact sub_pos.mp hegap

#print axioms strict_first_variable_jensen_violation

end D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
