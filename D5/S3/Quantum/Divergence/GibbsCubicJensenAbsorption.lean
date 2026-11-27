import D5.S3.Quantum.Divergence.GibbsCubicTranslationEntropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NoncommRing
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.GibbsCubicJensenAbsorption

open GibbsCubicTranslationEntropy
open SpectralCeilingRelativeEntropy (overlap overlap_weighted_column trace_cfc_product)

/-- A logarithmic Jensen gap controls variance on the positive support of the weights. -/
theorem quantitative_log_jensen {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    {R μ : ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, w i ≠ 0 → x i ∈ Ioc 0 R) (hμ : (∑ i, w i * x i) = μ) :
    (∑ i, w i * (x i - μ) ^ 2) / (2 * R ^ 2) ≤
      Real.log μ - ∑ i, w i * Real.log (x i) := by
  classical
  let f (z : ℝ) := -Real.log z - z ^ 2 / (2 * R ^ 2)
  let f' (z : ℝ) := -z⁻¹ - z / R ^ 2
  have hf (z : ℝ) (hz : 0 < z) : HasDerivAt f (f' z) z := by
    convert (Real.hasDerivAt_log hz.ne').neg.sub
      ((hasDerivAt_pow 2 z).div_const (2 * R ^ 2)) using 1 <;>
      first | rfl | (dsimp [f']; field_simp [hR.ne', hz.ne'] <;> ring)
  have hf' (z : ℝ) (hz : 0 < z) :
      HasDerivAt f' ((z ^ 2)⁻¹ - (R ^ 2)⁻¹) z := by
    convert (hasDerivAt_inv hz.ne').neg.sub ((hasDerivAt_id z).div_const (R ^ 2))
      using 1 <;> first | rfl | simp [one_div]
  have hconv : ConvexOn ℝ (Ioc 0 R) f := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := f')
      (f'' := fun z => (z ^ 2)⁻¹ - (R ^ 2)⁻¹) (convex_Ioc 0 R) ?_ ?_ ?_ ?_
    · exact fun z hz => (hf z hz.1).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ioc] at hz
      exact (hf z hz.1).hasDerivWithinAt
    · intro z hz
      rw [interior_Ioc] at hz
      exact (hf' z hz.1).hasDerivWithinAt
    · intro z hz
      rw [interior_Ioc] at hz
      exact sub_nonneg.mpr (by
        simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hz.1 2)
          ((sq_le_sq₀ hz.1.le hR.le).mpr hz.2.le))
  let y (i : ι) := if w i = 0 then R else x i
  have hy (i : ι) : y i ∈ Ioc 0 R := by
    by_cases hi : w i = 0
    · simpa [y, hi] using (show R ∈ Ioc 0 R from ⟨hR, le_rfl⟩)
    · simpa [y, hi] using hx i hi
  have hsum (g : ℝ → ℝ) : (∑ i, w i * g (y i)) = ∑ i, w i * g (x i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : w i = 0 <;> simp [y, hi]
  have hyμ : (∑ i, w i * y i) = μ := (hsum id).trans hμ
  have hj := hconv.map_sum_le (t := Finset.univ) (w := w) (p := y)
    (fun i _ => hw i) hw1 (fun i _ => hy i)
  simp only [smul_eq_mul] at hj
  rw [hyμ, hsum f] at hj
  have hfSum : (∑ i, w i * f (x i)) =
      -(∑ i, w i * Real.log (x i)) - (∑ i, w i * x i ^ 2) / (2 * R ^ 2) := by
    simp only [f, mul_sub, mul_neg, ← mul_div_assoc, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, Finset.sum_div]
  have hvar : (∑ i, w i * (x i - μ) ^ 2) = (∑ i, w i * x i ^ 2) - μ ^ 2 := by
    calc
      _ = ∑ i, (w i * x i ^ 2 - (2 * μ) * (w i * x i) + μ ^ 2 * w i) := by
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hμ, hw1]
        ring
  rw [hfSum] at hj
  dsimp only [f] at hj
  rw [hvar, sub_div]
  linarith only [hj]

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B M : Matrix n n ℂ}

/-- The residual in the left eigenbasis of B and right eigenbasis of M. -/
def mixedResidual (hB : B.IsHermitian) (hM : M.IsHermitian) (γ : ℝ) : Matrix n n ℂ :=
  (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (M - (γ : ℂ) • B) * hM.eigenvectorUnitary

private theorem mixedResidual_normSq (hB : B.IsHermitian) (hM : M.IsHermitian)
    (γ : ℝ) (i j : n) :
    Complex.normSq (mixedResidual hB hM γ i j) =
      (hM.eigenvalues j - γ * hB.eigenvalues i) ^ 2 * overlap hB hM i j := by
  let U : Matrix n n ℂ := hB.eigenvectorUnitary
  let V : Matrix n n ℂ := hM.eigenvectorUnitary
  let db := diagonal (fun i => (hB.eigenvalues i : ℂ))
  let dm := diagonal (fun j => (hM.eigenvalues j : ℂ))
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hV : V * Vᴴ = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hdb : Uᴴ * B * U = db := by
    simpa only [U, db, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
        hB.conjStarAlgAut_star_eigenvectorUnitary
  have hdm : Vᴴ * M * V = dm := by
    simpa only [V, dm, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
        hM.conjStarAlgAut_star_eigenvectorUnitary
  have hleft : Uᴴ * B = db * Uᴴ := by
    rw [← hdb, mul_assoc (Uᴴ * B), hU, mul_one]
  have hright : M * V = V * dm := by
    rw [← hdm, ← mul_assoc V, ← mul_assoc V, hV, one_mul]
  have hentry :
      (Uᴴ * (M - (γ : ℂ) • B) * V) i j =
        ((hM.eigenvalues j - γ * hB.eigenvalues i : ℝ) : ℂ) * (Uᴴ * V) i j := by
    have h₁ : (Uᴴ * M * V) i j = (Uᴴ * V) i j * (hM.eigenvalues j : ℂ) := by
      rw [mul_assoc, hright, ← mul_assoc, Matrix.mul_diagonal]
    have h₂ : (Uᴴ * B * V) i j = (hB.eigenvalues i : ℂ) * (Uᴴ * V) i j := by
      rw [hleft, mul_assoc, Matrix.diagonal_mul]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, h₁, h₂, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  have hoverlap : Complex.normSq ((Uᴴ * V) i j) = overlap hB hM i j := by
    calc
      _ = Complex.normSq (((Uᴴ * V)ᴴ) j i) := by
        rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
      _ = _ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Complex.normSq_eq_norm_sq] <;> rfl
  change Complex.normSq ((Uᴴ * (M - (γ : ℂ) • B) * V) i j) = _
  rw [hentry, Complex.normSq_mul, Complex.normSq_ofReal, hoverlap]
  ring

/-- The deficit in the actual cubic entropy slope. Zero-weight summands vanish. -/
def jensenGap (hB : B.IsHermitian) (hM : M.IsHermitian) : ℝ :=
  let S := (B * M ^ 2).trace.re
  let γ := (M ^ 3).trace.re / S
  let x := spectralRatio hB hM
  S * (Real.log γ - ∑ p, spectralWeight hB hM p * x p ^ 2 / S * Real.log (x p))

private theorem tilted_moments (hB : B.PosDef) (hM : M.PosSemidef) :
    let pi := spectralWeight hB.isHermitian hM.isHermitian
    let x := spectralRatio hB.isHermitian hM.isHermitian
    (∑ p, pi p * x p ^ 2) = (B * M ^ 2).trace.re ∧
    (∑ p, pi p * x p ^ 3) = (M ^ 3).trace.re := by
  dsimp only
  have hS := trace_cfc_product B M hB.isHermitian hM.isHermitian
    (id : ℝ → ℝ) (fun z => z ^ 2)
  rw [cfc_id ℝ B hB.isHermitian.isSelfAdjoint,
    cfc_pow_id M 2 hM.isHermitian.isSelfAdjoint] at hS
  have hT : (M ^ 3).trace.re = ∑ j, hM.isHermitian.eigenvalues j ^ 3 := by
    rw [← cfc_pow_id (R := ℝ) M 3 hM.isHermitian.isSelfAdjoint]
    exact D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum M hM.isHermitian _
  constructor
  · rw [hS, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [spectralWeight, spectralRatio]
    field_simp [(hB.eigenvalues_pos i).ne'] <;> ring
  · rw [hT, Fintype.sum_prod_type, ← overlap_weighted_column hB.isHermitian hM.isHermitian
      (fun j => hM.isHermitian.eigenvalues j ^ 3)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [spectralWeight, spectralRatio]
    field_simp [(hB.eigenvalues_pos i).ne'] <;> ring

set_option maxHeartbeats 1000000 in
/-- The quantitative Jensen bound for a nonzero PSD matrix. The numerator is the squared
Hilbert–Schmidt norm of B⁻¹ᐟ² (M − γ B) M in the mixed eigenbasis. -/
theorem jensenGap_ge_mixedResidual (hB : B.PosDef) (hM : M.PosSemidef) (hM₀ : M ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (hxR : ∀ p, spectralRatio hB.isHermitian hM.isHermitian p ≤ R) :
    let γ := (M ^ 3).trace.re / (B * M ^ 2).trace.re
    (∑ p : n × n, hM.isHermitian.eigenvalues p.2 ^ 2 / hB.isHermitian.eigenvalues p.1 *
        Complex.normSq (mixedResidual hB.isHermitian hM.isHermitian γ p.1 p.2)) /
        (2 * R ^ 2) ≤ jensenGap hB.isHermitian hM.isHermitian := by
  classical
  dsimp only
  let S := (B * M ^ 2).trace.re
  let γ := (M ^ 3).trace.re / S
  let pi := spectralWeight hB.isHermitian hM.isHermitian
  let x := spectralRatio hB.isHermitian hM.isHermitian
  let a (p : n × n) := pi p * x p ^ 2
  let ν (p : n × n) := a p / S
  obtain ⟨hS, hT⟩ := tilted_moments hB hM
  change (∑ p, a p) = S at hS
  change (∑ p, pi p * x p ^ 3) = (M ^ 3).trace.re at hT
  have ha (p : n × n) : 0 ≤ a p :=
    mul_nonneg (mul_nonneg (pow_nonneg (hB.eigenvalues_pos p.1).le 3) (sq_nonneg _))
      (sq_nonneg _)
  have hm : ∃ j, 0 < hM.isHermitian.eigenvalues j := by
    by_contra! h
    apply hM₀
    apply hM.isHermitian.eigenvalues_eq_zero_iff.mp
    funext j
    exact le_antisymm (h j) (hM.eigenvalues_nonneg j)
  obtain ⟨j, hj⟩ := hm
  have hcol : ∑ i, overlap hB.isHermitian hM.isHermitian i j = 1 := by
    have hc := overlap_weighted_column hB.isHermitian hM.isHermitian
      (fun k => if k = j then (1 : ℝ) else 0)
    rw [Finset.sum_comm] at hc
    simpa [ite_mul, Finset.sum_ite_eq'] using hc
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ =>
    show 0 ≤ overlap hB.isHermitian hM.isHermitian i j from sq_nonneg _)).mp
      (show 0 < ∑ i, overlap hB.isHermitian hM.isHermitian i j by
        rw [hcol]
        exact zero_lt_one)
  have hSpos : 0 < S := by
    rw [← hS]
    exact Finset.sum_pos' (fun p _ => ha p) ⟨(i, j), Finset.mem_univ _,
      mul_pos (mul_pos (pow_pos (hB.eigenvalues_pos i) 3) hi)
        (pow_pos (div_pos hj (hB.eigenvalues_pos i)) 2)⟩
  have hν (p : n × n) : 0 ≤ ν p := div_nonneg (ha p) hSpos.le
  have hν1 : ∑ p, ν p = 1 := by
    simp only [ν, ← Finset.sum_div, hS, div_self hSpos.ne']
  have hmean : (∑ p, ν p * x p) = γ := by
    calc
      _ = ∑ p, pi p * x p ^ 3 / S := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        dsimp only [ν, a]
        ring
      _ = _ := by rw [← Finset.sum_div, hT]
  have hpos (p : n × n) (hp : ν p ≠ 0) : x p ∈ Ioc 0 R := by
    refine ⟨lt_of_le_of_ne (div_nonneg (hM.eigenvalues_nonneg p.2)
      (hB.eigenvalues_pos p.1).le) ?_, hxR p⟩
    intro hzero
    exact hp (by simp [ν, a, ← hzero])
  have hj := mul_le_mul_of_nonneg_left
    (quantitative_log_jensen ν x hR hν hν1 hpos hmean) hSpos.le
  have hvar : S * (∑ p, ν p * (x p - γ) ^ 2) =
      ∑ p : n × n, hM.isHermitian.eigenvalues p.2 ^ 2 / hB.isHermitian.eigenvalues p.1 *
        Complex.normSq (mixedResidual hB.isHermitian hM.isHermitian γ p.1 p.2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mixedResidual_normSq]
    dsimp only [ν, a, pi, x, spectralRatio, spectralWeight]
    field_simp [hSpos.ne', (hB.eigenvalues_pos p.1).ne'] <;> ring
  rw [← mul_div_assoc, hvar] at hj
  exact hj

private theorem sum_normSq_eq_trace (A : Matrix n n ℂ) :
    (∑ p : n × n, Complex.normSq (A p.1 p.2)) = (Aᴴ * A).trace.re := by
  rw [Matrix.trace_mul_comm Aᴴ A, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

private theorem sum_mixedResidual_normSq (hB : B.IsHermitian) (hM : M.IsHermitian)
    (γ : ℝ) :
    let H := M - (γ : ℂ) • B
    (∑ p : n × n, Complex.normSq (mixedResidual hB hM γ p.1 p.2)) =
      (Hᴴ * H).trace.re := by
  dsimp only
  let U : Matrix n n ℂ := hB.eigenvectorUnitary
  let V : Matrix n n ℂ := hM.eigenvectorUnitary
  let H := M - (γ : ℂ) • B
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hV : V * Vᴴ = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  rw [sum_normSq_eq_trace]
  change ((Uᴴ * H * V)ᴴ * (Uᴴ * H * V)).trace.re = (Hᴴ * H).trace.re
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hprod : (Vᴴ * (Hᴴ * U)) * (Uᴴ * H * V) = Vᴴ * (Hᴴ * H) * V := by
    calc
      _ = Vᴴ * (Hᴴ * (U * Uᴴ) * H) * V := by noncomm_ring
      _ = _ := by rw [hU, mul_one]
  rw [hprod, Matrix.trace_mul_cycle, hV, one_mul]

private theorem correction_le_residual (hB : B.IsHermitian) (hM : M.IsHermitian)
    {bmin bmax : ℝ} (hbmin : 0 < bmin) (hbounds : ∀ i, hB.eigenvalues i ∈ Icc bmin bmax)
    (hbmax : bmin ≤ bmax) (γ : ℝ) :
    let H := M - (γ : ℂ) • B
    correction B M ≤ (bmax - bmin) * Real.log (bmax / bmin) / 2 * (Hᴴ * H).trace.re := by
  dsimp only
  let b := hB.eigenvalues
  let Q := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary).symm
  let d := diagonal (fun i => (b i : ℂ))
  let H := M - (γ : ℂ) • B
  let W := Q H
  have hQB : Q B = d := by
    simpa only [Q, b, d, Unitary.conjStarAlgAut_symm,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
        hB.conjStarAlgAut_star_eigenvectorUnitary
  have hW : W = Q M - (γ : ℂ) • d := by
    change Q (M - (γ : ℂ) • B) = _
    rw [map_sub, map_smul, hQB]
  let K := (bmax - bmin) * Real.log (bmax / bmin)
  have hK (i j : n) : (b i - b j) * (Real.log (b i) - Real.log (b j)) ≤ K := by
    obtain ⟨hi₁, hi₂⟩ := hbounds i
    obtain ⟨hj₁, hj₂⟩ := hbounds j
    have habs : |b i - b j| ≤ bmax - bmin :=
      abs_le.mpr ⟨by linarith only [hi₁, hj₂], by linarith only [hi₂, hj₁]⟩
    have hlogabs : |Real.log (b i) - Real.log (b j)| ≤ Real.log bmax - Real.log bmin := by
      have hi₀ : 0 < b i := hbmin.trans_le hi₁
      have hj₀ : 0 < b j := hbmin.trans_le hj₁
      exact abs_le.mpr ⟨by linarith only [Real.log_le_log hbmin hi₁, Real.log_le_log hj₀ hj₂],
        by linarith only [Real.log_le_log hi₀ hi₂, Real.log_le_log hbmin hj₁]⟩
    calc
      _ ≤ |(b i - b j) * (Real.log (b i) - Real.log (b j))| := le_abs_self _
      _ = |b i - b j| * |Real.log (b i) - Real.log (b j)| := abs_mul _ _
      _ ≤ (bmax - bmin) * (Real.log bmax - Real.log bmin) :=
        mul_le_mul habs hlogabs (abs_nonneg _) (sub_nonneg.mpr hbmax)
      _ = K := by
        dsimp only [K]
        rw [Real.log_div (hbmin.trans_le hbmax).ne' hbmin.ne']
  have hK₀ : 0 ≤ K :=
    mul_nonneg (sub_nonneg.mpr hbmax) (Real.log_nonneg (by
      apply (le_div_iff₀ hbmin).mpr
      simpa only [one_mul] using hbmax))
  have hterm (p : n × n) :
      (b p.1 - b p.2) * (Real.log (b p.1) - Real.log (b p.2)) *
          Complex.normSq (Q M p.1 p.2) ≤ K * Complex.normSq (W p.1 p.2) := by
    by_cases hp : p.1 = p.2
    · simpa only [hp, sub_self, zero_mul] using
        (mul_nonneg hK₀ (Complex.normSq_nonneg (W p.1 p.2)))
    · have hoff : W p.1 p.2 = Q M p.1 p.2 := by
        rw [hW]
        simp [d, Matrix.diagonal_apply_ne _ hp]
      rw [hoff]
      exact mul_le_mul_of_nonneg_right (hK p.1 p.2) (Complex.normSq_nonneg _)
  have hspec := correction_spectral B M hB hM
  dsimp only at hspec
  change correction B M = (1 / 2 : ℝ) * ∑ i, ∑ j,
    (b i - b j) * (Real.log (b i) - Real.log (b j)) * Complex.normSq (Q M i j) at hspec
  calc
    _ = (1 / 2 : ℝ) * ∑ p : n × n, (b p.1 - b p.2) *
        (Real.log (b p.1) - Real.log (b p.2)) * Complex.normSq (Q M p.1 p.2) := by
      rw [Fintype.sum_prod_type, hspec]
    _ ≤ (1 / 2 : ℝ) * ∑ p : n × n, K * Complex.normSq (W p.1 p.2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => hterm p)) (by norm_num)
    _ = _ := by
      have htrace : (Wᴴ * W).trace = (Hᴴ * H).trace := by
        change (star (Q H) * Q H).trace = (star H * H).trace
        rw [← map_star, ← map_mul]
        exact D5.S3.Quantum.Recovery.BKMSpectralVariance.trace_conjStarAlgAut_symm
          hB.eigenvectorUnitary (star H * H)
      rw [← Finset.mul_sum, sum_normSq_eq_trace, htrace]
      dsimp only [K]
      ring

set_option maxHeartbeats 1000000 in
/-- The compensated gap with the exact dependence on the two spectral ratios. -/
theorem jensenGap_sub_correction_ge (hB : B.PosDef) (hM : M.PosSemidef) (hM₀ : M ≠ 0)
    {bmin bmax mmin mmax : ℝ} (hbmin : 0 < bmin) (hbmax : bmin ≤ bmax)
    (hmmin : 0 ≤ mmin) (hmmax : 0 < mmax)
    (hBbounds : ∀ i, hB.isHermitian.eigenvalues i ∈ Icc bmin bmax)
    (hMbounds : ∀ j, hM.isHermitian.eigenvalues j ∈ Icc mmin mmax) :
    let γ := (M ^ 3).trace.re / (B * M ^ 2).trace.re
    let H := M - (γ : ℂ) • B
    let κ := bmax / bmin
    let ρ := mmin / mmax
    bmin / 2 * (ρ ^ 2 / κ - (κ - 1) * Real.log κ) * (Hᴴ * H).trace.re ≤
      jensenGap hB.isHermitian hM.isHermitian - correction B M := by
  dsimp only
  let γ := (M ^ 3).trace.re / (B * M ^ 2).trace.re
  let H := M - (γ : ℂ) • B
  let A := mixedResidual hB.isHermitian hM.isHermitian γ
  let N := (Hᴴ * H).trace.re
  let κ := bmax / bmin
  let ρ := mmin / mmax
  let R := mmax / bmin
  have hbmax₀ := hbmin.trans_le hbmax
  have hR : 0 < R := div_pos hmmax hbmin
  have hxR (p : n × n) : spectralRatio hB.isHermitian hM.isHermitian p ≤ R := by
    change hM.isHermitian.eigenvalues p.2 / hB.isHermitian.eigenvalues p.1 ≤ mmax / bmin
    exact (div_le_div_of_nonneg_right (hMbounds p.2).2 (hB.eigenvalues_pos p.1).le).trans
      (div_le_div_of_nonneg_left hmmax.le hbmin (hBbounds p.1).1)
  have hsum : mmin ^ 2 / bmax * N ≤
      ∑ p : n × n, hM.isHermitian.eigenvalues p.2 ^ 2 / hB.isHermitian.eigenvalues p.1 *
        Complex.normSq (A p.1 p.2) := by
    have hN : (∑ p : n × n, Complex.normSq (A p.1 p.2)) = N :=
      sum_mixedResidual_normSq hB.isHermitian hM.isHermitian γ
    rw [← hN, Finset.mul_sum]
    refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right ?_ (Complex.normSq_nonneg _))
    have hm := (sq_le_sq₀ hmmin (hM.eigenvalues_nonneg p.2)).mpr (hMbounds p.2).1
    exact (div_le_div_of_nonneg_right hm hbmax₀.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (hB.eigenvalues_pos p.1) (hBbounds p.1).2)
  have hG : bmin / 2 * (ρ ^ 2 / κ) * N ≤ jensenGap hB.isHermitian hM.isHermitian := by
    calc
      _ = (mmin ^ 2 / bmax * N) / (2 * R ^ 2) := by
        dsimp only [ρ, κ, R]
        field_simp [hbmin.ne', hbmax₀.ne', hmmax.ne'] <;> ring
      _ ≤ _ := (div_le_div_of_nonneg_right hsum (by positivity : 0 ≤ 2 * R ^ 2)).trans
        (jensenGap_ge_mixedResidual hB hM hM₀ hR hxR)
  have hJ : correction B M ≤ bmin / 2 * ((κ - 1) * Real.log κ) * N := by
    have hb : bmax - bmin = bmin * (κ - 1) := by
      dsimp only [κ]
      field_simp [hbmin.ne'] <;> ring
    calc
      _ ≤ (bmax - bmin) * Real.log κ / 2 * N :=
        correction_le_residual hB.isHermitian hM.isHermitian hbmin hBbounds hbmax γ
      _ = _ := by rw [hb]; ring
  change bmin / 2 * (ρ ^ 2 / κ - (κ - 1) * Real.log κ) * N ≤ _
  calc
    _ = bmin / 2 * (ρ ^ 2 / κ) * N - bmin / 2 * ((κ - 1) * Real.log κ) * N := by ring
    _ ≤ _ := sub_le_sub hG hJ

private theorem focal_bracket {κ ρ : ℝ} (hκ₁ : 1 ≤ κ) (hκ₂ : κ ≤ 36 / 25)
    (hρ : 2 / 3 ≤ ρ) : 1 / 9 ≤ ρ ^ 2 / κ - (κ - 1) * Real.log κ := by
  have hκ : 0 < κ := zero_lt_one.trans_le hκ₁
  have hd : 0 ≤ κ - 1 := sub_nonneg.mpr hκ₁
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hκ) hd
  have hd₂ := (sq_le_sq₀ hd (by norm_num : (0 : ℝ) ≤ 11 / 25)).mpr
    (show κ - 1 ≤ 11 / 25 by linarith only [hκ₂])
  have hρ₂ := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by linarith only [hρ] : 0 ≤ ρ)).mpr hρ
  have hratio : (25 / 81 : ℝ) ≤ ρ ^ 2 / κ := by
    apply (le_div_iff₀ hκ).mpr
    linarith only [hκ₂, hρ₂]
  have hLoss : (κ - 1) * Real.log κ ≤ (11 / 25 : ℝ) ^ 2 := by
    calc
      _ ≤ (κ - 1) ^ 2 := by simpa only [pow_two] using hlog
      _ ≤ _ := hd₂
  calc
    1 / 9 ≤ (25 / 81 : ℝ) - (11 / 25 : ℝ) ^ 2 := by norm_num
    _ ≤ _ := sub_le_sub hratio hLoss

set_option maxHeartbeats 1000000 in
/-- The focal spectral bounds give a `bmin / 18` remainder in the actual slope. -/
theorem focal_cubicEntropy_slope (hB : B.PosDef) (hM : M.PosDef)
    (hNorm : (B ^ 3).trace.re = 1)
    {bmin bmax mmin mmax : ℝ} (hbmin : 0 < bmin) (hbmax : bmin ≤ bmax)
    (hmmax : 0 < mmax)
    (hBbounds : ∀ i, hB.isHermitian.eigenvalues i ∈ Icc bmin bmax)
    (hMbounds : ∀ j, hM.isHermitian.eigenvalues j ∈ Icc mmin mmax)
    (hκ : bmax / bmin ≤ 36 / 25) (hρ : 2 / 3 ≤ mmin / mmax) :
    let pi := spectralWeight hB.isHermitian hM.isHermitian
    let x := spectralRatio hB.isHermitian hM.isHermitian
    let S := (B * M ^ 2).trace.re
    let E := (∑ p, pi p * x p ^ 2 * Real.log (x p ^ 2)) - S * Real.log S
    let H := M - (((M ^ 3).trace.re / S : ℝ) : ℂ) • B
    let G := jensenGap hB.isHermitian hM.isHermitian
    bmin / 18 * (Hᴴ * H).trace.re ≤ G - correction B M ∧
    ∃ d, HasDerivAt (fun s : ℝ => cubicEntropy B (M + s • B)) d 0 ∧
      d / 3 ≤ E - bmin / 18 * (Hᴴ * H).trace.re := by
  dsimp only
  let pi := spectralWeight hB.isHermitian hM.isHermitian
  let x := spectralRatio hB.isHermitian hM.isHermitian
  let S := (B * M ^ 2).trace.re
  let E := (∑ p, pi p * x p ^ 2 * Real.log (x p ^ 2)) - S * Real.log S
  let H := M - (((M ^ 3).trace.re / S : ℝ) : ℂ) • B
  let G := jensenGap hB.isHermitian hM.isHermitian
  let N := (Hᴴ * H).trace.re
  obtain ⟨_, _, _, _, _, hT, _, hmean, _, hd, _, _⟩ :=
    hasDerivAt_cubicEntropy_spectral_pair B M hB hM hNorm
  change (∑ p, pi p * x p ^ 2 / S * x p) = (M ^ 3).trace.re / S at hmean
  have hM₀ : M ≠ 0 := by
    intro hzero
    rw [hzero] at hT
    simpa using hT
  have hN : 0 ≤ N := by
    dsimp only [N]
    rw [← sum_normSq_eq_trace]
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hmmin : 0 ≤ mmin := by
    have h := (le_div_iff₀ hmmax).mp hρ
    exact (mul_nonneg (by norm_num) hmmax.le).trans h
  have hκ₁ : 1 ≤ bmax / bmin := (le_div_iff₀ hbmin).mpr (by simpa using hbmax)
  have hbracket := focal_bracket hκ₁ hκ hρ
  have hgap : bmin / 18 * N ≤ G - correction B M := by
    have hcoeff := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ bmin / 2 by positivity)
    calc
      _ = bmin / 2 * (1 / 9) * N := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hcoeff hN).trans
        (jensenGap_sub_correction_ge hB hM.posSemidef hM₀ hbmin hbmax hmmin hmmax hBbounds hMbounds)
  change bmin / 18 * N ≤ G - correction B M ∧ _
  refine ⟨hgap, 3 * (E + correction B M - G), ?_, ?_⟩
  · have hG : G = S * (Real.log (∑ p, pi p * x p ^ 2 / S * x p) -
          ∑ p, pi p * x p ^ 2 / S * Real.log (x p)) := by
      rw [hmean] <;> rfl
    rw [hG]
    exact hd
  · change 3 * (E + correction B M - G) / 3 ≤ E - bmin / 18 * N
    calc
      _ = E - (G - correction B M) := by ring
      _ ≤ _ := sub_le_sub_left hgap E

end D5.S3.Quantum.Divergence.GibbsCubicJensenAbsorption
