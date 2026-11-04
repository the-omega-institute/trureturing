/- GID: D5/S3/Quantum/NormCompression/FinitePowerSpectral
   generality: G
   mirror-B: none(waiver:ordinary-finite-power-supplier)
   mirror-E: none(waiver:ordinary-finite-power-supplier)
   anchors: []
   utility: none
   digest: Exact two-eigenvalue trace chart and positive boundary regularization. -/

import D5.S3.Quantum.NormCompression.FinitePowerTrace
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

noncomputable section

namespace D5.S3.Quantum.NormCompression.FinitePowerConcavity

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m : Type*} [Fintype m] [DecidableEq m]

local instance {n : Type*} [Fintype n] [DecidableEq n] : Pow (Matrix n n ℂ) ℝ := ⟨CFC.rpow⟩

/- The scalar inverse-metric coefficient, before matrix differentiation. -/
private theorem sinh_scaled_le {s v : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hv : 0 ≤ v) : Real.sinh (s * v) ≤ s * Real.sinh v := by
  have hc : ConvexOn ℝ (Set.Ici 0) Real.sinh := by
    refine MonotoneOn.convexOn_of_deriv (convex_Ici 0)
      Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn ?_
    intro x hx y hy hxy
    simp only [Real.deriv_sinh]
    exact Real.cosh_strictMonoOn.monotoneOn (interior_subset hx) (interior_subset hy) hxy
  have h := hc.2 (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)) hv
    (sub_nonneg.mpr hs1) hs0 (by ring : (1 - s) + s = 1)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.sinh_zero] using h

private theorem scalar_metric_gap {s a T D d : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hT : 2 * a < T) (hD : 2 * a ≤ D)
    (hd : d ^ 2 = T ^ 2 - 4 * a ^ 2) :
    (T - D) * (T + D / (2 * s + 1)) < d ^ 2 := by
  have hden : 0 < 2 * s + 1 := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hTD : 4 * a ^ 2 < T * D := by nlinarith
  have hDD : 4 * a ^ 2 ≤ D ^ 2 := by nlinarith
  apply (mul_lt_mul_iff_left₀ hden).mp
  field_simp
  nlinarith [mul_pos hs (sub_pos.mpr hTD)]

private theorem hyperbolic_metric_gap {s a v : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 < a) (hv : 0 < v) :
    let T := 2 * a * Real.cosh ((s + 1) * v)
    let D := 2 * s * a * Real.sinh v / Real.sinh (s * v)
    let d := 2 * a * Real.sinh ((s + 1) * v)
    (T - D) * (T + D / (2 * s + 1)) < d ^ 2 := by
  dsimp only
  apply scalar_metric_gap hs0 ha
  · have hcosh : 1 < Real.cosh ((s + 1) * v) :=
      Real.one_lt_cosh.mpr (ne_of_gt (by positivity))
    nlinarith
  · have hden : 0 < Real.sinh (s * v) := Real.sinh_pos_iff.mpr (mul_pos hs0 hv)
    apply (le_div_iff₀ hden).mpr
    have h := sinh_scaled_le hs0.le hs1.le hv.le
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h)]
  · have h := Real.cosh_sq_sub_sinh_sq ((s + 1) * v)
    have heq : Real.sinh ((s + 1) * v) ^ 2 =
        Real.cosh ((s + 1) * v) ^ 2 - 1 := by linarith
    calc
      (2 * a * Real.sinh ((s + 1) * v)) ^ 2 =
          4 * a ^ 2 * Real.sinh ((s + 1) * v) ^ 2 := by ring
      _ = 4 * a ^ 2 * (Real.cosh ((s + 1) * v) ^ 2 - 1) := by rw [heq]
      _ = (2 * a * Real.cosh ((s + 1) * v)) ^ 2 - 4 * a ^ 2 := by ring

private theorem root_power_cancel {q w : ℝ} (hq : 0 < q) (hw : 0 < w) :
    (w ^ (1 / (2 * q))) ^ (2 * q - 1) = w / w ^ (1 / (2 * q)) := by
  rw [Real.rpow_sub (Real.rpow_pos_of_pos hw _) _ _, Real.rpow_one,
    ← Real.rpow_mul hw.le]
  rw [show 1 / (2 * q) * (2 * q) = (1 : ℝ) by field_simp [hq.ne'], Real.rpow_one]

def boundaryTable (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![ε, ε; ε, 4 * ε]

private theorem boundary_det {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    (Aq q (boundaryTable ε)).det =
      ((ε ^ (1 / (2 * q))) ^ 2 * (4 ^ (1 / (2 * q)) - 1) : ℝ) := by
  simp only [Matrix.det_fin_two, Aq, boundaryTable, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hε.le]
  push_cast
  ring

/-- The corrected boundary columns are independent for every real q > 0. -/
theorem boundary_gram_posDef {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    (Aq q (boundaryTable ε) * (Aq q (boundaryTable ε))ᴴ).PosDef := by
  have hpos : 0 < (ε ^ (1 / (2 * q))) ^ 2 *
      ((4 : ℝ) ^ (1 / (2 * q)) - 1) := by
    apply mul_pos (sq_pos_of_pos (Real.rpow_pos_of_pos hε _))
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by positivity))
  have hdet : (Aq q (boundaryTable ε)).det ≠ 0 := by
    rw [boundary_det hq hε]
    exact_mod_cast hpos.ne'
  have hu : IsUnit (Aq q (boundaryTable ε)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  apply (Matrix.posSemidef_self_mul_conjTranspose _).posDef_iff_isUnit.mpr
  exact hu.mul (by simpa only [Matrix.star_eq_conjTranspose] using hu.star)

/-- Append the two independent boundary columns while shifting every existing entry. -/
def regularizedTable (ε : ℝ) (W : Matrix (Fin 2) m ℝ) :
    Matrix (Fin 2) (m ⊕ Fin 2) ℝ :=
  Matrix.fromCols (fun b j => W b j + ε) (boundaryTable ε)

theorem regularizedTable_pos {ε : ℝ} (hε : 0 < ε)
    (W : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j) :
    ∀ b j, 0 < regularizedTable ε W b j := by
  intro b j
  cases j with
  | inl j => exact add_pos_of_nonneg_of_pos (hW b j) hε
  | inr j =>
    change 0 < boundaryTable ε b j
    fin_cases b <;> fin_cases j <;> simp [boundaryTable] <;> positivity

theorem regularized_gram_posDef {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (W : Matrix (Fin 2) m ℝ) :
    (Aq q (regularizedTable ε W) * (Aq q (regularizedTable ε W))ᴴ).PosDef := by
  have hA : Aq q (regularizedTable ε W) =
      Matrix.fromCols (Aq q (fun b j => W b j + ε)) (Aq q (boundaryTable ε)) := by
    ext b j
    cases j <;> rfl
  rw [hA, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_self_mul_conjTranspose _)
    (boundary_gram_posDef hq hε)

private theorem Fq_fromCols_zero {n : Type*} [Fintype n] [DecidableEq n]
    {q : ℝ} (hq : 0 < q) (W : Matrix (Fin 2) m ℝ) :
    Fq q (Matrix.fromCols W (0 : Matrix (Fin 2) n ℝ)) = Fq q W := by
  have hA : Aq q (Matrix.fromCols W (0 : Matrix (Fin 2) n ℝ)) =
      Matrix.fromCols (Aq q W) (0 : Matrix (Fin 2) n ℂ) := by
    ext b j
    cases j with
    | inl j => rfl
    | inr j =>
      change (((0 : ℝ) ^ (1 / (2 * q)) : ℝ) : ℂ) = 0
      exact_mod_cast (Real.zero_rpow (by positivity : (1 : ℝ) / (2 * q) ≠ 0))
  rw [Fq, schattenPow_eq_eigenPow_rowGram (2 * q) (by positivity),
    Fq, schattenPow_eq_eigenPow_rowGram (2 * q) (by positivity), hA,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp

/-- The actual two-column regularization tends to the unregularized trace power. -/
theorem tendsto_regularized_Fq {q : ℝ} (hq : 0 < q) (W : Matrix (Fin 2) m ℝ) :
    Filter.Tendsto (fun ε : ℝ => Fq q (regularizedTable ε W)) (nhds 0)
      (nhds (Fq q W)) := by
  have hreg : Continuous (fun ε : ℝ => regularizedTable ε W) := by
    apply continuous_pi
    intro b
    apply continuous_pi
    intro j
    cases j with
    | inl j => exact continuous_const.add continuous_id
    | inr j =>
      change Continuous (fun ε : ℝ => boundaryTable ε b j)
      fin_cases b <;> fin_cases j <;> simp [boundaryTable] <;> fun_prop
  have hzero : regularizedTable 0 W = Matrix.fromCols W (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext b j
    cases j with
    | inl j => change W b j + 0 = W b j; simp
    | inr j =>
      change boundaryTable 0 b j = 0
      fin_cases b <;> fin_cases j <;> simp [boundaryTable]
  have h := ((continuous_Fq hq).comp hreg).tendsto 0
  change Filter.Tendsto (fun ε : ℝ => Fq q (regularizedTable ε W)) (nhds 0)
    (nhds (Fq q (regularizedTable 0 W))) at h
  rw [hzero, Fq_fromCols_zero hq] at h
  exact h

#print axioms boundary_gram_posDef

private theorem scalar_gap_with_weights {s T D d h : ℝ}
    (hs : 0 < s) (hden : 0 < T + D / (2 * s + 1))
    (hgap : (T - D) * (T + D / (2 * s + 1)) < d ^ 2)
    (g w : m → ℝ) (hw : ∀ j, 0 < w j)
    (hg : ∑ j, g j = -d * h)
    (hwsum : ∑ j, w j = T + D / (2 * s + 1)) :
    0 ≤ (1 / s) * ((∑ j, g j ^ 2 / w j) - (T - D) * h ^ 2) ∧
    ((1 / s) * ((∑ j, g j ^ 2 / w j) - (T - D) * h ^ 2) = 0 →
      h = 0 ∧ ∀ j, g j = 0) := by
  let c := T - D
  let k := T + D / (2 * s + 1)
  let u := ∑ j, g j ^ 2 / w j
  have hcs := Finset.sq_sum_div_le_sum_sq_div Finset.univ g (by simpa using hw)
  rw [hg, hwsum] at hcs
  have hcs' : d ^ 2 * h ^ 2 ≤ k * u := by
    have ht := (div_le_iff₀ hden).mp hcs
    dsimp only [k, u]
    nlinarith
  have hgap' : 0 < d ^ 2 - c * k := sub_pos.mpr hgap
  have hu : 0 ≤ u - c * h ^ 2 := by
    have hp := mul_nonneg hgap'.le (sq_nonneg h)
    have : 0 ≤ k * (u - c * h ^ 2) := by nlinarith
    exact nonneg_of_mul_nonneg_right this hden
  refine ⟨mul_nonneg (by positivity) hu, ?_⟩
  intro heq
  have heq' : u - c * h ^ 2 = 0 :=
    (mul_eq_zero.mp heq).resolve_left (by positivity)
  have hh : h = 0 := by
    by_contra hh
    have hp := mul_pos hgap' (sq_pos_of_ne_zero hh)
    have hk := congrArg (fun z : ℝ => k * z) heq'
    nlinarith
  refine ⟨hh, ?_⟩
  have hu0 : u = 0 := by simpa only [hh, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero] using heq'
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => div_nonneg (sq_nonneg (g j)) (hw j).le)).mp hu0
  intro j
  have hz : g j ^ 2 = 0 := (div_eq_zero_iff.mp (hall j (Finset.mem_univ j))).resolve_right
    (hw j).ne'
  exact sq_eq_zero_iff.mp hz

/- This identity checks the off-diagonal trace multiplicity and every local coefficient. -/
private theorem hessian_column_coefficients (s S₀₀ S₁₁ ℓ a b u v : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    -s * S₀₀ * u ^ 2 - s * S₁₁ * v ^ 2 +
        2 * ℓ * (u * v / 2 - (2 * s + 1) / 4 *
          (b / a * u ^ 2 + a / b * v ^ 2)) =
      -(s * (S₀₀ * u ^ 2 + 2 * ℓ * u * v + S₁₁ * v ^ 2) +
        (2 * s + 1) * ℓ / (2 * a * b) * (b * u - a * v) ^ 2) := by
  field_simp [ha, hb]
  <;> ring

private def sym2 (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; b, c]

private def spectralTrace (q a b c : ℝ) : ℝ :=
  ((a + c + Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) ^ q +
    ((a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) ^ q

private theorem spectralTrace_hasDerivAt {q : ℝ} {a b c : ℝ → ℝ}
    {da db dc t : ℝ} (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hc : HasDerivAt c dc t)
    (hdisc : 0 < (a t - c t) ^ 2 + 4 * b t ^ 2)
    (hlo : 0 < (a t + c t - Real.sqrt ((a t - c t) ^ 2 + 4 * b t ^ 2)) / 2) :
    let δ := Real.sqrt ((a t - c t) ^ 2 + 4 * b t ^ 2)
    let dδ := (2 * (a t - c t) * (da - dc) + 8 * b t * db) / (2 * δ)
    HasDerivAt (fun t : ℝ => spectralTrace q (a t) (b t) (c t))
      (((da + dc + dδ) / 2) * q * ((a t + c t + δ) / 2) ^ (q - 1) +
        ((da + dc - dδ) / 2) * q * ((a t + c t - δ) / 2) ^ (q - 1)) t := by
  dsimp only
  have hd : HasDerivAt (fun t : ℝ => (a t - c t) ^ 2 + 4 * b t ^ 2)
      (2 * (a t - c t) * (da - dc) + 8 * b t * db) t := by
    convert ((ha.sub hc).pow 2).add ((hb.pow 2).const_mul 4) using 1 <;> simp <;> ring
  have hr := hd.sqrt hdisc.ne'
  have hp := ((ha.add hc).add hr).div_const 2
  have hm := ((ha.add hc).sub hr).div_const 2
  have hhi : 0 < (a t + c t + Real.sqrt ((a t - c t) ^ 2 + 4 * b t ^ 2)) / 2 := by
    linarith [Real.sqrt_nonneg ((a t - c t) ^ 2 + 4 * b t ^ 2)]
  exact (hp.rpow_const (Or.inl hhi.ne')).add (hm.rpow_const (Or.inl hlo.ne'))

private theorem sym2_charpoly (a b c ξ η : ℝ)
    (hsum : ξ + η = a + c) (hprod : ξ * η = a * c - b ^ 2) :
    (sym2 a b c).charpoly =
      (Polynomial.X - Polynomial.C (ξ : ℂ)) *
        (Polynomial.X - Polynomial.C (η : ℂ)) := by
  have hs := congrArg (fun x : ℝ => Polynomial.C (x : ℂ)) hsum
  have hp := congrArg (fun x : ℝ => Polynomial.C (x : ℂ)) hprod
  push_cast at hs hp
  simp only [map_add, map_mul, map_sub, map_pow] at hs hp
  simp [Matrix.charpoly_fin_two, Matrix.trace, Matrix.det_fin_two, sym2,
    Fin.sum_univ_two]
  linear_combination Polynomial.X * hs - hp

private theorem sym2_explicit_charpoly (a b c : ℝ) :
    (sym2 a b c).charpoly =
      (Polynomial.X - Polynomial.C (((a + c + Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2 : ℝ) : ℂ)) *
      (Polynomial.X - Polynomial.C (((a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2 : ℝ) : ℂ)) := by
  apply sym2_charpoly
  · ring
  · have hd := Real.sq_sqrt (show 0 ≤ (a - c) ^ 2 + 4 * b ^ 2 by positivity)
    nlinarith

private theorem sym2_posDef_low_eigenvalue_pos (a b c : ℝ) (hR : (sym2 a b c).PosDef) :
    0 < (a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2 := by
  let η := (a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2
  have hmem : (η : ℂ) ∈ spectrum ℂ (sym2 a b c) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    rw [sym2_explicit_charpoly]
    simp [Polynomial.IsRoot, η]
  rw [hR.isHermitian.spectrum_eq_image_range] at hmem
  obtain ⟨x, ⟨i, rfl⟩, heq⟩ := hmem
  have heq' : hR.isHermitian.eigenvalues i = η := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using congrArg Complex.re heq
  change 0 < η
  rw [← heq']
  exact hR.eigenvalues_pos i

private theorem trace_rpow_sym2 (q a b c : ℝ) (hR : (sym2 a b c).PosSemidef) :
    (CFC.rpow (sym2 a b c) q).trace.re =
      ((a + c + Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) ^ q +
      ((a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) ^ q := by
  let ξ := (a + c + Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2
  let η := (a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2
  have hc := sym2_explicit_charpoly a b c
  have hr : (sym2 a b c).charpoly.roots = {(ξ : ℂ), (η : ℂ)} := by
    rw [hc, Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Polynomial.X_sub_C_ne_zero _)), Polynomial.roots_X_sub_C,
      Polynomial.roots_X_sub_C]
    rfl
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hR.nonneg,
    D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum _ hR.isHermitian]
  have he : ∑ i, hR.isHermitian.eigenvalues i ^ q =
      ((sym2 a b c).charpoly.roots.map (fun z : ℂ => z.re ^ q)).sum := by
    rw [hR.isHermitian.roots_charpoly_eq_eigenvalues]
    simp [Multiset.map_map, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, List.sum_ofFn]
  rw [he, hr]
  simp [ξ, η]

private def gramDiagonal (q : ℝ) (W : Matrix (Fin 2) m ℝ) (b : Fin 2) : ℝ :=
  ∑ j, W b j ^ (1 / q)

private def gramOffDiagonal (q : ℝ) (W : Matrix (Fin 2) m ℝ) : ℝ :=
  ∑ j, (W 0 j * W 1 j) ^ (1 / (2 * q))

private theorem power_root_sq {q w : ℝ} (hq : 0 < q) (hw : 0 ≤ w) :
    (w ^ (1 / (2 * q))) ^ 2 = w ^ (1 / q) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hw]
  congr 1
  field_simp [hq.ne']
  <;> ring

private theorem rowGram_sym2 {q : ℝ} (hq : 0 < q) (W : Matrix (Fin 2) m ℝ)
    (hW : ∀ b j, 0 ≤ W b j) :
    Aq q W * (Aq q W)ᴴ =
      sym2 (gramDiagonal q W 0) (gramOffDiagonal q W) (gramDiagonal q W 1) := by
  have he (b c : Fin 2) : (Aq q W * (Aq q W)ᴴ) b c =
      ((∑ j, W b j ^ (1 / (2 * q)) * W c j ^ (1 / (2 * q))) : ℝ) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Aq]
  have hdiag (b : Fin 2) : (∑ j, W b j ^ (1 / (2 * q)) *
      W b j ^ (1 / (2 * q))) = gramDiagonal q W b := by
    unfold gramDiagonal
    apply Finset.sum_congr rfl
    intro j _
    simpa [pow_two] using power_root_sq hq (hW b j)
  have hoff : (∑ j, W 0 j ^ (1 / (2 * q)) * W 1 j ^ (1 / (2 * q))) =
      gramOffDiagonal q W := by
    unfold gramOffDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact (Real.mul_rpow (hW 0 j) (hW 1 j)).symm
  ext b c
  rw [he]
  fin_cases b <;> fin_cases c
  · exact congrArg Complex.ofReal (hdiag 0)
  · exact congrArg Complex.ofReal hoff
  · change (((∑ j, W 1 j ^ (1 / (2 * q)) * W 0 j ^ (1 / (2 * q))) : ℝ) : ℂ) =
      (gramOffDiagonal q W : ℂ)
    simpa only [mul_comm] using congrArg Complex.ofReal hoff
  · exact congrArg Complex.ofReal (hdiag 1)

/-- A scalar spectral formula proved equal to the actual operator trace power. -/
theorem Fq_eq_two_eigenvalue_formula {q : ℝ} (hq : 0 < q)
    (W : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j) :
    let a := gramDiagonal q W 0
    let b := gramOffDiagonal q W
    let c := gramDiagonal q W 1
    Fq q W = ((a + c + Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) ^ q +
      ((a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) ^ q := by
  dsimp only
  rw [Fq_eq_trace_rpow hq, rowGram_sym2 hq W hW]
  apply trace_rpow_sym2
  rw [← rowGram_sym2 hq W hW]
  exact Matrix.posSemidef_self_mul_conjTranspose _

private theorem exp_pair_sum (u w r : ℝ) :
    Real.exp (u * r) + Real.exp (w * r) =
      2 * Real.exp ((u + w) / 2 * r) * Real.cosh (r * ((u - w) / 2)) := by
  rw [Real.cosh_eq]
  have hp : Real.exp ((u + w) / 2 * r) * Real.exp (r * ((u - w) / 2)) =
      Real.exp (u * r) := by rw [← Real.exp_add]; congr 1; ring
  have hm : Real.exp ((u + w) / 2 * r) * Real.exp (-(r * ((u - w) / 2))) =
      Real.exp (w * r) := by rw [← Real.exp_add]; congr 1; ring
  nlinarith

private theorem exp_pair_sub (u w r : ℝ) :
    Real.exp (u * r) - Real.exp (w * r) =
      2 * Real.exp ((u + w) / 2 * r) * Real.sinh (r * ((u - w) / 2)) := by
  rw [Real.sinh_eq]
  have hp : Real.exp ((u + w) / 2 * r) * Real.exp (r * ((u - w) / 2)) =
      Real.exp (u * r) := by rw [← Real.exp_add]; congr 1; ring
  have hm : Real.exp ((u + w) / 2 * r) * Real.exp (-(r * ((u - w) / 2))) =
      Real.exp (w * r) := by rw [← Real.exp_add]; congr 1; ring
  nlinarith

/-- The strict scalar coefficient for every ordered positive pair of eigenvalues
and every real exponent in the open interval, with no fixed-q specialization. -/
private theorem eigenvalue_metric_gap {s ξ η : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hη : 0 < η) (hξη : η < ξ) :
    let T := ξ ^ (s + 1) + η ^ (s + 1)
    let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
    let d := ξ ^ (s + 1) - η ^ (s + 1)
    (T - D) * (T + D / (2 * s + 1)) < d ^ 2 := by
  let u := Real.log ξ
  let w := Real.log η
  let v := (u - w) / 2
  let a := Real.exp ((u + w) / 2 * (s + 1))
  have hξ : 0 < ξ := hη.trans hξη
  have hv : 0 < v := by
    dsimp [v, u, w]
    exact div_pos (sub_pos.mpr (Real.log_lt_log hη hξη)) (by norm_num)
  have ha : 0 < a := Real.exp_pos _
  have hp (r : ℝ) : ξ ^ r + η ^ r =
      2 * Real.exp ((u + w) / 2 * r) * Real.cosh (r * v) := by
    rw [Real.rpow_def_of_pos hξ, Real.rpow_def_of_pos hη]
    exact exp_pair_sum u w r
  have hm (r : ℝ) : ξ ^ r - η ^ r =
      2 * Real.exp ((u + w) / 2 * r) * Real.sinh (r * v) := by
    rw [Real.rpow_def_of_pos hξ, Real.rpow_def_of_pos hη]
    exact exp_pair_sub u w r
  have hdiff : ξ - η = 2 * Real.exp ((u + w) / 2) * Real.sinh v := by
    simpa only [Real.rpow_one, mul_one, one_mul] using hm 1
  have hprod : (ξ * η) ^ s = Real.exp ((u + w) * s) := by
    rw [Real.rpow_def_of_pos (mul_pos hξ hη), Real.log_mul hξ.ne' hη.ne']
  have he : Real.exp ((u + w) * s) * Real.exp ((u + w) / 2) =
      a * Real.exp ((u + w) / 2 * s) := by
    dsimp [a]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hD : 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s) =
      2 * s * a * Real.sinh v / Real.sinh (s * v) := by
    rw [hprod, hdiff, hm s]
    have hE := (Real.exp_pos ((u + w) / 2 * s)).ne'
    have hS := (Real.sinh_pos_iff.mpr (mul_pos hs0 hv)).ne'
    field_simp [hE, hS]
    ring_nf at he ⊢
    nlinarith [congrArg (fun z : ℝ => s * Real.sinh v * z) he]
  dsimp only
  rw [hp (s + 1), hm (s + 1), hD]
  exact hyperbolic_metric_gap hs0 hs1 ha hv

private def gramDiagonalVelocity (q : ℝ) (W V : Matrix (Fin 2) m ℝ) (b : Fin 2) : ℝ :=
  ∑ j, V b j * (1 / q) * W b j ^ (1 / q - 1)

private def gramOffDiagonalVelocity (q : ℝ) (W V : Matrix (Fin 2) m ℝ) : ℝ :=
  ∑ j, (V 0 j * W 1 j + W 0 j * V 1 j) * (1 / (2 * q)) *
    (W 0 j * W 1 j) ^ (1 / (2 * q) - 1)

private theorem gramDiagonal_hasDerivAt {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < (W + t • V) b j) (b : Fin 2) :
    HasDerivAt (fun u : ℝ => gramDiagonal q (W + u • V) b)
      (gramDiagonalVelocity q (W + t • V) V b) t := by
  unfold gramDiagonal gramDiagonalVelocity
  apply HasDerivAt.fun_sum
  intro j _
  have h := ((hasDerivAt_const t (W b j)).add
    ((hasDerivAt_id t).mul_const (V b j))).rpow_const
      (p := 1 / q) (Or.inl (hW b j).ne')
  simpa using h

private theorem gramOffDiagonal_hasDerivAt {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < (W + t • V) b j) :
    HasDerivAt (fun u : ℝ => gramOffDiagonal q (W + u • V))
      (gramOffDiagonalVelocity q (W + t • V) V) t := by
  unfold gramOffDiagonal gramOffDiagonalVelocity
  apply HasDerivAt.fun_sum
  intro j _
  have h0 := (hasDerivAt_const t (W 0 j)).add ((hasDerivAt_id t).mul_const (V 0 j))
  have h1 := (hasDerivAt_const t (W 1 j)).add ((hasDerivAt_id t).mul_const (V 1 j))
  simpa using (h0.mul h1).rpow_const (p := 1 / (2 * q))
    (Or.inl (mul_pos (hW 0 j) (hW 1 j)).ne')

/-- First derivative of the actual Schatten power along an affine table path.
The spectral positivity premises describe the open SPD chart; they do not
assume any derivative, Hessian sign, or concavity. -/
private theorem Fq_affine_hasDerivAt {q t : ℝ} (hq : 0 < q)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < (W + t • V) b j)
    (hdisc : 0 < (gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
      4 * gramOffDiagonal q (W + t • V) ^ 2)
    (hlo : 0 < (gramDiagonal q (W + t • V) 0 + gramDiagonal q (W + t • V) 1 -
      Real.sqrt ((gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
        4 * gramOffDiagonal q (W + t • V) ^ 2)) / 2) :
    let a := gramDiagonal q (W + t • V) 0
    let b := gramOffDiagonal q (W + t • V)
    let c := gramDiagonal q (W + t • V) 1
    let da := gramDiagonalVelocity q (W + t • V) V 0
    let db := gramOffDiagonalVelocity q (W + t • V) V
    let dc := gramDiagonalVelocity q (W + t • V) V 1
    let δ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)
    let dδ := (2 * (a - c) * (da - dc) + 8 * b * db) / (2 * δ)
    HasDerivAt (fun u : ℝ => Fq q (W + u • V))
      (((da + dc + dδ) / 2) * q * ((a + c + δ) / 2) ^ (q - 1) +
        ((da + dc - dδ) / 2) * q * ((a + c - δ) / 2) ^ (q - 1)) t := by
  have hpos : ∀ᶠ u : ℝ in nhds t, ∀ b j, 0 < (W + u • V) b j := by
    apply Filter.eventually_all.mpr
    intro b
    apply Filter.eventually_all.mpr
    intro j
    have hcont : Continuous (fun u : ℝ => (W + u • V) b j) := by fun_prop
    exact (hcont.tendsto t).eventually (Ioi_mem_nhds (hW b j))
  have heq : (fun u : ℝ => Fq q (W + u • V)) =ᶠ[nhds t]
      (fun u => spectralTrace q (gramDiagonal q (W + u • V) 0)
        (gramOffDiagonal q (W + u • V)) (gramDiagonal q (W + u • V) 1)) := by
    filter_upwards [hpos] with u hu
    exact Fq_eq_two_eigenvalue_formula hq _ (fun b j => (hu b j).le)
  exact (spectralTrace_hasDerivAt (gramDiagonal_hasDerivAt W V hW 0)
    (gramOffDiagonal_hasDerivAt W V hW) (gramDiagonal_hasDerivAt W V hW 1)
    hdisc hlo).congr_of_eventuallyEq heq

private def spectralVelocity (q a b c da db dc : ℝ) : ℝ :=
  let δ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)
  let dδ := (2 * (a - c) * (da - dc) + 8 * b * db) / (2 * δ)
  ((da + dc + dδ) / 2) * q * ((a + c + δ) / 2) ^ (q - 1) +
    ((da + dc - dδ) / 2) * q * ((a + c - δ) / 2) ^ (q - 1)

/-- Differentiation of the spectral velocity, retaining all noncommuting
(off-diagonal) terms through the discriminant. -/
private theorem spectralVelocity_hasDerivAt {q : ℝ} {a b c da db dc : ℝ → ℝ}
    {dda ddb ddc : ℝ}
    (ha : HasDerivAt a (da 0) 0) (hb : HasDerivAt b (db 0) 0)
    (hc : HasDerivAt c (dc 0) 0)
    (hda : HasDerivAt da dda 0) (hdb : HasDerivAt db ddb 0)
    (hdc : HasDerivAt dc ddc 0)
    (hdisc : 0 < (a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)
    (hlo : 0 < (a 0 + c 0 - Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)) / 2) :
    let δ := Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)
    let v := 2 * (a 0 - c 0) * (da 0 - dc 0) + 8 * b 0 * db 0
    let dv := 2 * (da 0 - dc 0) ^ 2 + 2 * (a 0 - c 0) * (dda - ddc) +
      8 * (db 0) ^ 2 + 8 * b 0 * ddb
    let dδ := v / (2 * δ)
    let ddδ := (dv * (2 * δ) - v * (2 * dδ)) / (2 * δ) ^ 2
    let ξ := (a 0 + c 0 + δ) / 2
    let η := (a 0 + c 0 - δ) / 2
    let dξ := (da 0 + dc 0 + dδ) / 2
    let dη := (da 0 + dc 0 - dδ) / 2
    let ddξ := (dda + ddc + ddδ) / 2
    let ddη := (dda + ddc - ddδ) / 2
    HasDerivAt (fun t : ℝ => spectralVelocity q (a t) (b t) (c t) (da t) (db t) (dc t))
      (q * (ddξ * ξ ^ (q - 1) + ddη * η ^ (q - 1)) +
        q * (q - 1) * (dξ ^ 2 * ξ ^ (q - 2) + dη ^ 2 * η ^ (q - 2))) 0 := by
  dsimp only
  have hδ := (((ha.sub hc).pow 2).add ((hb.pow 2).const_mul 4)).sqrt hdisc.ne'
  have hδ' : HasDerivAt (fun t : ℝ => Real.sqrt ((a t - c t) ^ 2 + 4 * b t ^ 2))
      ((2 * (a 0 - c 0) * (da 0 - dc 0) + 8 * b 0 * db 0) /
        (2 * Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2))) 0 := by
    convert hδ using 1 <;> simp <;> ring
  have hv : HasDerivAt (fun t : ℝ =>
      2 * (a t - c t) * (da t - dc t) + 8 * b t * db t)
      (2 * (da 0 - dc 0) ^ 2 + 2 * (a 0 - c 0) * (dda - ddc) +
        8 * (db 0) ^ 2 + 8 * b 0 * ddb) 0 := by
    convert (((ha.sub hc).const_mul 2).mul (hda.sub hdc)).add
      ((hb.const_mul 8).mul hdb) using 1 <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq] <;> ring
  have hdδ := hv.div (hδ'.const_mul 2)
    (by positivity : 2 * Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2) ≠ 0)
  have hξ := ((ha.add hc).add hδ').div_const 2
  have hη := ((ha.add hc).sub hδ').div_const 2
  have hdξ := ((hda.add hdc).add hdδ).div_const 2
  have hdη := ((hda.add hdc).sub hdδ).div_const 2
  have hhi : 0 < (a 0 + c 0 + Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)) / 2 := by
    linarith [Real.sqrt_nonneg ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)]
  have h := ((hdξ.mul_const q).mul (hξ.rpow_const (p := q - 1) (Or.inl hhi.ne'))).add
    ((hdη.mul_const q).mul (hη.rpow_const (p := q - 1) (Or.inl hlo.ne')))
  convert h using 1
  · rfl
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq,
      show q - 1 - 1 = q - 2 by ring]
    ring

/- The local quadratic estimate in whitened coordinates. -/

end D5.S3.Quantum.NormCompression.FinitePowerConcavity
