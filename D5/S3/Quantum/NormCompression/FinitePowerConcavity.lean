/- GID: D5/S3/Quantum/NormCompression/FinitePowerConcavity
   generality: G
   mirror-B: none(waiver:ordinary-finite-power-supplier)
   mirror-E: none(waiver:ordinary-finite-power-supplier)
   anchors: []
   utility: none
   digest: Full-cone concavity of the actual trace power for every finite two-row table.
-/

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

/-- The rank-one inverse used after whitening, obtained from Mathlib's Woodbury identity. -/
private theorem inverse_rank_one {n : Type*} [Fintype n] [DecidableEq n]
    (u : n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ((1 : Matrix n n ℝ) + t • Matrix.vecMulVec u u)⁻¹ =
      1 - (t / (1 + t * (u ⬝ᵥ u))) • Matrix.vecMulVec u u := by
  let U : Matrix n Unit ℝ := fun i _ => u i
  let V : Matrix Unit n ℝ := fun _ j => t * u j
  let δ := 1 + t * (u ⬝ᵥ u)
  have hδ : 0 < δ := by
    have hn : 0 ≤ u ⬝ᵥ u := by
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
    dsimp only [δ]
    positivity
  have hsmall : (1 : Matrix Unit Unit ℝ) + V * U = Matrix.diagonal (fun _ => δ) := by
    ext i j
    cases i
    cases j
    change 1 + (∑ k, (t * u k) * u k) = δ
    simp [δ, dotProduct, Finset.mul_sum, mul_assoc]
  have hunit : IsUnit ((1 : Matrix Unit Unit ℝ)⁻¹ + V * (1 : Matrix n n ℝ)⁻¹ * U) := by
    simp only [inv_one, Matrix.mul_one]
    rw [hsmall]
    apply Matrix.isUnit_diagonal.mpr
    exact Pi.isUnit_iff.mpr (fun _ => isUnit_iff_ne_zero.mpr hδ.ne')
  have hwood := Matrix.add_mul_mul_inv_eq_sub (1 : Matrix n n ℝ) U
    (1 : Matrix Unit Unit ℝ) V isUnit_one isUnit_one hunit
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one] at hwood
  have hUV : U * V = t • Matrix.vecMulVec u u := by
    ext i j
    change (∑ _ : Unit, u i * (t * u j)) = t * (u i * u j)
    simp only [Fintype.sum_unique]
    ring
  have hdiag : (Matrix.diagonal (fun _ : Unit => δ))⁻¹ =
      Matrix.diagonal (fun _ : Unit => δ⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    cases i
    cases j
    simp [hδ.ne']
  rw [hUV, hsmall, hdiag] at hwood
  convert hwood using 2
  ext i j
  change t / (1 + t * (u ⬝ᵥ u)) * (u i * u j) =
    (U * Matrix.diagonal (fun _ : Unit => δ⁻¹) * V) i j
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_unique, Matrix.mul_diagonal, U, V]
  dsimp only [δ]
  ring

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

private theorem rpow_two_point_interpolation {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℂ) (hR : R.PosSemidef) (s ξ η : ℝ) (hne : ξ ≠ η)
    (hsp : ∀ x ∈ spectrum ℝ R, x = ξ ∨ x = η) :
    CFC.rpow R s = ((ξ ^ s - η ^ s) / (ξ - η)) • R +
      ((ξ * η ^ s - η * ξ ^ s) / (ξ - η)) • (1 : Matrix n n ℂ) := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hR.nonneg]
  have hf : (spectrum ℝ R).EqOn (fun x : ℝ => x ^ s)
      (fun x : ℝ => ((ξ ^ s - η ^ s) / (ξ - η)) * x +
        (ξ * η ^ s - η * ξ ^ s) / (ξ - η)) := by
    intro x hx
    rcases hsp x hx with rfl | rfl <;>
      field_simp [sub_ne_zero.mpr hne] <;> ring
  rw [cfc_congr hf,
    cfc_add_const ((ξ * η ^ s - η * ξ ^ s) / (ξ - η))
      (fun x : ℝ => ((ξ ^ s - η ^ s) / (ξ - η)) * x) R
      (by fun_prop) hR.isHermitian.isSelfAdjoint,
    cfc_const_mul_id ((ξ ^ s - η ^ s) / (ξ - η)) R hR.isHermitian.isSelfAdjoint]
  simp only [Algebra.algebraMap_eq_smul_one]

private theorem two_point_rpow_offDiagonal_pos {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℂ) (hR : R.PosSemidef) {s ξ η : ℝ} (hs : 0 < s)
    (hη : 0 ≤ η) (hξη : η < ξ)
    (hsp : ∀ x ∈ spectrum ℝ R, x = ξ ∨ x = η)
    (i j : n) (hij : i ≠ j) (hentry : 0 < (R i j).re) :
    0 < (CFC.rpow R s i j).re := by
  have hα : 0 < (ξ ^ s - η ^ s) / (ξ - η) :=
    div_pos (sub_pos.mpr (Real.rpow_lt_rpow hη hξη hs)) (sub_pos.mpr hξη)
  rw [rpow_two_point_interpolation R hR s ξ η (ne_of_gt hξη) hsp]
  simpa only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
    smul_zero, add_zero, Complex.smul_re, smul_eq_mul] using mul_pos hα hentry

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

/-- Off-diagonal positivity for the actual two-dimensional positive power.
No spectral ordering or distinctness assumption is imposed on the caller. -/
private theorem rpow_offDiagonal_pos (R : Matrix (Fin 2) (Fin 2) ℂ)
    (hR : R.PosSemidef) {s : ℝ} (hs : 0 < s) (hentry : 0 < (R 0 1).re) :
    0 < (CFC.rpow R s 0 1).re := by
  let ev := hR.isHermitian.eigenvalues
  have hsp : ∀ x ∈ spectrum ℝ R, x = ev 0 ∨ x = ev 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := hR.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    fin_cases i <;> simp [ev]
  have hne : ev 0 ≠ ev 1 := by
    intro heq
    have hscalar : R = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (ev 0) := by
      refine CFC.eq_algebraMap_of_spectrum_subset_singleton R (ev 0) ?_
        hR.isHermitian.isSelfAdjoint
      intro x hx
      rcases hsp x hx with h | h <;> simp_all
    have hzero : R 0 1 = 0 := by rw [hscalar]; simp [Algebra.algebraMap_eq_smul_one]
    simpa [hzero] using hentry
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact two_point_rpow_offDiagonal_pos R hR hs (hR.eigenvalues_nonneg 0) hlt
      (fun x hx => (hsp x hx).symm) 0 1 (by decide) hentry
  · exact two_point_rpow_offDiagonal_pos R hR hs (hR.eigenvalues_nonneg 1) hgt
      hsp 0 1 (by decide) hentry

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
private theorem local_quadratic_duality {y₀ y₁ t : ℝ}
    (hn : 0 < y₀ ^ 2 + y₁ ^ 2) (ht : 0 < t) (p₀ p₁ r₀ r₁ : ℝ) :
    let n := y₀ ^ 2 + y₁ ^ 2
    let H := 1 + t * n
    let U := y₀ * (p₀ - r₀) + y₁ * (p₁ - r₁)
    let V := y₁ * r₀ - y₀ * r₁ - (y₁ * p₀ - y₀ * p₁) / H
    0 ≤ p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (n + 1 / t) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      t * (y₁ * r₀ - y₀ * r₁) ^ 2 ∧
    (p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (n + 1 / t) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      t * (y₁ * r₀ - y₀ * r₁) ^ 2 = 0 → U = 0 ∧ V = 0) := by
  dsimp only
  let n := y₀ ^ 2 + y₁ ^ 2
  let H := 1 + t * n
  let U := y₀ * (p₀ - r₀) + y₁ * (p₁ - r₁)
  let V := y₁ * r₀ - y₀ * r₁ - (y₁ * p₀ - y₀ * p₁) / H
  have hH : 0 < H := by dsimp only [H]; positivity
  have hd : 0 < n + 1 / t := by positivity
  have hid : p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (n + 1 / t) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      t * (y₁ * r₀ - y₀ * r₁) ^ 2 = (U ^ 2 + H * V ^ 2) / n := by
    dsimp only [U, V, H, n]
    field_simp [hn.ne', ht.ne', hd.ne', hH.ne']
    <;> ring
  rw [hid]
  refine ⟨div_nonneg (add_nonneg (sq_nonneg U) (mul_nonneg hH.le (sq_nonneg V))) hn.le, ?_⟩
  intro heq
  have hsum : U ^ 2 + H * V ^ 2 = 0 := (div_eq_zero_iff.mp heq).resolve_right hn.ne'
  have hu : U = 0 := by nlinarith [mul_nonneg hH.le (sq_nonneg V)]
  have hv : V = 0 := by
    have : H * V ^ 2 = 0 := by nlinarith [sq_nonneg U]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hH.ne')
  exact ⟨hu, hv⟩

/- If the perpendicular numerator vanishes, local equality recovers the
original radial vector; no inverse-only or trace-only kernel is substituted. -/
private theorem local_quadratic_radial {y₀ y₁ t τ r₀ r₁ : ℝ}
    (hn : 0 < y₀ ^ 2 + y₁ ^ 2) (ht : 0 < t)
    (heq : (τ * y₀) ^ 2 + (τ * y₁) ^ 2 -
      (y₁ * (τ * y₀) - y₀ * (τ * y₁)) ^ 2 / (y₀ ^ 2 + y₁ ^ 2 + 1 / t) -
      2 * ((τ * y₀) * r₀ + (τ * y₁) * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      t * (y₁ * r₀ - y₀ * r₁) ^ 2 = 0) :
    r₀ = τ * y₀ ∧ r₁ = τ * y₁ := by
  obtain ⟨hu, hv⟩ := (local_quadratic_duality hn ht (τ * y₀) (τ * y₁) r₀ r₁).2 heq
  have hp : y₁ * (τ * y₀) - y₀ * (τ * y₁) = 0 := by ring
  rw [hp, zero_div, sub_zero] at hv
  have h₀ : (y₀ ^ 2 + y₁ ^ 2) * (r₀ - τ * y₀) = 0 := by
    linear_combination -y₀ * hu + y₁ * hv
  have h₁ : (y₀ ^ 2 + y₁ ^ 2) * (r₁ - τ * y₁) = 0 := by
    linear_combination -y₁ * hu - y₀ * hv
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_left hn.ne'),
    sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left hn.ne')⟩

/- This is the strictness step in the ordered eigenbasis. Positive pairwise
inner products are supplied by the strictly positive off-diagonal power and
nonzero nonnegative columns, including axial columns. -/
private theorem diagonal_kernel_scalar (y₀ y₁ : m → ℝ) {A B d₀ d₁ : ℝ}
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    (h₀ : ∑ j, y₀ j ^ 2 = d₀) (h₁ : ∑ j, y₁ j ^ 2 = d₁)
    (hpair : ∀ j k, 0 < y₀ j * y₀ k + y₁ j * y₁ k)
    (hg : ∀ j, (A - B) * y₀ j * y₁ j = 0) : A = B := by
  by_contra hAB
  have hne : A - B ≠ 0 := sub_ne_zero.mpr hAB
  have haxis (j : m) : y₀ j = 0 ∨ y₁ j = 0 := by
    have h := hg j
    rw [mul_assoc] at h
    exact mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne)
  have hex₀ : ∃ j, y₀ j ≠ 0 := by
    by_contra h
    push_neg at h
    have : d₀ = 0 := by rw [← h₀]; simp [h]
    exact hd₀.ne' this
  have hex₁ : ∃ j, y₁ j ≠ 0 := by
    by_contra h
    push_neg at h
    have : d₁ = 0 := by rw [← h₁]; simp [h]
    exact hd₁.ne' this
  obtain ⟨j, hj⟩ := hex₀
  obtain ⟨k, hk⟩ := hex₁
  have hj' : y₁ j = 0 := (haxis j).resolve_left hj
  have hk' : y₀ k = 0 := (haxis k).resolve_right hk
  simpa only [hj', hk', mul_zero, zero_mul, add_zero, lt_self_iff_false] using hpair j k

private theorem rotated_gram_moments (a b : m → ℝ) (u v ξ η : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (ha : ∑ j, a j ^ 2 = ξ * u ^ 2 + η * v ^ 2)
    (hb : ∑ j, b j ^ 2 = ξ * v ^ 2 + η * u ^ 2)
    (hab : ∑ j, a j * b j = (ξ - η) * u * v) :
    (∑ j, (u * a j + v * b j) ^ 2) = ξ ∧
    (∑ j, (-v * a j + u * b j) ^ 2) = η ∧
    (∑ j, (u * a j + v * b j) * (-v * a j + u * b j)) = 0 := by
  have h₀ : (∑ j, (u * a j + v * b j) ^ 2) =
      u ^ 2 * (∑ j, a j ^ 2) + 2 * u * v * (∑ j, a j * b j) +
        v ^ 2 * (∑ j, b j ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₁ : (∑ j, (-v * a j + u * b j) ^ 2) =
      v ^ 2 * (∑ j, a j ^ 2) - 2 * u * v * (∑ j, a j * b j) +
        u ^ 2 * (∑ j, b j ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₂ : (∑ j, (u * a j + v * b j) * (-v * a j + u * b j)) =
      -u * v * (∑ j, a j ^ 2) + (u ^ 2 - v ^ 2) * (∑ j, a j * b j) +
        u * v * (∑ j, b j ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ha, hb, hab] at h₀ h₁ h₂
  have he₀ : u ^ 2 * (ξ * u ^ 2 + η * v ^ 2) +
      2 * u * v * ((ξ - η) * u * v) + v ^ 2 * (ξ * v ^ 2 + η * u ^ 2) =
      ξ * (u ^ 2 + v ^ 2) ^ 2 := by ring
  have he₁ : v ^ 2 * (ξ * u ^ 2 + η * v ^ 2) -
      2 * u * v * ((ξ - η) * u * v) + u ^ 2 * (ξ * v ^ 2 + η * u ^ 2) =
      η * (u ^ 2 + v ^ 2) ^ 2 := by ring
  rw [he₀, huv] at h₀
  rw [he₁, huv] at h₁
  refine ⟨by simpa using h₀, by simpa using h₁, ?_⟩
  rw [h₂]
  ring

private theorem whitened_gram_moments (a b : m → ℝ) (u v : ℝ) {ξ η : ℝ}
    (hξ : 0 < ξ) (hη : 0 < η) (s : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (ha : ∑ j, a j ^ 2 = ξ * u ^ 2 + η * v ^ 2)
    (hb : ∑ j, b j ^ 2 = ξ * v ^ 2 + η * u ^ 2)
    (hab : ∑ j, a j * b j = (ξ - η) * u * v) :
    (∑ j, (ξ ^ (s / 2) * (u * a j + v * b j)) ^ 2) = ξ ^ (s + 1) ∧
    (∑ j, (η ^ (s / 2) * (-v * a j + u * b j)) ^ 2) = η ^ (s + 1) ∧
    (∑ j, (ξ ^ (s / 2) * (u * a j + v * b j)) *
      (η ^ (s / 2) * (-v * a j + u * b j))) = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := rotated_gram_moments a b u v ξ η huv ha hb hab
  have hp (x : ℝ) (hx : 0 < x) : (x ^ (s / 2)) ^ 2 * x = x ^ (s + 1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le,
      show s / 2 * 2 = s by ring, Real.rpow_add hx, Real.rpow_one]
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_pow, ← Finset.mul_sum, h₀]
    exact hp ξ hξ
  · simp only [mul_pow, ← Finset.mul_sum, h₁]
    exact hp η hη
  · have hterm (j : m) :
        ξ ^ (s / 2) * (u * a j + v * b j) *
          (η ^ (s / 2) * (-v * a j + u * b j)) =
        (ξ ^ (s / 2) * η ^ (s / 2)) *
          ((u * a j + v * b j) * (-v * a j + u * b j)) := by ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, h₂, mul_zero]

/- The complete inverse metric on Sym₂, including its off-diagonal direction. -/
private theorem inverse_metric_from_moments {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (y₀ y₁ w : m → ℝ) (hw : ∀ j, 0 < w j)
    (h₀ : ∑ j, y₀ j ^ 2 = ξ ^ (s + 1))
    (h₁ : ∑ j, y₁ j ^ 2 = η ^ (s + 1))
    (hcross : ∑ j, y₀ j * y₁ j = 0)
    (hwsum : ∑ j, w j = ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1))
    (N₀₀ N₀₁ N₁₁ : ℝ) :
    let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
    let g := fun j => (N₀₀ - N₁₁) * y₀ j * y₁ j + N₀₁ * (y₁ j ^ 2 - y₀ j ^ 2)
    let G := (1 / s) * (ξ ^ (s + 1) * N₀₀ ^ 2 + η ^ (s + 1) * N₁₁ ^ 2 + D * N₀₁ ^ 2) -
      ∑ j, (1 / s) * ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
        (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 - (g j) ^ 2 / w j)
    0 ≤ G ∧ (G = 0 → N₀₁ = 0 ∧ ∀ j, g j = 0) := by
  let T := ξ ^ (s + 1) + η ^ (s + 1)
  let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
  let d := ξ ^ (s + 1) - η ^ (s + 1)
  let g := fun j => (N₀₀ - N₁₁) * y₀ j * y₁ j + N₀₁ * (y₁ j ^ 2 - y₀ j ^ 2)
  have hξ : 0 < ξ := hη.trans hξη
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos (by positivity)
      (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs))
  have hden : 0 < T + D / (2 * s + 1) := by dsimp only [T]; positivity
  have hg : ∑ j, g j = -d * N₀₁ := by
    calc
      _ = (N₀₀ - N₁₁) * (∑ j, y₀ j * y₁ j) +
          N₀₁ * ((∑ j, y₁ j ^ 2) - (∑ j, y₀ j ^ 2)) := by
        dsimp only [g]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -d * N₀₁ := by rw [hcross, h₀, h₁]; dsimp only [d]; ring
  have hnorm : (∑ j, ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
      (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2)) =
      ξ ^ (s + 1) * N₀₀ ^ 2 + η ^ (s + 1) * N₁₁ ^ 2 + T * N₀₁ ^ 2 := by
    calc
      _ = (N₀₀ ^ 2 + N₀₁ ^ 2) * (∑ j, y₀ j ^ 2) +
          (N₁₁ ^ 2 + N₀₁ ^ 2) * (∑ j, y₁ j ^ 2) +
          2 * (N₀₀ + N₁₁) * N₀₁ * (∑ j, y₀ j * y₁ j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [h₀, h₁, hcross]; dsimp only [T]; ring
  have hid : (1 / s) * (ξ ^ (s + 1) * N₀₀ ^ 2 + η ^ (s + 1) * N₁₁ ^ 2 + D * N₀₁ ^ 2) -
      (∑ j, (1 / s) * ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
        (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 - (g j) ^ 2 / w j)) =
      (1 / s) * ((∑ j, (g j) ^ 2 / w j) - (T - D) * N₀₁ ^ 2) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hnorm]
    ring
  dsimp only
  change 0 ≤ _ ∧ (_ = 0 → N₀₁ = 0 ∧ ∀ j, g j = 0)
  rw [hid]
  exact scalar_gap_with_weights hs hden (eigenvalue_metric_gap hs hs1 hη hξη)
    g w hw hg hwsum

/- A complete quadratic bound in whitened coordinates, applied to arbitrary
velocity columns. The metric coefficient D is the actual power divided difference. -/
private theorem whitened_hessian_bound {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (y₀ y₁ v₀ v₁ t : m → ℝ) (ht : ∀ j, 0 < t j)
    (hn : ∀ j, 0 < y₀ j ^ 2 + y₁ j ^ 2)
    (h₀ : ∑ j, y₀ j ^ 2 = ξ ^ (s + 1))
    (h₁ : ∑ j, y₁ j ^ 2 = η ^ (s + 1))
    (hcross : ∑ j, y₀ j * y₁ j = 0)
    (hwsum : ∑ j, (y₀ j ^ 2 + y₁ j ^ 2 + 1 / t j) =
      ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1)) :
    let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
    let E₀₀ := ∑ j, y₀ j * v₀ j
    let E₁₁ := ∑ j, y₁ j * v₁ j
    let E₀₁ := (∑ j, (y₀ j * v₁ j + y₁ j * v₀ j)) / 2
    s / ξ ^ (s + 1) * E₀₀ ^ 2 + s / η ^ (s + 1) * E₁₁ ^ 2 +
      4 * s / D * E₀₁ ^ 2 ≤
      ∑ j, s * (v₀ j ^ 2 + v₁ j ^ 2 + t j * (y₁ j * v₀ j - y₀ j * v₁ j) ^ 2) := by
  let A := ξ ^ (s + 1)
  let B := η ^ (s + 1)
  let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
  let E₀₀ := ∑ j, y₀ j * v₀ j
  let E₁₁ := ∑ j, y₁ j * v₁ j
  let E₀₁ := (∑ j, (y₀ j * v₁ j + y₁ j * v₀ j)) / 2
  let N₀₀ := s / A * E₀₀
  let N₁₁ := s / B * E₁₁
  let N₀₁ := 2 * s / D * E₀₁
  let w := fun j => y₀ j ^ 2 + y₁ j ^ 2 + 1 / t j
  let g := fun j => (N₀₀ - N₁₁) * y₀ j * y₁ j + N₀₁ * (y₁ j ^ 2 - y₀ j ^ 2)
  let dual := fun j => (1 / s) * ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
    (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 - (g j) ^ 2 / w j)
  let pair := fun j => (N₀₀ * y₀ j + N₀₁ * y₁ j) * v₀ j +
    (N₀₁ * y₀ j + N₁₁ * y₁ j) * v₁ j
  let cost := fun j => s * (v₀ j ^ 2 + v₁ j ^ 2 +
    t j * (y₁ j * v₀ j - y₀ j * v₁ j) ^ 2)
  let M := s / A * E₀₀ ^ 2 + s / B * E₁₁ ^ 2 + 4 * s / D * E₀₁ ^ 2
  have hξ : 0 < ξ := hη.trans hξη
  have hA : 0 < A := Real.rpow_pos_of_pos hξ _
  have hB : 0 < B := Real.rpow_pos_of_pos hη _
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos (by positivity) (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs))
  have hw (j : m) : 0 < w j := add_pos (hn j) (one_div_pos.mpr (ht j))
  have hmetric : (1 / s) * (A * N₀₀ ^ 2 + B * N₁₁ ^ 2 + D * N₀₁ ^ 2) = M := by
    dsimp only [N₀₀, N₁₁, N₀₁, M]
    field_simp [hs.ne', hA.ne', hB.ne', hD.ne']
    <;> ring
  have hpair : ∑ j, pair j = M := by
    have hsum : ∑ j, pair j = N₀₀ * E₀₀ + N₁₁ * E₁₁ + 2 * N₀₁ * E₀₁ := by
      dsimp only [pair, E₀₀, E₁₁, E₀₁]
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    dsimp only [N₀₀, N₁₁, N₀₁, M]
    ring
  have hgap := (inverse_metric_from_moments hs hs1 hη hξη y₀ y₁ w hw
    h₀ h₁ hcross hwsum N₀₀ N₀₁ N₁₁).1
  change 0 ≤ (1 / s) * (A * N₀₀ ^ 2 + B * N₁₁ ^ 2 + D * N₀₁ ^ 2) - ∑ j, dual j at hgap
  rw [hmetric] at hgap
  have hlocal (j : m) : 0 ≤ cost j - 2 * pair j + dual j := by
    have h := (local_quadratic_duality (hn j) (ht j)
      (N₀₀ * y₀ j + N₀₁ * y₁ j) (N₀₁ * y₀ j + N₁₁ * y₁ j)
      (s * v₀ j) (s * v₁ j)).1
    have hnum : y₁ j * (N₀₀ * y₀ j + N₀₁ * y₁ j) -
        y₀ j * (N₀₁ * y₀ j + N₁₁ * y₁ j) = g j := by dsimp only [g]; ring
    rw [hnum] at h
    have he : s * (cost j - 2 * pair j + dual j) =
        (N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 + (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 -
        (g j) ^ 2 / w j -
        2 * ((N₀₀ * y₀ j + N₀₁ * y₁ j) * (s * v₀ j) +
          (N₀₁ * y₀ j + N₁₁ * y₁ j) * (s * v₁ j)) +
        (s * v₀ j) ^ 2 + (s * v₁ j) ^ 2 +
        t j * (y₁ j * (s * v₀ j) - y₀ j * (s * v₁ j)) ^ 2 := by
      dsimp only [cost, pair, dual]
      field_simp [hs.ne']
      <;> ring
    rw [← he] at h
    exact nonneg_of_mul_nonneg_right h hs
  have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hlocal j)
  have hsum' : 0 ≤ (∑ j, cost j) - 2 * M + ∑ j, dual j := by
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hpair] using hsum
  change M ≤ ∑ j, cost j
  linarith

private def spectralAcceleration (q a b c da db dc dda ddb ddc : ℝ) : ℝ :=
  let δ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)
  let v := 2 * (a - c) * (da - dc) + 8 * b * db
  let dv := 2 * (da - dc) ^ 2 + 2 * (a - c) * (dda - ddc) + 8 * db ^ 2 + 8 * b * ddb
  let dδ := v / (2 * δ)
  let ddδ := (dv * (2 * δ) - v * (2 * dδ)) / (2 * δ) ^ 2
  let ξ := (a + c + δ) / 2
  let η := (a + c - δ) / 2
  let dξ := (da + dc + dδ) / 2
  let dη := (da + dc - dδ) / 2
  let ddξ := (dda + ddc + ddδ) / 2
  let ddη := (dda + ddc - ddδ) / 2
  q * (ddξ * ξ ^ (q - 1) + ddη * η ^ (q - 1)) +
    q * (q - 1) * (dξ ^ 2 * ξ ^ (q - 2) + dη ^ 2 * η ^ (q - 2))

private def gramDiagonalAcceleration (q : ℝ) (W V : Matrix (Fin 2) m ℝ) (b : Fin 2) : ℝ :=
  ∑ j, (V b j) ^ 2 * (1 / q) * (1 / q - 1) * W b j ^ (1 / q - 2)

private def gramOffDiagonalAcceleration (q : ℝ) (W V : Matrix (Fin 2) m ℝ) : ℝ :=
  ∑ j, (2 * V 0 j * V 1 j * (1 / (2 * q)) * (W 0 j * W 1 j) ^ (1 / (2 * q) - 1) +
    (V 0 j * W 1 j + W 0 j * V 1 j) ^ 2 * (1 / (2 * q)) * (1 / (2 * q) - 1) *
      (W 0 j * W 1 j) ^ (1 / (2 * q) - 2))

private theorem gramDiagonalVelocity_hasDerivAt {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < (W + t • V) b j) (b : Fin 2) :
    HasDerivAt (fun u : ℝ => gramDiagonalVelocity q (W + u • V) V b)
      (gramDiagonalAcceleration q (W + t • V) V b) t := by
  unfold gramDiagonalVelocity gramDiagonalAcceleration
  apply HasDerivAt.fun_sum
  intro j _
  have h := (((hasDerivAt_const t (W b j)).add
    ((hasDerivAt_id t).mul_const (V b j))).rpow_const
      (p := 1 / q - 1) (Or.inl (hW b j).ne')).const_mul (V b j * (1 / q))
  convert h using 1 <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, id_eq, smul_eq_mul, zero_add, one_mul,
    show 1 / q - 1 - 1 = 1 / q - 2 by ring] <;>
    first | (funext u; try dsimp; ring) | ring

private theorem gramOffDiagonalVelocity_hasDerivAt {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < (W + t • V) b j) :
    HasDerivAt (fun u : ℝ => gramOffDiagonalVelocity q (W + u • V) V)
      (gramOffDiagonalAcceleration q (W + t • V) V) t := by
  unfold gramOffDiagonalVelocity gramOffDiagonalAcceleration
  apply HasDerivAt.fun_sum
  intro j _
  have h0 := (hasDerivAt_const t (W 0 j)).add ((hasDerivAt_id t).mul_const (V 0 j))
  have h1 := (hasDerivAt_const t (W 1 j)).add ((hasDerivAt_id t).mul_const (V 1 j))
  have hp := h0.mul h1
  have hdp := (h1.const_mul (V 0 j)).add (h0.mul_const (V 1 j))
  have h := (hdp.mul_const (1 / (2 * q))).mul
    (hp.rpow_const (p := 1 / (2 * q) - 1) (Or.inl (mul_pos (hW 0 j) (hW 1 j)).ne'))
  convert! h using 1 <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, id_eq, smul_eq_mul, zero_add, one_mul,
    show 1 / (2 * q) - 1 - 1 = 1 / (2 * q) - 2 by ring] <;>
    first | rfl | (funext u; simp only [Pi.mul_apply, Pi.add_apply]; rfl) | ring

/-- The appended regularization preserves each affine segment exactly. -/
theorem regularizedTable_affine (ε t : ℝ) (W V : Matrix (Fin 2) m ℝ) :
    regularizedTable ε ((1 - t) • W + t • V) =
      (1 - t) • regularizedTable ε W + t • regularizedTable ε V := by
  ext b j
  cases j with
  | inl j =>
    change ((1 - t) * W b j + t * V b j) + ε =
      (1 - t) * (W b j + ε) + t * (V b j + ε)
    ring
  | inr j =>
    change boundaryTable ε b j = (1 - t) * boundaryTable ε b j + t * boundaryTable ε b j
    ring

/-- Actual second derivative of the Schatten trace power in the positive SPD
chart, derived from the two eigenvalues rather than a formal Hessian premise. -/
private theorem Fq_affine_second_hasDerivAt {q : ℝ} (hq : 0 < q)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < W b j)
    (hdisc : 0 < (gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
      4 * gramOffDiagonal q W ^ 2)
    (hlo : 0 < (gramDiagonal q W 0 + gramDiagonal q W 1 -
      Real.sqrt ((gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
        4 * gramOffDiagonal q W ^ 2)) / 2) :
    HasDerivAt (deriv (fun u : ℝ => Fq q (W + u • V)))
      (spectralAcceleration q (gramDiagonal q W 0) (gramOffDiagonal q W) (gramDiagonal q W 1)
        (gramDiagonalVelocity q W V 0) (gramOffDiagonalVelocity q W V)
        (gramDiagonalVelocity q W V 1) (gramDiagonalAcceleration q W V 0)
        (gramOffDiagonalAcceleration q W V) (gramDiagonalAcceleration q W V 1)) 0 := by
  let a := fun u : ℝ => gramDiagonal q (W + u • V) 0
  let b := fun u : ℝ => gramOffDiagonal q (W + u • V)
  let c := fun u : ℝ => gramDiagonal q (W + u • V) 1
  let da := fun u : ℝ => gramDiagonalVelocity q (W + u • V) V 0
  let db := fun u : ℝ => gramOffDiagonalVelocity q (W + u • V) V
  let dc := fun u : ℝ => gramDiagonalVelocity q (W + u • V) V 1
  have hdiag (k : Fin 2) : Continuous (fun u : ℝ => gramDiagonal q (W + u • V) k) := by
    unfold gramDiagonal
    apply continuous_finset_sum
    intro j _
    exact (continuous_const.add (continuous_id.mul_const (V k j))).rpow_const
      (fun _ => Or.inr (by positivity))
  have hb : Continuous b := by
    dsimp only [b, gramOffDiagonal]
    apply continuous_finset_sum
    intro j _
    exact ((continuous_const.add (continuous_id.mul_const (V 0 j))).mul
      (continuous_const.add (continuous_id.mul_const (V 1 j)))).rpow_const
        (fun _ => Or.inr (by positivity))
  have ha : Continuous a := hdiag 0
  have hc : Continuous c := hdiag 1
  have hdiscC : Continuous (fun u : ℝ => (a u - c u) ^ 2 + 4 * b u ^ 2) := by fun_prop
  have hloC : Continuous (fun u : ℝ => (a u + c u -
      Real.sqrt ((a u - c u) ^ 2 + 4 * b u ^ 2)) / 2) := by fun_prop
  have hpos : ∀ᶠ u : ℝ in nhds 0, ∀ k j, 0 < (W + u • V) k j := by
    apply Filter.eventually_all.mpr
    intro k
    apply Filter.eventually_all.mpr
    intro j
    have hC : Continuous (fun u : ℝ => (W + u • V) k j) := by fun_prop
    exact (hC.tendsto 0).eventually (Ioi_mem_nhds (by simpa using hW k j))
  have hdisc' : 0 < (a 0 - c 0) ^ 2 + 4 * b 0 ^ 2 := by simpa [a, b, c] using hdisc
  have hlo' : 0 < (a 0 + c 0 - Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)) / 2 := by
    simpa [a, b, c] using hlo
  have heq : deriv (fun u : ℝ => Fq q (W + u • V)) =ᶠ[nhds 0]
      (fun u => spectralVelocity q (a u) (b u) (c u) (da u) (db u) (dc u)) := by
    filter_upwards [hpos, (hdiscC.tendsto 0).eventually (Ioi_mem_nhds hdisc'),
      (hloC.tendsto 0).eventually (Ioi_mem_nhds hlo')] with u hu hd hl
    exact (Fq_affine_hasDerivAt hq W V hu hd hl).deriv
  have hW₀ : ∀ k j, 0 < (W + (0 : ℝ) • V) k j := by simpa using hW
  have h := spectralVelocity_hasDerivAt (q := q) (gramDiagonal_hasDerivAt W V hW₀ 0)
    (gramOffDiagonal_hasDerivAt W V hW₀) (gramDiagonal_hasDerivAt W V hW₀ 1)
    (gramDiagonalVelocity_hasDerivAt W V hW₀ 0)
    (gramOffDiagonalVelocity_hasDerivAt W V hW₀)
    (gramDiagonalVelocity_hasDerivAt W V hW₀ 1) hdisc' hlo'
  convert h.congr_of_eventuallyEq heq using 1 <;>
    simp only [spectralAcceleration, a, b, c, da, db, dc, zero_smul, add_zero]

/- Exact full trace Hessian in a two-eigenvalue chart. The third symmetric
coordinate is retained through K; it is the noncommuting direction. -/
private theorem spectralAcceleration_decomposition
    (s a b c ξ η d e A B C AA BB CC : ℝ)
    (hξη : η < ξ) (hsum : a + c = ξ + η)
    (hdiff : a - c = (ξ - η) * d) (hoff : 2 * b = (ξ - η) * e)
    (hunit : d ^ 2 + e ^ 2 = 1) :
    let E₀₀ := (A + C + d * (A - C) + 2 * e * B) / 2
    let E₁₁ := (A + C - d * (A - C) - 2 * e * B) / 2
    let K := e * (A - C) / 2 - d * B
    spectralAcceleration (s + 1) a b c A B C AA BB CC =
      (s + 1) * ((ξ ^ s * ((1 + d) / 2) + η ^ s * ((1 - d) / 2)) * AA +
        (ξ ^ s - η ^ s) * e * BB +
        (ξ ^ s * ((1 - d) / 2) + η ^ s * ((1 + d) / 2)) * CC) +
      (s + 1) * (s * ξ ^ (s - 1) * E₀₀ ^ 2 + s * η ^ (s - 1) * E₁₁ ^ 2 +
        2 * ((ξ ^ s - η ^ s) / (ξ - η)) * K ^ 2) := by
  let δ := ξ - η
  let V := d * (A - C) + 2 * e * B
  let L := d * (AA - CC) + 2 * e * BB
  let K := e * (A - C) / 2 - d * B
  have hδ : 0 < δ := sub_pos.mpr hξη
  have hdisc : (a - c) ^ 2 + 4 * b ^ 2 = δ ^ 2 := by
    calc
      _ = δ ^ 2 * (d ^ 2 + e ^ 2) := by
        have hb : b = δ * e / 2 := by dsimp only [δ]; linarith
        rw [hdiff, hb]
        dsimp only [δ]
        ring
      _ = δ ^ 2 := by rw [hunit, mul_one]
  have hsqrt : Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2) = δ := by
    rw [hdisc, Real.sqrt_sq hδ.le]
  have hp : (a + c + δ) / 2 = ξ := by dsimp only [δ]; rw [hsum]; ring
  have hm : (a + c - δ) / 2 = η := by dsimp only [δ]; rw [hsum]; ring
  have hv : (2 * (a - c) * (A - C) + 8 * b * B) / (2 * δ) = V := by
    dsimp only [V, δ]
    rw [hdiff]
    have hb : b = (ξ - η) * e / 2 := by linarith
    rw [hb]
    field_simp [sub_ne_zero.mpr (ne_of_gt hξη)]
    <;> ring
  have hquad : (A - C) ^ 2 + 4 * B ^ 2 - V ^ 2 = 4 * K ^ 2 := by
    dsimp only [V, K]
    nlinarith [congrArg (fun z : ℝ => z * ((A - C) ^ 2 + 4 * B ^ 2)) hunit]
  have hacc : ((2 * (A - C) ^ 2 + 2 * (a - c) * (AA - CC) + 8 * B ^ 2 + 8 * b * BB) *
      (2 * δ) - (2 * (a - c) * (A - C) + 8 * b * B) * (2 * V)) / (2 * δ) ^ 2 =
      L + 4 * K ^ 2 / δ := by
    have hb : b = δ * e / 2 := by dsimp only [δ]; linarith
    have hnum : 2 * (a - c) * (A - C) + 8 * b * B = 2 * δ * V := by
      dsimp only [V, δ]
      rw [hdiff, hb]
      ring
    rw [hnum]
    calc
      _ = L + ((A - C) ^ 2 + 4 * B ^ 2 - V ^ 2) / δ := by
        dsimp only [L]
        rw [hdiff, hb]
        field_simp [hδ.ne']
        <;> ring
      _ = _ := by rw [hquad]
  dsimp only
  dsimp only [spectralAcceleration]
  rw [hsqrt, hp, hm, hv, hacc]
  simp only [show s + 1 - 1 = s by ring, show s + 1 - 2 = s - 1 by ring]
  dsimp only [V, L, K, δ]
  field_simp [sub_ne_zero.mpr (ne_of_gt hξη)]
  <;> ring

/- Boundary support version: h is beta*a*b and may be zero at an axial
column. The zero-denominator branch uses the actual allowed support tangent. -/
private theorem local_quadratic_duality_support {y₀ y₁ h : ℝ}
    (hn : 0 < y₀ ^ 2 + y₁ ^ 2) (hh : 0 ≤ h) (p₀ p₁ r₀ r₁ : ℝ)
    (hsupport : h = 0 → y₁ * r₀ - y₀ * r₁ = 0) :
    0 ≤ p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (y₀ ^ 2 + y₁ ^ 2 + h) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      (y₁ * r₀ - y₀ * r₁) ^ 2 / h := by
  rcases eq_or_lt_of_le hh with heq | hpos
  · have hh0 : h = 0 := heq.symm
    have hr := hsupport hh0
    have hid : p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (y₀ ^ 2 + y₁ ^ 2) -
        2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 =
        (y₀ * (p₀ - r₀) + y₁ * (p₁ - r₁)) ^ 2 / (y₀ ^ 2 + y₁ ^ 2) +
          ((y₁ * r₀ - y₀ * r₁) ^ 2 -
            2 * (y₁ * p₀ - y₀ * p₁) * (y₁ * r₀ - y₀ * r₁)) / (y₀ ^ 2 + y₁ ^ 2) := by
      field_simp [hn.ne']
      <;> ring
    simp only [hh0, add_zero, div_zero]
    rw [hid, hr]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_div, add_zero]
    exact div_nonneg (sq_nonneg _) hn.le
  · simpa [div_eq_mul_inv, mul_comm] using
      (local_quadratic_duality hn (one_div_pos.mpr hpos) p₀ p₁ r₀ r₁).1

private theorem local_quadratic_radial_support {y₀ y₁ h τ r₀ r₁ : ℝ}
    (hh : 0 ≤ h)
    (heq : (τ * y₀) ^ 2 + (τ * y₁) ^ 2 -
      (y₁ * (τ * y₀) - y₀ * (τ * y₁)) ^ 2 / (y₀ ^ 2 + y₁ ^ 2 + h) -
      2 * ((τ * y₀) * r₀ + (τ * y₁) * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      (y₁ * r₀ - y₀ * r₁) ^ 2 / h = 0) : r₀ = τ * y₀ ∧ r₁ = τ * y₁ := by
  have hp : y₁ * (τ * y₀) - y₀ * (τ * y₁) = 0 := by ring
  rw [hp, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] at heq
  have hd : 0 ≤ (y₁ * r₀ - y₀ * r₁) ^ 2 / h := div_nonneg (sq_nonneg _) hh
  constructor <;> nlinarith [sq_nonneg (r₀ - τ * y₀), sq_nonneg (r₁ - τ * y₁)]

/- A constructive oriented real eigenbasis for every positive-overlap SPD
row Gram. Distinctness follows from the actual positive off-diagonal entry. -/
private theorem positive_gram_rotation (a b c : ℝ) (hb : 0 < b)
    (hlo : 0 < (a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) :
    ∃ u v ξ η : ℝ, 0 < u ∧ 0 < v ∧ 0 < η ∧ η < ξ ∧ u ^ 2 + v ^ 2 = 1 ∧
      a = ξ * u ^ 2 + η * v ^ 2 ∧ c = ξ * v ^ 2 + η * u ^ 2 ∧
      b = (ξ - η) * u * v := by
  let δ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)
  have hdisc : 0 < (a - c) ^ 2 + 4 * b ^ 2 := by positivity
  have hδ : 0 < δ := Real.sqrt_pos.mpr hdisc
  have hδsq : δ ^ 2 = (a - c) ^ 2 + 4 * b ^ 2 := Real.sq_sqrt hdisc.le
  have habs : |a - c| < δ := by
    rw [← Real.sqrt_sq_eq_abs (a - c)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [sq_pos_of_pos hb])
  have hplus : 0 < δ + (a - c) := by linarith [(abs_lt.mp habs).1]
  have hminus : 0 < δ - (a - c) := by linarith [(abs_lt.mp habs).2]
  let u := Real.sqrt ((δ + (a - c)) / (2 * δ))
  let v := Real.sqrt ((δ - (a - c)) / (2 * δ))
  let ξ := (a + c + δ) / 2
  let η := (a + c - δ) / 2
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos hplus (by positivity))
  have hv : 0 < v := Real.sqrt_pos.mpr (div_pos hminus (by positivity))
  have hu₂ : u ^ 2 = (δ + (a - c)) / (2 * δ) :=
    Real.sq_sqrt (div_nonneg hplus.le (by positivity))
  have hv₂ : v ^ 2 = (δ - (a - c)) / (2 * δ) :=
    Real.sq_sqrt (div_nonneg hminus.le (by positivity))
  have huv : u ^ 2 + v ^ 2 = 1 := by rw [hu₂, hv₂]; field_simp [hδ.ne'] <;> ring
  have hprod : δ * u * v = b := by
    have heq : (δ * u * v) ^ 2 = b ^ 2 := by
      rw [mul_pow, mul_pow, hu₂, hv₂]
      field_simp [hδ.ne']
      nlinarith [hδsq]
    nlinarith [mul_pos (mul_pos hδ hu) hv]
  have hξη : ξ - η = δ := by dsimp only [ξ, η]; ring
  refine ⟨u, v, ξ, η, hu, hv, hlo, by dsimp only [ξ, η]; linarith, huv, ?_, ?_, ?_⟩
  · rw [hu₂, hv₂]
    dsimp only [ξ, η]
    field_simp [hδ.ne']
    <;> ring
  · rw [hu₂, hv₂]
    dsimp only [ξ, η]
    field_simp [hδ.ne']
    <;> ring
  · rw [hξη]
    exact hprod.symm

/- Exact entrywise coefficient conversion from ordinary affine-table jets
to the correctly normalized velocity z=dotW/(q*x^(2q-1)). -/
private theorem normalized_diagonal_jets {q w : ℝ} (hq : 0 < q) (hw : 0 < w) (v : ℝ) :
    v * (1 / q) * w ^ (1 / q - 1) =
      w ^ (1 / (2 * q)) * (v / (q * (w ^ (1 / (2 * q))) ^ (2 * q - 1))) ∧
    v ^ 2 * (1 / q) * (1 / q - 1) * w ^ (1 / q - 2) =
      -(q - 1) * (v / (q * (w ^ (1 / (2 * q))) ^ (2 * q - 1))) ^ 2 := by
  have hx : w ^ (1 / (2 * q)) ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
  constructor
  · rw [Real.rpow_sub hw (1 / q) 1, Real.rpow_one,
      ← power_root_sq hq hw.le, root_power_cancel hq hw]
    field_simp [hq.ne', hw.ne', hx]
    <;> ring
  · rw [Real.rpow_sub hw (1 / q) 2, Real.rpow_two,
      ← power_root_sq hq hw.le, root_power_cancel hq hw]
    field_simp [hq.ne', hw.ne', hx]
    <;> ring

private theorem normalized_offDiagonal_jets {q w₀ w₁ : ℝ}
    (hq : 0 < q) (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (v₀ v₁ : ℝ) :
    let a := w₀ ^ (1 / (2 * q))
    let b := w₁ ^ (1 / (2 * q))
    let z₀ := v₀ / (q * a ^ (2 * q - 1))
    let z₁ := v₁ / (q * b ^ (2 * q - 1))
    (v₀ * w₁ + w₀ * v₁) * (1 / (2 * q)) * (w₀ * w₁) ^ (1 / (2 * q) - 1) =
      (a * z₁ + b * z₀) / 2 ∧
    2 * v₀ * v₁ * (1 / (2 * q)) * (w₀ * w₁) ^ (1 / (2 * q) - 1) +
      (v₀ * w₁ + w₀ * v₁) ^ 2 * (1 / (2 * q)) * (1 / (2 * q) - 1) *
        (w₀ * w₁) ^ (1 / (2 * q) - 2) =
      z₀ * z₁ / 2 - (2 * q - 1) / 4 * (b / a * z₀ ^ 2 + a / b * z₁ ^ 2) := by
  have ha : w₀ ^ (1 / (2 * q)) ≠ 0 := (Real.rpow_pos_of_pos hw₀ _).ne'
  have hb : w₁ ^ (1 / (2 * q)) ≠ 0 := (Real.rpow_pos_of_pos hw₁ _).ne'
  dsimp only
  constructor
  · rw [Real.rpow_sub (mul_pos hw₀ hw₁) (1 / (2 * q)) 1, Real.rpow_one,
      Real.mul_rpow hw₀.le hw₁.le, root_power_cancel hq hw₀, root_power_cancel hq hw₁]
    field_simp [hq.ne', hw₀.ne', hw₁.ne', ha, hb]
    <;> ring
  · rw [Real.rpow_sub (mul_pos hw₀ hw₁) (1 / (2 * q)) 1,
      Real.rpow_sub (mul_pos hw₀ hw₁) (1 / (2 * q)) 2, Real.rpow_one, Real.rpow_two,
      Real.mul_rpow hw₀.le hw₁.le, root_power_cancel hq hw₀, root_power_cancel hq hw₁]
    field_simp [hq.ne', hw₀.ne', hw₁.ne', ha, hb]
    <;> ring

private theorem rotated_velocity_moments (a b z w : m → ℝ) (u v r t : ℝ) :
    (∑ j, (r * (u * a j + v * b j)) * (r * (u * z j + v * w j))) =
      r ^ 2 * (u ^ 2 * (∑ j, a j * z j) +
        u * v * (∑ j, (a j * w j + b j * z j)) + v ^ 2 * (∑ j, b j * w j)) ∧
    (∑ j, (t * (-v * a j + u * b j)) * (t * (-v * z j + u * w j))) =
      t ^ 2 * (v ^ 2 * (∑ j, a j * z j) -
        u * v * (∑ j, (a j * w j + b j * z j)) + u ^ 2 * (∑ j, b j * w j)) ∧
    (∑ j, ((r * (u * a j + v * b j)) * (t * (-v * z j + u * w j)) +
      (t * (-v * a j + u * b j)) * (r * (u * z j + v * w j)))) =
      r * t * (-2 * u * v * (∑ j, a j * z j) +
        (u ^ 2 - v ^ 2) * (∑ j, (a j * w j + b j * z j)) +
        2 * u * v * (∑ j, b j * w j)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib] <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/- The whitening map acts on both the actual columns and their normalized
   velocities. Its cross product has the full determinant factor. -/
private theorem whitening_column_cost (s u v r t k a b z w : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1) :
    s * ((r * (u * z + v * w)) ^ 2 + (t * (-v * z + u * w)) ^ 2 +
      k * ((t * (-v * a + u * b)) * (r * (u * z + v * w)) -
        (r * (u * a + v * b)) * (t * (-v * z + u * w))) ^ 2) =
      s * ((r ^ 2 * u ^ 2 + t ^ 2 * v ^ 2) * z ^ 2 +
        2 * (r ^ 2 - t ^ 2) * u * v * z * w +
        (r ^ 2 * v ^ 2 + t ^ 2 * u ^ 2) * w ^ 2) +
      s * k * (r * t) ^ 2 * (b * z - a * w) ^ 2 := by
  have hc : (t * (-v * a + u * b)) * (r * (u * z + v * w)) -
      (r * (u * a + v * b)) * (t * (-v * z + u * w)) =
      r * t * (u ^ 2 + v ^ 2) * (b * z - a * w) := by ring
  rw [hc, huv]
  ring

private theorem positive_half_power_sq (x : ℝ) (hx : 0 < x) (s : ℝ) :
    (x ^ (s / 2)) ^ 2 = x ^ s := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
  congr 1
  ring

/- Transforming the full spectral metric back to the original velocities.
   This retains the off-diagonal coordinate and is used by the actual trace
   Hessian calculation, rather than postulating its sign. -/
private theorem rotated_hessian_bound {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (a b z w : m → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u ^ 2 + v ^ 2 = 1)
    (h₀ : ∑ j, a j ^ 2 = ξ * u ^ 2 + η * v ^ 2)
    (h₁ : ∑ j, b j ^ 2 = ξ * v ^ 2 + η * u ^ 2)
    (hc : ∑ j, a j * b j = (ξ - η) * u * v) :
    let A := ∑ j, a j * z j
    let B := (∑ j, (a j * w j + b j * z j)) / 2
    let C := ∑ j, b j * w j
    let E₀₀ := u ^ 2 * A + 2 * u * v * B + v ^ 2 * C
    let E₁₁ := v ^ 2 * A - 2 * u * v * B + u ^ 2 * C
    let E₀₁ := -u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C
    let ℓ := (ξ ^ s - η ^ s) * u * v
    s * ξ ^ (s - 1) * E₀₀ ^ 2 + s * η ^ (s - 1) * E₁₁ ^ 2 +
        2 * ((ξ ^ s - η ^ s) / (ξ - η)) * E₀₁ ^ 2 ≤
      ∑ j, (s * ((ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * z j ^ 2 +
        2 * ℓ * z j * w j + (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * w j ^ 2) +
        (2 * s + 1) * ℓ / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2) := by
  let r := ξ ^ (s / 2)
  let t := η ^ (s / 2)
  let L := (ξ ^ s - η ^ s) * u * v
  let k := fun j => (2 * s + 1) * L / (2 * s * a j * b j * (r * t) ^ 2)
  let y₀ := fun j => r * (u * a j + v * b j)
  let y₁ := fun j => t * (-v * a j + u * b j)
  let z₀ := fun j => r * (u * z j + v * w j)
  let z₁ := fun j => t * (-v * z j + u * w j)
  have hξ : 0 < ξ := hη.trans hξη
  have hr : 0 < r := Real.rpow_pos_of_pos hξ _
  have ht : 0 < t := Real.rpow_pos_of_pos hη _
  have hr₂ : r ^ 2 = ξ ^ s := positive_half_power_sq ξ hξ s
  have ht₂ : t ^ 2 = η ^ s := positive_half_power_sq η hη s
  have hrt : (r * t) ^ 2 = (ξ * η) ^ s := by
    rw [mul_pow, hr₂, ht₂, Real.mul_rpow hξ.le hη.le]
  have hL : 0 < L := by
    exact mul_pos (mul_pos (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)) hu) hv
  have hk (j : m) : 0 < k j := by
    have haj := ha j
    have hbj := hb j
    dsimp only [k]
    positivity
  have hy (j : m) : 0 < y₀ j ^ 2 + y₁ j ^ 2 := by
    have h : 0 < y₀ j := mul_pos hr (add_pos (mul_pos hu (ha j)) (mul_pos hv (hb j)))
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos h) (sq_nonneg _)
  obtain ⟨hy₀, hy₁, hyc⟩ := whitened_gram_moments a b u v hξ hη s huv h₀ h₁ hc
  have hwsum : ∑ j, (y₀ j ^ 2 + y₁ j ^ 2 + 1 / k j) =
      ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1) := by
    have hkinv (j : m) : 1 / k j =
        (2 * s * (r * t) ^ 2 / ((2 * s + 1) * L)) * (a j * b j) := by
      dsimp only [k]
      field_simp [(ha j).ne', (hb j).ne', hs.ne', hr.ne', ht.ne', hL.ne',
        show 2 * s + 1 ≠ 0 by positivity]
      <;> ring
    simp_rw [hkinv]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hy₀, hy₁, ← Finset.mul_sum, hc, hrt]
    dsimp only [L]
    field_simp [hu.ne', hv.ne', (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)).ne']
    <;> ring
  have h := whitened_hessian_bound hs hs1 hη hξη y₀ y₁ z₀ z₁ k hk hy
    hy₀ hy₁ hyc hwsum
  obtain ⟨hz₀, hz₁, hzc⟩ := rotated_velocity_moments a b z w u v r t
  dsimp only at h ⊢
  change _ ≤ ∑ j, _ at h
  have hcost (j : m) : s * (z₀ j ^ 2 + z₁ j ^ 2 +
      k j * (y₁ j * z₀ j - y₀ j * z₁ j) ^ 2) =
      s * ((ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * z j ^ 2 +
        2 * L * z j * w j + (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * w j ^ 2) +
        (2 * s + 1) * L / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2 := by
    dsimp only [z₀, z₁, y₀, y₁]
    rw [whitening_column_cost s u v r t (k j) (a j) (b j) (z j) (w j) huv, hr₂, ht₂]
    dsimp only [k, L]
    field_simp [hs.ne', hr.ne', ht.ne', (ha j).ne', (hb j).ne']
    <;> ring
  simp_rw [hcost] at h
  dsimp only [y₀, y₁, z₀, z₁] at h
  rw [hz₀, hz₁, hzc, hr₂, ht₂] at h
  have hp (x : ℝ) (hx : 0 < x) : x ^ (s + 1) = x ^ s * x := by
    rw [Real.rpow_add hx, Real.rpow_one]
  have hm (x : ℝ) (hx : 0 < x) : x ^ (s - 1) = x ^ s / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  convert h using 1
  rw [hp ξ hξ, hp η hη, hm ξ hξ, hm η hη, Real.mul_rpow hξ.le hη.le]
  simp only [mul_pow, div_pow, hr₂, ht₂]
  field_simp [hξ.ne', hη.ne', (Real.rpow_pos_of_pos hξ s).ne',
      (Real.rpow_pos_of_pos hη s).ne',
      (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)).ne',
      (sub_pos.mpr hξη).ne', hs.ne']
  <;> ring

set_option maxHeartbeats 800000 in
private theorem spectralAcceleration_nonpos_of_columns {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (a b z w : m → ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hoverlap : 0 < ∑ j, a j * b j)
    (hlo : 0 < ((∑ j, a j ^ 2) + (∑ j, b j ^ 2) -
      Real.sqrt (((∑ j, a j ^ 2) - (∑ j, b j ^ 2)) ^ 2 +
        4 * (∑ j, a j * b j) ^ 2)) / 2) :
    spectralAcceleration (s + 1) (∑ j, a j ^ 2) (∑ j, a j * b j) (∑ j, b j ^ 2)
      (∑ j, a j * z j) ((∑ j, (a j * w j + b j * z j)) / 2) (∑ j, b j * w j)
      (∑ j, -s * z j ^ 2)
      (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
        (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)))
      (∑ j, -s * w j ^ 2) ≤ 0 := by
  obtain ⟨u, v, ξ, η, hu, hv, hη, hξη, huv, h₀, h₁, hc⟩ :=
    positive_gram_rotation (∑ j, a j ^ 2) (∑ j, a j * b j) (∑ j, b j ^ 2)
      hoverlap hlo
  let A := ∑ j, a j * z j
  let B := (∑ j, (a j * w j + b j * z j)) / 2
  let C := ∑ j, b j * w j
  let d := u ^ 2 - v ^ 2
  let e := 2 * u * v
  let S₀ := ξ ^ s * u ^ 2 + η ^ s * v ^ 2
  let S₁ := ξ ^ s * v ^ 2 + η ^ s * u ^ 2
  let L := (ξ ^ s - η ^ s) * u * v
  let Q := ∑ j, (s * (S₀ * z j ^ 2 + 2 * L * z j * w j + S₁ * w j ^ 2) +
    (2 * s + 1) * L / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2)
  let H := s * ξ ^ (s - 1) * (u ^ 2 * A + 2 * u * v * B + v ^ 2 * C) ^ 2 +
    s * η ^ (s - 1) * (v ^ 2 * A - 2 * u * v * B + u ^ 2 * C) ^ 2 +
    2 * ((ξ ^ s - η ^ s) / (ξ - η)) *
      (-u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C) ^ 2
  have hbound : H ≤ Q := rotated_hessian_bound hs hs1 hη hξη a b z w ha hb
    u v hu hv huv h₀ h₁ hc
  have hsum : (∑ j, a j ^ 2) + (∑ j, b j ^ 2) = ξ + η := by
    rw [h₀, h₁]
    linear_combination (ξ + η) * huv
  have hdiff : (∑ j, a j ^ 2) - (∑ j, b j ^ 2) = (ξ - η) * d := by
    rw [h₀, h₁]; dsimp only [d]; ring
  have hoff : 2 * (∑ j, a j * b j) = (ξ - η) * e := by rw [hc]; dsimp only [e]; ring
  have hunit : d ^ 2 + e ^ 2 = 1 := by
    calc
      _ = (u ^ 2 + v ^ 2) ^ 2 := by dsimp only [d, e]; ring
      _ = 1 := by rw [huv]; norm_num
  have hd₀ : (1 + d) / 2 = u ^ 2 := by dsimp only [d]; linarith
  have hd₁ : (1 - d) / 2 = v ^ 2 := by dsimp only [d]; linarith
  have hE₀ : (A + C + d * (A - C) + 2 * e * B) / 2 =
      u ^ 2 * A + 2 * u * v * B + v ^ 2 * C := by
    dsimp only [d, e]
    linear_combination -(A + C) / 2 * huv
  have hE₁ : (A + C - d * (A - C) - 2 * e * B) / 2 =
      v ^ 2 * A - 2 * u * v * B + u ^ 2 * C := by
    dsimp only [d, e]
    linear_combination -(A + C) / 2 * huv
  have hK : (e * (A - C) / 2 - d * B) ^ 2 =
      (-u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C) ^ 2 := by
    dsimp only [d, e]; ring
  have hcost : S₀ * (∑ j, -s * z j ^ 2) +
      (ξ ^ s - η ^ s) * e *
        (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
          (b j / a j * z j ^ 2 + a j / b j * w j ^ 2))) +
      S₁ * (∑ j, -s * w j ^ 2) = -Q := by
    have he : (ξ ^ s - η ^ s) * e = 2 * L := by dsimp only [e, L]; ring
    rw [he]
    dsimp only [Q]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    linear_combination hessian_column_coefficients s S₀ S₁ L (a j) (b j) (z j) (w j)
      (ha j).ne' (hb j).ne'
  have heq := spectralAcceleration_decomposition s (∑ j, a j ^ 2) (∑ j, a j * b j)
    (∑ j, b j ^ 2) ξ η d e A B C
    (∑ j, -s * z j ^ 2)
    (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
      (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)))
    (∑ j, -s * w j ^ 2) hξη hsum hdiff hoff hunit
  dsimp only at heq
  rw [hd₀, hd₁, hE₀, hE₁, hK] at heq
  change _ = (s + 1) * _ + (s + 1) * H at heq
  rw [hcost] at heq
  change _ ≤ 0
  rw [heq]
  change (s + 1) * (-Q) + (s + 1) * H ≤ 0
  nlinarith [mul_nonneg (by linarith : 0 ≤ s + 1) (sub_nonneg.mpr hbound)]

/- Native differentiation of the actual Schatten trace is connected to the
   complete quadratic metric above; positivity describes only the SPD chart. -/
private theorem Fq_affine_second_nonpos {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < W b j)
    (hoverlap : 0 < gramOffDiagonal q W)
    (hR : (Aq q W * (Aq q W)ᴴ).PosDef) :
    deriv (deriv (fun t : ℝ => Fq q (W + t • V))) 0 ≤ 0 := by
  have hq : 0 < q := by linarith
  let a := fun j => W 0 j ^ (1 / (2 * q))
  let b := fun j => W 1 j ^ (1 / (2 * q))
  let z := fun j => V 0 j / (q * (a j) ^ (2 * q - 1))
  let w := fun j => V 1 j / (q * (b j) ^ (2 * q - 1))
  have ha (j : m) : 0 < a j := Real.rpow_pos_of_pos (hW 0 j) _
  have hb (j : m) : 0 < b j := Real.rpow_pos_of_pos (hW 1 j) _
  have hd₀ : (∑ j, a j ^ 2) = gramDiagonal q W 0 := by
    unfold gramDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact power_root_sq hq (hW 0 j).le
  have hd₁ : (∑ j, b j ^ 2) = gramDiagonal q W 1 := by
    unfold gramDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact power_root_sq hq (hW 1 j).le
  have hc : (∑ j, a j * b j) = gramOffDiagonal q W := by
    unfold gramOffDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact (Real.mul_rpow (hW 0 j).le (hW 1 j).le).symm
  have hR' : (sym2 (gramDiagonal q W 0) (gramOffDiagonal q W) (gramDiagonal q W 1)).PosDef := by
    rw [← rowGram_sym2 hq W (fun b j => (hW b j).le)]
    exact hR
  have hlo := sym2_posDef_low_eigenvalue_pos _ _ _ hR'
  have hdisc : 0 < (gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
      4 * gramOffDiagonal q W ^ 2 := by positivity
  have hderiv := (Fq_affine_second_hasDerivAt hq W V hW hdisc hlo).deriv
  rw [hderiv]
  have hjet₀ (j : m) := normalized_diagonal_jets hq (hW 0 j) (V 0 j)
  have hjet₁ (j : m) := normalized_diagonal_jets hq (hW 1 j) (V 1 j)
  have hjet (j : m) := normalized_offDiagonal_jets hq (hW 0 j) (hW 1 j) (V 0 j) (V 1 j)
  have hv₀ : gramDiagonalVelocity q W V 0 = ∑ j, a j * z j := by
    unfold gramDiagonalVelocity
    exact Finset.sum_congr rfl (fun j _ => (hjet₀ j).1)
  have hv₁ : gramDiagonalVelocity q W V 1 = ∑ j, b j * w j := by
    unfold gramDiagonalVelocity
    exact Finset.sum_congr rfl (fun j _ => (hjet₁ j).1)
  have hv : gramOffDiagonalVelocity q W V = (∑ j, (a j * w j + b j * z j)) / 2 := by
    unfold gramOffDiagonalVelocity
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => (hjet j).1)
  have hvv₀ : gramDiagonalAcceleration q W V 0 = ∑ j, -(q - 1) * z j ^ 2 := by
    unfold gramDiagonalAcceleration
    exact Finset.sum_congr rfl (fun j _ => (hjet₀ j).2)
  have hvv₁ : gramDiagonalAcceleration q W V 1 = ∑ j, -(q - 1) * w j ^ 2 := by
    unfold gramDiagonalAcceleration
    exact Finset.sum_congr rfl (fun j _ => (hjet₁ j).2)
  have hvv : gramOffDiagonalAcceleration q W V =
      ∑ j, (z j * w j / 2 - (2 * (q - 1) + 1) / 4 *
        (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)) := by
    unfold gramOffDiagonalAcceleration
    apply Finset.sum_congr rfl
    intro j _
    convert (hjet j).2 using 1 <;> dsimp only [a, b, z, w] <;> ring
  rw [hv₀, hv₁, hv, hvv₀, hvv₁, hvv]
  have h := spectralAcceleration_nonpos_of_columns (by linarith : 0 < q - 1)
    (by linarith : q - 1 < 1) a b z w ha hb (by rwa [hc])
    (by rwa [hd₀, hd₁, hc])
  rw [hd₀, hd₁, hc, sub_add_cancel] at h
  exact h

private theorem affine_table_shift (W V : Matrix (Fin 2) m ℝ) (t u : ℝ) :
    W + (u + t) • V = (W + t • V) + u • V := by
  ext b j
  change W b j + (u + t) * V b j = (W b j + t * V b j) + u * V b j
  ring

private theorem Fq_affine_concave {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ b j, 0 < (W + t • V) b j)
    (hoverlap : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < gramOffDiagonal q (W + t • V))
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (Aq q (W + t • V) * (Aq q (W + t • V))ᴴ).PosDef) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => Fq q (W + t • V)) := by
  have hq : 0 < q := by linarith
  have hcont : Continuous (fun t : ℝ => Fq q (W + t • V)) :=
    (continuous_Fq hq).comp (by fun_prop)
  have hchart (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      0 < (gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
        4 * gramOffDiagonal q (W + t • V) ^ 2 ∧
      0 < (gramDiagonal q (W + t • V) 0 + gramDiagonal q (W + t • V) 1 -
        Real.sqrt ((gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
          4 * gramOffDiagonal q (W + t • V) ^ 2)) / 2 := by
    refine ⟨by have := hoverlap t ht; positivity, ?_⟩
    apply sym2_posDef_low_eigenvalue_pos
    rw [← rowGram_sym2 hq _ (fun b j => (hpos t ht b j).le)]
    exact hR t ht
  refine concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hcont.continuousOn ?_ ?_ ?_
  · intro t ht
    have hc := hchart t (interior_subset ht)
    exact (Fq_affine_hasDerivAt hq W V (hpos t (interior_subset ht)) hc.1 hc.2).differentiableAt.differentiableWithinAt
  · intro t ht
    have hc := hchart t (interior_subset ht)
    have hd := (Fq_affine_second_hasDerivAt hq (W + t • V) V
      (hpos t (interior_subset ht)) hc.1 hc.2).differentiableAt
    have hfun : (fun u : ℝ => Fq q ((W + t • V) + u • V)) =
        (fun u : ℝ => Fq q (W + (u + t) • V)) := by
      funext u
      rw [affine_table_shift]
    rw [hfun] at hd
    have hshift : deriv (fun u : ℝ => Fq q (W + (u + t) • V)) =
        fun u : ℝ => deriv (fun r : ℝ => Fq q (W + r • V)) (u + t) :=
      funext (fun u => deriv_comp_add_const (fun r : ℝ => Fq q (W + r • V)) t u)
    rw [hshift] at hd
    have hd' := (differentiableAt_comp_add_const (a := (0 : ℝ)) (b := t)).mp hd
    have hd'' : DifferentiableAt ℝ (deriv (fun u : ℝ => Fq q (W + u • V))) t := by
      simpa only [zero_add] using hd'
    exact hd''.differentiableWithinAt
  · intro t ht
    have h := Fq_affine_second_nonpos hq1 hq2 (W + t • V) V
      (hpos t (interior_subset ht)) (hoverlap t (interior_subset ht)) (hR t (interior_subset ht))
    have hfun : (fun u : ℝ => Fq q ((W + t • V) + u • V)) =
        (fun u : ℝ => Fq q (W + (u + t) • V)) := by
      funext u
      rw [affine_table_shift]
    rw [hfun] at h
    have hshift : deriv (fun u : ℝ => Fq q (W + (u + t) • V)) =
        fun u : ℝ => deriv (fun r : ℝ => Fq q (W + r • V)) (u + t) :=
      funext (fun u => deriv_comp_add_const (fun r : ℝ => Fq q (W + r • V)) t u)
    rw [hshift, deriv_comp_add_const] at h
    change deriv (deriv (fun u : ℝ => Fq q (W + u • V))) t ≤ 0
    simpa only [zero_add] using h

private theorem regularized_concavity {q ε : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hε : 0 < ε) (W V : Matrix (Fin 2) m ℝ)
    (hW : ∀ b j, 0 ≤ W b j) (hV : ∀ b j, 0 ≤ V b j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * Fq q (regularizedTable ε W) + t * Fq q (regularizedTable ε V) ≤
      Fq q (regularizedTable ε ((1 - t) • W + t • V)) := by
  have hq : 0 < q := by linarith
  let U := regularizedTable ε W
  let T := regularizedTable ε V
  have heq (u : ℝ) : U + u • (T - U) =
      regularizedTable ε ((1 - u) • W + u • V) := by
    rw [regularizedTable_affine]
    dsimp only [U, T]
    module
  have hnonneg (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ∀ b j, 0 ≤ ((1 - u) • W + u • V) b j := by
    intro b j
    change 0 ≤ (1 - u) * W b j + u * V b j
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) (hW b j)) (mul_nonneg hu.1 (hV b j))
  have hpos (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : ∀ b j, 0 < (U + u • (T - U)) b j := by
    rw [heq]
    exact regularizedTable_pos hε _ (hnonneg u hu)
  have hoverlap (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      0 < gramOffDiagonal q (U + u • (T - U)) := by
    unfold gramOffDiagonal
    apply Finset.sum_pos
    · intro j _
      exact Real.rpow_pos_of_pos (mul_pos (hpos u hu 0 j) (hpos u hu 1 j)) _
    · exact ⟨Sum.inr 0, Finset.mem_univ _⟩
  have hR (u : ℝ) (_hu : u ∈ Set.Icc (0 : ℝ) 1) :
      (Aq q (U + u • (T - U)) * (Aq q (U + u • (T - U)))ᴴ).PosDef := by
    rw [heq]
    exact regularized_gram_posDef hq hε _
  have hc := Fq_affine_concave hq1 hq2 U (T - U) hpos hoverlap hR
  have h := hc.2 (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    add_sub_cancel] at h
  simpa only [heq t] using h

/-- Full nonnegative-cone concavity for every finite column type and every
real 1 < q < 2, including singular, axial, zero and empty boundary tables. -/
theorem concaveOn_Fq {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    ConcaveOn ℝ {W : Matrix (Fin 2) m ℝ | ∀ b j, 0 ≤ W b j} (Fq q) := by
  have hq : 0 < q := by linarith
  refine ⟨?_, ?_⟩
  · intro W hW V hV a b ha hb _hab i j
    change 0 ≤ a * W i j + b * V i j
    exact add_nonneg (mul_nonneg ha (hW i j)) (mul_nonneg hb (hV i j))
  · intro W hW V hV a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have haeq : a = 1 - b := by linarith
    subst a
    have hL : Filter.Tendsto (fun ε : ℝ =>
        (1 - b) * Fq q (regularizedTable ε W) + b * Fq q (regularizedTable ε V))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds ((1 - b) * Fq q W + b * Fq q V)) :=
      (((tendsto_regularized_Fq hq W).const_mul (1 - b)).add
        ((tendsto_regularized_Fq hq V).const_mul b)).mono_left nhdsWithin_le_nhds
    have hR : Filter.Tendsto
        (fun ε : ℝ => Fq q (regularizedTable ε ((1 - b) • W + b • V)))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (Fq q ((1 - b) • W + b • V))) :=
      (tendsto_regularized_Fq hq ((1 - b) • W + b • V)).mono_left nhdsWithin_le_nhds
    have hineq : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        (1 - b) * Fq q (regularizedTable ε W) + b * Fq q (regularizedTable ε V) ≤
          Fq q (regularizedTable ε ((1 - b) • W + b • V)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact regularized_concavity hq1 hq2 hε W V hW hV hb hb1
    exact le_of_tendsto_of_tendsto hL hR hineq

theorem Fq_add_ge {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j) (hV : ∀ b j, 0 ≤ V b j) :
    Fq q W + Fq q V ≤ Fq q (W + V) := by
  have hq : 0 < q := by linarith
  have h := (concaveOn_Fq hq1 hq2).2 hW hV
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have heq : (1 / 2 : ℝ) • W + (1 / 2 : ℝ) • V = (1 / 2 : ℝ) • (W + V) := by module
  rw [heq, Fq_smul hq (by norm_num) (W + V) (fun b j => add_nonneg (hW b j) (hV b j))] at h
  simp only [smul_eq_mul] at h
  linarith

theorem monotoneOn_Fq {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j)
    (hWV : ∀ b j, W b j ≤ V b j) : Fq q W ≤ Fq q V := by
  have hdiff : ∀ b j, 0 ≤ (V - W) b j := fun b j => sub_nonneg.mpr (hWV b j)
  have h := Fq_add_ge hq1 hq2 W (V - W) hW hdiff
  rw [add_sub_cancel] at h
  exact (le_add_of_nonneg_right (Fq_nonneg q (V - W))).trans h

#print axioms concaveOn_Fq

end D5.S3.Quantum.NormCompression.FinitePowerConcavity
