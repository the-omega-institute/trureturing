/- GID: D5/S3/Weil/TestFunctions/SmoothExternalMomentElimination
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/SmoothExternalMomentElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Smooth even exterior corrections eliminate any prescribed finite moment list. -/

import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Integral

namespace D5.S3.Weil.TestFunctions.SmoothExternalMomentElimination

open Function MeasureTheory Matrix Metric Set
open scoped ContDiff Pointwise

noncomputable section

private theorem hasCompactSupport_iterate_deriv
    (q : ℕ) {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (deriv^[q] g) := by
  induction q with
  | zero => simpa
  | succ q ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

private theorem tsupport_iterate_deriv_subset
    (q : ℕ) (g : ℝ → ℝ) : tsupport ((deriv^[q]) g) ⊆ tsupport g := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply']
      exact tsupport_deriv_subset.trans ih

private theorem integral_pow_mul_iterate_deriv_succ
    (n q : ℕ) {g : ℝ → ℝ} (hgSmooth : ContDiff ℝ ∞ g)
    (hgCompact : HasCompactSupport g) :
    (∫ x, x ^ n * (deriv^[q + 1] g) x) =
      -(n : ℝ) * ∫ x, x ^ (n - 1) * (deriv^[q] g) x := by
  let v : ℝ → ℝ := deriv^[q] g
  let v' : ℝ → ℝ := deriv^[q + 1] g
  let u : ℝ → ℝ := fun x => x ^ n
  let u' : ℝ → ℝ := fun x => (n : ℝ) * x ^ (n - 1)
  have hvSmooth : ContDiff ℝ ∞ v := ContDiff.iterate_deriv q hgSmooth
  have hvCompact : HasCompactSupport v :=
    hasCompactSupport_iterate_deriv q hgCompact
  have hv'Compact : HasCompactSupport v' := by
    simpa only [v, v', Function.iterate_succ_apply'] using hvCompact.deriv
  have huDeriv (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u'] using hasDerivAt_pow n x
  have hvDeriv (x : ℝ) : HasDerivAt v (v' x) x := by
    simpa only [v, v', Function.iterate_succ_apply'] using
      ((ContDiff.iterate_deriv q hgSmooth).differentiable (by simp) x).hasDerivAt
  have huContinuous : Continuous u := by
    dsimp only [u]
    fun_prop
  have huv' : Integrable (u * v') :=
    (huContinuous.mul
      (ContDiff.iterate_deriv (q + 1) hgSmooth).continuous).integrable_of_hasCompactSupport
        hv'Compact.mul_left
  have hu'v : Integrable (u' * v) := by
    have hu'Continuous : Continuous u' := by
      fun_prop
    exact (hu'Continuous.mul hvSmooth.continuous).integrable_of_hasCompactSupport
      hvCompact.mul_left
  have huv : Integrable (u * v) :=
    (huContinuous.mul hvSmooth.continuous).integrable_of_hasCompactSupport hvCompact.mul_left
  have hparts := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (u' := u') (v := v) (v' := v')
    (fun x _ => huDeriv x) (fun x _ => hvDeriv x) huv' hu'v huv
  have hconst : (∫ x, (n : ℝ) * x ^ (n - 1) * v x) =
      (n : ℝ) * ∫ x, x ^ (n - 1) * v x := by
    rw [show (fun x => (n : ℝ) * x ^ (n - 1) * v x) =
        fun x => (n : ℝ) * (x ^ (n - 1) * v x) by
      funext x
      ring]
    exact integral_const_mul (n : ℝ) (fun x : ℝ => x ^ (n - 1) * v x)
  change (∫ x, u x * v' x) = -(n : ℝ) * ∫ x, x ^ (n - 1) * v x
  rw [hparts, hconst]
  ring

private theorem integral_pow_mul_iterate_deriv_self
    (n : ℕ) {g : ℝ → ℝ} (hgSmooth : ContDiff ℝ ∞ g)
    (hgCompact : HasCompactSupport g) :
    (∫ x, x ^ n * (deriv^[n] g) x) =
      (-1 : ℝ) ^ n * n.factorial * ∫ x, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [integral_pow_mul_iterate_deriv_succ (n + 1) n hgSmooth hgCompact]
      simp only [Nat.add_sub_cancel]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      ring

private theorem integral_pow_mul_iterate_deriv_eq_zero
    (n q : ℕ) (hnq : n < q) {g : ℝ → ℝ} (hgSmooth : ContDiff ℝ ∞ g)
    (hgCompact : HasCompactSupport g) :
    (∫ x, x ^ n * (deriv^[q] g) x) = 0 := by
  induction n generalizing q with
  | zero =>
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      rw [integral_pow_mul_iterate_deriv_succ 0 q hgSmooth hgCompact]
      norm_num
  | succ n ih =>
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      rw [integral_pow_mul_iterate_deriv_succ (n + 1) q hgSmooth hgCompact]
      simp only [Nat.add_sub_cancel]
      rw [ih q (by omega)]
      ring

private theorem signed_measure_integrable_of_jordan_restrict_eq
    (epsilon : SignedMeasure ℝ) {s : Set ℝ} (hsCompact : IsCompact s)
    (hpos : epsilon.toJordanDecomposition.posPart.restrict s =
      epsilon.toJordanDecomposition.posPart)
    (hneg : epsilon.toJordanDecomposition.negPart.restrict s =
      epsilon.toJordanDecomposition.negPart)
    {g : ℝ → ℝ} (hg : ContinuousOn g s) :
    MeasureTheory.Integrable g
      (epsilon.transpose (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip).variation := by
  have hposInt : Integrable g epsilon.toJordanDecomposition.posPart := by
    rw [← hpos]
    exact hg.integrableOn_compact hsCompact
  have hnegInt : Integrable g epsilon.toJordanDecomposition.negPart := by
    rw [← hneg]
    exact hg.integrableOn_compact hsCompact
  have hposSigned : VectorMeasure.Integrable
      epsilon.toJordanDecomposition.posPart.toSignedMeasure g := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hposInt
  have hnegSigned : VectorMeasure.Integrable
      epsilon.toJordanDecomposition.negPart.toSignedMeasure g := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hnegInt
  change MeasureTheory.Integrable g
    (epsilon.transpose (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip).variation
  rw [VectorMeasure.variation_transpose_lsmul_flip]
  rw [← epsilon.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  exact hposSigned.sub_vectorMeasure hnegSigned

private theorem reflected_even_power_integral
    (n : ℕ) {g : ℝ → ℝ} (hg : HasCompactSupport g) (hgContinuous : Continuous g) :
    (∫ x, x ^ (2 * n) * (g x + g (-x))) = 2 * ∫ x, x ^ (2 * n) * g x := by
  have hpowContinuous : Continuous (fun x : ℝ => x ^ (2 * n)) := continuous_id.pow _
  have hbase : Integrable (fun x => x ^ (2 * n) * g x) :=
    (hpowContinuous.mul hgContinuous).integrable_of_hasCompactSupport hg.mul_left
  have hreflected : Integrable (fun x => x ^ (2 * n) * g (-x)) := by
    have hcomp : HasCompactSupport (g ∘ fun x : ℝ => -x) := by
      change HasCompactSupport (g ∘ (Homeomorph.neg ℝ))
      rw [HasCompactSupport, tsupport_comp_eq_preimage g (Homeomorph.neg ℝ)]
      exact (Homeomorph.neg ℝ).isCompact_preimage.mpr hg.isCompact
    exact (hpowContinuous.mul
      (hgContinuous.comp continuous_neg)).integrable_of_hasCompactSupport hcomp.mul_left
  rw [show (fun x => x ^ (2 * n) * (g x + g (-x))) =
      (fun x => x ^ (2 * n) * g x) + (fun x => x ^ (2 * n) * g (-x)) by
        funext x; simp only [Pi.add_apply]; ring]
  rw [show (∫ x, ((fun x => x ^ (2 * n) * g x) +
      (fun x => x ^ (2 * n) * g (-x))) x) =
      (∫ x, x ^ (2 * n) * g x) + ∫ x, x ^ (2 * n) * g (-x) by
        exact integral_add hbase hreflected]
  have hneg : (∫ x, x ^ (2 * n) * g (-x)) = ∫ x, x ^ (2 * n) * g x := by
    rw [← integral_neg_eq_self (fun x : ℝ => x ^ (2 * n) * g (-x)) volume]
    simp only [neg_neg, pow_mul, neg_sq]
  rw [hneg]
  ring

/-- A compactly supported discrepancy admits an even smooth exterior correction that cancels
every even moment through degree `2 * K`. -/
theorem smooth_external_finite_moment_elimination
    (L : ℝ) (K : ℕ) (epsilon : SignedMeasure ℝ)
    (hpos : epsilon.toJordanDecomposition.posPart.restrict (Icc (-(2 * L)) (2 * L)) =
      epsilon.toJordanDecomposition.posPart)
    (hneg : epsilon.toJordanDecomposition.negPart.restrict (Icc (-(2 * L)) (2 * L)) =
      epsilon.toJordanDecomposition.negPart) :
    ∃ kappa : ℝ → ℝ,
      Function.Even kappa ∧
      ContDiff ℝ ∞ kappa ∧
      HasCompactSupport kappa ∧
      tsupport kappa ⊆ (Icc (-(2 * L)) (2 * L))ᶜ ∧
      ∀ j : ℕ, j ≤ K →
        (∫ᵛ u, u ^ (2 * j) ∂<•epsilon) + ∫ u, u ^ (2 * j) * kappa u = 0 := by
  classical
  let a : ℝ := 2 * L + 2
  let psi : ContDiffBump a := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let basis : Fin (K + 1) → ℝ → ℝ := fun r x =>
    (deriv^[2 * r.1] (psi : ℝ → ℝ)) x +
      (deriv^[2 * r.1] (psi : ℝ → ℝ)) (-x)
  let momentMatrix : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ := fun j r =>
    ∫ x, x ^ (2 * j.1) * basis r x
  have hpsiSmooth : ContDiff ℝ ∞ (psi : ℝ → ℝ) := psi.contDiff
  have hpsiCompact : HasCompactSupport (psi : ℝ → ℝ) := psi.hasCompactSupport
  have hmatrix (j r : Fin (K + 1)) :
      momentMatrix j r =
        2 * ∫ x, x ^ (2 * j.1) * (deriv^[2 * r.1] (psi : ℝ → ℝ)) x := by
    exact reflected_even_power_integral j.1
      (hasCompactSupport_iterate_deriv (2 * r.1) hpsiCompact)
      (ContDiff.iterate_deriv (2 * r.1) hpsiSmooth).continuous
  have habove (j r : Fin (K + 1)) (hjr : j < r) : momentMatrix j r = 0 := by
    rw [hmatrix]
    rw [integral_pow_mul_iterate_deriv_eq_zero (2 * j.1) (2 * r.1)
      (by omega) hpsiSmooth hpsiCompact]
    ring
  have hdiag (j : Fin (K + 1)) :
      momentMatrix j j =
        2 * (2 * j.1).factorial * ∫ x, psi x := by
    rw [hmatrix, integral_pow_mul_iterate_deriv_self (2 * j.1) hpsiSmooth hpsiCompact]
    rw [show (-1 : ℝ) ^ (2 * j.1) = 1 by rw [pow_mul]; norm_num]
    ring
  have hdiag_ne (j : Fin (K + 1)) : momentMatrix j j ≠ 0 := by
    have hpsiIntegral : 0 < ∫ x, psi x := psi.integral_pos
    rw [hdiag]
    positivity
  have hlower : momentMatrix.BlockTriangular
      (OrderDual.toDual : Fin (K + 1) → OrderDual (Fin (K + 1))) := by
    intro i j hji
    exact habove i j (by simpa using hji)
  have hdet : momentMatrix.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular momentMatrix hlower]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hdiag_ne j
  have hdetUnit : IsUnit momentMatrix.det := isUnit_iff_ne_zero.mpr hdet
  let target : Fin (K + 1) → ℝ := fun j =>
    -(∫ᵛ u, u ^ (2 * j.1) ∂<•epsilon)
  let coefficients : Fin (K + 1) → ℝ := momentMatrix⁻¹.mulVec target
  let kappa : ℝ → ℝ := fun x => ∑ r, coefficients r * basis r x
  have hsolve : momentMatrix.mulVec coefficients = target := by
    change momentMatrix.mulVec (momentMatrix⁻¹.mulVec target) = target
    rw [Matrix.mulVec_mulVec, momentMatrix.mul_nonsing_inv hdetUnit, Matrix.one_mulVec]
  have hbasisEven (r : Fin (K + 1)) : Function.Even (basis r) := by
    intro x
    simp only [basis, neg_neg, add_comm]
  have hbasisSmooth (r : Fin (K + 1)) : ContDiff ℝ ∞ (basis r) := by
    exact (ContDiff.iterate_deriv (2 * r.1) hpsiSmooth).add
      ((ContDiff.iterate_deriv (2 * r.1) hpsiSmooth).comp contDiff_neg)
  have hbasisCompact (r : Fin (K + 1)) : HasCompactSupport (basis r) := by
    have hderivCompact := hasCompactSupport_iterate_deriv (2 * r.1) hpsiCompact
    have hreflected : HasCompactSupport
        ((deriv^[2 * r.1] (psi : ℝ → ℝ)) ∘ fun x : ℝ => -x) := by
      simpa only [Homeomorph.coe_neg] using
        hderivCompact.comp_homeomorph (Homeomorph.neg ℝ)
    exact hderivCompact.add hreflected
  have hkappaEven : Function.Even kappa := by
    intro x
    simp only [kappa, hbasisEven _ x]
  have hkappaSmooth : ContDiff ℝ ∞ kappa := by
    exact ContDiff.sum fun r _ => by
      simpa only [smul_eq_mul] using
        ContDiff.const_smul (coefficients r) (hbasisSmooth r)
  have hkappaCompact : HasCompactSupport kappa := by
    dsimp only [kappa]
    rw [show (fun x => ∑ r : Fin (K + 1), coefficients r * basis r x) =
        ∑ r : Fin (K + 1), fun x => coefficients r * basis r x by
      funext x
      simp]
    exact HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun r x => coefficients r * basis r x)
      fun r _ => (hbasisCompact r).mul_left
  have hbasisSupport (r : Fin (K + 1)) :
      tsupport (basis r) ⊆
        closedBall a 1 ∪ (Homeomorph.neg ℝ) ⁻¹' closedBall a 1 := by
    have hderivSupport :
        tsupport ((deriv^[2 * r.1]) (psi : ℝ → ℝ)) ⊆ closedBall a 1 :=
      (tsupport_iterate_deriv_subset (2 * r.1) (psi : ℝ → ℝ)).trans (by
        simpa only [psi, ContDiffBump.tsupport_eq] using
          (subset_rfl : closedBall a 1 ⊆ closedBall a 1))
    refine (tsupport_add _ _).trans (union_subset ?_ ?_)
    · exact hderivSupport.trans subset_union_left
    · change tsupport (((deriv^[2 * r.1]) (psi : ℝ → ℝ)) ∘
          (Homeomorph.neg ℝ)) ⊆ _
      rw [tsupport_comp_eq_preimage _ (Homeomorph.neg ℝ)]
      exact (preimage_mono hderivSupport).trans subset_union_right
  have hkappaSupportUnion :
      tsupport kappa ⊆ closedBall a 1 ∪ (Homeomorph.neg ℝ) ⁻¹' closedBall a 1 := by
    dsimp only [kappa]
    induction (Finset.univ : Finset (Fin (K + 1))) using Finset.induction_on with
    | empty => simp
    | @insert r s hrs ih =>
        simp only [Finset.sum_insert, hrs, not_false_eq_true]
        refine (tsupport_add _ _).trans (union_subset ?_ ih)
        exact (tsupport_mul_subset_right).trans (hbasisSupport r)
  have hkappaExternal : tsupport kappa ⊆ (Icc (-(2 * L)) (2 * L))ᶜ := by
    intro x hx
    have hxUnion := hkappaSupportUnion hx
    simp only [mem_union, mem_closedBall, Real.dist_eq, Homeomorph.coe_neg,
      mem_preimage] at hxUnion
    simp only [mem_compl_iff, mem_Icc, not_and_or]
    rcases hxUnion with hxpos | hxneg
    · right
      rw [abs_le] at hxpos
      linarith [hxpos.1]
    · left
      rw [abs_le] at hxneg
      linarith [hxneg.2]
  refine ⟨kappa, hkappaEven, hkappaSmooth, hkappaCompact, hkappaExternal, ?_⟩
  intro j hj
  let jf : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hjInt : VectorMeasure.Integrable epsilon (fun u => u ^ (2 * j)) := by
    have h := signed_measure_integrable_of_jordan_restrict_eq epsilon isCompact_Icc hpos hneg
      (g := fun u => u ^ (2 * j)) (by fun_prop)
    change MeasureTheory.Integrable (fun u => u ^ (2 * j))
      (epsilon.transpose (ContinuousLinearMap.lsmul ℝ ℝ).flip).variation at h
    simpa only [VectorMeasure.Integrable,
      VectorMeasure.variation_transpose_lsmul_flip] using h
  have htermInt (r : Fin (K + 1)) :
      Integrable (fun u => u ^ (2 * j) * (coefficients r * basis r u)) := by
    have htermContinuous :
        Continuous (fun u : ℝ => u ^ (2 * j) * (coefficients r * basis r u)) := by
      fun_prop
    exact htermContinuous.integrable_of_hasCompactSupport
      ((hbasisCompact r).mul_left.mul_left)
  have hmomentKappa :
      (∫ u, u ^ (2 * j) * kappa u) = momentMatrix jf ⬝ᵥ coefficients := by
    simp only [kappa, Finset.mul_sum]
    rw [integral_finsetSum _ fun r _ => htermInt r]
    simp only [dotProduct, Finset.univ]
    apply Finset.sum_congr rfl
    intro r _
    change (∫ u, u ^ (2 * j) * (coefficients r * basis r u)) =
      (∫ u, u ^ (2 * j) * basis r u) * coefficients r
    rw [show (fun u => u ^ (2 * j) * (coefficients r * basis r u)) =
        fun u => coefficients r * (u ^ (2 * j) * basis r u) by
      funext u
      ring]
    rw [integral_const_mul]
    ring
  rw [hmomentKappa]
  have hsolveAt : momentMatrix jf ⬝ᵥ coefficients = target jf := congrFun hsolve jf
  rw [hsolveAt]
  dsimp only [target, jf]
  ring

#print axioms smooth_external_finite_moment_elimination

end

end D5.S3.Weil.TestFunctions.SmoothExternalMomentElimination
