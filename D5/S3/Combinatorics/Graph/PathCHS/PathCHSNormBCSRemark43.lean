/- GID: D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Complete homogeneous symmetric path norms admit explicit formulas. -/

/-
admission_basis: open-problem-resolution (#18566; Proved)
escape_witness: scaled_S_eval
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18981.
The sine-mode angles use ReferenceFrame.TopEigenspace.modeAngle,
with a private correspondence to the printed angle.
The spectral nodes use the expression 2*cos(modeAngle n (i+1)) inline;
the equal rotationTrace owner is instance-level and cannot be imported here.
Declaration proof_shape (same-delivery helpers expanded):
  trigForm: bind-only; consumers: result, claim, chs_eq_trig.
  bilateralForm: bind-only; consumers: result, claim, bilateral_eq_pathFormula.
  claim: bind-only; consumers: result.
  reflect_prod_linear: bind-only; consumers: partial_fraction_numerator.
  partial_fraction_numerator: bind-only; consumers: hsymm_partial_fractions.
  hsymm_partial_fractions: content; escape_witness: PathCHSNormClosedForm.eval_hsymm_coeff; consumers: chs_eq_trig.
  modeAngle_eq: bind-only; consumers: chs_eq_trig, node_weight.
  node_injective: bind-only; consumers: nodal_eq_S, chs_eq_trig, node_weight.
  node_root: bind-only; consumers: nodal_eq_S.
  S_monic: bind-only; consumers: nodal_eq_S.
  nodal_eq_S: bind-only; consumers: node_reciprocal_product, node_weight.
  scaled_S_eval: content; escape_witness: scaled_S_eval; consumers: node_reciprocal_product.
  node_reciprocal_product: content; escape_witness: scaled_S_eval; consumers: chs_eq_node_hsymm.
  node_weight: bind-only; consumers: chs_eq_trig.
  binomZ_zero_of_lt: bind-only; consumers: binomZ_reflect, bilateral_eq_pathFormula.
  binomZ_reflect: bind-only; consumers: bilateral_eq_pathFormula.
  bilateral_eq_pathFormula: bind-only; consumers: result.
  chs_eq_node_hsymm: content; escape_witness: scaled_S_eval; consumers: chs_eq_trig.
  chs_eq_trig: content; escape_witness: scaled_S_eval; consumers: result.
  result: content; escape_witness: scaled_S_eval; consumers: settling result.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import D5.S0.Conventions.IntegerIndexBinomial
import D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductContinuants
import D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace
import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

open D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43

open D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

/-- The first expression of Remark 4.3:
`2^(n+d)/(n+1) * Σ_{k=1}^{n} (-1)^(k+1) cos^(n-1+d)(πk/(n+1)) sin²(πk/(n+1))`. -/
noncomputable def trigForm (n d : ℕ) : ℝ :=
  (2 : ℝ) ^ (n + d) / (n + 1) * ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℝ) ^ (k + 1) * Real.cos (Real.pi * k / (n + 1)) ^ (n - 1 + d) *
      Real.sin (Real.pi * k / (n + 1)) ^ 2

/-- The second expression of Remark 4.3:
`Σ_{j=-∞}^{∞} [binom(n+d-1, (n+1)j + d/2) - binom(n+d-1, (n+1)j + d/2 - 1)]` (binomials outside `0..n+d-1`
are `0`; all but finitely many summands vanish). -/
noncomputable def bilateralForm (n d : ℕ) : ℤ :=
  ∑ᶠ j : ℤ, ((D5.S0.Conventions.IntegerIndexBinomial.binom (n + d - 1) ((n + 1 : ℤ) * j + (d / 2 : ℕ)) : ℤ) -
    D5.S0.Conventions.IntegerIndexBinomial.binom (n + d - 1) ((n + 1 : ℤ) * j + (d / 2 : ℕ) - 1))

/-- Bouthat–Chávez–Sheng, arXiv:2606.17356v1, Remark 4.3 ("we have found that the following appears to hold
for all n ≥ 1 and all even d ≥ 2"): `‖P_n‖_{X,d}^d` equals both expressions, where
`‖P_n‖_{X,d}^d = h_d(λ(P_n))` is `D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chs n d`. -/
def claim : Prop :=
  ∀ n d : ℕ, 1 ≤ n → 2 ≤ d → Even d → chs n d = trigForm n d ∧ chs n d = bilateralForm n d

end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43


set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43
noncomputable section
open Polynomial

private theorem reflect_prod_linear {ι K : Type*} [DecidableEq ι] [Field K]
    (s : Finset ι) (a : ι → K) :
    reflect s.card (∏ i ∈ s, (X-C (a i))) = ∏ i ∈ s, (1-C (a i)*X) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.card_insert_of_notMem hi, Finset.prod_insert hi,
      Finset.prod_insert hi, Nat.add_comm, reflect_mul]
    · rw [ih]
      simp [reflect_sub]
    · simp
    · apply le_trans (natDegree_prod_le _ _)
      simp

private theorem partial_fraction_numerator {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Nonempty ι] (a : ι → K) (ha : Function.Injective a) :
    (∑ i, C (a i ^ (Fintype.card ι-1) /
      ∏ j ∈ Finset.univ.erase i, (a i-a j)) *
      ∏ j ∈ Finset.univ.erase i, (1-C (a j)*X)) = (1 : Polynomial K) := by
  have he := Lagrange.eq_interpolate (s := Finset.univ) (v := a)
    (f := (X : Polynomial K)^(Fintype.card ι-1)) ha.injOn (by
      rw [degree_X_pow, Finset.card_univ, Nat.cast_lt]
      exact Nat.sub_one_lt (Fintype.card_ne_zero))
  have h := congrArg (reflect (Fintype.card ι-1)) he
  rw [reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero] at h
  rw [Lagrange.interpolate_apply] at h
  let reflectHom : Polynomial K →+ Polynomial K :=
    { toFun := reflect (Fintype.card ι-1)
      map_zero' := by simp
      map_add' := fun p q => reflect_add p q (Fintype.card ι-1) }
  change (1 : Polynomial K) = reflectHom (∑ i,
    C (((X : Polynomial K)^(Fintype.card ι-1)).eval (a i)) * Lagrange.basis Finset.univ a i) at h
  rw [map_sum] at h
  change (1 : Polynomial K) = ∑ i,
    reflect (Fintype.card ι-1)
      (C (((X : Polynomial K)^(Fintype.card ι-1)).eval (a i)) * Lagrange.basis Finset.univ a i) at h
  symm
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [eval_pow, eval_X, Lagrange.basis, Lagrange.basisDivisor,
    Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]
  rw [show C (a i ^ (Fintype.card ι-1)) *
      (C ((∏ j ∈ Finset.univ.erase i, (a i-a j))⁻¹) *
        ∏ j ∈ Finset.univ.erase i, (X-C (a j))) =
      C (a i ^ (Fintype.card ι-1) / ∏ j ∈ Finset.univ.erase i, (a i-a j)) *
        ∏ j ∈ Finset.univ.erase i, (X-C (a j)) by rw [div_eq_mul_inv,map_mul]; ring]
  rw [reflect_C_mul]
  congr 1
  have hc : (Finset.univ.erase i : Finset ι).card = Fintype.card ι-1 := by simp
  rw [← hc, reflect_prod_linear]

private theorem hsymm_partial_fractions {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Nonempty ι] (a : ι → K) (ha : Function.Injective a) (d : ℕ) :
    MvPolynomial.eval a (MvPolynomial.hsymm ι K d) =
      ∑ i, a i ^ (Fintype.card ι-1+d) /
        ∏ j ∈ Finset.univ.erase i, (a i-a j) := by
  let w : ι → K := fun i => a i ^ (Fintype.card ι-1) /
    ∏ j ∈ Finset.univ.erase i, (a i-a j)
  let H : PowerSeries K := ∑ i, PowerSeries.C (w i) *
    PowerSeries.mk (fun d => a i ^ d)
  let P : PowerSeries K := ∏ i, (1-PowerSeries.C (a i)*PowerSeries.X)
  have hHP : H*P=1 := by
    dsimp [H]
    rw [Finset.sum_mul]
    have he (i : ι) : (PowerSeries.C (w i)*PowerSeries.mk (fun d => a i^d))*P =
        PowerSeries.C (w i)*∏ j ∈ Finset.univ.erase i,
          (1-PowerSeries.C (a j)*PowerSeries.X) := by
      dsimp [P]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      calc
        _ = PowerSeries.C (w i) *
          ((PowerSeries.mk (fun d => a i^d))*(1-PowerSeries.C (a i)*PowerSeries.X)) *
          ∏ j ∈ Finset.univ.erase i, (1-PowerSeries.C (a j)*PowerSeries.X) := by ring
        _ = _ := by rw [D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.geometric_mul_linear,mul_one]
    simp_rw [he]
    have hp := congrArg (Polynomial.coeToPowerSeries.ringHom (R := K))
      (partial_fraction_numerator a ha)
    simp only [map_sum,map_mul,map_prod,map_sub,map_one] at hp
    simpa only [Polynomial.coeToPowerSeries.ringHom_apply,Polynomial.coe_C,Polynomial.coe_X,w] using hp
  have hG := D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.hsymm_series_product a
  change (PowerSeries.mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι K d))*P=1 at hG
  have he : (PowerSeries.mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι K d))=H := by
    calc
      _ = (PowerSeries.mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι K d))*(H*P) := by rw [hHP,mul_one]
      _ = H*((PowerSeries.mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι K d))*P) := by ring
      _ = H := by rw [hG,mul_one]
  have hc := congrArg (PowerSeries.coeff d) he
  simp only [PowerSeries.coeff_mk] at hc
  rw [hc]
  dsimp [H]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PowerSeries.coeff_C_mul,PowerSeries.coeff_mk,w,pow_add]
  ring

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43


set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43
noncomputable section
open Polynomial Polynomial.Chebyshev D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

private theorem modeAngle_eq (n : ℕ) (i : Fin n) :
    D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1) =
      Real.pi*(i.val+1)/(n+1) := by
  simp [D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle, mul_comm]

private theorem node_injective (n : ℕ) : Function.Injective (fun i : Fin n => (2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) := by
  intro i j h
  apply Fin.ext
  have hc : Real.cos (((i.val : ℝ)+1)*Real.pi/(n+1)) =
      Real.cos (((j.val : ℝ)+1)*Real.pi/(n+1)) := by
    have hc := mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h
    simpa only [D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle, Nat.cast_add, Nat.cast_one] using hc
  exact ((Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n))
    (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) hc

private theorem node_root (n : ℕ) (i : Fin n) : (S ℝ n).eval ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) = 0 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hx : Real.cos (((i.val : ℝ)+1)*Real.pi/(n+1)) ∈ (U ℝ n).roots := by
    rw [roots_U_real]
    exact Finset.mem_val.mpr (Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩)
  have hroot := Polynomial.isRoot_of_mem_roots hx
  rw [S_eq_U_comp_half_mul_X, eval_comp]
  simpa only [Polynomial.IsRoot, eval_mul, eval_C, eval_X, invOf_eq_inv, D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle,
    Nat.cast_add, Nat.cast_one, inv_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)] using hroot

private theorem S_monic (n : ℕ) : (S ℝ n).Monic := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  change (S ℝ n).leadingCoeff = 1
  rw [S_eq_U_comp_half_mul_X,
    leadingCoeff_comp (by norm_num [invOf_eq_inv]),
    leadingCoeff_U_natCast, natDegree_U_natCast, leadingCoeff_C_mul_X,
    invOf_eq_inv, ← mul_pow]
  norm_num

private theorem nodal_eq_S (n : ℕ) : Lagrange.nodal Finset.univ (fun i : Fin n => (2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) = S ℝ n := by
  have hd : Lagrange.nodal Finset.univ (fun i : Fin n => (2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) ∣ S ℝ n := by
    apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C (node_injective n))
    intro i
    exact dvd_iff_isRoot.mpr (node_root n i)
  exact (eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic (S_monic n) hd
    (by rw [chebS_degree,Lagrange.natDegree_nodal,Finset.card_univ,Fintype.card_fin])).symm

private theorem scaled_S_eval (t : ℝ) (ht : t ≠ 0) (n : ℕ) :
    t^n*(S ℝ n).eval t⁻¹ = (cont (fun _ => (t^2)) 1 1) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cont]
  | one => simp [cont,ht]
  | more n ih ih1 =>
    push_cast
    rw [S_add_two,eval_sub,eval_mul,eval_X]
    simp only [cont]
    rw [show t^(n+2)*(t⁻¹*(S ℝ (↑n+1)).eval t⁻¹-(S ℝ n).eval t⁻¹) =
      t^(n+1)*(S ℝ (↑n+1)).eval t⁻¹-t^2*(t^n*(S ℝ n).eval t⁻¹) by
        rw [pow_succ,pow_succ]; field_simp]
    rw [ih,show t^(n+1)*(S ℝ (↑n+1)).eval t⁻¹ = (cont (fun _ => (t^2)) 1 1) (n+1) by simpa using ih1]

private theorem node_reciprocal_product (n : ℕ) (t : ℝ) :
    ∏ i : Fin n, (1-t*(2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) = (cont (fun _ => (t^2)) 1 1) n := by
  by_cases ht : t=0
  · subst t; simp [continuant_zero]
  · rw [← scaled_S_eval t ht n,← nodal_eq_S,Lagrange.eval_nodal]
    have hc : t^n = ∏ _i : Fin n, t := (Fin.prod_const n t).symm
    rw [hc,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    field_simp

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43


set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43
noncomputable section
open Polynomial Polynomial.Chebyshev

private theorem node_weight (n : ℕ) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))-(2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (j.val+1)))))⁻¹ =
      2*(-1 : ℝ)^i.val * Real.sin (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1))^2/(n+1) := by
  let θ := D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)
  have harg : ((n : ℝ)+1)*θ = (i.val+1)*Real.pi := by
    dsimp only [θ]
    rw [modeAngle_eq]
    field_simp
  have hu : (U ℝ n).eval (Real.cos θ) = 0 := by
    change (U ℝ n).eval (Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1))) = 0
    apply Polynomial.isRoot_of_mem_roots
    rw [roots_U_real]
    apply Finset.mem_val.mpr
    apply Finset.mem_image.mpr
    refine ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
    simp only [D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle, Nat.cast_add, Nat.cast_one]
  have hd := congrArg (Polynomial.eval (Real.cos θ))
    (add_one_mul_T_eq_poly_in_U (R := ℝ) (n : ℤ))
  simp only [eval_mul,eval_add,eval_intCast,eval_one,eval_sub,eval_X,eval_pow,
    T_real_cos,hu,mul_zero,zero_sub] at hd
  push_cast at hd
  rw [harg,show (i.val : ℝ)+1 = (i.val+1 : ℕ) by norm_num,Real.cos_nat_mul_pi] at hd
  have htrig := Real.sin_sq_add_cos_sq θ
  have hder : (derivative (S ℝ n)).eval ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) =
      (derivative (U ℝ n)).eval (Real.cos θ)/2 := by
    letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    rw [S_eq_U_comp_half_mul_X,derivative_comp]
    simp [θ,eval_comp,invOf_eq_inv,div_eq_mul_inv] <;> ring
  have hprod : ∏ j ∈ Finset.univ.erase i, ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))-(2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (j.val+1)))) =
      (derivative (S ℝ n)).eval ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) := by
    rw [← nodal_eq_S, Lagrange.eval_nodal_derivative_eval_node_eq
      (v := fun j : Fin n => 2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (j.val+1))) (Finset.mem_univ i),
      Lagrange.eval_nodal]
  have hsign : (-1 : ℝ)^i.val * (-1 : ℝ)^i.val = 1 := by
    rw [← mul_pow]; norm_num
  have he : (∏ j ∈ Finset.univ.erase i, ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))-(2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (j.val+1)))))*
      (2*(-1 : ℝ)^i.val * Real.sin θ^2) = (n : ℝ)+1 := by
    rw [hprod,hder]
    rw [pow_succ] at hd
    linear_combination ((-1 : ℝ)^i.val)*hd +
      (((-1 : ℝ)^i.val)*(derivative (U ℝ n)).eval (Real.cos θ))*htrig +
      ((n : ℝ)+1)*hsign
  have hn : (n : ℝ)+1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
  apply (eq_div_iff hn).2
  have hz : (∏ j ∈ Finset.univ.erase i, ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))-(2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (j.val+1))))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 ((node_injective n) h).symm)
  apply (mul_left_cancel₀ hz)
  rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul]
  simpa [θ] using he.symm

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43


set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43
open D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

private theorem binomZ_zero_of_lt (L : ℕ) (r : ℤ) (h : (L : ℤ) < r) : D5.S0.Conventions.IntegerIndexBinomial.binom L r = 0 := by
  rw [D5.S0.Conventions.IntegerIndexBinomial.binom, if_neg (by omega)]
  exact_mod_cast Nat.choose_eq_zero_of_lt (show L < r.toNat by omega)

private theorem binomZ_reflect (L : ℕ) (r : ℤ) : D5.S0.Conventions.IntegerIndexBinomial.binom L r = D5.S0.Conventions.IntegerIndexBinomial.binom L ((L : ℤ)-r) := by
  by_cases h0 : 0 ≤ r
  · by_cases hL : r ≤ L
    · unfold D5.S0.Conventions.IntegerIndexBinomial.binom
      rw [if_neg (by omega), if_neg (by omega)]
      have he : ((L : ℤ)-r).toNat = L-r.toNat := by omega
      rw [he, Nat.choose_symm (by omega)]
    · rw [binomZ_zero_of_lt L r (by omega)]
      simp only [D5.S0.Conventions.IntegerIndexBinomial.binom,if_pos (show (L : ℤ)-r < 0 by omega)]
  · rw [binomZ_zero_of_lt L ((L : ℤ)-r) (by omega)]
    simp [D5.S0.Conventions.IntegerIndexBinomial.binom, show r < 0 by omega]

private theorem bilateral_eq_pathFormula (n m : ℕ) (hn : 1 ≤ n) :
    bilateralForm n (2*m) = pathFormula n m := by
  classical
  let N := n+1
  let L := n+2*m-1
  let M := m/N+1
  let f : ℤ → ℤ := fun j =>
    (D5.S0.Conventions.IntegerIndexBinomial.binom L ((N : ℤ)*j+m) : ℤ)-D5.S0.Conventions.IntegerIndexBinomial.binom L ((N : ℤ)*j+m-1)
  let s := (Finset.range M).image (fun k : ℕ => -(k : ℤ))
  let t := (Finset.range M).image (fun k : ℕ => (k : ℤ)+1)
  have hN : 0 < N := by exact Nat.succ_pos n
  have hL : (L : ℤ) = (N : ℤ)+2*m-2 := by dsimp [L,N]; omega
  have hz (j : ℤ) (hj : j ∉ s ∪ t) : f j = 0 := by
    by_cases hj0 : j ≤ 0
    · have hjr : j = -( (-j).toNat : ℤ) := by omega
      have hlarge : M ≤ (-j).toNat := by
        by_contra! hh
        apply hj
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨(-j).toNat, Finset.mem_range.mpr hh, hjr.symm⟩
      have hmul : m < (-j).toNat*N := by
        have hq : m/N < (-j).toNat := Nat.lt_of_succ_le hlarge
        exact (Nat.div_lt_iff_lt_mul hN).mp hq
      have hr : (N : ℤ)*j+m < 0 := by
        have hmul' : (m : ℤ) < ((-j).toNat : ℤ)*N := by exact_mod_cast hmul
        rw [hjr]
        nlinarith
      simp only [f, D5.S0.Conventions.IntegerIndexBinomial.binom,if_pos (show (N : ℤ)*j+m < 0 by omega),
        if_pos (show (N : ℤ)*j+m-1 < 0 by omega),Int.cast_zero,sub_self]
    · have hjr : j = ((j-1).toNat : ℤ)+1 := by omega
      have hlarge : M ≤ (j-1).toNat := by
        by_contra! hh
        apply hj
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨(j-1).toNat, Finset.mem_range.mpr hh, hjr.symm⟩
      have hmul : m < (j-1).toNat*N := by
        have hq : m/N < (j-1).toNat := Nat.lt_of_succ_le hlarge
        exact (Nat.div_lt_iff_lt_mul hN).mp hq
      have hr : (L : ℤ) < (N : ℤ)*j+m-1 := by
        have hmul' : (m : ℤ) < ((j-1).toNat : ℤ)*N := by exact_mod_cast hmul
        rw [hjr,hL]
        nlinarith
      simp only [f, binomZ_zero_of_lt L _ hr,
        binomZ_zero_of_lt L _ (by omega : (L : ℤ) < (N : ℤ)*j+m),
        Int.cast_zero, sub_self]
  have he : bilateralForm n (2*m) = ∑ j ∈ s ∪ t, f j := by
    unfold bilateralForm
    simp only [Nat.mul_div_cancel_left m Nat.zero_lt_two]
    change (∑ᶠ j : ℤ, f j) = _
    apply finsum_eq_finsetSum_of_support_subset
    intro j hj
    by_contra h
    exact hj (hz j h)
  rw [he, Finset.sum_union]
  · dsimp only [s,t]
    rw [Finset.sum_image, Finset.sum_image, ← Finset.sum_add_distrib]
    · unfold pathFormula
      dsimp [M,N]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f,L,N]
      rw [binomZ_reflect (n+2*m-1) (((n : ℤ)+1)*(↑k+1)+↑m),
        binomZ_reflect (n+2*m-1) (((n : ℤ)+1)*(↑k+1)+↑m-1)]
      have hcast : ((n+2*m-1 : ℕ) : ℤ) = n+2*m-1 := by omega
      rw [hcast]
      have h1 : (n : ℤ)+2*m-1-(((n : ℤ)+1)*(↑k+1)+↑m) = ↑m-↑k*((n : ℤ)+1)-2 := by push_cast; ring
      have h2 : (n : ℤ)+2*m-1-(((n : ℤ)+1)*(↑k+1)+↑m-1) = ↑m-↑k*((n : ℤ)+1)-1 := by push_cast; ring
      have h3 : (((n : ℤ)+1) : ℤ)*(-↑k)+↑m = ↑m-↑k*((n : ℤ)+1) := by ring
      rw [h1,h2,h3]
      rw [show n+2*m-1 = 2*m+n-1 by omega]
      ring
    · intro a _ b _ hab
      exact Nat.cast_injective (by linarith [hab] : (a : ℤ) = b)
    · intro a _ b _ hab
      exact Nat.cast_injective (by linarith [hab] : (a : ℤ) = b)
  · apply Finset.disjoint_left.mpr
    intro j hs ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b,hb,h⟩ := Finset.mem_image.mp ht
    omega

end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43


set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43
noncomputable section
open PowerSeries D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

private theorem chs_eq_node_hsymm (n d : ℕ) :
    chs n d = MvPolynomial.eval (fun i : Fin n => (2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) (MvPolynomial.hsymm (Fin n) ℝ d) := by
  let G : PowerSeries ℝ := mk fun d => MvPolynomial.eval (fun i : Fin n => (2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) (MvPolynomial.hsymm (Fin n) ℝ d)
  let H : PowerSeries ℝ := mk fun d => chs n d
  let P : PowerSeries ℝ := (cont (fun _ => (X^2)) 1 1) n
  have hp : (∏ i : Fin n, (1 - C ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1))))*X)) = P := by
    have hpoly : (∏ i : Fin n, (1-Polynomial.C ((2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1))))*Polynomial.X)) =
        (cont (fun _ => (Polynomial.X^2 : Polynomial ℝ)) 1 1) n := by
      apply Polynomial.funext
      intro t
      have he := continuant_map (Polynomial.evalRingHom t) (Polynomial.X^2 : Polynomial ℝ) n
      change Polynomial.eval t ((cont (fun _ => (Polynomial.X^2 : Polynomial ℝ)) 1 1) n) =
        (cont (fun _ => (Polynomial.eval t (Polynomial.X^2 : Polynomial ℝ))) 1 1) n at he
      simp only [Polynomial.eval_pow,Polynomial.eval_X] at he
      rw [he]
      simpa only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_one,
        Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,mul_comm] using node_reciprocal_product n t
    have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℝ)) hpoly
    rw [continuant_map] at h
    simpa [P] using h
  have hG : G*P=1 := by
    have h := D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.hsymm_series_product (fun i : Fin n => (2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1))))
    rwa [hp] at h
  have hH : H*P=1 := D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.path_hsymm_series n
  have he : H=G := by
    calc
      H = H*(G*P) := by rw [hG,mul_one]
      _ = G*(H*P) := by ring
      _ = G := by rw [hH,mul_one]
  have hc := congrArg (coeff d) he
  simpa [H,G] using hc

private theorem chs_eq_trig (n d : ℕ) (hn : 1 ≤ n) : chs n d = trigForm n d := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  rw [chs_eq_node_hsymm,D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43.hsymm_partial_fractions (fun i : Fin n => (2 * Real.cos (D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle n (i.val+1)))) (node_injective n)]
  simp only [Fintype.card_fin,div_eq_mul_inv,node_weight]
  unfold trigForm
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun i _ => i.val+1) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i _ j _ hij
    exact Fin.ext (by omega)
  · intro k hk
    refine ⟨⟨k-1,by have := (Finset.mem_Icc.mp hk); omega⟩,Finset.mem_univ _,?_⟩
    have := (Finset.mem_Icc.mp hk)
    simp only [Fin.val_mk]
    omega
  · intro i hi
    simp only [modeAngle_eq,mul_pow,Nat.cast_add,Nat.cast_one]
    have hp : (2 : ℝ)^(n-1+d)*2 = (2 : ℝ)^(n+d) := by
      rw [← pow_succ]
      congr 1
      omega
    have hs : (-1 : ℝ)^(i.val+1+1) = (-1 : ℝ)^i.val := by
      rw [show i.val+1+1=i.val+2 by omega,pow_add]
      norm_num
    rw [hs]
    rw [div_eq_mul_inv]
    linear_combination (norm := (simp only [div_eq_mul_inv]; ring_nf)) (Real.cos (Real.pi*(i.val+1)/(n+1))^(n-1+d)*
      ((-1 : ℝ)^i.val)*Real.sin (Real.pi*(i.val+1)/(n+1))^2*((n : ℝ)+1)⁻¹)*hp

theorem result : D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43.claim := by
  intro n d hn hd heven
  refine ⟨chs_eq_trig n d hn,?_⟩
  obtain ⟨m,hm⟩ := heven
  have he : d=2*m := by omega
  rw [he,D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chs_formula,D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43.bilateral_eq_pathFormula n m hn]

end
end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43
