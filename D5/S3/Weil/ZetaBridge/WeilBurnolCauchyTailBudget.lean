/- GID: D5/S3/Weil/ZetaBridge/WeilBurnolCauchyTailBudget
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilBurnolCauchyTailBudget
   mirror-E: none(waiver:actual-quadratic-tail-budget)
   anchors: []
   digest: Cancel the actual exceptional head and control the full quadratic remainder by a sum-of-squared-decay budget, then apply the existing executable depth selector. -/

import D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A direct quadratic tail certificate

The new constant controls the quadratic remainder directly. It is not an
upper bound on the older entrywise absolute mixed-majorant total. Exact
exceptional-head cancellation removes all finite target contributions from
this budget. Cauchy-Schwarz retains every coefficient cross term and changes
(sum D_i)^2 to sum D_i^2 in the scalar tail coefficient.

The remaining scalar spectral-tail input is the precise interface for
Brent, Platt and Trudgian (2021), Theorem 1, equations (1)-(3). This file
proves no numerical zeta counting inequality. Its tail is two-sided and
indexed by actual zeros with full analytic multiplicities; a positive-height
half-endpoint literature formula requires a separate normalization proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Weil.ZetaBridge.WeilBurnolCauchyTailBudget

noncomputable section
open MeasureTheory Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget
open scoped BigOperators ComplexConjugate Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem synthesis_norm_sq_le (a v : ι → ℂ) :
    ‖∑ i, a i * v i‖ ^ 2 ≤
      finiteComplexEnergy a * ∑ i, ‖v i‖ ^ 2 := by
  have ht : ‖∑ i, a i * v i‖ ≤ ∑ i, ‖a i‖ * ‖v i‖ := by
    calc
      _ ≤ ∑ i, ‖a i * v i‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul]
  have hs : 0 ≤ ∑ i, ‖a i‖ * ‖v i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have ht2 : ‖∑ i, a i * v i‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖v i‖) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr ht)
      (add_nonneg hs (norm_nonneg (∑ i, a i * v i)))
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖a i‖) (fun i => ‖v i‖)
  simpa only [finiteComplexEnergy, Complex.normSq_eq_norm_sq] using ht2.trans hcs

/-- Finite Cauchy-Schwarz controls the product of both synthesized evaluations. -/
theorem synthesized_product_le_squared_decay
    (a v w : ι → ℂ) (D : ι → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hD : ∀ i, 0 ≤ D i)
    (hv : ∀ i, ‖v i‖ ≤ D i * u) (hw : ∀ i, ‖w i‖ ≤ D i * u) :
    ‖∑ i, a i * v i‖ * ‖∑ i, a i * w i‖ ≤
      finiteComplexEnergy a * (∑ i, D i ^ 2) * u ^ 2 := by
  have hsq (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ D i * u) :
      ‖∑ i, a i * f i‖ ^ 2 ≤
        finiteComplexEnergy a * (∑ i, D i ^ 2) * u ^ 2 := by
    have hsum : (∑ i, ‖f i‖ ^ 2) ≤ (∑ i, D i ^ 2) * u ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h := mul_nonneg (sub_nonneg.mpr (hf i))
        (add_nonneg (mul_nonneg (hD i) hu) (norm_nonneg (f i)))
      nlinarith
    calc
      _ ≤ finiteComplexEnergy a * ∑ i, ‖f i‖ ^ 2 := synthesis_norm_sq_le a f
      _ ≤ finiteComplexEnergy a * ((∑ i, D i ^ 2) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (finiteComplexEnergy_nonneg a)
      _ = _ := by ring
  have hp := hsq v hv
  have hm := hsq w hw
  nlinarith [sq_nonneg (‖∑ i, a i * v i‖ - ‖∑ i, a i * w i‖)]

variable {Z : ZeroData} (F : FiniteEvenWeilOrbitFrame Z ι)

private theorem killer_synthesis_summand_bound
    (P : OrbitBurnolPacket F) (D : ι → ℝ) (hD : ∀ i, 0 ≤ D i)
    (a : ι → ℂ) (n : ℕ)
    (hp : ∀ i, ‖fourierLaplace (P.killer i) (Z.gamma n)‖ ≤
      D i * inverseQuadraticEnvelope Z n)
    (hm : ∀ i, ‖fourierLaplace (P.killer i) (conj (Z.gamma n))‖ ≤
      D i * inverseQuadraticEnvelope Z n) :
    ‖zeroSummand Z (convolutionSquare (finiteWeilLinearCombination a P.killer)) n‖ ≤
      finiteComplexEnergy a * (∑ i, D i ^ 2) * fourthMomentSummand Z n := by
  have hu : 0 ≤ inverseQuadraticEnvelope Z n := by unfold inverseQuadraticEnvelope; positivity
  have hprod := synthesized_product_le_squared_decay a
    (fun i => fourierLaplace (P.killer i) (Z.gamma n))
    (fun i => fourierLaplace (P.killer i) (conj (Z.gamma n)))
    D (inverseQuadraticEnvelope Z n) hu hD hp hm
  rw [zeroSummand, fourierLaplace_convolutionSquare_complex,
    fourierLaplace_finiteWeilLinearCombination,
    fourierLaplace_finiteWeilLinearCombination, norm_mul, norm_mul, Complex.norm_conj]
  have hnat : ‖(Z.multiplicity n : ℂ)‖ = (Z.multiplicity n : ℝ) := by simp
  rw [hnat]
  calc
    _ ≤ (Z.multiplicity n : ℝ) *
        (finiteComplexEnergy a * (∑ i, D i ^ 2) * inverseQuadraticEnvelope Z n ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = _ := by unfold fourthMomentSummand; ring

private theorem exceptional_summand_zero
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) (n : ℕ)
    (hn : n ∈ P.exceptional) (ho : n ∉ frameTargetIndices F) :
    zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) n = 0 := by
  have hk : fourierLaplace (finiteWeilLinearCombination a P.killer) (Z.gamma n) = 0 := by
    rw [fourierLaplace_finiteWeilLinearCombination]
    apply Finset.sum_eq_zero
    intro i _
    rw [P.kills_exception i n hn ho, mul_zero]
  rw [burnolSynthesis_zeroSummand, zeroSummand,
    fourierLaplace_convolutionSquare_complex, hk]
  simp

/-- The finite exceptional head cancels exactly against the selected target
contribution. Only the exceptional complement remains to be estimated. -/
theorem burnolRemainder_eq_exceptional_tail
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) :
    burnolRemainder F P N a =
      (∑' n : {n : ℕ // n ∉ P.exceptional},
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) n.1).re := by
  have hall := zeroSummand_summable_of_zeroData Z
    (convolutionSquare (burnolSynthesis F P N a))
  have hhead :
      (∑ n ∈ P.exceptional,
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) n) =
      ∑ n ∈ frameTargetIndices F,
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) n := by
    symm
    apply Finset.sum_subset P.target_subset
    intro n hn ho
    exact exceptional_summand_zero F P N a n hn ho
  rw [burnolRemainder, burnolFullQuadratic, zeroSum_eq_tsum_of_zeroData,
    ← hall.sum_add_tsum_subtype_compl P.exceptional, Complex.add_re,
    hhead, burnolSynthesis_target_union_value]
  ring

/-- A direct complete-quadratic estimate. No old mixed-majorant upper bound is
assumed or inferred. All cross terms are controlled jointly by Cauchy-Schwarz. -/
theorem burnol_uniform_cauchy_tail_bound
    (P : OrbitBurnolPacket F) (D : ι → ℝ) (Theta : ℝ)
    (hD : ∀ i, 0 ≤ D i)
    (hp : ∀ n ∉ P.exceptional, ∀ i,
      ‖fourierLaplace (P.killer i) (Z.gamma n)‖ ≤ D i * inverseQuadraticEnvelope Z n)
    (hm : ∀ n ∉ P.exceptional, ∀ i,
      ‖fourierLaplace (P.killer i) (conj (Z.gamma n))‖ ≤ D i * inverseQuadraticEnvelope Z n)
    (hspectral : Summable (fun n : {n : ℕ // n ∉ P.exceptional} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ P.exceptional}, fourthMomentSummand Z n.1) ≤ Theta)
    (N : ℕ) (a : ι → ℂ) :
    |burnolRemainder F P N a| ≤
      ((1 / 4 : ℝ) ^ (N + 1) * ((∑ i, D i ^ 2) * Theta)) * finiteComplexEnergy a := by
  let c : ℝ := (1 / 4 : ℝ) ^ (N + 1) * finiteComplexEnergy a * (∑ i, D i ^ 2)
  have hc : 0 ≤ c :=
    mul_nonneg (mul_nonneg (by positivity) (finiteComplexEnergy_nonneg a))
      (Finset.sum_nonneg fun i _ => sq_nonneg (D i))
  have hsum := (zeroSummand_summable_of_zeroData Z
    (convolutionSquare (burnolSynthesis F P N a))).subtype (fun n => n ∉ P.exceptional)
  have hpoint (n : {n : ℕ // n ∉ P.exceptional}) :
      ‖zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) n.1‖ ≤
        c * fourthMomentSummand Z n.1 := by
    have hb := P.peak_tail n.1 n.2
    have hbase : ‖fourierLaplace P.peak (Z.gamma n.1) *
        conj (fourierLaplace P.peak (conj (Z.gamma n.1)))‖ ≤ (1 / 4 : ℝ) := by
      rw [norm_mul, Complex.norm_conj]
      calc
        _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
          mul_le_mul hb.1 hb.2 (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    rw [burnolSynthesis_zeroSummand, norm_mul, norm_pow]
    calc
      _ ≤ (1 / 4 : ℝ) ^ (N + 1) *
          (finiteComplexEnergy a * (∑ i, D i ^ 2) * fourthMomentSummand Z n.1) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hbase (N + 1))
          (killer_synthesis_summand_bound F P D hD a n.1 (hp n.1 n.2) (hm n.1 n.2))
          (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [c]; ring
  rw [burnolRemainder_eq_exceptional_tail]
  calc
    _ ≤ ‖∑' n : {n : ℕ // n ∉ P.exceptional},
        zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) n.1‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' n : {n : ℕ // n ∉ P.exceptional},
        ‖zeroSummand Z (convolutionSquare (burnolSynthesis F P N a)) n.1‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : {n : ℕ // n ∉ P.exceptional}, c * fourthMomentSummand Z n.1 :=
      hsum.norm.tsum_le_tsum hpoint (hspectral.mul_left c)
    _ = c * ∑' n : {n : ℕ // n ∉ P.exceptional}, fourthMomentSummand Z n.1 := by rw [tsum_mul_left]
    _ ≤ c * Theta := mul_le_mul_of_nonneg_left htail hc
    _ = _ := by dsimp [c]; ring

/-- Two finite jet bounds per actual killer discharge every transform-decay
hypothesis. The only infinite estimate left is the scalar spectral tail. -/
theorem burnol_cauchy_tail_bound_of_two_jets
    (P : OrbitBurnolPacket F) (J0 J2 : ι → ℝ) (Theta : ℝ)
    (hs : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Set.Icc (-1) 1)
    (h0 : ∀ i, (∫ x : ℝ, ‖P.killer i x‖) ≤ J0 i)
    (h2 : ∀ i, (∫ x : ℝ, ‖((deriv^[2]) (P.killer i : ℝ → ℂ)) x‖) ≤ J2 i)
    (hspectral : Summable (fun n : {n : ℕ // n ∉ P.exceptional} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ P.exceptional}, fourthMomentSummand Z n.1) ≤ Theta)
    (N : ℕ) (a : ι → ℂ) :
    |burnolRemainder F P N a| ≤
      ((1 / 4 : ℝ) ^ (N + 1) * ((∑ i, (3 * (J0 i + J2 i)) ^ 2) * Theta)) *
        finiteComplexEnergy a := by
  apply burnol_uniform_cauchy_tail_bound F P (fun i => 3 * (J0 i + J2 i)) Theta
  · intro i
    have hJ0 := (integral_nonneg fun x => norm_nonneg (P.killer i x)).trans (h0 i)
    have hJ2 := (integral_nonneg fun x => norm_nonneg
      (((deriv^[2]) (P.killer i : ℝ → ℂ)) x)).trans (h2 i)
    positivity
  · intro n _ i
    exact (zero_transform_pair_le_three_jets Z (P.killer i) _ _ (hs i) (h0 i) (h2 i) n).1
  · intro n _ i
    exact (zero_transform_pair_le_three_jets Z (P.killer i) _ _ (hs i) (h0 i) (h2 i) n).2
  · exact hspectral
  · exact htail

/-- The existing exact integer selector applies to the direct quadratic
constant, without identifying it with the older entrywise majorant. -/
theorem cauchy_budget_full_gram_margin
    (P : OrbitBurnolPacket F) (J0 J2 : ι → ℝ) (Theta : ℝ)
    (hs : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Set.Icc (-1) 1)
    (h0 : ∀ i, (∫ x : ℝ, ‖P.killer i x‖) ≤ J0 i)
    (h2 : ∀ i, (∫ x : ℝ, ‖((deriv^[2]) (P.killer i : ℝ → ℂ)) x‖) ≤ J2 i)
    (hspectral : Summable (fun n : {n : ℕ // n ∉ P.exceptional} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ P.exceptional}, fourthMomentSummand Z n.1) ≤ Theta)
    (c d p q : ℕ) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q)
    (hround : (∑ i, (3 * (J0 i + J2 i)) ^ 2) * Theta ≤ (c : ℝ) / (d : ℝ))
    (N : ℕ) (hN : rationalQuarterDepth c d p q ≤ N) (a : ι → ℂ) :
    (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
      -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a := by
  have heps := rationalQuarterDepth_real_sound c d p q N hd hp hq hN _ hround
  have hm (i : ι) : (1 : ℝ) ≤ (Z.multiplicity (F.index i) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Z.multiplicity_pos (F.index i)))
  have ht : frameOddTargetQuadratic F a ≤ -4 * finiteComplexEnergy a := by
    simpa only [mul_one] using frameOddTargetQuadratic_le_massFloor F 1 hm a
  have hr := (le_abs_self _).trans
    (burnol_cauchy_tail_bound_of_two_jets F P J0 J2 Theta hs h0 h2 hspectral htail N a)
  have hsmall := mul_le_mul_of_nonneg_right heps.le (finiteComplexEnergy_nonneg a)
  rw [fullWeilGram_quadratic]
  change burnolFullQuadratic F P N a ≤ -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a
  unfold burnolRemainder at hr
  linarith

end

open scoped BigOperators

/-- Executable arithmetic for the direct quadratic constant; it has no finite
head term because the actual exceptional head was proved to cancel. -/
def rationalCauchyTailBudget {ι : Type*} [Fintype ι]
    (J0 J2 : ι → ℚ) (Theta : ℚ) : ℚ :=
  (∑ i, (3 * (J0 i + J2 i)) ^ 2) * Theta

/-- The executable rational expression has exactly the real coefficient used
by cauchy_budget_full_gram_margin. -/
theorem rationalCauchyTailBudget_cast {ι : Type*} [Fintype ι]
    (J0 J2 : ι → ℚ) (Theta : ℚ) :
    (rationalCauchyTailBudget J0 J2 Theta : ℝ) =
      (∑ i, (3 * ((J0 i : ℝ) + (J2 i : ℝ))) ^ 2) * (Theta : ℝ) := by
  unfold rationalCauchyTailBudget
  push_cast
  rfl

#print axioms synthesized_product_le_squared_decay
#print axioms burnolRemainder_eq_exceptional_tail
#print axioms burnol_uniform_cauchy_tail_bound
#print axioms burnol_cauchy_tail_bound_of_two_jets
#print axioms cauchy_budget_full_gram_margin
#print axioms rationalCauchyTailBudget_cast

end D5.S3.Weil.ZetaBridge.WeilBurnolCauchyTailBudget
