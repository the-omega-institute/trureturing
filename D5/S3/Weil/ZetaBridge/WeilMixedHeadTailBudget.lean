/- GID: D5/S3/Weil/ZetaBridge/WeilMixedHeadTailBudget
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilMixedHeadTailBudget
   mirror-E: none(waiver:certified-head-and-tail-budget)
   anchors: []
   digest: Bound the actual full mixed majorant by finite transform enclosures and a scalar fourth-moment tail, and feed that bound to the executable common-depth theorem. -/

import D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget
import D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite head and scalar zero-tail control of the mixed majorant

Literature interface: Brent, Platt and Trudgian, Accurate estimation of sums
over zeros of the Riemann zeta-function, Math. Comp. 90 (2021), 2923-2935,
Theorem 1, equations (1)-(3), DOI 10.1090/mcom/3652. Their positive-height
sum counts multiplicities and gives half weight at endpoints. The present
owner uses an explicit finite index set and its complement; an application
of the literature estimate must separately reconcile those conventions.

The operator-family constant is not an assumed input here. It is derived
from finite head enclosures, two-sided transform decay of each actual test,
and a one-dimensional positive zero-tail bound. This owner does not purport
to prove or automatically import the published numerical zero-count bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget

open MeasureTheory
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget
open scoped BigOperators ComplexConjugate Matrix

variable {ι : Type*} [Fintype ι]

/-- The decay envelope uses the real part of gamma, the actual zero ordinate. -/
def inverseQuadraticEnvelope (Z : ZeroData) (n : ℕ) : ℝ :=
  (1 + (Z.gamma n).re ^ 2)⁻¹

/-- Analytic multiplicity is counted once in the positive fourth moment. -/
def fourthMomentSummand (Z : ZeroData) (n : ℕ) : ℝ :=
  (Z.multiplicity n : ℝ) * inverseQuadraticEnvelope Z n ^ 2

/-- A finite expression for a mixed-majorant head from certified transform bounds. -/
def finiteMixedHeadBound (Z : ZeroData) (E : Finset ℕ)
    (plus minus : ι → ℕ → ℝ) : ℝ :=
  ∑ n ∈ E, (Z.multiplicity n : ℝ) * (∑ i, plus i n) * (∑ i, minus i n)

private theorem mixed_norm_le (Z : ZeroData) (g h : WeilTestFunction)
    (n : ℕ) (u v : ℝ)
    (hu : ‖fourierLaplace g (Z.gamma n)‖ ≤ u)
    (hv : ‖fourierLaplace h (conj (Z.gamma n))‖ ≤ v) :
    ‖mixedWeilSummand Z g h n‖ ≤ (Z.multiplicity n : ℝ) * u * v := by
  rw [mixedWeilSummand_factorization, norm_mul, norm_mul, Complex.norm_conj]
  have hm : ‖(Z.multiplicity n : ℂ)‖ = (Z.multiplicity n : ℝ) := by simp
  rw [hm]
  have huv := mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)
  have h := mul_le_mul_of_nonneg_left huv (Nat.cast_nonneg (Z.multiplicity n))
  simpa only [mul_assoc] using h

private theorem sum_mixed_product (Z : ZeroData) (g : ι → WeilTestFunction)
    (n : ℕ) (u v : ι → ℝ)
    (hu : ∀ i, ‖fourierLaplace (g i) (Z.gamma n)‖ ≤ u i)
    (hv : ∀ i, ‖fourierLaplace (g i) (conj (Z.gamma n))‖ ≤ v i) :
    finiteMixedMajorant Z g n ≤
      (Z.multiplicity n : ℝ) * (∑ i, u i) * (∑ i, v i) := by
  unfold finiteMixedMajorant
  calc
    _ ≤ ∑ i, ∑ j, (Z.multiplicity n : ℝ) * u i * v j := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _ => mixed_norm_le Z (g i) (g j) n _ _ (hu i) (hv j)
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

/-- Every finite head term, including off-diagonal terms, has a finite bound. -/
theorem finiteMixedMajorant_head_le (Z : ZeroData) (g : ι → WeilTestFunction)
    (E : Finset ℕ) (plus minus : ι → ℕ → ℝ)
    (hplus : ∀ n ∈ E, ∀ i, ‖fourierLaplace (g i) (Z.gamma n)‖ ≤ plus i n)
    (hminus : ∀ n ∈ E, ∀ i,
      ‖fourierLaplace (g i) (conj (Z.gamma n))‖ ≤ minus i n) :
    (∑ n ∈ E, finiteMixedMajorant Z g n) ≤ finiteMixedHeadBound Z E plus minus := by
  exact Finset.sum_le_sum fun n hn =>
    sum_mixed_product Z g n (fun i => plus i n) (fun i => minus i n)
      (hplus n hn) (hminus n hn)

/-- Two conjugate-node decay bounds control all mixed terms with a single
scalar fourth moment and the explicit finite coefficient factor (sum D_i)^2. -/
theorem finiteMixedMajorant_pointwise_decay
    (Z : ZeroData) (g : ι → WeilTestFunction) (D : ι → ℝ) (n : ℕ)
    (hplus : ∀ i, ‖fourierLaplace (g i) (Z.gamma n)‖ ≤
      D i * inverseQuadraticEnvelope Z n)
    (hminus : ∀ i, ‖fourierLaplace (g i) (conj (Z.gamma n))‖ ≤
      D i * inverseQuadraticEnvelope Z n) :
    finiteMixedMajorant Z g n ≤ (∑ i, D i) ^ 2 * fourthMomentSummand Z n := by
  have h := sum_mixed_product Z g n
    (fun i => D i * inverseQuadraticEnvelope Z n)
    (fun i => D i * inverseQuadraticEnvelope Z n) hplus hminus
  simp only [← Finset.sum_mul] at h
  calc
    _ ≤ (Z.multiplicity n : ℝ) *
        ((∑ i, D i) * inverseQuadraticEnvelope Z n) *
        ((∑ i, D i) * inverseQuadraticEnvelope Z n) := h
    _ = _ := by unfold fourthMomentSummand; ring

/-- The actual infinite operator-family constant is bounded by a finite head
plus an explicitly scaled scalar spectral tail. No C-bound is a premise. -/
theorem finiteMixedMajorantTotal_le_head_tail
    (Z : ZeroData) (g : ι → WeilTestFunction) (E : Finset ℕ)
    (D : ι → ℝ) (plus minus : ι → ℕ → ℝ) (Theta : ℝ)
    (hplus : ∀ n ∈ E, ∀ i, ‖fourierLaplace (g i) (Z.gamma n)‖ ≤ plus i n)
    (hminus : ∀ n ∈ E, ∀ i,
      ‖fourierLaplace (g i) (conj (Z.gamma n))‖ ≤ minus i n)
    (hdecayPlus : ∀ n ∉ E, ∀ i, ‖fourierLaplace (g i) (Z.gamma n)‖ ≤
      D i * inverseQuadraticEnvelope Z n)
    (hdecayMinus : ∀ n ∉ E, ∀ i,
      ‖fourierLaplace (g i) (conj (Z.gamma n))‖ ≤ D i * inverseQuadraticEnvelope Z n)
    (hspectral : Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1) ≤ Theta) :
    finiteMixedMajorantTotal Z g ≤
      finiteMixedHeadBound Z E plus minus + (∑ i, D i) ^ 2 * Theta := by
  have hall := finiteMixedMajorant_summable Z g
  have hsub := hall.subtype (fun n => n ∉ E)
  have hpoint (n : {n : ℕ // n ∉ E}) :
      finiteMixedMajorant Z g n.1 ≤ (∑ i, D i) ^ 2 * fourthMomentSummand Z n.1 :=
    finiteMixedMajorant_pointwise_decay Z g D n.1
      (hdecayPlus n.1 n.2) (hdecayMinus n.1 n.2)
  have htailMixed : (∑' n : {n : ℕ // n ∉ E}, finiteMixedMajorant Z g n.1) ≤
      (∑ i, D i) ^ 2 * Theta := by
    calc
      _ ≤ ∑' n : {n : ℕ // n ∉ E}, (∑ i, D i) ^ 2 * fourthMomentSummand Z n.1 :=
        hsub.tsum_le_tsum hpoint (hspectral.mul_left _)
      _ = (∑ i, D i) ^ 2 * ∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1 := by
        rw [tsum_mul_left]
      _ ≤ _ := mul_le_mul_of_nonneg_left htail (sq_nonneg _)
  unfold finiteMixedMajorantTotal
  rw [← hall.sum_add_tsum_subtype_compl E]
  exact add_le_add (finiteMixedMajorant_head_le Z g E plus minus hplus hminus) htailMixed

/-- A reciprocal-fourth ordinate bound controls the exact envelope used above. -/
theorem fourthMomentSummand_le_inverse_fourth (Z : ZeroData) (n : ℕ)
    (hheight : (Z.gamma n).re ≠ 0) :
    fourthMomentSummand Z n ≤ (Z.multiplicity n : ℝ) / (Z.gamma n).re ^ 4 := by
  have ht : 0 < (Z.gamma n).re ^ 2 := sq_pos_of_ne_zero hheight
  have hd : (Z.gamma n).re ^ 4 ≤ (1 + (Z.gamma n).re ^ 2) ^ 2 := by nlinarith
  unfold fourthMomentSummand inverseQuadraticEnvelope
  rw [← inv_pow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hd

/-- In a radius-one support window the exponential strip cost is bounded by
three, so the two finite L1 enclosures give a rational decay coefficient. -/
theorem closedStripJetBudget_le_three_jets
    (g : WeilTestFunction) (J0 J2 : ℝ)
    (hs : tsupport (g : ℝ → ℂ) ⊆ Set.Icc (-1) 1)
    (hJ0 : (∫ x : ℝ, ‖g x‖) ≤ J0)
    (hJ2 : (∫ x : ℝ, ‖((deriv^[2]) (g : ℝ → ℂ)) x‖) ≤ J2) :
    closedStripJetBudget g (1 / 2) ≤ 3 * (J0 + J2) := by
  have hJ : 0 ≤ J0 + J2 := add_nonneg
    ((integral_nonneg fun x => norm_nonneg (g x)).trans hJ0)
    ((integral_nonneg fun x => norm_nonneg (((deriv^[2]) (g : ℝ → ℂ)) x)).trans hJ2)
  have hexp : Real.exp ((1 / 2 : ℝ) * 1) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) * 1 ≤ 1)).trans
      Real.exp_one_lt_three.le
  exact (closedStripJetBudget_le_support_jets g 1 (1 / 2) J0 J2
    (by norm_num) hs hJ0 hJ2).trans (mul_le_mul_of_nonneg_right hexp hJ)

private theorem gamma_in_half_strip (Z : ZeroData) (n : ℕ) :
    |(Z.gamma n).im| ≤ (1 / 2 : ℝ) := by
  rw [ZeroData.gamma, ← gammaOf_eq_spectralParameter]
  exact (Zeta23.WeilEF.abs_gammaOf_im_lt (Z.zero_isNontrivial n).2).le

/-- Both actual zero-node evaluations follow from the same two finite jets. -/
theorem zero_transform_pair_le_three_jets
    (Z : ZeroData) (g : WeilTestFunction) (J0 J2 : ℝ)
    (hs : tsupport (g : ℝ → ℂ) ⊆ Set.Icc (-1) 1)
    (hJ0 : (∫ x : ℝ, ‖g x‖) ≤ J0)
    (hJ2 : (∫ x : ℝ, ‖((deriv^[2]) (g : ℝ → ℂ)) x‖) ≤ J2) (n : ℕ) :
    ‖fourierLaplace g (Z.gamma n)‖ ≤
        (3 * (J0 + J2)) * inverseQuadraticEnvelope Z n ∧
      ‖fourierLaplace g (conj (Z.gamma n))‖ ≤
        (3 * (J0 + J2)) * inverseQuadraticEnvelope Z n := by
  have hbudget := closedStripJetBudget_le_three_jets g J0 J2 hs hJ0 hJ2
  have hdecay := (closedStripJetBudget_spec g (1 / 2) (by norm_num)).2
  have him := gamma_in_half_strip Z n
  have hbound (w : ℂ) (hw : |w.im| ≤ (1 / 2 : ℝ)) :
      ‖fourierLaplace g w‖ ≤ (3 * (J0 + J2)) / (1 + w.re ^ 2) :=
    (hdecay w hw).trans (div_le_div_of_nonneg_right hbudget (by positivity))
  constructor
  · simpa only [inverseQuadraticEnvelope, div_eq_mul_inv] using hbound (Z.gamma n) him
  · have himc : |(conj (Z.gamma n)).im| ≤ (1 / 2 : ℝ) := by simpa using him
    simpa only [Complex.conj_re, inverseQuadraticEnvelope, div_eq_mul_inv] using
      hbound (conj (Z.gamma n)) himc

/-- A complete majorant budget from fixed support, two finite L1 enclosures
per test, and one scalar spectral tail. No transform-decay or C-bound premise
remains. The scalar tail is the separately identified number-theoretic input. -/
theorem finiteMixedMajorantTotal_le_unit_support_jets
    (Z : ZeroData) (g : ι → WeilTestFunction) (E : Finset ℕ)
    (J0 J2 : ι → ℝ) (Theta : ℝ)
    (hs : ∀ i, tsupport (g i : ℝ → ℂ) ⊆ Set.Icc (-1) 1)
    (hJ0 : ∀ i, (∫ x : ℝ, ‖g i x‖) ≤ J0 i)
    (hJ2 : ∀ i, (∫ x : ℝ, ‖((deriv^[2]) (g i : ℝ → ℂ)) x‖) ≤ J2 i)
    (hspectral : Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1) ≤ Theta) :
    finiteMixedMajorantTotal Z g ≤
      (∑ i, 3 * (J0 i + J2 i)) ^ 2 *
        ((∑ n ∈ E, fourthMomentSummand Z n) + Theta) := by
  let D : ι → ℝ := fun i => 3 * (J0 i + J2 i)
  let V : ι → ℕ → ℝ := fun i n => D i * inverseQuadraticEnvelope Z n
  have hb (n : ℕ) (i : ι) :=
    zero_transform_pair_le_three_jets Z (g i) (J0 i) (J2 i) (hs i) (hJ0 i) (hJ2 i) n
  have hC := finiteMixedMajorantTotal_le_head_tail Z g E D V V Theta
    (fun n _ i => (hb n i).1) (fun n _ i => (hb n i).2)
    (fun n _ i => (hb n i).1) (fun n _ i => (hb n i).2) hspectral htail
  have hhead : finiteMixedHeadBound Z E V V =
      (∑ i, D i) ^ 2 * ∑ n ∈ E, fourthMomentSummand Z n := by
    unfold finiteMixedHeadBound
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [V]
    simp only [← Finset.sum_mul]
    unfold fourthMomentSummand
    ring
  rw [hhead] at hC
  dsimp only [D] at hC
  nlinarith [hC]

#print axioms closedStripJetBudget_le_three_jets
#print axioms zero_transform_pair_le_three_jets
#print axioms finiteMixedMajorantTotal_le_unit_support_jets
#print axioms finiteMixedMajorant_head_le
#print axioms finiteMixedMajorant_pointwise_decay
#print axioms finiteMixedMajorantTotal_le_head_tail
#print axioms fourthMomentSummand_le_inverse_fourth

end D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
