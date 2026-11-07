/- GID: D5/S3/VertexAlgebra/Analysis/SmoothCircleContact
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/SmoothCircleContact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth circle binomial derivatives and Banach-valued finite contact expansion. -/

import D5.S3.VertexAlgebra.Analysis.IntegerNewton
import D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Fourier reconstruction, integration, differentiation, binomial coefficients,
and unconditional sum rearrangements are Mathlib suppliers, Apache 2.0. This
module adds a pointwise PRODUCT coefficient formula, not circle convolution.
The Banach coefficient family below is independent of any lattice model.

proof_shape: delta_smooth_contact_formula: content
admission_basis: escape-witness
escape_witness: The integer recurrence reconstructs the coefficients, ordinary
derivatives realize their binomial Fourier multipliers, and absolute double
majorants justify each contact-series reindexing before support vanishing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open Complex MeasureTheory Set Finset Function AddCircle

namespace D5.S3.VertexAlgebra.Analysis
open IntegerNewton
open D5.S3.VertexAlgebra.FieldNormalProductLocality (delta)

private theorem continuousCircle_integrable {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) : Integrable F haarAddCircle :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

namespace SmoothCircleFourier.Test

/-- The original periodic lift, bundled in the uniform norm on the quotient circle. -/
def circle (f : Test) : C(AddCircle period, ℂ) :=
  ⟨f.periodic.lift, f.smooth.continuous.quotient_liftOn' _⟩

def scale (c : ℂ) (f : Test) : Test where
  lift x := c * f.lift x
  smooth := contDiff_const.mul f.smooth
  periodic x := congrArg (c * ·) (f.periodic x)

def subtract (f g : Test) : Test where
  lift x := f.lift x - g.lift x
  smooth := f.smooth.sub g.smooth
  periodic x := by dsimp only; rw [f.periodic x, g.periodic x]

/-- Ordinary pointwise multiplication of the existing smooth tests. -/
def product (f g : Test) : Test where
  lift x := f.lift x * g.lift x
  smooth := f.smooth.mul g.smooth
  periodic x := by dsimp only; rw [f.periodic x, g.periodic x]

def derivative (f : Test) : Test where
  lift := deriv f.lift
  smooth := (contDiff_infty_iff_deriv.mp f.smooth).2
  periodic := by simpa only [jet, iteratedDeriv_one] using jet_periodic f 1

/-- D = -i d/dθ with the Fourier sign of the original smearing. -/
def frequencyDerivative (f : Test) : Test := scale (-Complex.I) f.derivative

/-- P_j = binom(D,j), defined as a finite differential operator on the ACTUAL test. -/
def frequencyBinomial (f : Test) : ℕ → Test
  | 0 => f
  | j+1 => scale ((j+1 : ℂ)⁻¹)
      ((f.frequencyBinomial j).frequencyDerivative.subtract
        (scale (j : ℂ) (f.frequencyBinomial j)))

private theorem coefficient_circle_map (f : Test) (m : ℤ) :
    f.coefficient m = fourierCoeff f.circle m := coefficient_circle f m

private theorem circle_scale (c : ℂ) (f : Test) :
    (scale c f).circle = c • f.circle := by
  ext x
  induction x using Quotient.inductionOn with
  | h x => simp [circle, scale, Function.Periodic.lift_coe]

private theorem circle_subtract (f g : Test) :
    (f.subtract g).circle = f.circle - g.circle := by
  ext x
  induction x using Quotient.inductionOn with
  | h x => simp [circle, subtract, Function.Periodic.lift_coe]

private theorem circle_product (f g : Test) :
    (f.product g).circle = f.circle * g.circle := by
  ext x
  induction x using Quotient.inductionOn with
  | h x => simp [circle, product, Function.Periodic.lift_coe]

private theorem coefficient_scale (c : ℂ) (f : Test) (m : ℤ) :
    (scale c f).coefficient m = c * f.coefficient m := by
  rw [coefficient_circle_map, coefficient_circle_map]
  change fourierCoeff (scale c f).circle m = c * fourierCoeff f.circle m
  rw [circle_scale]
  exact fourierCoeff.const_smul f.circle c m

private theorem coefficient_subtract (f g : Test) (m : ℤ) :
    (f.subtract g).coefficient m = f.coefficient m - g.coefficient m := by
  rw [coefficient_circle_map, coefficient_circle_map, coefficient_circle_map]
  change fourierCoeff (f.subtract g).circle m =
    fourierCoeff f.circle m - fourierCoeff g.circle m
  rw [circle_subtract]
  simp only [fourierCoeff, ContinuousMap.sub_apply, smul_sub]
  exact integral_sub ((continuousCircle_integrable f.circle).fourier_smul _)
    ((continuousCircle_integrable g.circle).fourier_smul _)

/-- The zero frequency is proved by FTC and periodicity, without dividing by m. -/
private theorem coefficient_derivative_zero (f : Test) :
    f.derivative.coefficient 0 = 0 := by
  have hf : Differentiable ℝ f.lift := f.smooth.differentiable (by simp)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := period) (fun x _ => (hf x).hasDerivAt)
    (f.derivative.smooth.continuous.intervalIntegrable 0 period)
  have hend : f.lift period = f.lift 0 := by simpa using f.periodic 0
  rw [hend, sub_self] at hint
  simp only [coefficient, coeffJet, jet, iteratedDeriv_zero,
    fourierCoeffOn_eq_integral, neg_zero, fourier_zero, one_smul, derivative]
  rw [hint, smul_zero]

/-- Differentiation multiplies by i*m at EVERY integer, including zero. -/
private theorem coefficient_derivative (f : Test) (m : ℤ) :
    f.derivative.coefficient m = (Complex.I * (m : ℂ)) * f.coefficient m := by
  by_cases hm : m = 0
  · subst m
    simp [coefficient_derivative_zero]
  · have h := coeffJet_step f 0 m hm
    have hn : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hd : f.coeffJet 1 m = f.derivative.coefficient m := by
      simp only [coeffJet, coefficient, jet, iteratedDeriv_zero, iteratedDeriv_one,
        derivative]
    rw [show f.coeffJet 0 m = f.coefficient m from rfl, hd] at h
    rw [h]
    field_simp [hn, Complex.I_ne_zero]

private theorem coefficient_frequencyDerivative (f : Test) (m : ℤ) :
    f.frequencyDerivative.coefficient m = (m : ℂ) * f.coefficient m := by
  rw [frequencyDerivative, coefficient_scale, coefficient_derivative]
  ring_nf
  simp [Complex.I_sq]

private theorem complex_choose_step (m : ℤ) (j : ℕ) :
    ((Ring.choose m (j+1) : ℤ) : ℂ) =
      (j+1 : ℂ)⁻¹ * ((m : ℂ)-j) * ((Ring.choose m j : ℤ) : ℂ) := by
  have hj : (j+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hc (k : ℕ) : ((Ring.choose m k : ℤ) : ℂ) = Ring.choose (m : ℂ) k :=
    Ring.map_choose (Int.castRingHom ℂ) m k
  rw [hc, hc]
  calc
    _ = ((j+1 : ℂ)⁻¹ * (j+1)) * Ring.choose (m : ℂ) (j+1) := by
      rw [inv_mul_cancel₀ hj, one_mul]
    _ = (j+1 : ℂ)⁻¹ * (((m : ℂ)-j) * Ring.choose (m : ℂ) j) := by
      rw [mul_assoc, choose_succ_mul]
    _ = _ := by ring

/-- The generalized integer binomial is the multiplier, without truncating m to ℕ. -/
theorem coefficient_frequencyBinomial (f : Test) (j : ℕ) (m : ℤ) :
    (f.frequencyBinomial j).coefficient m =
      ((Ring.choose m j : ℤ) : ℂ) * f.coefficient m := by
  induction j with
  | zero => simp [frequencyBinomial, Ring.choose_zero_right]
  | succ j ih =>
    simp only [frequencyBinomial, coefficient_scale, coefficient_subtract,
      coefficient_frequencyDerivative, ih, complex_choose_step]
    ring

/-- Every finite differential operator P_j preserves a neighborhood of zero. -/
private theorem frequencyBinomial_eventually_zero (f : Test) (j : ℕ) (x : ℝ)
    (hf : f.lift =ᶠ[𝓝 x] 0) :
    (f.frequencyBinomial j).lift =ᶠ[𝓝 x] 0 := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    have hd := ih.deriv
    filter_upwards [ih, hd] with y hy hdy
    simp only [Pi.zero_apply, deriv_const] at hy hdy
    simp [frequencyBinomial, scale, subtract, frequencyDerivative, derivative, hy, hdy]

/-- Pull back a zero neighborhood from the quotient circle before differentiating. -/
private theorem frequencyBinomial_zero_off_support (f : Test) (j : ℕ) (x : ℝ)
    (hx : (x : AddCircle period) ∉ tsupport f.periodic.lift) :
    (f.frequencyBinomial j).lift x = 0 := by
  have hcircle : f.periodic.lift =ᶠ[𝓝 (x : AddCircle period)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hreal : f.lift =ᶠ[𝓝 x] 0 := by
    have hh := hcircle.comp_tendsto (AddCircle.continuous_mk' period).continuousAt
    change (fun y : ℝ => f.periodic.lift (y : AddCircle period)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℂ)) at hh
    filter_upwards [hh] with y hy
    exact hy
  exact (frequencyBinomial_eventually_zero f j x hreal).eq_of_nhds

/-- Stronger than separated supports: a pointwise zero product suffices. -/
theorem frequencyBinomial_product_zero (f g : Test)
    (hfg : ∀ x : ℝ, f.lift x * g.lift x = 0) (j : ℕ) :
    ∀ x : ℝ, ((f.frequencyBinomial j).product g).lift x = 0 := by
  intro x
  by_cases hg : g.lift x = 0
  · simp [product, hg]
  · have hgcircle : g.circle (x : AddCircle period) ≠ 0 := by
      simpa only [circle, ContinuousMap.coe_mk, Function.Periodic.lift_coe] using hg
    have hgnear : ∀ᶠ y in 𝓝 (x : AddCircle period), g.circle y ≠ 0 :=
      g.circle.continuous.continuousAt.eventually_ne hgcircle
    have hfgcircle (y : AddCircle period) : f.circle y * g.circle y = 0 := by
      induction y using Quotient.inductionOn with
      | h y => simpa only [circle, ContinuousMap.coe_mk, Function.Periodic.lift_coe] using hfg y
    have hfnear : f.periodic.lift =ᶠ[𝓝 (x : AddCircle period)] 0 := by
      filter_upwards [hgnear] with y hy
      exact (mul_eq_zero.mp (hfgcircle y)).resolve_right hy
    have hz := frequencyBinomial_zero_off_support f j x
      (notMem_tsupport_iff_eventuallyEq.mpr hfnear)
    simp [product, hz]

/-- Closed supports are on the quotient circle, so there is no seam condition. -/
theorem product_zero_of_disjoint_tsupport (f g : Test)
    (h : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)) :
    ∀ x : ℝ, f.lift x * g.lift x = 0 := by
  intro x
  by_cases hf : f.lift x = 0
  · simp [hf]
  by_cases hg : g.lift x = 0
  · simp [hg]
  have hfx : (x : AddCircle period) ∈ tsupport f.periodic.lift :=
    subset_closure (by simpa only [Function.mem_support, Function.Periodic.lift_coe] using hf)
  have hgx : (x : AddCircle period) ∈ tsupport g.periodic.lift :=
    subset_closure (by simpa only [Function.mem_support, Function.Periodic.lift_coe] using hg)
  exact False.elim (Set.disjoint_left.mp h hfx hgx)

end SmoothCircleFourier.Test

section FourierProduct
variable {T : ℝ} [Fact (0 < T)]

/-- For fixed G,t this is the bounded coefficient functional of the POINTWISE product. -/
private def productCoefficientLinear (G : C(AddCircle T, ℂ)) (t : ℤ) :
    C(AddCircle T, ℂ) →ₗ[ℂ] ℂ where
  toFun F := fourierCoeff (F*G) t
  map_add' F H := by
    simp only [fourierCoeff, ContinuousMap.mul_apply, ContinuousMap.add_apply,
      add_mul, smul_add]
    exact integral_add ((continuousCircle_integrable (F*G)).fourier_smul _)
      ((continuousCircle_integrable (H*G)).fourier_smul _)
  map_smul' c F := by
    simp only [fourierCoeff, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x : AddCircle T,
      fourier (-t) x * (c * F x * G x) = c * (fourier (-t) x * (F x * G x)) by
        intro x; ring]
    exact integral_const_mul c _

private def productCoefficientCLM (G : C(AddCircle T, ℂ)) (t : ℤ) :
    C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  (productCoefficientLinear G t).mkContinuous ‖G‖ (by
    intro F
    change ‖∫ x : AddCircle T, fourier (-t) x • (F x * G x) ∂haarAddCircle‖ ≤ ‖G‖ * ‖F‖
    have hbound : ∀ᵐ x : AddCircle T ∂haarAddCircle,
        ‖fourier (-t) x • (F x * G x)‖ ≤ ‖F‖ * ‖G‖ := by
      filter_upwards [] with x
      simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul, norm_mul]
      exact mul_le_mul (F.norm_coe_le_norm x) (G.norm_coe_le_norm x)
        (norm_nonneg _) (norm_nonneg _)
    simpa [measureReal_def, mul_comm] using
      MeasureTheory.norm_integral_le_of_norm_le_const hbound)

private theorem productCoefficientCLM_fourier (G : C(AddCircle T, ℂ)) (t m : ℤ) :
    productCoefficientCLM G t (fourier m) = fourierCoeff G (t-m) := by
  change (∫ x : AddCircle T, fourier (-t) x • (fourier m x * G x) ∂haarAddCircle) =
    ∫ x : AddCircle T, fourier (-(t-m)) x • G x ∂haarAddCircle
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← fourier_add, show -t+m = -(t-m) by ring]

/-- Uniform Fourier reconstruction, followed by a continuous coefficient
functional, proves the product formula and absolute convergence. -/
theorem fourierCoeff_mul_hasSum (F G : C(AddCircle T, ℂ))
    (hF : Summable (fun m : ℤ => ‖fourierCoeff F m‖)) (t : ℤ) :
    HasSum (fun m : ℤ => fourierCoeff F m * fourierCoeff G (t-m))
      (fourierCoeff (F*G) t) ∧
    Summable (fun m : ℤ => ‖fourierCoeff F m * fourierCoeff G (t-m)‖) := by
  have h := (productCoefficientCLM G t).hasSum
    (hasSum_fourier_series_of_summable hF.of_norm)
  have hsum : HasSum (fun m : ℤ => fourierCoeff F m * fourierCoeff G (t-m))
      (fourierCoeff (F*G) t) := by
    simp only [map_smul, productCoefficientCLM_fourier, smul_eq_mul] at h
    simpa only [productCoefficientCLM, LinearMap.mkContinuous_apply,
      productCoefficientLinear, LinearMap.coe_mk, AddHom.coe_mk] using h
  have habs : Summable (fun m : ℤ => ‖fourierCoeff F m * fourierCoeff G (t-m)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (hF.mul_right ‖productCoefficientCLM G t‖)
    intro m
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← productCoefficientCLM_fourier G t m]
    simpa only [fourier_norm, mul_one] using
      (productCoefficientCLM G t).le_opNorm (fourier m)
  exact ⟨hsum, habs⟩

end FourierProduct

namespace SmoothCircleFourier.Test

private theorem coefficient_product_hasSum (f g : Test) (t : ℤ) :
    HasSum (fun m : ℤ => f.coefficient m * g.coefficient (t-m))
      ((f.product g).coefficient t) ∧
    Summable (fun m : ℤ => ‖f.coefficient m * g.coefficient (t-m)‖) := by
  have hf : Summable (fun m : ℤ => ‖fourierCoeff f.circle m‖) := by
    simpa only [weight, pow_zero, mul_one, coefficient_circle_map] using
      (show Summable (fun m : ℤ => f.weight 0 m) from f.weighted_summable 0)
  have h := fourierCoeff_mul_hasSum f.circle g.circle hf t
  simpa only [← circle_product, ← coefficient_circle_map] using h

private theorem binomial_product_hasSum (f g : Test) (j : ℕ) (t : ℤ) :
    HasSum (fun m : ℤ =>
      (((Ring.choose m j : ℤ) : ℂ) * f.coefficient m) * g.coefficient (t-m))
      (((f.frequencyBinomial j).product g).coefficient t) ∧
    Summable (fun m : ℤ =>
      ‖(((Ring.choose m j : ℤ) : ℂ) * f.coefficient m) * g.coefficient (t-m)‖) := by
  simpa only [coefficient_frequencyBinomial] using
    coefficient_product_hasSum (f.frequencyBinomial j) g t

end SmoothCircleFourier.Test

namespace FiniteDeltaContact
open SmoothCircleFourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem one_abs_add (m n : ℤ) :
    1+|((m+n : ℤ) : ℝ)| ≤ (1+|(m : ℝ)|)*(1+|(n : ℝ)|) := by
  simp only [Int.cast_add]
  have h := abs_add_le (m : ℝ) (n : ℝ)
  nlinarith [mul_nonneg (abs_nonneg (m : ℝ)) (abs_nonneg (n : ℝ))]

private theorem one_abs_sub (t i : ℤ) :
    1+|((t-i : ℤ) : ℝ)| ≤ (1+|(t : ℝ)|)*(1+|(i : ℝ)|) := by
  simpa only [sub_eq_add_neg, Int.cast_neg, abs_neg] using one_abs_add t (-i)

/-- An explicit finite constant; retaining the finite sum avoids an unnecessary
evaluation of the binomial sum. It is independent of the frequency t. -/
private def contactConstant (K : ℝ) (R j : ℕ) : ℝ :=
  ∑ i ∈ range (j+1),
    ‖(((-1 : ℤ)^(j-i) * (j.choose i : ℤ)) : ℂ)‖ * K *
      (1+|(i : ℝ)|)^R * (1+|(i : ℝ)|)^R

private theorem contactConstant_nonneg {K : ℝ} (hK : 0 ≤ K) (R j : ℕ) :
    0 ≤ contactConstant K R j := by
  apply sum_nonneg
  intro i hi
  positivity

private theorem contactCoefficient_bound (C : ℤ → ℤ → E) (K : ℝ) (R : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (j : ℕ) (t : ℤ) :
    ‖contactCoefficient C j t‖ ≤ contactConstant K R j * (1+|(t : ℝ)|)^R := by
  classical
  rw [contactCoefficient]
  calc
    _ ≤ ∑ i ∈ range (j+1),
        ‖(((-1 : ℤ)^(j-i) * (j.choose i : ℤ)) • C i (t-i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ range (j+1),
        (‖(((-1 : ℤ)^(j-i) * (j.choose i : ℤ)) : ℂ)‖ * K *
          (1+|(i : ℝ)|)^R * (1+|(i : ℝ)|)^R) * (1+|(t : ℝ)|)^R := by
      apply sum_le_sum
      intro i hi
      rw [← Int.cast_smul_eq_zsmul ℂ, norm_smul]
      simp only [Int.cast_mul, Int.cast_pow]
      have hshift : (1+|((t-(i : ℤ) : ℤ) : ℝ)|)^R ≤
          (1+|(t : ℝ)|)^R * (1+|(i : ℝ)|)^R := by
        simpa only [mul_pow, Int.cast_natCast] using
          pow_le_pow_left₀ (by positivity) (one_abs_sub t i) R
      have hc := hC i (t-i)
      simp only [Int.cast_natCast] at hc
      have hci : ‖C i (t-i)‖ ≤ K * (1+|(i : ℝ)|)^R *
          ((1+|(t : ℝ)|)^R * (1+|(i : ℝ)|)^R) :=
        hc.trans (mul_le_mul_of_nonneg_left hshift (by positivity))
      calc
        _ ≤ ‖(((-1 : ℤ)^(j-i) * (j.choose i : ℤ)) : ℂ)‖ *
            (K * (1+|(i : ℝ)|)^R *
              ((1+|(t : ℝ)|)^R * (1+|(i : ℝ)|)^R)) :=
          mul_le_mul_of_nonneg_left hci (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [← sum_mul]; rfl

private theorem weight_product_summable (f g : Test) (p q : ℕ) (L : ℝ) :
    Summable (fun mn : ℤ × ℤ => L * f.weight p mn.1 * g.weight q mn.2) := by
  have h := (f.weighted_summable p).mul_of_nonneg (g.weighted_summable q)
    (f.weight_nonneg p) (g.weight_nonneg q)
  simpa only [mul_assoc] using h.mul_left L

/-- Absolute norm convergence is available before any double-smear rearrangement. -/
theorem double_smear_absolute (C : ℤ → ℤ → E) (K : ℝ) (R : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (f g : Test) :
    Summable (fun mn : ℤ × ℤ =>
      ‖(f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun mn => ?_) (weight_product_summable f g R R K)
  rw [norm_smul, norm_mul]
  calc
    _ ≤ (‖f.coefficient mn.1‖ * ‖g.coefficient mn.2‖) *
        (K*(1+|(mn.1 : ℝ)|)^R*(1+|(mn.2 : ℝ)|)^R) :=
      mul_le_mul_of_nonneg_left (hC mn.1 mn.2) (by positivity)
    _ = _ := by dsimp [Test.weight]; ring

private def newtonTerm (C : ℤ → ℤ → E) (f g : Test) (j : ℕ) (mn : ℤ × ℤ) : E :=
  ((f.coefficient mn.1 * g.coefficient mn.2) *
    ((Ring.choose mn.1 j : ℤ) : ℂ)) • contactCoefficient C j (mn.1+mn.2)

private theorem newtonTerm_bound (C : ℤ → ℤ → E) (K : ℝ) (R : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (f g : Test) (j : ℕ) (mn : ℤ × ℤ) :
    ‖newtonTerm C f g j mn‖ ≤
      contactConstant K R j * f.weight (R+j) mn.1 * g.weight R mn.2 := by
  have hL := contactConstant_nonneg hK R j
  have hsum : (1+|((mn.1+mn.2 : ℤ) : ℝ)|)^R ≤
      ((1+|(mn.1 : ℝ)|)*(1+|(mn.2 : ℝ)|))^R :=
    pow_le_pow_left₀ (by positivity) (one_abs_add mn.1 mn.2) R
  have hcontact : ‖contactCoefficient C j (mn.1+mn.2)‖ ≤
      contactConstant K R j * ((1+|(mn.1 : ℝ)|)*(1+|(mn.2 : ℝ)|))^R :=
    (contactCoefficient_bound C K R hK hC j _).trans
      (mul_le_mul_of_nonneg_left hsum hL)
  calc
    _ = (‖f.coefficient mn.1‖ * ‖g.coefficient mn.2‖) *
        (‖((Ring.choose mn.1 j : ℤ) : ℂ)‖ *
          ‖contactCoefficient C j (mn.1+mn.2)‖) := by
      simp only [newtonTerm, norm_smul, norm_mul]
      ring
    _ ≤ (‖f.coefficient mn.1‖ * ‖g.coefficient mn.2‖) *
        ((1+|(mn.1 : ℝ)|)^j * (contactConstant K R j *
          ((1+|(mn.1 : ℝ)|)*(1+|(mn.2 : ℝ)|))^R)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (norm_int_choose_le_pow mn.1 j) hcontact
        (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [Test.weight]; rw [pow_add, mul_pow]; ring

private theorem newtonTerm_absolute (C : ℤ → ℤ → E) (K : ℝ) (R : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (f g : Test) (j : ℕ) :
    Summable (fun mn : ℤ × ℤ => ‖newtonTerm C f g j mn‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (newtonTerm_bound C K R hK hC f g j)
    (weight_product_summable f g (R+j) R (contactConstant K R j))

/-- New coordinates (t,m) correspond to old coordinates (m,t-m). -/
private def sumCoordinates : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun tm := (tm.2, tm.1-tm.2)
  invFun mn := (mn.1+mn.2, mn.1)
  left_inv tm := by ext <;> simp
  right_inv mn := by ext <;> simp

private theorem contact_row_hasSum (C : ℤ → ℤ → E) (f g : Test) (j : ℕ) (t : ℤ) :
    HasSum (fun m : ℤ => newtonTerm C f g j (sumCoordinates (t,m)))
      ((((f.frequencyBinomial j).product g).coefficient t) • contactCoefficient C j t) := by
  have h := (Test.binomial_product_hasSum f g j t).1.smul_const
    (contactCoefficient C j t)
  convert h using 1
  funext m
  change ((f.coefficient m * g.coefficient (t-m)) *
      ((Ring.choose m j : ℤ) : ℂ)) • contactCoefficient C j (m+(t-m)) =
    (((Ring.choose m j : ℤ) : ℂ) * f.coefficient m * g.coefficient (t-m)) •
      contactCoefficient C j t
  rw [show m+(t-m) = t by omega]
  congr 1
  ring

/-- Each outer contact series is absolutely norm convergent. This is established
from the reindexed double majorant, before evaluating its iterated sum. -/
theorem contact_series_absolute (C : ℤ → ℤ → E) (K : ℝ) (R : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (f g : Test) (j : ℕ) :
    Summable (fun t : ℤ =>
      ‖(((f.frequencyBinomial j).product g).coefficient t) • contactCoefficient C j t‖) := by
  have ha := newtonTerm_absolute C K R hK hC f g j
  have hr : Summable (fun tm : ℤ × ℤ =>
      ‖newtonTerm C f g j (sumCoordinates tm)‖) :=
    sumCoordinates.summable_iff.mpr ha
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hr.prod
  intro t
  rw [← (contact_row_hasSum C f g j t).tsum_eq]
  exact norm_tsum_le_tsum_norm (hr.prod_factor t)

/-- Finite delta contact formula in an arbitrary complex Banach space.

The hypotheses concern the ORIGINAL coefficients C, not a smeared locality
conclusion. All modes are integer, and N = 0 has an empty contact sum. The two
absolute convergence statements are part of the conclusion. -/
theorem delta_smooth_contact_formula (C : ℤ → ℤ → E) (K : ℝ) (R N : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (hdelta : delta^[N] C = 0) (f g : Test) :
    Summable (fun mn : ℤ × ℤ =>
      ‖(f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2‖) ∧
    (∀ j : ℕ, Summable (fun t : ℤ =>
      ‖(((f.frequencyBinomial j).product g).coefficient t) • contactCoefficient C j t‖)) ∧
    (∑' mn : ℤ × ℤ, (f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2) =
      ∑ j ∈ range N, ∑' t : ℤ,
        (((f.frequencyBinomial j).product g).coefficient t) • contactCoefficient C j t := by
  classical
  have habs := double_smear_absolute C K R hK hC f g
  have hterm (j : ℕ) := newtonTerm_absolute C K R hK hC f g j
  have hout := contact_series_absolute C K R hK hC f g
  refine ⟨habs, hout, ?_⟩
  have hpoint (mn : ℤ × ℤ) :
      (f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2 =
        ∑ j ∈ range N, newtonTerm C f g j mn := by
    rw [delta_newton C N hdelta mn.1 mn.2, smul_sum]
    apply sum_congr rfl
    intro j hj
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    rfl
  calc
    _ = ∑' mn : ℤ × ℤ, ∑ j ∈ range N, newtonTerm C f g j mn :=
      tsum_congr hpoint
    _ = ∑ j ∈ range N, ∑' mn : ℤ × ℤ, newtonTerm C f g j mn :=
      Summable.tsum_finsetSum (fun j _ => (hterm j).of_norm)
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hrabs : Summable (fun tm : ℤ × ℤ =>
          ‖newtonTerm C f g j (sumCoordinates tm)‖) :=
        sumCoordinates.summable_iff.mpr (hterm j)
      have hr := hrabs.of_norm
      calc
        _ = ∑' tm : ℤ × ℤ, newtonTerm C f g j (sumCoordinates tm) :=
          (sumCoordinates.tsum_eq _).symm
        _ = ∑' t : ℤ, ∑' m : ℤ, newtonTerm C f g j (sumCoordinates (t,m)) :=
          hr.tsum_prod
        _ = _ := tsum_congr (fun t => (contact_row_hasSum C f g j t).tsum_eq)

/-- A pointwise zero product is enough; no closure or domain commutation premise
is hidden in this generic Banach coefficient theorem. -/
theorem double_smear_eq_zero_of_product_zero (C : ℤ → ℤ → E) (K : ℝ) (R N : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (hdelta : delta^[N] C = 0) (f g : Test)
    (hfg : ∀ x : ℝ, f.lift x * g.lift x = 0) :
    (∑' mn : ℤ × ℤ, (f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2) = 0 := by
  rw [(delta_smooth_contact_formula C K R N hK hC hdelta f g).2.2]
  apply sum_eq_zero
  intro j hj
  have hz : ((f.frequencyBinomial j).product g).lift = 0 :=
    funext (Test.frequencyBinomial_product_zero f g hfg j)
  have hc (t : ℤ) : ((f.frequencyBinomial j).product g).coefficient t = 0 := by
    simp [Test.coefficient, Test.coeffJet, Test.jet, hz, fourierCoeffOn_eq_integral]
  simp only [hc, zero_smul, tsum_zero]

/-- Closed quotient-circle supports imply the same zero double smear. -/
theorem double_smear_eq_zero_of_disjoint_tsupport
    (C : ℤ → ℤ → E) (K : ℝ) (R N : ℕ) (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (hdelta : delta^[N] C = 0) (f g : Test)
    (hfg : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)) :
    (∑' mn : ℤ × ℤ, (f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2) = 0 :=
  double_smear_eq_zero_of_product_zero C K R N hK hC hdelta f g
    (Test.product_zero_of_disjoint_tsupport f g hfg)

end FiniteDeltaContact

end D5.S3.VertexAlgebra.Analysis
