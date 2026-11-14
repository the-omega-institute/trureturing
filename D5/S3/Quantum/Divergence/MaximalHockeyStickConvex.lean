/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickConvex
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickConvex
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Actual general-convex finite reverse-test costs and maximal hockey equality. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticEquality
import D5.S3.Analytic.Convexity.CurvaturePerspectiveEndpoints
import D5.S3.Quantum.Divergence.MaximalHockeyStickOperational

/-! Arbitrary traces and the full closed perspective, including infinite endpoints. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ENNReal
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
open D5.S3.Quantum.Divergence.MaximalHockeyStickOriginalPair
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticCanonical
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticEquality
open D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickOperational

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickConvex

variable {n : Type*} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}

private def one : Positive := ⟨1, by norm_num⟩

/-- The finite affine contribution for the original, arbitrary traces. -/
def affineMass (f : ℝ → ℝ) (A B : Matrix n n ℂ) : ℝ :=
  f 1 * B.trace.re + rightDeriv f 1 * (A.trace.re - B.trace.re)

/-- One nonnegative scalar hinge, with the atom at one in the negative branch. -/
def hinge (u v : ℝ) (t : Positive) : ℝ :=
  if t ≤ one then max ((t : ℝ) * v - u) 0 else max (u - (t : ℝ) * v) 0

/-- Actual negative or positive hockey cost of a finite reverse test. -/
def testKernel {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)
    (t : Positive) : ℝ := ∑ i, hinge (R.p i) (R.q i) t

/-- Actual overlap optimization in the two scalar orientations. -/
def maximalKernel (A B : Matrix n n ℂ) (t : Positive) : ℝ :=
  if t ≤ one then (t : ℝ) * B.trace.re - overlapValue A ((t : ℝ) • B)
  else maximalHockey A B t

/-- The sum of actual closed-perspective costs, over the given finite alphabet. -/
def finiteCost (hf : ConvexOn ℝ (Ioi 0) f) {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : EReal :=
  ∑ i, closedPerspective hf (R.p i) (R.q i)

/-- Infimum over all finite alphabets and actual reverse preparations. -/
def maximalValue (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ) : EReal :=
  sInf {z : EReal | ∃ k : ℕ, ∃ R : ReverseTest A B k, z = finiteCost hf R}

/-- Curvature integral of actual maximal hockey costs, plus the finite affine mass. -/
def hockeyValue (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ) : EReal :=
  (affineMass f A B : EReal) +
    (∫⁻ t, ENNReal.ofReal (maximalKernel A B t) ∂curvature hf : ℝ≥0∞)

/-- Each branch of the integrated kernel is the infimum of the original
classical profile over all actual finite reverse tests. -/
theorem maximal_kernel_eq_operational (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : Positive) :
    maximalKernel A B t = if t ≤ one then operationalNegativeHockey A B t
      else operationalHockey A B t := by
  unfold maximalKernel
  rw [operational_negative_hockey_eq A B hA hB t t.2,
    operational_hockey_eq A B hA hB t t.2]

/-- The integrated value is exactly the curvature integral of the actual
finite operational infima, with its original affine mass and endpoint scope. -/
theorem hockey_value_eq_operational (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hockeyValue hf A B = (affineMass f A B : EReal) +
      (∫⁻ t, ENNReal.ofReal (if t ≤ one then operationalNegativeHockey A B t
        else operationalHockey A B t) ∂curvature hf : ℝ≥0∞) := by
  unfold hockeyValue
  simp_rw [maximal_kernel_eq_operational A B hA hB]

private theorem hinge_measurable (u v : ℝ) : Measurable (hinge u v) := by
  exact Measurable.ite measurableSet_Iic
    ((measurable_subtype_coe.mul_const v).sub_const u |>.max measurable_const)
    ((measurable_const.sub (measurable_subtype_coe.mul_const v)).max measurable_const)

private theorem hinge_nonneg (u v : ℝ) (t : Positive) : 0 ≤ hinge u v t := by
  unfold hinge
  split <;> exact le_max_right _ _

private theorem test_kernel_measurable {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : Measurable (testKernel R) :=
  Finset.measurable_sum _ (fun i _ => hinge_measurable (R.p i) (R.q i))

private theorem test_kernel_eq {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : Positive) :
    testKernel R t = if t ≤ one then R.hockey t - A.trace.re + (t : ℝ) * B.trace.re
      else R.hockey t := by
  unfold testKernel hinge
  split_ifs with ht
  · rw [ReverseTest.hockey, left_mass R, right_mass R, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h : max ((t : ℝ) * R.q i - R.p i) 0 =
        max (R.p i - (t : ℝ) * R.q i) 0 - R.p i + (t : ℝ) * R.q i := by
      rcases le_total (R.p i) ((t : ℝ) * R.q i) with h | h
      · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
        ring
      · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
        ring
    exact h
  · rfl

private theorem kernel_gap {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : Positive) :
    testKernel R t = maximalKernel A B t + gap R t := by
  rw [test_kernel_eq]
  unfold maximalKernel gap maximalHockey
  split_ifs <;> ring

private theorem maximal_kernel_nonneg (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : Positive) :
    0 ≤ maximalKernel A B t := by
  unfold maximalKernel
  split_ifs
  · obtain ⟨X, hX, he⟩ := overlap_attained A ((t : ℝ) • B) hA (hB.smul t.2.le)
    have htr := (Complex.nonneg_iff.mp (Matrix.le_iff.mp hX.2.2).trace_nonneg).1
    rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul, Complex.real_smul] at htr
    simpa only [← he, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using htr
  · exact maximal_hockey_nonneg hA hB t.2.le

private theorem maximal_kernel_measurable (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : Measurable (maximalKernel A B) := by
  obtain ⟨R, -, -⟩ := quadratic_reverse_test_attained_profile A B hA hB
  convert (test_kernel_measurable R).sub
    (actual_gap_profile_data R hA hB).2.continuous.measurable using 1
  funext t
  change maximalKernel A B t = testKernel R t - gap R t
  rw [kernel_gap]
  ring

private theorem remainder_eq_hinge (hf : ConvexOn ℝ (Ioi 0) f) (u v : ℝ) :
    curvatureRemainder hf u v = ∫⁻ t, ENNReal.ofReal (hinge u v t) ∂curvature hf := by
  change (∫⁻ t in Iic one, ENNReal.ofReal ((t : ℝ) * v - u) ∂curvature hf) +
      (∫⁻ t in Ioi one, ENNReal.ofReal (u - (t : ℝ) * v) ∂curvature hf) = _
  symm
  have he : (fun t => ENNReal.ofReal (hinge u v t)) =
      (Iic one).piecewise (fun t : Positive => ENNReal.ofReal ((t : ℝ) * v - u))
        (fun t : Positive => ENNReal.ofReal (u - (t : ℝ) * v)) := by
    funext t
    by_cases ht : t ≤ one <;> simp [hinge, Set.piecewise, ht]
  rw [he, lintegral_piecewise (s := Iic one) measurableSet_Iic.nullMeasurableSet, compl_Iic]

private theorem finite_cost_decomposition (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    finiteCost hf R = (affineMass f A B : EReal) +
      (∫⁻ t, ENNReal.ofReal (testKernel R t) ∂curvature hf : ℝ≥0∞) := by
  have hsum (s : Finset (Fin k)) :
      (∑ i ∈ s, closedPerspective hf (R.p i) (R.q i)) =
      ((∑ i ∈ s, (f 1 * R.q i + rightDeriv f 1 * (R.p i - R.q i)) : ℝ) : EReal) +
      ((∑ i ∈ s, curvatureRemainder hf (R.p i) (R.q i) : ℝ≥0∞) : EReal) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [closedPerspective_eq_affine_add_curvature hf (R.p_nonneg i) (R.q_nonneg i),
        ih, EReal.coe_add, EReal.coe_ennreal_add]
      ac_rfl
  have ha : (∑ i, (f 1 * R.q i + rightDeriv f 1 * (R.p i - R.q i))) =
      affineMass f A B := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← left_mass R, ← right_mass R]
    rfl
  rw [finiteCost, hsum, ha]
  congr 1
  rw [show (fun t => ENNReal.ofReal (testKernel R t)) =
      (fun t => ∑ i, ENNReal.ofReal (hinge (R.p i) (R.q i) t)) by
    funext t
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => hinge_nonneg (R.p i) (R.q i) t)]
  rw [lintegral_finsetSum _ (fun i _ => (hinge_measurable (R.p i) (R.q i)).ennreal_ofReal)]
  simp_rw [remainder_eq_hinge]

/-- Every actual finite test bounds the actual all-finite infimum above. -/
private theorem maximal_le_test (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    maximalValue hf A B ≤ finiteCost hf R := sInf_le ⟨k, R, rfl⟩

private theorem hockey_le_test (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hockeyValue hf A B ≤ finiteCost hf R := by
  rw [hockey_value_eq_operational hf A B hA hB, finite_cost_decomposition]
  apply add_le_add le_rfl
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  unfold testKernel hinge
  split_ifs with ht
  · change operationalNegativeHockey A B t ≤ negativeHockey R t
    unfold operationalNegativeHockey
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro z ⟨j, T, rfl⟩
      exact Finset.sum_nonneg (fun i _ => le_max_right _ _)
    · exact ⟨k, R, rfl⟩
  · change operationalHockey A B t ≤ R.hockey t
    unfold operationalHockey
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro z ⟨j, T, rfl⟩
      exact Finset.sum_nonneg (fun i _ => le_max_right _ _)
    · exact ⟨k, R, rfl⟩

private theorem hockey_le_maximal (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hockeyValue hf A B ≤ maximalValue hf A B := by
  apply le_sInf
  rintro _ ⟨k, R, rfl⟩
  exact hockey_le_test hf R hA hB

private theorem test_integral_split (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∫⁻ t, ENNReal.ofReal (testKernel R t) ∂curvature hf) =
      (∫⁻ t, ENNReal.ofReal (maximalKernel A B t) ∂curvature hf) +
      ∫⁻ t, ENNReal.ofReal (gap R t) ∂curvature hf := by
  simp_rw [kernel_gap R, ENNReal.ofReal_add (maximal_kernel_nonneg A B hA hB _)
    ((actual_gap_profile_data R hA hB).1 _).1]
  exact lintegral_add_left (maximal_kernel_measurable A B hA hB).ennreal_ofReal _

/-- Finite actual cost makes the nonnegative curvature gap integrable and
splits the cost as maximal hockey value plus its real gap integral. -/
private theorem finite_cost_gap (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hfin : finiteCost hf R ≠ ⊤) :
    Integrable (gap R) (curvature hf) ∧
      finiteCost hf R = hockeyValue hf A B +
        ((∫ t : PositiveThreshold, gap R t ∂curvature hf : ℝ) : EReal) := by
  have hsplit := test_integral_split hf R hA hB
  have htest : (∫⁻ t, ENNReal.ofReal (testKernel R t) ∂curvature hf) ≠ ⊤ := by
    intro h
    apply hfin
    rw [finite_cost_decomposition, h, EReal.coe_ennreal_top, EReal.coe_add_top]
  have hgap : (∫⁻ t, ENNReal.ofReal (gap R t) ∂curvature hf) ≠ ⊤ := by
    exact ne_top_of_le_ne_top htest (by rw [hsplit]; exact le_add_left le_rfl)
  have hn : 0 ≤ᵐ[curvature hf] gap R :=
    Eventually.of_forall (fun t => ((actual_gap_profile_data R hA hB).1 t).1)
  have hi : Integrable (gap R) (curvature hf) :=
    ⟨(actual_gap_profile_data R hA hB).2.continuous.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).2 (lt_top_iff_ne_top.mpr hgap)⟩
  refine ⟨hi, ?_⟩
  rw [finite_cost_decomposition, hsplit, EReal.coe_ennreal_add, ← add_assoc, hockeyValue]
  congr 1
  change ((∫⁻ t : PositiveThreshold, ENNReal.ofReal (gap R t) ∂curvature hf : ℝ≥0∞) : EReal) =
    ((∫ t : PositiveThreshold, gap R t ∂curvature hf : ℝ) : EReal)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, EReal.coe_ennreal_ofReal]
  exact congrArg (fun z : ℝ => (z : EReal)) (max_eq_left (integral_nonneg_of_ae hn))

/-- The common-interior condition gives equality for every real convex
function as an equality of extended values, without endpoint or value finiteness. -/
theorem commute_implies_integrated_eq (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hc : let S := A + B
      let C := MaximalHockeyStickSupport.normalize S A
      let P := interiorProjection C
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) :
    maximalValue hf A B = hockeyValue hf A B := by
  obtain ⟨R, -, hprofile⟩ := quadratic_reverse_test_attained_profile A B hA hB
  have hall := (original_all_thresholds_iff_commute A B hA hB).2 hc
  have hk : testKernel R = maximalKernel A B := by
    funext t
    rw [kernel_gap]
    have hg : gap R t = 0 := by
      unfold gap
      rw [hprofile, ← hall t t.2, sub_self]
    rw [hg, add_zero]
  apply le_antisymm
  · apply (maximal_le_test hf R).trans
    rw [finite_cost_decomposition, hk]
    exact le_rfl
  · exact hockey_le_maximal hf A B hA hB

/-- A real finite infimum supplies actual finite-cost approximate tests.
No minimizing test or fixed alphabet size is assumed. -/
private theorem approximate_finite_tests (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (c : ℝ) (hc : maximalValue hf A B = (c : EReal)) :
    ∃ tests : ∀ j : ℕ, Σ k : ℕ, ReverseTest A B k,
      ∀ j, finiteCost hf (tests j).2 < ((c + 1 / ((j : ℝ) + 1) : ℝ) : EReal) := by
  have hex (j : ℕ) : ∃ k : ℕ, ∃ R : ReverseTest A B k,
      finiteCost hf R < ((c + 1 / ((j : ℝ) + 1) : ℝ) : EReal) := by
    have hlt : maximalValue hf A B < ((c + 1 / ((j : ℝ) + 1) : ℝ) : EReal) := by
      rw [hc, EReal.coe_lt_coe_iff]
      have hp : 0 < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    obtain ⟨z, ⟨k, R, rfl⟩, hz⟩ := sInf_lt_iff.mp hlt
    exact ⟨k, R, hz⟩
  choose k R hR using hex
  exact ⟨fun j => ⟨k j, R j⟩, hR⟩

/-- Full-support curvature and a real finite actual infimum classify equality
by the original common-interior commutator for every finite PSD pair. -/
theorem integrated_eq_iff_commute (hf : ConvexOn ℝ (Ioi 0) f)
    [(curvature hf).IsOpenPosMeasure]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : maximalValue hf A B = (c : EReal)) :
    let S := A + B
    let C := MaximalHockeyStickSupport.normalize S A
    let P := interiorProjection C
    (maximalValue hf A B = hockeyValue hf A B) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by
  dsimp only
  constructor
  · intro he
    obtain ⟨tests, htests⟩ := approximate_finite_tests hf A B c hc
    have hcost (j : ℕ) : finiteCost hf (tests j).2 ≠ ⊤ :=
      ne_top_of_lt (htests j)
    have hg (j : ℕ) := finite_cost_gap hf (tests j).2 hA hB (hcost j)
    have hH : hockeyValue hf A B = (c : EReal) := he.symm.trans hc
    letI : IsLocallyFiniteMeasure (curvature hf : Measure PositiveThreshold) :=
      curvature_locallyFinite hf
    apply vanishing_curvature_gaps_imply_commute A B hA hB (curvature hf) tests
      (fun j => (hg j).1)
    apply squeeze_zero (g := fun j : ℕ => 1 / ((j : ℝ) + 1))
    · intro j
      exact integral_nonneg (fun t => ((actual_gap_profile_data (tests j).2 hA hB).1 t).1)
    · intro j
      have h := htests j
      rw [(hg j).2, hH, ← EReal.coe_add, EReal.coe_lt_coe_iff] at h
      change c + (∫ t : PositiveThreshold, gap (tests j).2 t ∂curvature hf) <
        c + 1 / ((j : ℝ) + 1) at h
      linarith
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact commute_implies_integrated_eq hf A B hA hB

#print axioms integrated_eq_iff_commute
#print axioms commute_implies_integrated_eq

end D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
