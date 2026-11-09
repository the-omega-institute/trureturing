/- GID: D5/S3/Quantum/Algebra/PauliFixedProductLinear
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PauliFixedProductLinear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict small-parameter improvement for the same actual fixed-product Pauli family. -/

import D5.S3.Quantum.Algebra.PauliFixedProductFamily
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

noncomputable section
namespace D5.S3.Quantum.Algebra.PauliLinearCertificate

/-- The source constant for unit spin products. -/
def constant : ℝ := 1 + 2 * Real.sqrt 2
/-- The linear certificate with the original denominator. -/
def linear (eps d : ℝ) : ℝ :=
  2 * constant * d * eps / (Real.sqrt 2 - 2 * constant * eps)
/-- The original quadratic root, including its independent cap. -/
def old (eps d : ℝ) : ℝ :=
  min d ((constant * eps + Real.sqrt (constant^2*eps^2+4*constant*d*eps))/2)

private theorem sqrt_two : 1 ≤ Real.sqrt 2 ∧ (Real.sqrt 2)^2 = 2 := by
  constructor
  · exact Real.one_le_sqrt.mpr (by norm_num)
  · exact Real.sq_sqrt (by norm_num)

private theorem constant_pos : 0 < constant := by
  unfold constant
  positivity

/-- The strict comparison uses the original cap and is uniform over the stated d range. -/
private theorem strict_comparison (eps d : ℝ) (heps : 0 < eps)
    (hsmall : eps < 1 / (16 * constant)) (hd : 1 ≤ d) (hdtop : d ≤ Real.sqrt 2) :
    0 < Real.sqrt 2 - 2 * constant * eps ∧
    linear eps d < old eps d := by
  have hc := constant_pos
  have hs := sqrt_two
  have hx : 0 < constant * eps := mul_pos hc heps
  have hxsmall : constant * eps < 1/16 := by
    have hh := (lt_div_iff₀ (show 0 < 16*constant by positivity)).mp hsmall
    nlinarith
  have hden : 0 < Real.sqrt 2 - 2*constant*eps := by nlinarith [hs.1]
  have hlin : linear eps d ≤ 4*(constant*eps) := by
    unfold linear
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (le_of_lt hx) (sub_nonneg.mpr hdtop)]
  have hxroot : 4*(constant*eps) < Real.sqrt (constant*eps) := by
    have hsq := Real.sq_sqrt (le_of_lt hx)
    have hnonneg := Real.sqrt_nonneg (constant*eps)
    nlinarith
  have hroot : Real.sqrt (constant*eps) ≤
      (constant*eps + Real.sqrt (constant^2*eps^2+4*constant*d*eps))/2 := by
    have hr : 0 ≤ constant^2*eps^2+4*constant*d*eps := by positivity
    have hsqr := Real.sq_sqrt hr
    have hsr := Real.sq_sqrt (le_of_lt hx)
    have hn := Real.sqrt_nonneg (constant^2*eps^2+4*constant*d*eps)
    have hn' := Real.sqrt_nonneg (constant*eps)
    have hmul : constant*eps ≤ constant*d*eps := by nlinarith
    have : 2*Real.sqrt (constant*eps) ≤
        Real.sqrt (constant^2*eps^2+4*constant*d*eps) := by nlinarith [sq_nonneg (constant*eps)]
    linarith
  refine ⟨hden, lt_min ?_ ?_⟩
  · have : linear eps d < 1 := by linarith
    linarith
  · exact lt_of_le_of_lt hlin (lt_of_lt_of_le hxroot hroot)

end D5.S3.Quantum.Algebra.PauliLinearCertificate


noncomputable section
open scoped InnerProductSpace TensorProduct
namespace D5.S3.Quantum.Algebra.PauliFixedProductFamily
open PauliLinearCertificate

/-- The norm of the complete actual residual, without averaging. -/
def epsilon (t : ℝ) : ℝ := Real.sqrt (reportSquared t)
/-- The exact local bilinear action bound. -/
def localBound (t : ℝ) : ℝ := Real.sqrt (1+t^2)
/-- The source-stated endpoint of the strict improvement interval. -/
def smallEndpoint : ℝ := 1/(192*Real.sqrt 2*constant)

private theorem epsilon_eq (t : ℝ) : epsilon t = 12*Real.sqrt 2*|t| := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have heq : reportSquared t = (12*Real.sqrt 2*|t|)^2 := by
    rw [full_report]
    simp only [mul_pow, sq_abs, hs]
    ring
  rw [epsilon, heq, Real.sqrt_sq (by positivity)]

private theorem parameter_small (t : ℝ) (h : |t| < smallEndpoint) :
    epsilon t < 1/(16*constant) ∧ |t|<1 := by
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1≤Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hc : 1≤constant := by dsimp [constant]; linarith
  have hcp : 0<constant := by linarith
  have hh := (lt_div_iff₀ (show 0<192*Real.sqrt 2*constant by positivity)).mp h
  constructor
  · rw [epsilon_eq]
    apply (lt_div_iff₀ (show 0<16*constant by positivity)).2
    nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hc) (abs_nonneg t),
      mul_nonneg (sub_nonneg.mpr hs1) (abs_nonneg t)]

/-- The interval is nonempty and uses its literal stated endpoint. -/
theorem small_interval_nonempty : ∃ t : ℝ, 0 < |t| ∧ |t|<smallEndpoint := by
  have hp : 0<smallEndpoint := by unfold smallEndpoint constant; positivity
  refine ⟨smallEndpoint/2, ?_, ?_⟩ <;> rw [abs_of_pos (by positivity)] <;> linarith

/-- The complete residual of the same family supplies a strictly improved certificate. -/
theorem actual_strict_improvement (t : ℝ) (ht : 0 < |t|) (hsmall : |t|<smallEndpoint) :
    0<Real.sqrt 2-2*constant*epsilon t ∧
    (∃ a : J, D t a a≠0) ∧ D t (e 0)≠0 ∧
    (∀ a : J, ‖a‖=1 → ‖D t a a‖ ≤ linear (epsilon t) (localBound t)) ∧
    |t|/2 ≤ linear (epsilon t) (localBound t) ∧
    linear (epsilon t) (localBound t) < old (epsilon t) (localBound t) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1≤Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hc : 1≤constant := by dsimp [constant]; linarith
  have heps : 0<epsilon t := by rw [epsilon_eq]; positivity
  have hparam := parameter_small t hsmall
  have hd : 1≤localBound t := by
    dsimp [localBound]
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg t])
  have hdt : localBound t ≤ Real.sqrt 2 := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_abs t, abs_nonneg t]
  have hcompare := strict_comparison (epsilon t) (localBound t) heps hparam.1 hd hdt
  have hdom : |t|/2 ≤ linear (epsilon t) (localBound t) := by
    unfold linear
    apply (le_div_iff₀ hcompare.1).2
    have hdenle : Real.sqrt 2-2*constant*epsilon t≤Real.sqrt 2 :=
      sub_le_self _ (by positivity)
    have hcd : 1≤constant*localBound t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd)]
    have hm : 0≤(constant*localBound t-1)*(Real.sqrt 2*|t|) :=
      mul_nonneg (sub_nonneg.mpr hcd) (by positivity)
    calc
      |t|/2*(Real.sqrt 2-2*constant*epsilon t)≤|t|/2*Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hdenle (by positivity)
      _≤2*constant*localBound t*epsilon t := by
        rw [epsilon_eq]
        nlinarith [show 0≤Real.sqrt 2*|t| by positivity]
  rcases exact_support_gap t with ⟨_,_,_,_,hactive,_,_⟩
  obtain ⟨hdiag,hunit,_⟩ := hactive (abs_pos.mp ht)
  refine ⟨hcompare.1,hdiag,hunit,?_,hdom,hcompare.2⟩
  intro a ha
  exact le_trans ((exact_defects t).1.2 ⟨a,ha,rfl⟩) hdom

/-- An actual member of the literal interval has both nonzero defects and the strict certificate. -/
theorem nonempty_improvement : ∃ t : ℝ,
    (type_of% (family_contract t)) ∧
    (type_of% (exact_defects t)) ∧
    (type_of% (exact_constants t)) ∧
    (type_of% (exact_action_data t)) ∧
    (type_of% (exact_label_data t)) ∧
    (type_of% (exact_support_gap t)) ∧
    0 < |t| ∧ |t|<smallEndpoint ∧
    (∃ a : J, D t a a≠0) ∧ D t (e 0)≠0 ∧
    |t|/2≤linear (epsilon t) (localBound t) ∧
    linear (epsilon t) (localBound t)<old (epsilon t) (localBound t) := by
  obtain ⟨t,ht,hs⟩ := small_interval_nonempty
  obtain ⟨_,hdiag,hunit,_,hdom,hstrict⟩ := actual_strict_improvement t ht hs
  exact ⟨t,family_contract t,exact_defects t,exact_constants t,exact_action_data t,
    exact_label_data t,exact_support_gap t,ht,hs,hdiag,hunit,hdom,hstrict⟩

end D5.S3.Quantum.Algebra.PauliFixedProductFamily
