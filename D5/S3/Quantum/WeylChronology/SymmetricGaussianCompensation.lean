/- GID: D5/S3/Quantum/WeylChronology/SymmetricGaussianCompensation
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:constructed-control-and-uniform-test)
   anchors: []
   digest: Matched split compensation cancels the endpoint cocycle exactly and yields one count test valid across bounded Gaussian closure uncertainty. -/

import D5.S3.Quantum.WeylChronology.GoldenGaussianClosure
import D5.S3.Estimation.ErrorExponents.BernoulliIntervalThreshold

/-!
# Matched split compensation and a common robust decision

The old one-sided compensator leaves eta=X*dy-Y*dx. This file constructs a
different physical sequence: half compensation, the existing chronological
word, and the same half compensation. Equality of the two errors, not smallness,
is the exact algebraic condition for universal endpoint-independent cocycle
cancellation in this two-half architecture. Residual displacement remains.

The general unequal-half formula is retained; no independent errors are
silently equated. For a centered Gaussian the remaining overlap is real and
positive, so the added phase vanishes and the closure budget is quadratic.
A single preselected count threshold is then proved valid for every fixed
acquisition in a stated visibility/displacement envelope. This changes the
previous pairwise-optimal-test quantifier, without claiming minimax optimality.

Library audit at e093071699088b3e97584cfb2b53e56923642eff found no matching split
compensation owner/draft. SchrodingerDisplacement, runWord, Gaussian integration,
RamseyResidualOverlap and the existing binomial KL tails are reused. Analytic
context: Vutha et al., arXiv:1702.01833; Fluehmann and Home, PRL 125,043602
(2020). The symmetric sequence is derived here from their standard Weyl
algebraic setting. It is a proposed control protocol, not a reported experiment.

The protocol needs known inventory and coherent pre/post control. The exact
cancellation assumes the two halves experience the same realized error. Other
pulse noise, displaced/non-Gaussian reference phases and shot correlations are
outside these claims. The fringe is the existing overlap readout; this file does
not claim a new general L2 two-path Born-law completion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.SymmetricGaussianCompensation

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory unitInterval
open D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
open D5.S3.Quantum.WeylChronology.GaussianDisplacementOverlap
open D5.S3.Quantum.WeylChronology.GoldenWordInterferometry
open D5.S3.Quantum.WeylChronology.RamseyResidualOverlap
open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
open D5.S3.Estimation.ErrorExponents.BernoulliIntervalThreshold
open D5.S0.Diagonal.MarginBound

noncomputable section

/-- Exact cocycle from two imperfect half compensators. The first error pair
belongs to the earlier half, and the second to the later half. -/
def splitPhase (X Y ux uy vx vy : ℝ) : ℝ :=
  (X * (vy - uy) - Y * (vx - ux)) / 2 + vy * ux - vx * uy

/-- The earlier half, chronological word, and later half, as actual actions. -/
def splitCompensatedWord (a b ux uy vx vy : ℝ) (word : List Bool)
    (f : ℝ → ℂ) : ℝ → ℂ :=
  displacement (-(a * word.count true) / 2 + vx) (-(b * word.count false) / 2 + vy)
    (runWord a b word
      (displacement (-(a * word.count true) / 2 + ux)
        (-(b * word.count false) / 2 + uy) f))

private theorem phase_mul (u v : ℝ) :
    Complex.exp ((u : ℂ) * Complex.I) * Complex.exp ((v : ℂ) * Complex.I) =
      Complex.exp (((u + v : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The full unequal-half action, including its mismatch phase and net residual. -/
theorem split_compensation_normal_form (a b ux uy vx vy : ℝ)
    (word : List Bool) (f : ℝ → ℂ) :
    splitCompensatedWord a b ux uy vx vy word f =
      Complex.exp (((a * b * (magnusCenter word : ℝ) +
        splitPhase (a * word.count true) (b * word.count false) ux uy vx vy : ℝ) : ℂ) *
          Complex.I) • displacement (ux + vx) (uy + vy) f := by
  let X : ℝ := a * word.count true
  let Y : ℝ := b * word.count false
  change displacement (-X / 2 + vx) (-Y / 2 + vy)
    (runWord a b word (displacement (-X / 2 + ux) (-Y / 2 + uy) f)) = _
  rw [run_word_normal_form, displacement_smul]
  change _ • displacement (-X / 2 + vx) (-Y / 2 + vy)
    (displacement X Y (displacement (-X / 2 + ux) (-Y / 2 + uy) f)) = _
  rw [displacement_comp X Y (-X / 2 + ux) (-Y / 2 + uy) f,
    displacement_smul, displacement_comp, smul_smul, smul_smul, phase_mul, phase_mul]
  have hx : (-X / 2 + vx) + (X + (-X / 2 + ux)) = ux + vx := by ring
  have hy : (-Y / 2 + vy) + (Y + (-Y / 2 + uy)) = uy + vy := by ring
  have hphase :
      (a * b * (magnusCenter word : ℝ) + (Y * (-X / 2 + ux) - X * (-Y / 2 + uy))) +
        ((-Y / 2 + vy) * (X + (-X / 2 + ux)) -
          (-X / 2 + vx) * (Y + (-Y / 2 + uy))) =
      a * b * (magnusCenter word : ℝ) + splitPhase X Y ux uy vx vy := by
    unfold splitPhase
    ring
  rw [hx, hy, hphase]

/-- Matched half errors cancel the cocycle at every endpoint, with no size premise. -/
theorem matched_split_phase_zero (X Y ux uy : ℝ) : splitPhase X Y ux uy ux uy = 0 := by
  unfold splitPhase
  ring

/-- Matching is necessary as well as sufficient for universal zero real cocycle
within this two-half architecture. This is not a converse for one fixed endpoint. -/
theorem universal_split_cancellation_iff_matched (ux uy vx vy : ℝ) :
    (∀ X Y : ℝ, splitPhase X Y ux uy vx vy = 0) ↔ ux = vx ∧ uy = vy := by
  constructor
  · intro h
    have h0 := h 0 0
    have hx := h 2 0
    have hy := h 0 2
    unfold splitPhase at h0 hx hy
    constructor <;> nlinarith
  · rintro ⟨hx, hy⟩
    intro X Y
    rw [← hx, ← hy]
    exact matched_split_phase_zero X Y ux uy

/-- Symmetric compensation with total residual (dx,dy), half in each stroke. -/
def symmetricCompensatedWord (a b dx dy : ℝ) (word : List Bool) (f : ℝ → ℂ) : ℝ → ℂ :=
  splitCompensatedWord a b (dx / 2) (dy / 2) (dx / 2) (dy / 2) word f

/-- Chronology phase is preserved while the unwanted endpoint phase is absent. -/
theorem symmetric_compensation_phase_free (a b dx dy : ℝ)
    (word : List Bool) (f : ℝ → ℂ) :
    symmetricCompensatedWord a b dx dy word f =
      Complex.exp (((a * b * (magnusCenter word : ℝ) : ℝ) : ℂ) * Complex.I) •
        displacement dx dy f := by
  unfold symmetricCompensatedWord
  rw [split_compensation_normal_form, matched_split_phase_zero, add_zero]
  have hx : dx / 2 + dx / 2 = dx := by ring
  have hy : dy / 2 + dy / 2 = dy := by ring
  rw [hx, hy]

/-- An actual normalized Gaussian expectation of the symmetric control sequence. -/
def symmetricGaussianExpectation (s a b dx dy : ℝ) (word : List Bool) : ℂ :=
  (∫ q : ℝ, star (gaussianSeed s q) *
    symmetricCompensatedWord a b dx dy word (gaussianSeed s) q) / gaussianMass s

/-- The exact remaining expectation has no compensator-induced phase. -/
theorem symmetric_gaussian_expectation_exact (s a b dx dy : ℝ)
    (word : List Bool) (hs : 0 < s) :
    symmetricGaussianExpectation s a b dx dy word =
      Complex.exp (((a * b * (magnusCenter word : ℝ) : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-displacementCost s dx dy) : ℂ) := by
  unfold symmetricGaussianExpectation
  rw [symmetric_compensation_phase_free]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hfun :
      (fun q : ℝ => star (gaussianSeed s q) *
        (Complex.exp (((a * b * (magnusCenter word : ℝ) : ℝ) : ℂ) * Complex.I) *
          displacement dx dy (gaussianSeed s) q)) =
      (fun q : ℝ => Complex.exp (((a * b * (magnusCenter word : ℝ) : ℝ) : ℂ) * Complex.I) *
        (star (gaussianSeed s q) * displacement dx dy (gaussianSeed s) q)) := by
    funext q
    ring
  rw [hfun, integral_const_mul, mul_div_assoc]
  change _ * gaussianOverlap s dx dy = _
  rw [gaussian_overlap_exact s dx dy hs]

/-- The existing overlap-sensitive sine-analyzer readout for this new protocol. -/
def symmetricClosureFringe (s a b dx dy visibility : ℝ) (word : List Bool) : ℝ :=
  overlapChronologyFringe visibility (a * b / 2) word (gaussianOverlap s dx dy)

/-- The only Gaussian effect on this centered-reference readout is attenuation. -/
theorem symmetric_closure_fringe_eq_visible (s a b dx dy visibility : ℝ)
    (word : List Bool) (hs : 0 < s) :
    symmetricClosureFringe s a b dx dy visibility word =
      visibleChronologyFringe (visibility * Real.exp (-displacementCost s dx dy))
        (a * b / 2) word := by
  unfold symmetricClosureFringe overlapChronologyFringe
  rw [gaussian_overlap_exact s dx dy hs]
  simp only [overlapRamseyFringe, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re,
    Real.cos_sub_pi_div_two]
  unfold visibleChronologyFringe visibilitySignal
  ring

/-- The first-order endpoint phase is removed from the certified probability budget. -/
theorem symmetric_closure_quadratic_budget (s a b dx dy visibility : ℝ)
    (word : List Bool) (hs : 0 < s) :
    |symmetricClosureFringe s a b dx dy visibility word -
      visibleChronologyFringe visibility (a * b / 2) word| ≤
        |visibility| / 2 * displacementCost s dx dy := by
  have h := overlap_closure_error_le visibility (a * b / 2) word (gaussianOverlap s dx dy)
  change |symmetricClosureFringe s a b dx dy visibility word -
    visibleChronologyFringe visibility (a * b / 2) word| ≤ _ at h
  exact h.trans (mul_le_mul_of_nonneg_left (gaussian_overlap_defect_le_cost s dx dy hs)
    (by positivity))

private theorem visible_contrast_deviation (v v0 k : ℝ) (word : List Bool) :
    |visibleChronologyFringe v k word - visibleChronologyFringe v0 k word| ≤ |v-v0|/2 := by
  have he : visibleChronologyFringe v k word - visibleChronologyFringe v0 k word =
      ((v-v0)/2) * Real.sin (2*k*(magnusCenter word : ℝ)) := by
    unfold visibleChronologyFringe visibilitySignal
    ring
  rw [he, abs_mul, abs_div]
  norm_num only [abs_ofNat]
  calc
    _ ≤ (|v-v0|/2)*1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
    _ = _ := mul_one _

/-- Unknown contrast and closure errors have one common deterministic envelope. -/
theorem symmetric_uncertainty_budget (s a b dx dy v v0 vmax ev qmax : ℝ)
    (word : List Bool) (hs : 0 < s) (hv0 : 0 ≤ v) (hvmax : v ≤ vmax)
    (hcontrast : |v-v0| ≤ ev) (hcost : displacementCost s dx dy ≤ qmax) :
    |symmetricClosureFringe s a b dx dy v word - visibleChronologyFringe v0 (a*b/2) word| ≤
      (ev + vmax*qmax)/2 := by
  have h0 := symmetric_closure_quadratic_budget s a b dx dy v word hs
  have h1 := visible_contrast_deviation v v0 (a*b/2) word
  have htri := abs_sub_le (symmetricClosureFringe s a b dx dy v word)
    (visibleChronologyFringe v (a*b/2) word) (visibleChronologyFringe v0 (a*b/2) word)
  rw [abs_of_nonneg hv0] at h0
  have hcost0 := displacement_cost_nonneg s dx dy hs
  have hprod : v * displacementCost s dx dy ≤ vmax * qmax :=
    mul_le_mul hvmax hcost hcost0 (hv0.trans hvmax)
  linarith

/-- Visibility below one makes every acquired probability strictly interior. -/
theorem symmetric_fringe_strict (s a b dx dy v : ℝ) (word : List Bool)
    (hs : 0 < s) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    0 < symmetricClosureFringe s a b dx dy v word ∧
      symmetricClosureFringe s a b dx dy v word < 1 := by
  rw [symmetric_closure_fringe_eq_visible s a b dx dy v word hs]
  have he0 := (Real.exp_pos (-displacementCost s dx dy)).le
  have he1 : Real.exp (-displacementCost s dx dy) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (displacement_cost_nonneg s dx dy hs))
  have hvv0 : 0 ≤ v * Real.exp (-displacementCost s dx dy) := mul_nonneg hv0 he0
  have hvvle : v * Real.exp (-displacementCost s dx dy) ≤ v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he1 hv0
  have hvv1 : v * Real.exp (-displacementCost s dx dy) < 1 := hvvle.trans_lt hv1
  have hsin := Real.abs_sin_le_one (2*(a*b/2)*(magnusCenter word : ℝ))
  have hsignal : |v * Real.exp (-displacementCost s dx dy) *
      Real.sin (2*(a*b/2)*(magnusCenter word : ℝ))| ≤
      v * Real.exp (-displacementCost s dx dy) := by
    rw [abs_mul, abs_of_nonneg hvv0]
    simpa using mul_le_mul_of_nonneg_left hsin hvv0
  unfold visibleChronologyFringe visibilitySignal
  have hb := abs_le.mp hsignal
  constructor <;> linarith [hb.1, hb.2]

/-- A parameter of Mathlib's existing binomial count measure, with physical validity proved. -/
def symmetricProbability (s a b dx dy v : ℝ) (word : List Bool)
    (hs : 0 < s) (hv0 : 0 ≤ v) (hv1 : v < 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨symmetricClosureFringe s a b dx dy v word,
    (symmetric_fringe_strict s a b dx dy v word hs hv0 hv1).1.le,
    (symmetric_fringe_strict s a b dx dy v word hs hv0 hv1).2.le⟩

/-- One event is selected before either actual visibility or closure error is known.
All pairs in the envelope obey the same certified risk bound for that same test. -/
theorem one_test_for_all_symmetric_acquisitions
    (s a b v0 vmax ev qmax u t v : ℝ) (left right : List Bool) (shots : ℕ)
    (hs : 0 < s) (hmax : vmax < 1)
    (hu0 : 0 < u) (hut : u < t) (htv : t < v) (hv1 : v < 1)
    (hleft : visibleChronologyFringe v0 (a*b/2) left + (ev+vmax*qmax)/2 ≤ u)
    (hright : v ≤ visibleChronologyFringe v0 (a*b/2) right - (ev+vmax*qmax)/2) :
    ∃ event : Set ℝ, MeasurableSet event ∧
      ∀ (vl vr dxl dyl dxr dyr : ℝ)
        (hl0 : 0 ≤ vl) (hlmax : vl ≤ vmax) (hr0 : 0 ≤ vr) (hrmax : vr ≤ vmax),
        |vl-v0| ≤ ev → |vr-v0| ≤ ev →
        displacementCost s dxl dyl ≤ qmax → displacementCost s dxr dyr ≤ qmax →
        (Bin(ℝ, shots, symmetricProbability s a b dxl dyl vl left hs hl0
            (hlmax.trans_lt hmax)).real event +
          Bin(ℝ, shots, symmetricProbability s a b dxr dyr vr right hs hr0
            (hrmax.trans_lt hmax)).real eventᶜ) / 2 ≤
          Real.exp (-(shots : ℝ) * thresholdRate u t v) := by
  refine ⟨thresholdEvent shots t, measurableSet_Ici, ?_⟩
  intro vl vr dxl dyl dxr dyr hl0 hlmax hr0 hrmax hlv hrv hlQ hrQ
  have hl := symmetric_uncertainty_budget s a b dxl dyl vl v0 vmax ev qmax left
    hs hl0 hlmax hlv hlQ
  have hr := symmetric_uncertainty_budget s a b dxr dyr vr v0 vmax ev qmax right
    hs hr0 hrmax hrv hrQ
  have hlbound := abs_le.mp hl
  have hrbound := abs_le.mp hr
  apply threshold_risk_le_exponential shots u t v hu0 hut htv hv1
  · exact (symmetric_fringe_strict s a b dxl dyl vl left hs hl0 (hlmax.trans_lt hmax)).1
  · change symmetricClosureFringe s a b dxl dyl vl left ≤ u
    linarith [hlbound.2]
  · change v ≤ symmetricClosureFringe s a b dxr dyr vr right
    linarith [hrbound.1]
  · exact (symmetric_fringe_strict s a b dxr dyr vr right hs hr0 (hrmax.trans_lt hmax)).2

#print axioms split_compensation_normal_form
#print axioms universal_split_cancellation_iff_matched
#print axioms symmetric_compensation_phase_free
#print axioms symmetric_gaussian_expectation_exact
#print axioms symmetric_closure_quadratic_budget
#print axioms one_test_for_all_symmetric_acquisitions

end
end D5.S3.Quantum.WeylChronology.SymmetricGaussianCompensation
