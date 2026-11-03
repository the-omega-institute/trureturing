import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicCoefficientIdentity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
The original cubic is evaluated as an analytic function before taking its
negative Laurent coefficients. The external root is an independent parameter.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalytic

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianCubicKernel

/-- The original binomial series, evaluated by its convergent sum in the disk. -/
def H (v : ℂ) : ℂ := ∑' n : ℕ, halfBinomial n * v ^ n

private lemma H_hasFPowerSeries :
    HasFPowerSeriesOnBall H (binomialSeries ℂ (-1 / 2 : ℂ)) 0 1 := by
  apply Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.congr
  intro v hv
  have hs := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
    (a := (-1 / 2 : ℂ))).hasSum hv
  have he : HasSum (fun n : ℕ => halfBinomial n * v ^ n)
      ((1 + v) ^ (-1 / 2 : ℂ)) := by
    simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, zero_add, halfBinomial_choose] using hs
  exact he.tsum_eq.symm

private lemma H_differentiableAt {v : ℂ} (hv : ‖v‖ < 1) :
    DifferentiableAt ℂ H v := by
  apply (H_hasFPowerSeries.analyticAt_of_mem ?_).differentiableAt
  simpa [edist_dist, dist_eq_norm, ENNReal.ofReal_lt_one] using hv

/-- The external point need not lie in the convergence disk of H. -/
def beta (b : ℂ) : ℝ := min 1 ‖b‖

def omega (a x : ℂ) : ℂ := H a / a * H (x / a)

def externalOmega (b hb x : ℂ) : ℂ := hb / b * H (x / b)

def polarNumerator (a b x : ℂ) : ℂ :=
  a * b * (a + b + 2) + x * (2 * a * b + a + b)

def TT (b hb a x : ℂ) : ℂ :=
  omega a x * externalOmega b hb x *
    (polarNumerator a b x / (2 * (a - b) ^ 2) + scalarC x)

def UT (b hb a x : ℂ) : ℂ :=
  -(omega a x * externalOmega b hb x) *
    (x * polarNumerator a b x / (2 * (a * b - x) ^ 2) + scalarC x)

/-- The coefficient of a^(-s-1), with the positive circle orientation. -/
def negativeContour (K : ℂ → ℂ) (s : ℕ) (r : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ a in C(0, r), K a * a ^ s

private lemma beta_pos {b : ℂ} (hb : b ≠ 0) : 0 < beta b := by
  exact lt_min (by norm_num) (norm_pos_iff.mpr hb)

private lemma beta_le_one (b : ℂ) : beta b ≤ 1 := min_le_left _ _

private lemma beta_le_norm (b : ℂ) : beta b ≤ ‖b‖ := min_le_right _ _

/-- The common annulus excludes both polar divisors and validates every H factor. -/
private lemma annulus_conditions {b a x : ℂ} (hb : b ≠ 0)
    (hinner : ‖x‖ / beta b < ‖a‖) (houter : ‖a‖ < beta b) :
    a ≠ 0 ∧ a ≠ b ∧ a * b ≠ x ∧
      ‖a‖ < 1 ∧ ‖x / a‖ < 1 ∧ ‖x / b‖ < 1 ∧ ‖x‖ < 1 := by
  have hB := beta_pos hb
  have haPos : 0 < ‖a‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg x) hB.le) hinner
  have ha : a ≠ 0 := norm_pos_iff.mp haPos
  have hxa : ‖x‖ < ‖a‖ * beta b := (div_lt_iff₀ hB).mp hinner
  have ha1 := houter.trans_le (beta_le_one b)
  have haB := houter.trans_le (beta_le_norm b)
  have hx_a : ‖x‖ < ‖a‖ :=
    hxa.trans_le (mul_le_of_le_one_right haPos.le (beta_le_one b))
  have hx_ab : ‖x‖ < ‖a‖ * ‖b‖ :=
    hxa.trans_le (mul_le_mul_of_nonneg_left (beta_le_norm b) haPos.le)
  have hxB : ‖x‖ < ‖b‖ := hx_a.trans haB
  have hab : a * b ≠ x := by
    intro heq
    have heqNorm : ‖a‖ * ‖b‖ = ‖x‖ := by simpa only [norm_mul] using congrArg norm heq
    linarith
  refine ⟨ha, ne_of_apply_ne norm (ne_of_lt haB), hab, ha1, ?_, ?_, hx_a.trans ha1⟩
  · rw [norm_div]
    exact (div_lt_one haPos).mpr hx_a
  · rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hb)).mpr hxB

/-- Fixed inner and outer circles are simultaneously available at every sewing point. -/
private lemma sewing_radii {b z : ℂ} (hz0 : 0 < ‖z‖) (hz : ‖z‖ < beta b) :
    ∃ r rho : ℝ, 0 < r ∧ ‖z ^ 2‖ / beta b < r ∧
      r < ‖z‖ ∧ ‖z‖ < rho ∧ rho < beta b := by
  have hB : 0 < beta b := hz0.trans hz
  have hsq : ‖z ^ 2‖ / beta b < ‖z‖ := by
    rw [norm_pow]
    apply (div_lt_iff₀ hB).mpr
    nlinarith
  obtain ⟨r, hrInner, hrz⟩ := exists_between hsq
  obtain ⟨rho, hzrho, hrho⟩ := exists_between hz
  exact ⟨r, rho, lt_of_le_of_lt (div_nonneg (norm_nonneg _) hB.le) hrInner,
    hrInner, hrz, hzrho, hrho⟩

/-- The literal differential acquires a minus sign under the neck inversion. -/
theorem omega_inversion (u x : ℂ) (hu : u ≠ 0) (hx : x ≠ 0) :
    omega (x / u) x * (-x / u ^ 2) = -omega u x := by
  have hquot : x / (x / u) = u := by field_simp [hu, hx]
  rw [omega, hquot, omega]
  field_simp [hu, hx]
  <;> ring

private lemma kernels_differentiable_a {b a x : ℂ} (hb : b ≠ 0) (hroot : ℂ)
    (hinner : ‖x‖ / beta b < ‖a‖) (houter : ‖a‖ < beta b) :
    DifferentiableAt ℂ (fun u => TT b hroot u x) a ∧
      DifferentiableAt ℂ (fun u => UT b hroot u x) a := by
  obtain ⟨ha, hab, habx, ha1, hxa, _, _⟩ := annulus_conditions hb hinner houter
  have hquot : DifferentiableAt ℂ (fun u : ℂ => x / u) a :=
    differentiableAt_const.div differentiableAt_id ha
  have hw : DifferentiableAt ℂ (fun u => omega u x) a :=
    ((H_differentiableAt ha1).div differentiableAt_id ha).mul
      ((H_differentiableAt hxa).comp a hquot)
  have hN : DifferentiableAt ℂ (fun u => polarNumerator u b x) a := by
    unfold polarNumerator
    fun_prop
  have hTTden : (2 * (a - b) ^ 2 : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr hab))
  have hUTden : (2 * (a * b - x) ^ 2 : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr habx))
  constructor
  · exact (hw.mul_const _).mul ((hN.div (by fun_prop) hTTden).add_const _)
  · exact (hw.mul_const _).neg.mul
      (((hN.const_mul x).div (by fun_prop) hUTden).add_const _)

private lemma negativeContour_independent {K : ℂ → ℂ} {l B r R : ℝ} (s : ℕ)
    (hK : ∀ a : ℂ, l < ‖a‖ → ‖a‖ < B → DifferentiableAt ℂ K a)
    (hr0 : 0 < r) (hR0 : 0 < R) (hlr : l < r) (hrB : r < B)
    (hlR : l < R) (hRB : R < B) :
    negativeContour K s r = negativeContour K s R := by
  have ordered : ∀ u v : ℝ, 0 < u → l < u → v < B → u ≤ v →
      negativeContour K s v = negativeContour K s u := by
    intro u v hu hlu hv huv
    unfold negativeContour
    congr 1
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hu huv Set.countable_empty
    · intro a ha
      have hav : ‖a‖ ≤ v := by simpa using ha.1
      have hua : u ≤ ‖a‖ := le_of_not_gt (by simpa using ha.2)
      exact ((hK a (hlu.trans_le hua) (hav.trans_lt hv)).mul
        (differentiableAt_id.pow s)).continuousAt.continuousWithinAt
    · intro a ha
      have hav : ‖a‖ < v := by simpa using ha.1.1
      have hua : u < ‖a‖ := lt_of_not_ge (by simpa using ha.1.2)
      exact (hK a (hlu.trans hua) (hav.trans hv)).mul (differentiableAt_id.pow s)
  rcases le_total r R with h | h
  · exact (ordered r R hr0 hlr hRB h).symm
  · exact ordered R r hR0 hlR hrB h

private def contourRadius (b x : ℂ) : ℝ := (‖x‖ / beta b + beta b) / 2

private lemma contourRadius_admissible {b x : ℂ} (hb : b ≠ 0)
    (hx : ‖x‖ < beta b ^ 2) :
    0 < contourRadius b x ∧ ‖x‖ / beta b < contourRadius b x ∧
      contourRadius b x < beta b := by
  have hB := beta_pos hb
  have hxB : ‖x‖ / beta b < beta b := by
    apply (div_lt_iff₀ hB).mpr
    nlinarith
  have hx0 := div_nonneg (norm_nonneg x) hB.le
  unfold contourRadius
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- These definitions use integrals of the literal functions, independent of formal series. -/
def Tcoeff (b hb : ℂ) (s : ℕ) (x : ℂ) : ℂ :=
  negativeContour (fun a => TT b hb a x) s (contourRadius b x)

def Ucoeff (b hb : ℂ) (s : ℕ) (x : ℂ) : ℂ :=
  negativeContour (fun a => UT b hb a x) s (contourRadius b x)

/-- Every admissible fixed contour computes the same actual negative coefficients. -/
theorem coefficients_on_fixed_contour {b x : ℂ} (hb : b ≠ 0)
    (hx : ‖x‖ < beta b ^ 2) (root : ℂ) (s : ℕ) {r : ℝ}
    (hr0 : 0 < r) (hinner : ‖x‖ / beta b < r) (houter : r < beta b) :
    Tcoeff b root s x = negativeContour (fun a => TT b root a x) s r ∧
      Ucoeff b root s x = negativeContour (fun a => UT b root a x) s r ∧
      CircleIntegrable (fun a => TT b root a x * a ^ s) 0 r ∧
      CircleIntegrable (fun a => UT b root a x * a ^ s) 0 r := by
  obtain ⟨hR0, hinnerR, houterR⟩ := contourRadius_admissible hb hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact negativeContour_independent s
      (fun a hi ho => (kernels_differentiable_a hb root hi ho).1)
      hR0 hr0 hinnerR houterR hinner houter
  · exact negativeContour_independent s
      (fun a hi ho => (kernels_differentiable_a hb root hi ho).2)
      hR0 hr0 hinnerR houterR hinner houter
  · apply ContinuousOn.circleIntegrable hr0.le
    intro a ha
    have har : ‖a‖ = r := by simpa using ha
    exact (((kernels_differentiable_a hb root (by simpa [har] using hinner)
      (by simpa [har] using houter)).1).mul
        (differentiableAt_id.pow s)).continuousAt.continuousWithinAt
  · apply ContinuousOn.circleIntegrable hr0.le
    intro a ha
    have har : ‖a‖ = r := by simpa using ha
    exact (((kernels_differentiable_a hb root (by simpa [har] using hinner)
      (by simpa [har] using houter)).2).mul
        (differentiableAt_id.pow s)).continuousAt.continuousWithinAt

private lemma negativeContour_bound {K : ℂ → ℂ} (s : ℕ) {r M : ℝ}
    (hr : 0 ≤ r) (hM : ∀ a ∈ sphere (0 : ℂ) r, ‖K a‖ ≤ M) :
    ‖negativeContour K s r‖ ≤ M * r ^ (s + 1) := by
  have hbound : ∀ a ∈ sphere (0 : ℂ) r, ‖K a * a ^ s‖ ≤ M * r ^ s := by
    intro a ha
    have har : ‖a‖ = r := by simpa using ha
    rw [norm_mul, norm_pow, har]
    exact mul_le_mul_of_nonneg_right (hM a ha) (pow_nonneg hr s)
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hbound
  change ‖(2 * Real.pi * Complex.I)⁻¹ *
    (∮ a in C(0, r), K a * a ^ s)‖ ≤ r * (M * r ^ s) at h
  convert h using 1
  rw [pow_succ]
  ring

private lemma kernel_circle_bound {b x : ℂ} (hb : b ≠ 0) (root : ℂ) {r : ℝ}
    (hr0 : 0 < r) (hinner : ‖x‖ / beta b < r) (houter : r < beta b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ sphere (0 : ℂ) r,
      ‖TT b root a x‖ ≤ M ∧ ‖UT b root a x‖ ≤ M := by
  have hd (a : ℂ) (ha : a ∈ sphere (0 : ℂ) r) :
      DifferentiableAt ℂ (fun u => TT b root u x) a ∧
        DifferentiableAt ℂ (fun u => UT b root u x) a := by
    have har : ‖a‖ = r := by simpa using ha
    exact kernels_differentiable_a hb root (by simpa [har] using hinner)
      (by simpa [har] using houter)
  have hcT : ContinuousOn (fun a => TT b root a x) (sphere 0 r) :=
    fun a ha => (hd a ha).1.continuousAt.continuousWithinAt
  have hcU : ContinuousOn (fun a => UT b root a x) (sphere 0 r) :=
    fun a ha => (hd a ha).2.continuousAt.continuousWithinAt
  obtain ⟨MT, hMT⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hcT
  obtain ⟨MU, hMU⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hcU
  refine ⟨max 0 (max MT MU), le_max_left _ _, ?_⟩
  intro a ha
  exact ⟨(hMT a ha).trans ((le_max_left MT MU).trans (le_max_right _ _)),
    (hMU a ha).trans ((le_max_right MT MU).trans (le_max_right _ _))⟩

/-- A single bound controls every negative mode on any strict inner contour. -/
theorem coefficients_bound {b x : ℂ} (hb : b ≠ 0)
    (hx : ‖x‖ < beta b ^ 2) (root : ℂ) {r : ℝ}
    (hr0 : 0 < r) (hinner : ‖x‖ / beta b < r) (houter : r < beta b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℕ,
      ‖Tcoeff b root s x‖ ≤ M * r ^ (s + 1) ∧
      ‖Ucoeff b root s x‖ ≤ M * r ^ (s + 1) := by
  obtain ⟨M, hM0, hM⟩ := kernel_circle_bound hb root hr0 hinner houter
  refine ⟨M, hM0, fun s => ?_⟩
  rw [(coefficients_on_fixed_contour hb hx root s hr0 hinner houter).1,
    (coefficients_on_fixed_contour hb hx root s hr0 hinner houter).2.1]
  exact ⟨negativeContour_bound s hr0.le (fun a ha => (hM a ha).1),
    negativeContour_bound s hr0.le (fun a ha => (hM a ha).2)⟩

private lemma scalarC_differentiableAt {x : ℂ} (hx : ‖x‖ < 1) :
    DifferentiableAt ℂ scalarC x := by
  obtain ⟨hF, hF', _⟩ := D5.S3.Analytic.OriginalHalfBinomialPeriod.picard_fuchs hx
  have hne := OriginalGaussianPeriodIdentity.period_ne_zero hx
  exact (differentiableAt_id.div_const 2).sub
    (((differentiableAt_id.mul (differentiableAt_const.sub differentiableAt_id)).mul
      hF').div hF hne)

private lemma kernels_differentiable_x {b a x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hinner : ‖x‖ / beta b < ‖a‖) (houter : ‖a‖ < beta b) :
    DifferentiableAt ℂ (fun xi => TT b root a xi) x ∧
      DifferentiableAt ℂ (fun xi => UT b root a xi) x := by
  obtain ⟨_, _, habx, _, hxa, hxb, hx1⟩ := annulus_conditions hb hinner houter
  have hw : DifferentiableAt ℂ (fun xi => omega a xi) x :=
    ((H_differentiableAt hxa).comp x (differentiableAt_id.div_const a)).const_mul _
  have he : DifferentiableAt ℂ (fun xi => externalOmega b root xi) x :=
    ((H_differentiableAt hxb).comp x (differentiableAt_id.div_const b)).const_mul _
  have hN : DifferentiableAt ℂ (fun xi => polarNumerator a b xi) x := by
    unfold polarNumerator
    fun_prop
  have hUden : (2 * (a * b - x) ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr habx))
  exact ⟨(hw.mul he).mul ((hN.div_const _).add (scalarC_differentiableAt hx1)),
    (hw.mul he).neg.mul (((differentiableAt_id.mul hN).div (by fun_prop) hUden).add
      (scalarC_differentiableAt hx1))⟩

/-- The literal kernels have genuine Taylor series in x on every strict fixed disk. -/
theorem literal_modulus_series {b a : ℂ} (hb : b ≠ 0) (root : ℂ)
    (ha : ‖a‖ < beta b) {eta : ℝ≥0} (heta : 0 < eta)
    (hetab : (eta : ℝ) < ‖a‖ * beta b) :
    HasFPowerSeriesOnBall (fun x => TT b root a x)
      (cauchyPowerSeries (fun x => TT b root a x) 0 eta) 0 eta ∧
      HasFPowerSeriesOnBall (fun x => UT b root a x)
        (cauchyPowerSeries (fun x => UT b root a x) 0 eta) 0 eta := by
  have hd (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) eta) :
      DifferentiableAt ℂ (fun xi => TT b root a xi) x ∧
        DifferentiableAt ℂ (fun xi => UT b root a xi) x := by
    have hxeta : ‖x‖ ≤ eta := by simpa using hx
    apply kernels_differentiable_x hb root
    · exact (div_lt_iff₀ (beta_pos hb)).mpr (hxeta.trans_lt hetab)
    · exact ha
  have hdT : DifferentiableOn ℂ (fun x => TT b root a x) (closedBall 0 eta) :=
    fun x hx => (hd x hx).1.differentiableWithinAt
  have hdU : DifferentiableOn ℂ (fun x => UT b root a x) (closedBall 0 eta) :=
    fun x hx => (hd x hx).2.differentiableWithinAt
  exact ⟨hdT.hasFPowerSeriesOnBall heta, hdU.hasFPowerSeriesOnBall heta⟩

private lemma kernels_continuous_joint {b a x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hinner : ‖x‖ / beta b < ‖a‖) (houter : ‖a‖ < beta b) :
    ContinuousAt (fun ax : ℂ × ℂ => TT b root ax.1 ax.2) (a, x) ∧
      ContinuousAt (fun ax : ℂ × ℂ => UT b root ax.1 ax.2) (a, x) := by
  obtain ⟨ha, hab, habx, ha1, hxa, hxb, hx1⟩ := annulus_conditions hb hinner houter
  have hHa : ContinuousAt (fun ax : ℂ × ℂ => H ax.1) (a, x) :=
    (H_differentiableAt ha1).continuousAt.comp continuousAt_fst
  have hHxa : ContinuousAt (fun ax : ℂ × ℂ => H (ax.2 / ax.1)) (a, x) :=
    (H_differentiableAt hxa).continuousAt.comp (continuousAt_snd.div continuousAt_fst ha)
  have hHxb : ContinuousAt (fun ax : ℂ × ℂ => H (ax.2 / b)) (a, x) :=
    (H_differentiableAt hxb).continuousAt.comp (continuousAt_snd.div_const b)
  have hw : ContinuousAt (fun ax : ℂ × ℂ => omega ax.1 ax.2) (a, x) :=
    (hHa.div continuousAt_fst ha).mul hHxa
  have he : ContinuousAt (fun ax : ℂ × ℂ => externalOmega b root ax.2) (a, x) :=
    hHxb.const_mul _
  have hC : ContinuousAt (fun ax : ℂ × ℂ => scalarC ax.2) (a, x) :=
    (scalarC_differentiableAt hx1).continuousAt.comp continuousAt_snd
  have hN : ContinuousAt (fun ax : ℂ × ℂ => polarNumerator ax.1 b ax.2) (a, x) := by
    unfold polarNumerator
    fun_prop
  have hTden : (2 * (a - b) ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr hab))
  have hUden : (2 * (a * b - x) ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr habx))
  exact ⟨(hw.mul he).mul ((hN.div (by fun_prop) hTden).add hC),
    (hw.mul he).neg.mul (((continuousAt_snd.mul hN).div (by fun_prop) hUden).add hC)⟩

/-- Iterated circle integrals for the mode and modulus indices. -/
def doubleContour (K : ℂ → ℂ → ℂ) (s d : ℕ) (r eta : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∮ xi in C(0, eta), negativeContour (fun a => K a xi) s r / xi ^ (d + 1)

private lemma doubleContour_bound {K : ℂ → ℂ → ℂ} (s d : ℕ) {r eta M : ℝ}
    (hr : 0 ≤ r) (heta : 0 < eta)
    (hM : ∀ a ∈ sphere (0 : ℂ) r, ∀ xi ∈ sphere (0 : ℂ) eta, ‖K a xi‖ ≤ M) :
    ‖doubleContour K s d r eta‖ ≤ M * r ^ (s + 1) / eta ^ d := by
  have hbound : ∀ xi ∈ sphere (0 : ℂ) eta,
      ‖negativeContour (fun a => K a xi) s r / xi ^ (d + 1)‖ ≤
        M * r ^ (s + 1) / eta ^ (d + 1) := by
    intro xi hxi
    have hnorm : ‖xi‖ = eta := by simpa using hxi
    rw [norm_div, norm_pow, hnorm]
    exact div_le_div_of_nonneg_right
      (negativeContour_bound s hr (fun a ha => hM a ha xi hxi)) (by positivity)
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const heta.le hbound
  change ‖doubleContour K s d r eta‖ ≤ eta * (M * r ^ (s + 1) / eta ^ (d + 1)) at h
  convert h using 1
  rw [pow_succ]
  field_simp [heta.ne']
  <;> ring

/-- The two-index Cauchy estimate is uniform in the mode and modulus degree. -/
theorem double_contours_bound {b : ℂ} (hb : b ≠ 0) (root : ℂ) {r eta : ℝ}
    (hr : 0 < r) (hrb : r < beta b) (heta : 0 < eta) (hetab : eta < r * beta b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s d : ℕ,
      ‖doubleContour (TT b root) s d r eta‖ ≤ M * r ^ (s + 1) / eta ^ d ∧
      ‖doubleContour (UT b root) s d r eta‖ ≤ M * r ^ (s + 1) / eta ^ d := by
  let S := (sphere (0 : ℂ) r) ×ˢ (sphere (0 : ℂ) eta)
  have hc (ax : ℂ × ℂ) (hax : ax ∈ S) :
      ContinuousAt (fun ax : ℂ × ℂ => TT b root ax.1 ax.2) ax ∧
        ContinuousAt (fun ax : ℂ × ℂ => UT b root ax.1 ax.2) ax := by
    have har : ‖ax.1‖ = r := by simpa using hax.1
    have hxeta : ‖ax.2‖ = eta := by simpa using hax.2
    apply kernels_continuous_joint hb root
    · apply (div_lt_iff₀ (beta_pos hb)).mpr
      simpa [har, hxeta] using hetab
    · simpa [har] using hrb
  have hcompact : IsCompact S := (isCompact_sphere (0 : ℂ) r).prod
    (isCompact_sphere (0 : ℂ) eta)
  obtain ⟨MT, hMT⟩ := hcompact.exists_bound_of_continuousOn
    (fun ax hax => (hc ax hax).1.continuousWithinAt)
  obtain ⟨MU, hMU⟩ := hcompact.exists_bound_of_continuousOn
    (fun ax hax => (hc ax hax).2.continuousWithinAt)
  let M := max 0 (max MT MU)
  have hT : ∀ a ∈ sphere (0 : ℂ) r, ∀ xi ∈ sphere (0 : ℂ) eta,
      ‖TT b root a xi‖ ≤ M := by
    intro a ha xi hxi
    exact (hMT (a, xi) ⟨ha, hxi⟩).trans
      ((le_max_left MT MU).trans (le_max_right 0 _))
  have hU : ∀ a ∈ sphere (0 : ℂ) r, ∀ xi ∈ sphere (0 : ℂ) eta,
      ‖UT b root a xi‖ ≤ M := by
    intro a ha xi hxi
    exact (hMU (a, xi) ⟨ha, hxi⟩).trans
      ((le_max_right MT MU).trans (le_max_right 0 _))
  exact ⟨M, le_max_left _ _, fun s d =>
    ⟨doubleContour_bound s d hr.le heta hT, doubleContour_bound s d hr.le heta hU⟩⟩

private lemma pairScalar_div_bound (s t : ℕ) :
    ‖pairScalar s (t + 1) / (t + 1 : ℂ)‖ ≤ (s : ℝ) * ‖halfBinomial s‖ := by
  have ht : (t + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero t
  have hst : (s : ℂ) + (t + 1 : ℂ) ≠ 0 := by
    have hpos : 0 < s + (t + 1) := by omega
    exact_mod_cast Nat.ne_of_gt hpos
  have he : pairScalar s (t + 1) / (t + 1 : ℂ) =
      (s : ℂ) * halfBinomial s * halfBinomial (t + 1) / (s + (t + 1) : ℂ) := by
    unfold pairScalar
    push_cast
    field_simp [ht, hst]
    <;> ring
  have hh : ‖halfBinomial (t + 1)‖ ≤ 1 := by
    rw [halfBinomial_eq_signed_centralWeight, norm_mul, norm_pow]
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (centralWeight_nonneg (t + 1))] using weight_le_one (t + 1)
  have hden : 1 ≤ ‖(s + (t + 1) : ℂ)‖ := by
    have hcast : (s + (t + 1) : ℂ) = ((s + (t + 1) : ℕ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_natCast]
    exact_mod_cast (show 1 ≤ s + (t + 1) by omega)
  rw [he, norm_div]
  calc
    _ ≤ ‖(s : ℂ) * halfBinomial s * halfBinomial (t + 1)‖ :=
      div_le_self (norm_nonneg _) hden
    _ ≤ (s : ℝ) * ‖halfBinomial s‖ := by
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (mul_one _)

private lemma weighted_doubleContour_summable {K : ℂ → ℂ → ℂ} {r eta M : ℝ}
    (s : ℕ) {x : ℂ} (hr : 0 ≤ r) (hr1 : r < 1) (heta : 0 < eta)
    (hx : ‖x‖ < eta) (hM : 0 ≤ M)
    (hK : ∀ t d : ℕ, ‖doubleContour K t d r eta‖ ≤ M * r ^ (t + 1) / eta ^ d) :
    Summable (fun td : ℕ × ℕ => ‖pairScalar s (td.1 + 1) / (td.1 + 1 : ℂ) *
      doubleContour K (td.1 + 1) td.2 r eta * x ^ td.2‖) := by
  have htheta0 : 0 ≤ ‖x‖ / eta := div_nonneg (norm_nonneg x) heta.le
  have htheta1 : ‖x‖ / eta < 1 := (div_lt_one heta).mpr hx
  have hprod := (summable_geometric_of_lt_one hr hr1).mul_of_nonneg
    (summable_geometric_of_lt_one htheta0 htheta1)
    (fun n => pow_nonneg hr n) (fun n => pow_nonneg htheta0 n)
  have hs := hprod.mul_left ((s : ℝ) * ‖halfBinomial s‖ * M * r ^ 2)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun td => ?_) hs
  rw [norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ ((s : ℝ) * ‖halfBinomial s‖) *
        (M * r ^ ((td.1 + 1) + 1) / eta ^ td.2) * ‖x‖ ^ td.2 := by
      gcongr
      · exact pairScalar_div_bound s td.1
      · exact hK (td.1 + 1) td.2
    _ = ((s : ℝ) * ‖halfBinomial s‖ * M * r ^ 2) *
        (r ^ td.1 * (‖x‖ / eta) ^ td.2) := by
      rw [div_pow, show (td.1 + 1) + 1 = td.1 + 2 by omega, pow_add]
      ring

/-- Absolute summability over the full Cartesian set of both coefficient indices. -/
theorem double_contours_absolute {b x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (s : ℕ) {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) (hx : ‖x‖ < eta) :
    Summable (fun td : ℕ × ℕ => ‖pairScalar s (td.1 + 1) / (td.1 + 1 : ℂ) *
      doubleContour (TT b root) (td.1 + 1) td.2 r eta * x ^ td.2‖) ∧
    Summable (fun td : ℕ × ℕ => ‖pairScalar s (td.1 + 1) / (td.1 + 1 : ℂ) *
      doubleContour (UT b root) (td.1 + 1) td.2 r eta * x ^ td.2‖) := by
  obtain ⟨M, hM, hbound⟩ := double_contours_bound hb root hr hrb heta hetab
  exact ⟨weighted_doubleContour_summable s hr.le (hrb.trans_le (beta_le_one b)) heta hx hM
      (fun t d => (hbound t d).1),
    weighted_doubleContour_summable s hr.le (hrb.trans_le (beta_le_one b)) heta hx hM
      (fun t d => (hbound t d).2)⟩

/-- The normalization uses positive real square roots and the original complex powers. -/
def pValue (b hb z : ℂ) (n : ℕ) : ℂ :=
  Tcoeff b hb (n + 1) (z ^ 2) /
    ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1))

def qValue (b hb z : ℂ) (n : ℕ) : ℂ :=
  Ucoeff b hb (n + 1) (z ^ 2) /
    ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1))

private lemma normalized_summable {c : ℕ → ℂ} {z : ℂ} {r M : ℝ}
    (hz : 0 < ‖z‖) (hr : 0 ≤ r) (hrz : r < ‖z‖)
    (hc : ∀ s : ℕ, ‖c s‖ ≤ M * r ^ (s + 1)) :
    Summable (fun n : ℕ => ‖c (n + 1) /
      ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1))‖) := by
  have htheta0 : 0 ≤ r / ‖z‖ := div_nonneg hr hz.le
  have htheta1 : r / ‖z‖ < 1 := (div_lt_one hz).mpr hrz
  have hgeom := ((summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one htheta0 htheta1)).mul_left (M * r)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hgeom
  have hden : 1 ≤ ‖(Real.sqrt (n + 1 : ℝ) : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using
      (Real.one_le_sqrt.mpr (by positivity : (1 : ℝ) ≤ n + 1))
  calc
    _ = (‖c (n + 1)‖ / ‖z‖ ^ (n + 1)) /
        ‖(Real.sqrt (n + 1 : ℝ) : ℂ)‖ := by
      rw [norm_div, norm_mul, norm_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ‖c (n + 1)‖ / ‖z‖ ^ (n + 1) :=
      div_le_self (by positivity) hden
    _ ≤ (M * r ^ ((n + 1) + 1)) / ‖z‖ ^ (n + 1) :=
      div_le_div_of_nonneg_right (hc (n + 1)) (by positivity)
    _ = (M * r) * (r / ‖z‖) ^ (n + 1) := by
      rw [div_pow, pow_succ]
      ring

private lemma memℓp_two_of_summable_norm {f : ℕ → ℂ}
    (hf : Summable (fun n => ‖f n‖)) : Memℓp f 2 := by
  have hm : Memℓp f 1 := memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using hf)
  exact hm.of_exponent_ge (by norm_num)

/-- Membership is proved from the actual contour bounds, before any operator is applied. -/
theorem normalized_coefficients_mem {b z : ℂ} (root : ℂ)
    (hz0 : 0 < ‖z‖) (hz : ‖z‖ < beta b) :
    Summable (fun n => ‖pValue b root z n‖) ∧
      Summable (fun n => ‖qValue b root z n‖) ∧
      Memℓp (pValue b root z) 2 ∧ Memℓp (qValue b root z) 2 := by
  have hb : b ≠ 0 := norm_pos_iff.mp (hz0.trans (hz.trans_le (beta_le_norm b)))
  have hx : ‖z ^ 2‖ < beta b ^ 2 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z, beta_pos hb]
  obtain ⟨r, rho, hr0, hinner, hrz, _, _⟩ := sewing_radii hz0 hz
  obtain ⟨M, _, hM⟩ := coefficients_bound hb hx root hr0 hinner (hrz.trans hz)
  have hp : Summable (fun n => ‖pValue b root z n‖) :=
    normalized_summable hz0 hr0.le hrz (fun s => (hM s).1)
  have hq : Summable (fun n => ‖qValue b root z n‖) :=
    normalized_summable hz0 hr0.le hrz (fun s => (hM s).2)
  exact ⟨hp, hq, memℓp_two_of_summable_norm hp, memℓp_two_of_summable_norm hq⟩

/-- The actual external row uses the given root, not an evaluation of H at b. -/
def eValue (b hb z : ℂ) (n : ℕ) : ℂ :=
  z ^ (n + 1) * currentRow b hb (n + 1) / (Real.sqrt (n + 1 : ℝ) : ℂ)

private lemma currentRow_outer_bound {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    {rho : ℝ} (hrho : 0 < rho) (hrhob : rho < beta b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℕ,
      ‖currentRow b root s‖ * rho ^ s ≤ M * (s : ℝ) * (s + 1 : ℝ) := by
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hrhoB := hrhob.trans_le (beta_le_norm b)
  have hrho1 := hrhob.trans_le (beta_le_one b)
  have hrhoball : (rho : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [edist_dist, dist_eq_norm, ENNReal.ofReal_lt_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrho] using hrho1
  have hrhorad : (rho : ℂ) ∈ Metric.eball (0 : ℂ) (binomialSeries ℂ (1 / 2 : ℂ)).radius :=
    Metric.eball_subset_eball (binomialSeries_radius_ge_one (a := (1 / 2 : ℂ))) hrhoball
  have hg : Summable (fun k : ℕ => ‖Ring.choose (1 / 2 : ℂ) k‖ * rho ^ k) := by
    simpa [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho] using
      (binomialSeries ℂ (1 / 2 : ℂ)).summable_norm_apply hrhorad
  let B := ∑' k : ℕ, ‖Ring.choose (1 / 2 : ℂ) k‖ * rho ^ k
  have hB0 : 0 ≤ B := tsum_nonneg (fun k => by positivity)
  have hterm (s k : ℕ) (hk : k ≤ s) :
      ‖Ring.choose (1 / 2 : ℂ) k * b ^ k / b ^ (s + 1)‖ * rho ^ s ≤ B / ‖b‖ := by
    have hkB : ‖Ring.choose (1 / 2 : ℂ) k‖ * rho ^ k ≤ B :=
      hg.le_tsum k (fun j _ => by positivity)
    have hpr : rho ^ s = rho ^ k * rho ^ (s - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    have hpb : ‖b‖ ^ (s + 1) = ‖b‖ ^ k * ‖b‖ ^ (s - k) * ‖b‖ := by
      rw [← pow_add, Nat.add_sub_of_le hk, pow_succ]
    rw [norm_div, norm_mul, norm_pow, norm_pow]
    calc
      _ = (‖Ring.choose (1 / 2 : ℂ) k‖ * rho ^ k) *
          (rho ^ (s - k) / ‖b‖ ^ (s - k)) / ‖b‖ := by
        rw [hpr, hpb]
        field_simp [hB.ne']
        <;> ring
      _ ≤ B * 1 / ‖b‖ := by
        apply div_le_div_of_nonneg_right ?_ hB.le
        exact mul_le_mul hkB
          ((div_le_one (pow_pos hB _)).mpr
            (pow_le_pow_left₀ hrho.le hrhoB.le _))
          (by positivity) hB0
      _ = B / ‖b‖ := by ring
  refine ⟨‖root‖ * B / ‖b‖, by positivity, fun s => ?_⟩
  have hsum : ‖∑ k ∈ Finset.range (s + 1),
      Ring.choose (1 / 2 : ℂ) k * b ^ k / b ^ (s + 1)‖ * rho ^ s ≤
        (s + 1 : ℝ) * (B / ‖b‖) := by
    calc
      _ ≤ (∑ k ∈ Finset.range (s + 1),
          ‖Ring.choose (1 / 2 : ℂ) k * b ^ k / b ^ (s + 1)‖) * rho ^ s :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
      _ ≤ ∑ _k ∈ Finset.range (s + 1), B / ‖b‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun k hk => hterm s k (by
          have := Finset.mem_range.mp hk
          omega))
      _ = _ := by simp
  calc
    _ = (s : ℝ) * ‖root‖ *
        (‖∑ k ∈ Finset.range (s + 1),
          Ring.choose (1 / 2 : ℂ) k * b ^ k / b ^ (s + 1)‖ * rho ^ s) := by
      rw [currentRow, norm_mul, norm_mul, Complex.norm_natCast]
      ring
    _ ≤ (s : ℝ) * ‖root‖ * ((s + 1 : ℝ) * (B / ‖b‖)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

private lemma external_majorant {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    {rho R : ℝ} (hrho : 0 < rho) (hrhob : rho < beta b) (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ n : ℕ,
      ‖eValue b root z n‖ ≤
        M * (((n + 1 : ℕ) : ℝ) ^ 2 + (n + 1 : ℕ)) * (R / rho) ^ (n + 1) := by
  obtain ⟨M, hM, hbound⟩ := currentRow_outer_bound hb root hrho hrhob
  refine ⟨M, hM, fun z hz n => ?_⟩
  have hden : 1 ≤ ‖(Real.sqrt (n + 1 : ℝ) : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using
      (Real.one_le_sqrt.mpr (by positivity : (1 : ℝ) ≤ n + 1))
  have hcs : ‖currentRow b root (n + 1)‖ ≤
      M * (n + 1 : ℝ) * ((n + 1 : ℕ) + 1 : ℝ) / rho ^ (n + 1) := by
    apply (le_div_iff₀ (pow_pos hrho _)).mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hbound (n + 1)
  calc
    _ ≤ ‖z ^ (n + 1) * currentRow b root (n + 1)‖ := by
      rw [eValue, norm_div]
      exact div_le_self (norm_nonneg _) hden
    _ ≤ R ^ (n + 1) *
        (M * (n + 1 : ℝ) * ((n + 1 : ℕ) + 1 : ℝ) / rho ^ (n + 1)) := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz _) hcs
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [div_pow]
      push_cast
      ring

private lemma polynomial_geometric_summable {theta : ℝ} (htheta0 : 0 ≤ theta)
    (htheta1 : theta < 1) :
    Summable (fun s : ℕ => ((s : ℝ) ^ 2 + s) * theta ^ s) := by
  have hthetanorm : ‖theta‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg htheta0]
  simpa only [add_mul, pow_one] using
    (summable_pow_mul_geometric_of_norm_lt_one 2 hthetanorm).add
      (summable_pow_mul_geometric_of_norm_lt_one 1 hthetanorm)

/-- An outer radius proves summability of the genuine external row on the full disk. -/
theorem external_row_mem {b z : ℂ} (root : ℂ) (hz : ‖z‖ < beta b) :
    Summable (fun n => ‖eValue b root z n‖) ∧ Memℓp (eValue b root z) 2 := by
  have hb : b ≠ 0 := norm_pos_iff.mp
    (lt_of_le_of_lt (norm_nonneg z) (hz.trans_le (beta_le_norm b)))
  obtain ⟨rho, hzrho, hrhob⟩ := exists_between hz
  have hrho : 0 < rho := lt_of_le_of_lt (norm_nonneg z) hzrho
  obtain ⟨M, _, hbound⟩ := external_majorant hb root hrho hrhob (norm_nonneg z)
  have hpoly := polynomial_geometric_summable
    (div_nonneg (norm_nonneg z) hrho.le) ((div_lt_one hrho).mpr hzrho)
  have hmajor := ((summable_nat_add_iff 1).mpr hpoly).mul_left M
  have he : Summable (fun n => ‖eValue b root z n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hbound z le_rfl)
    simpa only [mul_assoc] using hmajor
  exact ⟨he, memℓp_two_of_summable_norm he⟩

def eVector (b hb z : ℂ) (hz : ‖z‖ < beta b) : OriginalGaussianResolvent.H :=
  ⟨eValue b hb z, (external_row_mem hb hz).2⟩

/-- The normal sum of the external row's coordinate vectors. -/
def eSeries (b hb z : ℂ) : OriginalGaussianResolvent.H :=
  ∑' n : ℕ, lp.single 2 n (eValue b hb z n)

private lemma eSeries_eq_vector {b z : ℂ} (root : ℂ) (hz : ‖z‖ < beta b) :
    eSeries b root z = eVector b root z hz := by
  exact (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (eVector b root z hz)).tsum_eq

/-- The external H-valued sum converges normally on each strict closed sewing disk. -/
theorem external_normal_convergence {b : ℂ} (root : ℂ) {R : ℝ}
    (hR : 0 ≤ R) (hRb : R < beta b) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ n : ℕ,
      ‖(lp.single 2 n (eValue b root z n) : OriginalGaussianResolvent.H)‖ ≤ u n := by
  have hb : b ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hR (hRb.trans_le (beta_le_norm b)))
  obtain ⟨rho, hRrho, hrhob⟩ := exists_between hRb
  have hrho : 0 < rho := lt_of_le_of_lt hR hRrho
  obtain ⟨M, _, hbound⟩ := external_majorant hb root hrho hrhob hR
  refine ⟨fun n => M * (((n + 1 : ℕ) : ℝ) ^ 2 + (n + 1 : ℕ)) *
    (R / rho) ^ (n + 1), ?_, ?_⟩
  · have hpoly := polynomial_geometric_summable (div_nonneg hR hrho.le)
      ((div_lt_one hrho).mpr hRrho)
    convert ((summable_nat_add_iff 1).mpr hpoly).mul_left M using 1
    funext n
    ring
  · intro z hz n
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    exact hbound z hz n

/-- The external row has an honest holomorphic extension through z=0. -/
private lemma eSeries_differentiableAt {b z : ℂ} (root : ℂ) (hz : ‖z‖ < beta b) :
    DifferentiableAt ℂ (eSeries b root) z := by
  obtain ⟨R, hzR, hRb⟩ := exists_between hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  obtain ⟨u, hu, hbound⟩ := external_normal_convergence root hR.le hRb
  have hterm (n : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ => (lp.single 2 n (eValue b root w n) : OriginalGaussianResolvent.H))
        (ball 0 R) := by
    intro w _
    have he : DifferentiableAt ℂ (fun w => eValue b root w n) w := by
      unfold eValue
      fun_prop
    have hsingle := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n).differentiableAt.comp w he
    exact hsingle.differentiableWithinAt
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu hterm isOpen_ball
    (fun n w hw => hbound w (by simpa using le_of_lt (show ‖w‖ < R by simpa using hw)) n)
  exact hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hzR))

/-- The analytic external row has exactly the original currentRow coordinates. -/
theorem external_row_analytic {b z : ℂ} (root : ℂ) (hz : ‖z‖ < beta b) :
    AnalyticAt ℂ (eSeries b root) z ∧
      ∀ n : ℕ, eSeries b root z n = eValue b root z n := by
  have hd : DifferentiableOn ℂ (eSeries b root) (ball 0 (beta b)) := by
    intro w hw
    exact (eSeries_differentiableAt root (by simpa using hw)).differentiableWithinAt
  refine ⟨hd.analyticAt (isOpen_ball.mem_nhds (by simpa using hz)), ?_⟩
  intro n
  rw [eSeries_eq_vector root hz]
  rfl

/-- The holomorphic external row takes the zero vector at the unsewn point. -/
theorem eSeries_zero (b root : ℂ) : eSeries b root 0 = 0 := by
  simp [eSeries, eValue]

theorem eSeries_first_order {b : ℂ} (hb : b ≠ 0) (root : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (eSeries b root) (fun z : ℂ => z) := by
  have h := (eSeries_differentiableAt (z := (0 : ℂ)) root (by simpa using beta_pos hb)).isBigO_sub
  simpa only [eSeries_zero, sub_zero] using h

/-- The whole literal TT kernel pulls back to UT, including its scalar term. -/
theorem kernel_inversion (b root u x : ℂ) (hu : u ≠ 0) (hx : x ≠ 0)
    (hpolar : u * b ≠ x) :
    TT b root (x / u) x * (-x / u ^ 2) = UT b root u x := by
  have hden : x / u - b ≠ 0 := by
    intro h
    have h' : x = b * u := (div_eq_iff hu).mp (sub_eq_zero.mp h)
    exact hpolar (by rw [h']; ring)
  have hP : polarNumerator (x / u) b x / (2 * (x / u - b) ^ 2) =
      x * polarNumerator u b x / (2 * (u * b - x) ^ 2) := by
    unfold polarNumerator
    field_simp [hu, hden, sub_ne_zero.mpr hpolar]
    <;> ring
  unfold TT
  rw [hP]
  calc
    _ = (omega (x / u) x * (-x / u ^ 2)) * externalOmega b root x *
        (x * polarNumerator u b x / (2 * (u * b - x) ^ 2) + scalarC x) := by ring
    _ = _ := by
      rw [omega_inversion u x hu hx]
      unfold UT
      ring

/-- Both external-root signs, and all complex scalar multiples, are retained. -/
theorem coefficients_external_linear (c b root : ℂ) (s : ℕ) (x : ℂ) :
    Tcoeff b (c * root) s x = c * Tcoeff b root s x ∧
      Ucoeff b (c * root) s x = c * Ucoeff b root s x := by
  have hT : (fun a => TT b (c * root) a x * a ^ s) =
      fun a => c * (TT b root a x * a ^ s) := by
    funext a
    unfold TT externalOmega
    ring
  have hU : (fun a => UT b (c * root) a x * a ^ s) =
      fun a => c * (UT b root a x * a ^ s) := by
    funext a
    unfold UT externalOmega
    ring
  constructor
  · unfold Tcoeff negativeContour
    rw [hT, circleIntegral.integral_const_mul]
    ring
  · unfold Ucoeff negativeContour
    rw [hU, circleIntegral.integral_const_mul]
    ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalytic
