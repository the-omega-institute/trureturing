/- GID: D5/S3/Weil/Budget/CaratheodoryScaleCovariance
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/CaratheodoryScaleCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Even resolvent spectra give covariant Caratheodory functions and budgets. -/

import D5.S3.Weil.Budget.PositiveCayleyScaleTransport
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 and current-origin searches found no Herglotz-kernel or Caratheodory
     scale-covariance owner, and no reusable observer-side scale parameter.
   * Body-shape searches for `(z + w) / (z - w)`, conjugation-invariant
     measure maps, and total resolvent mass found no canonical D5 primitive.
   * Pinned Mathlib supplies Bochner `integral_map`, integration against
     `withDensity`, and finite-measure integrability bounds, but no exact
     covariance theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace D5.S3.Weil.Budget.CaratheodoryScaleCovariance

open CayleyScaleChange PositiveCayleyScaleTransport

/-- The non-normalized Herglotz kernel used by the source. -/
noncomputable def caratheodoryKernel (z w : Complex) : Complex :=
  (z + w) / (z - w)

/-- The source's non-normalized Caratheodory function at Cayley scale `scale`. -/
noncomputable def caratheodoryFunction
    (source : Measure Real) (scale : Real) (w : Complex) : Complex :=
  ∫ z, caratheodoryKernel z w ∂cayleySpectralMeasure source scale

/-- The observer-side parameter, opposite to the spectral transport parameter. -/
noncomputable def observerScaleParameter (a b : Real) : Real :=
  (b - a) / (a + b)

/-- The total mass of the resolvent-weighted source measure. -/
noncomputable def resolventBudget (source : Measure Real) (scale : Real) : Real :=
  (resolventWeightedMeasure source scale Set.univ).toReal

private theorem measurable_cayleyCoordinate (scale : Real) :
    Measurable (cayleyCoordinate scale) := by
  unfold cayleyCoordinate
  fun_prop

private theorem measurable_caratheodoryKernel (w : Complex) :
    Measurable fun z => caratheodoryKernel z w := by
  unfold caratheodoryKernel
  fun_prop

private theorem measurable_resolvent_density (scale : Real) :
    Measurable fun spectral : Real =>
      ENNReal.ofReal ((spectral ^ 2 + scale ^ 2)⁻¹) := by
  fun_prop

private theorem map_withDensity_eq
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : Measure alpha) (f : alpha -> beta) (g : beta -> ENNReal)
    (hf : Measurable f) (hg : Measurable g) :
    (Measure.map f mu).withDensity g =
      Measure.map f (mu.withDensity (g ∘ f)) := by
  ext s hs
  rw [withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hg hf]
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs)]
  rfl

private theorem resolventWeightedMeasure_neg_invariant
    (source : Measure Real) (scale : Real)
    (hEven : Measure.map (fun x : Real => -x) source = source) :
    Measure.map (fun x : Real => -x) (resolventWeightedMeasure source scale) =
      resolventWeightedMeasure source scale := by
  let density : Real -> ENNReal := fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + scale ^ 2)⁻¹)
  have hdensity : Measurable density := measurable_resolvent_density scale
  have hcomp : density ∘ (fun x : Real => -x) = density := by
    funext x
    simp [density]
  have hmap := map_withDensity_eq source (fun x : Real => -x) density
    measurable_neg hdensity
  unfold resolventWeightedMeasure
  change Measure.map (fun x : Real => -x) (source.withDensity density) =
    source.withDensity density
  calc
    Measure.map (fun x : Real => -x) (source.withDensity density) =
        (Measure.map (fun x : Real => -x) source).withDensity density := by
      simpa only [hcomp] using hmap.symm
    _ = source.withDensity density := by rw [hEven]

private theorem cayleyCoordinate_norm
    (scale spectral : Real) (hscale : 0 < scale) :
    ‖cayleyCoordinate scale spectral‖ = 1 := by
  have hden : (spectral : Complex) - Complex.I * (scale : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  unfold cayleyCoordinate
  rw [norm_div]
  have hnorm :
      ‖(spectral : Complex) + Complex.I * (scale : Complex)‖ =
        ‖(spectral : Complex) - Complex.I * (scale : Complex)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  rw [hnorm, div_self]
  simpa using hden

private theorem kernel_den_ne
    (z w : Complex) (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) : z - w ≠ 0 := by
  intro h
  have hzw : z = w := sub_eq_zero.mp h
  rw [hzw] at hz
  linarith

private theorem caratheodoryKernel_norm_le
    (z w : Complex) (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) :
    ‖caratheodoryKernel z w‖ ≤ (1 + ‖w‖) / (1 - ‖w‖) := by
  have hnum : ‖z + w‖ ≤ 1 + ‖w‖ := by
    simpa only [hz] using norm_add_le z w
  have hden : 1 - ‖w‖ ≤ ‖z - w‖ := by
    simpa only [hz] using norm_sub_norm_le z w
  have hpos : 0 < 1 - ‖w‖ := sub_pos.mpr hw
  unfold caratheodoryKernel
  rw [norm_div]
  exact div_le_div₀ (by positivity) hnum hpos hden

private theorem observerScaleParameter_mem_unit
    (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    |observerScaleParameter a b| < 1 := by
  have hab : 0 < a + b := add_pos ha hb
  rw [abs_lt]
  constructor
  · unfold observerScaleParameter
    rw [lt_div_iff₀ hab]
    linarith
  · unfold observerScaleParameter
    rw [div_lt_iff₀ hab]
    linarith

private theorem realDiskAutomorphism_mem_unit
    (r : Real) (w : Complex) (hr : |r| < 1) (hw : ‖w‖ < 1) :
    ‖realDiskAutomorphism r w‖ < 1 := by
  have hrsq : r ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one r).2 hr
  have hwsq : Complex.normSq w < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg w]
  simp only [Complex.normSq_apply] at hwsq
  have hnormSq :
      Complex.normSq (w + (r : Complex)) <
        Complex.normSq (1 + (r : Complex) * w) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  have hdenpos : 0 < ‖1 + (r : Complex) * w‖ := by
    have : 0 < Complex.normSq (1 + (r : Complex) * w) :=
      lt_of_le_of_lt (Complex.normSq_nonneg _) hnormSq
    rw [← Complex.sq_norm] at this
    nlinarith [norm_nonneg (1 + (r : Complex) * w)]
  unfold realDiskAutomorphism
  rw [norm_div, div_lt_one hdenpos]
  nlinarith [Complex.sq_norm (w + (r : Complex)),
    Complex.sq_norm (1 + (r : Complex) * w), norm_nonneg (w + (r : Complex)),
    norm_nonneg (1 + (r : Complex) * w)]

private theorem resolvent_ratio_nonneg
    (a b spectral : Real) (hb : 0 < b) :
    0 ≤ (spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) := by
  positivity

private theorem resolvent_ratio_le
    (a b spectral : Real) (hb : 0 < b) :
    (spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) ≤
      1 + a ^ 2 / b ^ 2 := by
  have hden : 0 < spectral ^ 2 + b ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  field_simp [ne_of_gt hb]
  nlinarith [sq_nonneg spectral, sq_nonneg a, sq_nonneg b]

private theorem resolvent_density_ratio
    (a b spectral : Real) (ha : 0 < a) (hb : 0 < b) :
    ENNReal.ofReal ((spectral ^ 2 + a ^ 2)⁻¹) *
        ENNReal.ofReal
          ((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2)) =
      ENNReal.ofReal ((spectral ^ 2 + b ^ 2)⁻¹) := by
  have hratio := resolvent_ratio_nonneg a b spectral hb
  have hda : 0 ≤ (spectral ^ 2 + a ^ 2)⁻¹ := by positivity
  have hdb : 0 ≤ (spectral ^ 2 + b ^ 2)⁻¹ := by positivity
  rw [← ENNReal.ofReal_mul hda]
  apply (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg hda hratio) hdb).2
  have hsa : spectral ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hsb : spectral ^ 2 + b ^ 2 ≠ 0 := by positivity
  field_simp [hsa, hsb]

private theorem resolventWeightedMeasure_scale_change
    (source : Measure Real) (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    resolventWeightedMeasure source b =
      (resolventWeightedMeasure source a).withDensity fun spectral =>
        ENNReal.ofReal
          ((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2)) := by
  let densityA : Real -> ENNReal := fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + a ^ 2)⁻¹)
  let densityB : Real -> ENNReal := fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + b ^ 2)⁻¹)
  let ratio : Real -> ENNReal := fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2))
  have hdensityA : Measurable densityA := measurable_resolvent_density a
  have hratio : Measurable ratio := by
    dsimp only [ratio]
    fun_prop
  have hdensity : densityA * ratio = densityB := by
    funext spectral
    exact resolvent_density_ratio a b spectral ha hb
  unfold resolventWeightedMeasure
  change source.withDensity densityB =
    (source.withDensity densityA).withDensity ratio
  rw [← withDensity_mul source hdensityA hratio, hdensity]

private theorem integral_eq_of_neg_pair
    (mu : Measure Real)
    (hneg : Measure.map (fun x : Real => -x) mu = mu)
    (f g : Real -> Complex) (hf : Integrable f mu) (hg : Integrable g mu)
    (hpair : ∀ x, f x + f (-x) = g x + g (-x)) :
    ∫ x, f x ∂mu = ∫ x, g x ∂mu := by
  have hfneg : Integrable (fun x => f (-x)) mu := by
    change Integrable (f ∘ fun x : Real => -x) mu
    rw [← measurableEmbedding_neg.integrable_map_iff, hneg]
    exact hf
  have hgneg : Integrable (fun x => g (-x)) mu := by
    change Integrable (g ∘ fun x : Real => -x) mu
    rw [← measurableEmbedding_neg.integrable_map_iff, hneg]
    exact hg
  have hifneg : (∫ x, f (-x) ∂mu) = ∫ x, f x ∂mu := by
    rw [← measurableEmbedding_neg.integral_map (μ := mu) f, hneg]
  have higneg : (∫ x, g (-x) ∂mu) = ∫ x, g x ∂mu := by
    rw [← measurableEmbedding_neg.integral_map (μ := mu) g, hneg]
  have hsum :
      (∫ x, f x + f (-x) ∂mu) = ∫ x, g x + g (-x) ∂mu := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpair
  rw [integral_add hf hfneg, integral_add hg hgneg, hifneg, higneg] at hsum
  have htwo : (2 : Complex) * (∫ x, f x ∂mu) =
      (2 : Complex) * ∫ x, g x ∂mu := by
    simpa only [two_mul] using hsum
  exact mul_left_cancel₀ (by norm_num : (2 : Complex) ≠ 0) htwo

private theorem kernel_cayley_formula
    (scale spectral : Real) (w : Complex) (hscale : 0 < scale)
    (hw : ‖w‖ < 1) :
    let denominator :=
      (spectral : Complex) * (1 - w) +
        Complex.I * (scale : Complex) * (1 + w)
    caratheodoryKernel (cayleyCoordinate scale spectral) w =
        ((spectral : Complex) * (1 + w) +
          Complex.I * (scale : Complex) * (1 - w)) / denominator ∧
      denominator ≠ 0 := by
  dsimp only
  have hcden :
      (spectral : Complex) - Complex.I * (scale : Complex) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hkden := kernel_den_ne (cayleyCoordinate scale spectral) w
    (cayleyCoordinate_norm scale spectral hscale) hw
  have hdenIdentity :
      cayleyCoordinate scale spectral - w =
        ((spectral : Complex) * (1 - w) +
          Complex.I * (scale : Complex) * (1 + w)) /
            ((spectral : Complex) - Complex.I * (scale : Complex)) := by
    unfold cayleyCoordinate
    field_simp [hcden]
    ring
  have hformulaDen :
      (spectral : Complex) * (1 - w) +
          Complex.I * (scale : Complex) * (1 + w) ≠ 0 := by
    intro h
    apply hkden
    rw [hdenIdentity, h]
    simp
  constructor
  · unfold caratheodoryKernel
    rw [hdenIdentity]
    unfold cayleyCoordinate
    field_simp [hcden, hkden, hformulaDen]
    ring
  · exact hformulaDen

private theorem kernel_cayley_pair_formula
    (scale spectral : Real) (w : Complex) (hscale : 0 < scale)
    (hw : ‖w‖ < 1) :
    let denominator :=
      (scale : Complex) ^ 2 * (1 + w) ^ 2 +
        (spectral : Complex) ^ 2 * (1 - w) ^ 2
    caratheodoryKernel (cayleyCoordinate scale spectral) w +
        caratheodoryKernel (cayleyCoordinate scale (-spectral)) w =
      2 * (((scale : Complex) ^ 2 + (spectral : Complex) ^ 2) *
        (1 - w ^ 2)) / denominator ∧
      denominator ≠ 0 := by
  dsimp only
  have hpos := kernel_cayley_formula scale spectral w hscale hw
  have hneg := kernel_cayley_formula scale (-spectral) w hscale hw
  rcases hpos with ⟨hposEq, hposDen⟩
  rcases hneg with ⟨hnegEq, hnegDen⟩
  have hdenIdentity :
      (scale : Complex) ^ 2 * (1 + w) ^ 2 +
          (spectral : Complex) ^ 2 * (1 - w) ^ 2 =
        -(((spectral : Complex) * (1 - w) +
              Complex.I * (scale : Complex) * (1 + w)) *
          (((-spectral : Real) : Complex) * (1 - w) +
              Complex.I * (scale : Complex) * (1 + w))) := by
    simp only [Complex.ofReal_neg]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hden :
      (scale : Complex) ^ 2 * (1 + w) ^ 2 +
          (spectral : Complex) ^ 2 * (1 - w) ^ 2 ≠ 0 := by
    rw [hdenIdentity]
    exact neg_ne_zero.mpr (mul_ne_zero hposDen hnegDen)
  have add_fractions (np nn dp dn : Complex) (hdp : dp ≠ 0) (hdn : dn ≠ 0) :
      np / dp + nn / dn = (np * dn + nn * dp) / (dp * dn) := by
    field_simp [hdp, hdn]
  have hnumerator :
      ((spectral : Complex) * (1 + w) +
            Complex.I * (scale : Complex) * (1 - w)) *
          (((-spectral : Real) : Complex) * (1 - w) +
            Complex.I * (scale : Complex) * (1 + w)) +
        (((-spectral : Real) : Complex) * (1 + w) +
            Complex.I * (scale : Complex) * (1 - w)) *
          ((spectral : Complex) * (1 - w) +
            Complex.I * (scale : Complex) * (1 + w)) =
        -(2 * (((scale : Complex) ^ 2 + (spectral : Complex) ^ 2) *
          (1 - w ^ 2))) := by
    simp only [Complex.ofReal_neg]
    ring_nf
    rw [Complex.I_sq]
    ring
  constructor
  · rw [hposEq, hnegEq]
    rw [add_fractions _ _ _ _ hposDen hnegDen, hnumerator, hdenIdentity]
    rw [neg_div, div_neg]
  · exact hden

private theorem realDiskAutomorphism_den_ne
    (r : Real) (w : Complex) (hr : |r| < 1) (hw : ‖w‖ < 1) :
    1 + (r : Complex) * w ≠ 0 := by
  intro h
  have hmul : (r : Complex) * w = -1 := by
    linear_combination h
  have hnorm := congrArg norm hmul
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg, norm_one] at hnorm
  have hproduct : |r| * ‖w‖ < 1 := by
    nlinarith [abs_nonneg r, norm_nonneg w]
  linarith

private theorem scale_pair_ratio_identity
    (a b spectral : Real) (w : Complex) (ha : 0 < a) (hb : 0 < b)
    (hw : ‖w‖ < 1) :
    let u := realDiskAutomorphism (observerScaleParameter a b) w
    let denominatorA :=
      (a : Complex) ^ 2 * (1 + u) ^ 2 +
        (spectral : Complex) ^ 2 * (1 - u) ^ 2
    let denominatorB :=
      (b : Complex) ^ 2 * (1 + w) ^ 2 +
        (spectral : Complex) ^ 2 * (1 - w) ^ 2
    ((a / b : Real) : Complex) * (1 - u ^ 2) / denominatorA =
      (1 - w ^ 2) / denominatorB := by
  dsimp only
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have haC : (a : Complex) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hbC : (b : Complex) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have habC : ((a + b : Real) : Complex) ≠ 0 := by exact_mod_cast hab
  have hsunit := observerScaleParameter_mem_unit a b ha hb
  have hphi := realDiskAutomorphism_den_ne
    (observerScaleParameter a b) w hsunit hw
  have hu := realDiskAutomorphism_mem_unit
    (observerScaleParameter a b) w hsunit hw
  have hdenA := (kernel_cayley_pair_formula a spectral
    (realDiskAutomorphism (observerScaleParameter a b) w) ha hu).2
  have hdenB := (kernel_cayley_pair_formula b spectral w hb hw).2
  have hplusCoefficient :
      (((2 * b / (a + b) : Real) : Complex)) =
        1 + (observerScaleParameter a b : Complex) := by
    exact_mod_cast (show 2 * b / (a + b) =
      1 + observerScaleParameter a b by
        unfold observerScaleParameter
        field_simp [hab]
        ring)
  have hminusCoefficient :
      (((2 * a / (a + b) : Real) : Complex)) =
        1 - (observerScaleParameter a b : Complex) := by
    exact_mod_cast (show 2 * a / (a + b) =
      1 - observerScaleParameter a b by
        unfold observerScaleParameter
        field_simp [hab]
        ring)
  have hphiComm : 1 + w * (observerScaleParameter a b : Complex) ≠ 0 := by
    simpa only [mul_comm] using hphi
  have hplus :
      1 + realDiskAutomorphism (observerScaleParameter a b) w =
        (((2 * b / (a + b) : Real) : Complex) * (1 + w)) /
          (1 + (observerScaleParameter a b : Complex) * w) := by
    rw [hplusCoefficient]
    unfold realDiskAutomorphism
    field_simp [hphi, hphiComm]
    ring
  have hminus :
      1 - realDiskAutomorphism (observerScaleParameter a b) w =
        (((2 * a / (a + b) : Real) : Complex) * (1 - w)) /
          (1 + (observerScaleParameter a b : Complex) * w) := by
    rw [hminusCoefficient]
    unfold realDiskAutomorphism
    field_simp [hphi, hphiComm]
    ring
  have hsquare :
      1 - realDiskAutomorphism (observerScaleParameter a b) w ^ 2 =
        (((4 * a * b / (a + b) ^ 2 : Real) : Complex) * (1 - w ^ 2)) /
          (1 + (observerScaleParameter a b : Complex) * w) ^ 2 := by
    rw [show 1 - realDiskAutomorphism (observerScaleParameter a b) w ^ 2 =
      (1 + realDiskAutomorphism (observerScaleParameter a b) w) *
        (1 - realDiskAutomorphism (observerScaleParameter a b) w) by ring]
    rw [hplus, hminus]
    push_cast
    field_simp [hab, hphi]
    ring
  have hdenScale :
      (a : Complex) ^ 2 *
          (1 + realDiskAutomorphism (observerScaleParameter a b) w) ^ 2 +
        (spectral : Complex) ^ 2 *
          (1 - realDiskAutomorphism (observerScaleParameter a b) w) ^ 2 =
        (((4 * a ^ 2 / (a + b) ^ 2 : Real) : Complex) *
          ((b : Complex) ^ 2 * (1 + w) ^ 2 +
            (spectral : Complex) ^ 2 * (1 - w) ^ 2)) /
          (1 + (observerScaleParameter a b : Complex) * w) ^ 2 := by
    rw [hplus, hminus]
    push_cast
    field_simp [hab, hphi]
    ring
  have hcoefficient :
      ((a / b : Real) : Complex) *
          ((4 * a * b / (a + b) ^ 2 : Real) : Complex) =
        ((4 * a ^ 2 / (a + b) ^ 2 : Real) : Complex) := by
    exact_mod_cast (show (a / b) * (4 * a * b / (a + b) ^ 2) =
      4 * a ^ 2 / (a + b) ^ 2 by
        field_simp [ne_of_gt hb, hab])
  have hcoefficientNonzero :
      ((4 * a ^ 2 / (a + b) ^ 2 : Real) : Complex) ≠ 0 := by
    exact_mod_cast (show 4 * a ^ 2 / (a + b) ^ 2 ≠ 0 by positivity)
  have cancel_fractions (A C1 C2 N D d : Complex)
      (hd : d ≠ 0) (hC2 : C2 ≠ 0) (hD : D ≠ 0)
      (hcoeff : A * C1 = C2) :
      A * (C1 * N / d ^ 2) / (C2 * D / d ^ 2) = N / D := by
    field_simp [hd, hC2, hD]
    rw [hcoeff]
    ring
  rw [hsquare, hdenScale]
  exact cancel_fractions _ _ _ _ _ _ hphi hcoefficientNonzero hdenB hcoefficient

private theorem covariance_pair_identity
    (a b spectral : Real) (w : Complex)
    (ha : 0 < a) (hb : 0 < b) (hw : ‖w‖ < 1) :
    let s := observerScaleParameter a b
    let u := realDiskAutomorphism s w
    (((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) : Real) : Complex) *
          caratheodoryKernel (cayleyCoordinate b spectral) w +
        (((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) : Real) : Complex) *
          caratheodoryKernel (cayleyCoordinate b (-spectral)) w =
      ((a / b : Real) : Complex) *
          caratheodoryKernel (cayleyCoordinate a spectral) u +
        ((a / b : Real) : Complex) *
          caratheodoryKernel (cayleyCoordinate a (-spectral)) u := by
  dsimp only
  have hsunit := observerScaleParameter_mem_unit a b ha hb
  have hu := realDiskAutomorphism_mem_unit
    (observerScaleParameter a b) w hsunit hw
  have hleftPair := kernel_cayley_pair_formula b spectral w hb hw
  have hrightPair := kernel_cayley_pair_formula a spectral
    (realDiskAutomorphism (observerScaleParameter a b) w) ha hu
  have hratio := scale_pair_ratio_identity a b spectral w ha hb hw
  rcases hleftPair with ⟨hleftEq, hleftDen⟩
  rcases hrightPair with ⟨hrightEq, hrightDen⟩
  rw [← mul_add, hleftEq, ← mul_add, hrightEq]
  calc
    (((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) : Real) : Complex) *
          (2 * (((b : Complex) ^ 2 + (spectral : Complex) ^ 2) *
            (1 - w ^ 2)) /
            ((b : Complex) ^ 2 * (1 + w) ^ 2 +
              (spectral : Complex) ^ 2 * (1 - w) ^ 2)) =
        2 * ((a : Complex) ^ 2 + (spectral : Complex) ^ 2) *
          ((1 - w ^ 2) /
            ((b : Complex) ^ 2 * (1 + w) ^ 2 +
              (spectral : Complex) ^ 2 * (1 - w) ^ 2)) := by
      have hsb : spectral ^ 2 + b ^ 2 ≠ 0 := by positivity
      have hsbC : ((spectral ^ 2 + b ^ 2 : Real) : Complex) ≠ 0 := by
        exact_mod_cast hsb
      push_cast at hsbC ⊢
      field_simp [hleftDen, hsbC]
      ring
    _ = 2 * ((a : Complex) ^ 2 + (spectral : Complex) ^ 2) *
          (((a / b : Real) : Complex) *
            (1 - realDiskAutomorphism (observerScaleParameter a b) w ^ 2) /
              ((a : Complex) ^ 2 *
                  (1 + realDiskAutomorphism (observerScaleParameter a b) w) ^ 2 +
                (spectral : Complex) ^ 2 *
                  (1 - realDiskAutomorphism (observerScaleParameter a b) w) ^ 2)) := by
      rw [hratio]
    _ = ((a / b : Real) : Complex) *
          (2 * (((a : Complex) ^ 2 + (spectral : Complex) ^ 2) *
            (1 - realDiskAutomorphism (observerScaleParameter a b) w ^ 2)) /
            ((a : Complex) ^ 2 *
                (1 + realDiskAutomorphism (observerScaleParameter a b) w) ^ 2 +
              (spectral : Complex) ^ 2 *
                (1 - realDiskAutomorphism (observerScaleParameter a b) w) ^ 2)) := by
      ring

private theorem caratheodory_zero_eq_budget
    (source : Measure Real) (scale : Real) (hscale : 0 < scale)
    [IsFiniteMeasure (resolventWeightedMeasure source scale)] :
    caratheodoryFunction source scale 0 =
      (resolventBudget source scale : Complex) := by
  unfold caratheodoryFunction cayleySpectralMeasure
  rw [MeasureTheory.integral_map
    (measurable_cayleyCoordinate scale).aemeasurable
    (measurable_caratheodoryKernel 0).aestronglyMeasurable]
  have hpoint : ∀ spectral : Real,
      caratheodoryKernel (cayleyCoordinate scale spectral) 0 = 1 := by
    intro spectral
    have hc : cayleyCoordinate scale spectral ≠ 0 := by
      exact norm_ne_zero_iff.mp (by simp [cayleyCoordinate_norm scale spectral hscale])
    simp [caratheodoryKernel, hc]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  simp [resolventBudget, measureReal_def]

private theorem caratheodory_scale_covariance_main
    (source : Measure Real) (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (hEven : Measure.map (fun x : Real => -x) source = source)
    [IsFiniteMeasure (resolventWeightedMeasure source a)]
    [IsFiniteMeasure (resolventWeightedMeasure source b)]
    (w : Complex) (hw : ‖w‖ < 1) :
    caratheodoryFunction source b w =
      ((a / b : Real) : Complex) *
        caratheodoryFunction source a
          (realDiskAutomorphism (observerScaleParameter a b) w) := by
  let weightedA := resolventWeightedMeasure source a
  let ratio : Real -> ENNReal := fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2))
  let u := realDiskAutomorphism (observerScaleParameter a b) w
  let left : Real -> Complex := fun spectral =>
    (((spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) : Real) : Complex) *
      caratheodoryKernel (cayleyCoordinate b spectral) w
  let right : Real -> Complex := fun spectral =>
    ((a / b : Real) : Complex) *
      caratheodoryKernel (cayleyCoordinate a spectral) u
  have hsunit := observerScaleParameter_mem_unit a b ha hb
  have hu : ‖u‖ < 1 := realDiskAutomorphism_mem_unit
    (observerScaleParameter a b) w hsunit hw
  have hratio : Measurable ratio := by
    dsimp only [ratio]
    fun_prop
  have hleftMeas : AEStronglyMeasurable left weightedA := by
    have hratioReal : Measurable fun spectral : Real =>
        (spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) := by fun_prop
    exact (hratioReal.complex_ofReal.mul
      ((measurable_caratheodoryKernel w).comp
        (measurable_cayleyCoordinate b))).aestronglyMeasurable
  have hrightMeas : AEStronglyMeasurable right weightedA := by
    exact (measurable_const.mul
      ((measurable_caratheodoryKernel u).comp
        (measurable_cayleyCoordinate a))).aestronglyMeasurable
  have hleft : Integrable left weightedA := by
    apply Integrable.of_bound hleftMeas
      ((1 + a ^ 2 / b ^ 2) * ((1 + ‖w‖) / (1 - ‖w‖)))
    apply Filter.Eventually.of_forall
    intro spectral
    have hratioNonneg := resolvent_ratio_nonneg a b spectral hb
    have hratioBound := resolvent_ratio_le a b spectral hb
    have hkernel := caratheodoryKernel_norm_le
      (cayleyCoordinate b spectral) w (cayleyCoordinate_norm b spectral hb) hw
    dsimp only [left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hratioNonneg]
    exact mul_le_mul hratioBound hkernel (norm_nonneg _)
      (by positivity)
  have hright : Integrable right weightedA := by
    apply Integrable.of_bound hrightMeas
      ((a / b) * ((1 + ‖u‖) / (1 - ‖u‖)))
    apply Filter.Eventually.of_forall
    intro spectral
    have habNonneg : 0 ≤ a / b := div_nonneg ha.le hb.le
    have hkernel := caratheodoryKernel_norm_le
      (cayleyCoordinate a spectral) u (cayleyCoordinate_norm a spectral ha) hu
    dsimp only [right]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg habNonneg]
    exact mul_le_mul_of_nonneg_left hkernel habNonneg
  have hweightedEven : Measure.map (fun x : Real => -x) weightedA = weightedA := by
    dsimp only [weightedA]
    exact resolventWeightedMeasure_neg_invariant source a hEven
  have hpair : ∀ spectral, left spectral + left (-spectral) =
      right spectral + right (-spectral) := by
    intro spectral
    dsimp only [left, right, u]
    simpa only [neg_sq] using covariance_pair_identity a b spectral w ha hb hw
  have hintegrals := integral_eq_of_neg_pair weightedA hweightedEven
    left right hleft hright hpair
  have hratioTop : ∀ᵐ spectral ∂weightedA, ratio spectral < ⊤ := by
    exact Filter.Eventually.of_forall fun spectral => by
      dsimp only [ratio]
      exact ENNReal.ofReal_lt_top
  have hleftIntegral :
      caratheodoryFunction source b w = ∫ spectral, left spectral ∂weightedA := by
    unfold caratheodoryFunction cayleySpectralMeasure
    rw [MeasureTheory.integral_map
      (measurable_cayleyCoordinate b).aemeasurable
      (measurable_caratheodoryKernel w).aestronglyMeasurable]
    rw [resolventWeightedMeasure_scale_change source a b ha hb]
    change (∫ spectral, caratheodoryKernel (cayleyCoordinate b spectral) w
      ∂weightedA.withDensity ratio) = _
    rw [integral_withDensity_eq_integral_toReal_smul hratio hratioTop]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro spectral
    have hratioNonneg := resolvent_ratio_nonneg a b spectral hb
    dsimp only [ratio, left]
    rw [ENNReal.toReal_ofReal hratioNonneg]
    exact Complex.real_smul
  have hrightIntegral :
      ((a / b : Real) : Complex) * caratheodoryFunction source a u =
        ∫ spectral, right spectral ∂weightedA := by
    unfold caratheodoryFunction cayleySpectralMeasure
    rw [MeasureTheory.integral_map
      (measurable_cayleyCoordinate a).aemeasurable
      (measurable_caratheodoryKernel u).aestronglyMeasurable]
    rw [← integral_const_mul]
  rw [hleftIntegral, hrightIntegral]
  exact hintegrals

/-- For an even positive real source with finite resolvent masses, the full
Caratheodory covariance and its resolvent-budget specialization hold together. -/
theorem caratheodory_scale_covariance
    (source : Measure Real) (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (hEven : Measure.map (fun x : Real => -x) source = source)
    [IsFiniteMeasure (resolventWeightedMeasure source a)]
    [IsFiniteMeasure (resolventWeightedMeasure source b)]
    (w : Complex) (hw : ‖w‖ < 1) :
    caratheodoryFunction source b w =
        ((a / b : Real) : Complex) *
          caratheodoryFunction source a
            (realDiskAutomorphism (observerScaleParameter a b) w) ∧
      (resolventBudget source b : Complex) =
        ((a / b : Real) : Complex) *
          caratheodoryFunction source a
            (observerScaleParameter a b : Complex) := by
  constructor
  · exact caratheodory_scale_covariance_main source a b ha hb hEven w hw
  · rw [← caratheodory_zero_eq_budget source b hb]
    rw [caratheodory_scale_covariance_main source a b ha hb hEven 0 (by simp)]
    simp [realDiskAutomorphism]

#print axioms caratheodory_scale_covariance

end D5.S3.Weil.Budget.CaratheodoryScaleCovariance
