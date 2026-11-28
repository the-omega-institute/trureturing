/- GID: D5/S3/LatticeGauge/ReflectionPositivity
   generality: G
   mirror-B: none(waiver:covered-by-lattice-reflection-positivity4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential Gram positivity and the Haar change of variables at the seam. -/

import D5.S3.LatticeGauge.Basic

/-!
Omega original.

Exponential Gram positivity and the Haar change of variables at the seam.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Matrix Filter

namespace Omega.LatticeGauge

private theorem integrable_conjugate {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) : Integrable (fun x => star (f x)) μ :=
  Complex.conjCLE.toContinuousLinearEquiv.integrable_comp_iff.mpr hf

private theorem expGram_diagonal {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsFiniteMeasure μ] (c : I → X → ℝ) (hc : ∀ i, Measurable (c i))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i x, ‖c i x‖ ≤ B)
    (f : X → ℂ) (hf : Integrable f μ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ r : ℝ, 0 ≤ r ∧ (∫ p : X × X, star (f p.1) * f p.2 *
      (Real.exp (β * ∑ i, c i p.1 * c i p.2) : ℂ) ∂(μ.prod μ)) = (r : ℂ) := by
  classical
  let dot (p : X × X) := ∑ i, c i p.1 * c i p.2
  let z (p : X × X) := β * dot p
  let C : ℝ := β * (Fintype.card I * (B * B))
  have hC : 0 ≤ C := by positivity
  have hz : Measurable z := measurable_const.mul
    (Finset.measurable_sum _ fun i _ => ((hc i).comp measurable_fst).mul
      ((hc i).comp measurable_snd))
  have hz_le (p : X × X) : ‖z p‖ ≤ C := by
    rw [show ‖z p‖ = β * ‖dot p‖ by simp [z, norm_mul, Real.norm_eq_abs, abs_of_nonneg hβ]]
    apply mul_le_mul_of_nonneg_left _ hβ
    calc
      ‖dot p‖ ≤ ∑ i, ‖c i p.1 * c i p.2‖ := norm_sum_le _ _
      _ ≤ ∑ _i : I, B * B := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul (hb i p.1) (hb i p.2) (norm_nonneg _) hB
      _ = _ := by simp [nsmul_eq_mul]
  let test (p : X × X) := star (f p.1) * f p.2
  have htest : Integrable test (μ.prod μ) := (integrable_conjugate hf).mul_prod hf
  let coeff (n : ℕ) (p : X × X) : ℝ := (z p) ^ n / n.factorial
  have hcMeas (n : ℕ) : Measurable (coeff n) := (hz.pow_const n).div_const _
  have hcBound (n : ℕ) (p : X × X) : ‖coeff n p‖ ≤ C ^ n / n.factorial := by
    rw [show ‖coeff n p‖ = ‖z p‖ ^ n / n.factorial by simp [coeff, norm_div, norm_pow]]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hz_le p) _) (by positivity)
  have hexp (t : ℝ) : HasSum (fun n : ℕ => t ^ n / n.factorial) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ, congrFun NormedSpace.exp_eq_tsum_div t]
    exact (Real.summable_pow_div_factorial t).hasSum
  have hsum : HasSum (fun n => ∫ p, test p * (coeff n p : ℂ) ∂(μ.prod μ))
      (∫ p, test p * (Real.exp (z p) : ℂ) ∂(μ.prod μ)) := by
    apply hasSum_integral_of_dominated_convergence (fun n p => ‖test p‖ * (C ^ n / n.factorial))
    · exact fun n => htest.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.measurable.comp (hcMeas n)).aestronglyMeasurable)
    · exact fun n => ae_of_all _ fun p => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hcBound n p) (norm_nonneg _)
    · exact ae_of_all _ fun p => ((hexp C).mul_left ‖test p‖).summable
    · simpa only [funext fun p => ((hexp C).mul_left ‖test p‖).tsum_eq] using
        htest.norm.mul_const (Real.exp C)
    · exact ae_of_all _ fun p => (Complex.ofRealCLM.hasSum (hexp (z p))).mul_left (test p)
  have hcoeff (n : ℕ) : ∃ r : ℝ, 0 ≤ r ∧
      (∫ p, test p * (coeff n p : ℂ) ∂(μ.prod μ)) = (r : ℂ) := by
    let word (j : Fin n → I) (x : X) : ℂ := ∏ a, (c (j a) x : ℂ)
    let weighted (j : Fin n → I) (x : X) := f x * word j x
    let scalar : ℝ := β ^ n / n.factorial
    have hweighted (j : Fin n → I) : Integrable (weighted j) μ := by
      apply hf.mul_bdd (c := B ^ n)
      · exact (Finset.measurable_prod _ fun a _ =>
          Complex.continuous_ofReal.measurable.comp (hc (j a))).aestronglyMeasurable
      · apply ae_of_all
        intro x
        calc
          ‖word j x‖ ≤ ∏ a : Fin n, ‖(c (j a) x : ℂ)‖ := Finset.norm_prod_le _ _
          _ ≤ ∏ _a : Fin n, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun a _ => by rw [Complex.norm_real]; exact hb (j a) x)
          _ = _ := by simp
    have hexpand (p : X × X) :
        test p * (coeff n p : ℂ) =
          (scalar : ℂ) * ∑ j : Fin n → I, star (weighted j p.1) * weighted j p.2 := by
      have hpow : (dot p) ^ n = ∑ j : Fin n → I, ∏ a, c (j a) p.1 * c (j a) p.2 := by
        simpa [dot] using Finset.sum_pow' Finset.univ (fun i => c i p.1 * c i p.2) n
      have hword (j : Fin n → I) (x : X) : star (word j x) = word j x := by
        unfold word
        rw [star_prod]
        simp only [show ∀ t : ℝ, star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal]
      have hfactor : coeff n p = scalar * ∑ j : Fin n → I, ∏ a, c (j a) p.1 * c (j a) p.2 := by
        change (β * dot p) ^ n / n.factorial = _
        rw [mul_pow, hpow]
        unfold scalar
        ring
      simp only [hfactor, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_prod,
        Finset.prod_mul_distrib, Finset.mul_sum, star_mul, weighted, hword]
      apply Finset.sum_congr rfl
      intro j _
      unfold test word
      ring
    rw [show (∫ p, test p * (coeff n p : ℂ) ∂(μ.prod μ)) =
      (∫ p, (scalar : ℂ) * ∑ j : Fin n → I, star (weighted j p.1) * weighted j p.2
        ∂(μ.prod μ)) from integral_congr_ae (ae_of_all _ hexpand)]
    rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
      (integrable_conjugate (hweighted j)).mul_prod (hweighted j))]
    have hwordIntegral (j : Fin n → I) :
        (∫ p : X × X, star (weighted j p.1) * weighted j p.2 ∂(μ.prod μ)) =
          (Complex.normSq (∫ x, weighted j x ∂μ) : ℂ) := by
      rw [integral_prod_mul (fun x => star (weighted j x)) (weighted j)]
      rw [show (∫ x, star (weighted j x) ∂μ) =
        star (∫ x, weighted j x ∂μ) from integral_conj]
      exact (mul_comm _ _).trans (Complex.mul_conj _)
    simp_rw [hwordIntegral, ← Complex.ofReal_sum, ← Complex.ofReal_mul]
    exact ⟨_, mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _), rfl⟩
  have hre := Complex.reCLM.hasSum hsum
  have him := Complex.imCLM.hasSum hsum
  refine ⟨_, ?_, Complex.ext (Complex.ofReal_re _).symm ?_⟩
  · change 0 ≤ Complex.reCLM (∫ p, test p * (Real.exp (z p) : ℂ) ∂(μ.prod μ))
    rw [← hre.tsum_eq]
    exact tsum_nonneg fun n => by
      obtain ⟨r, hr, heq⟩ := hcoeff n
      simpa [heq] using hr
  · change Complex.imCLM (∫ p, test p * (Real.exp (z p) : ℂ) ∂(μ.prod μ)) = 0
    rw [← him.tsum_eq]
    rw [show (fun n => Complex.imCLM (∫ p, test p * (coeff n p : ℂ) ∂(μ.prod μ))) =
      (fun _ : ℕ => 0) from funext fun n => by
        obtain ⟨r, _, heq⟩ := hcoeff n
        simp [heq], tsum_zero]

private theorem seam_measurePreserving {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    [Group H] [MeasurableMul₂ H] [MeasurableInv H] (μ : Measure X) [SFinite μ]
    (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    MeasurePreserving (fun q : (X × H) × (X × H) => ((q.1.1, q.2.1), q.1.2⁻¹ * q.2.2))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod ν) := by
  have inner : MeasurePreserving (fun q : H × X × H => (q.2.1, q.1, q.2.2))
      (ν.prod (μ.prod ν)) (μ.prod (ν.prod ν)) :=
    (measurePreserving_prodAssoc μ ν ν).comp
      (((Measure.measurePreserving_swap (μ := ν) (ν := μ)).prod (MeasurePreserving.id ν)).comp
        ((measurePreserving_prodAssoc ν μ ν).symm MeasurableEquiv.prodAssoc))
  have reorder : MeasurePreserving (fun q : (X × H) × (X × H) => ((q.1.1, q.2.1), q.1.2, q.2.2))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)) :=
    ((measurePreserving_prodAssoc μ μ (ν.prod ν)).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id μ).prod inner).comp (measurePreserving_prodAssoc μ ν (μ.prod ν)))
  exact ((MeasurePreserving.id (μ.prod μ)).prod
    (measurePreserving_snd.comp (measurePreserving_prod_inv_mul ν ν))).comp reorder

private theorem seam_integral {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    [Group H] [MeasurableMul₂ H] [MeasurableInv H] (μ : Measure X) [SFinite μ]
    (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (k : (X × X) × H → ℂ) (hk : AEStronglyMeasurable k ((μ.prod μ).prod ν)) :
    (∫ q : (X × H) × (X × H), k ((q.1.1, q.2.1), q.1.2⁻¹ * q.2.2) ∂((μ.prod ν).prod (μ.prod ν))) =
      ∫ q, k q ∂((μ.prod μ).prod ν) := by
  let e := seam_measurePreserving μ ν
  conv_rhs => rw [← e.map_eq]
  exact (integral_map e.measurable.aemeasurable (e.map_eq.symm ▸ hk)).symm

variable {n : Fin 4 → ℕ} {G : Type*} [Group G] {d : ℕ}
variable [MeasurableSpace G]

section Haar

variable [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]

/-- The Gibbs pairing of a reflected conjugate and an independent positive-half observable. -/
noncomputable def wilsonOSPair (D : GaugeData G d) (β : ℝ) (F H : (Link n → G) → ℂ) : ℂ :=
  (∫ u : Box n G, conj (F u.1.1) * H u.1.2 * (Real.exp (β * wilsonAction D u) : ℂ)
    ∂boxMeasure μ n) / (partition (n := n) μ D β : ℂ)

/-- Gibbs expectation of the reflected conjugate times the original half observable. -/
noncomputable def wilsonOS (D : GaugeData G d) (β : ℝ) (F : (Link n → G) → ℂ) : ℂ :=
  (∫ u : Box n G, conj (F u.1.1) * F u.1.2 * (Real.exp (β * wilsonAction D u) : ℂ)
    ∂boxMeasure μ n) / (partition (n := n) μ D β : ℂ)

private def gaugedFeature (D : GaugeData G d)
    (i : BoundaryLink n × Fin d × Fin d × Bool)
    (x : (Link n → G) × (BoundarySite n → G)) : ℝ :=
  feature D (boundaryGauge x.2 (boundary x.1) i.1) i.2.2.1 i.2.1 i.2.2.2

private theorem measurable_gaugedFeature (D : GaugeData G d)
    (i : BoundaryLink n × Fin d × Fin d × Bool) : Measurable (gaugedFeature D i) := by
  have h : Measurable (fun x : (Link n → G) × (BoundarySite n → G) =>
      boundaryGauge x.2 (boundary x.1) i.1) := by
    unfold boundaryGauge boundary
    fun_prop
  unfold gaugedFeature feature
  cases hi : i.2.2.2
  · exact Complex.measurable_re.comp ((D.measurable_entry i.2.2.1 i.2.1).comp h)
  · exact Complex.measurable_im.comp ((D.measurable_entry i.2.2.1 i.2.1).comp h)

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem abs_gaugedFeature_le (D : GaugeData G d)
    (i : BoundaryLink n × Fin d × Fin d × Bool) (x : (Link n → G) × (BoundarySite n → G)) :
    ‖gaugedFeature D i x‖ ≤ 1 := by
  cases hi : i.2.2.2
  · simpa [gaugedFeature, feature, hi, Real.norm_eq_abs] using
      (Complex.abs_re_le_norm _).trans (norm_entry_le D _ i.2.2.1 i.2.1)
  · simpa [gaugedFeature, feature, hi, Real.norm_eq_abs] using
      (Complex.abs_im_le_norm _).trans (norm_entry_le D _ i.2.2.1 i.2.1)

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem crossing_eq_gram (D : GaugeData G d)
    (x y : (Link n → G) × (BoundarySite n → G)) :
    (∑ e : BoundaryLink n,
      (D.rep (seamHolonomy (boundary x.1) (boundary y.1) (x.2⁻¹ * y.2) e)).trace.re) =
      ∑ i, gaugedFeature D i x * gaugedFeature D i y := by
  simp only [seam_pairing, Fintype.sum_prod_type, gaugedFeature]
  apply Finset.sum_congr rfl
  intro e _
  rw [← pairing_eq, ← pairing_mul D (boundary x.1 e)
    (boundaryGauge (x.2⁻¹ * y.2) (boundary y.1) e) (x.2 (bsrc e)) (x.2 (bdst e))]
  congr 1
  simp only [boundaryGauge, Pi.mul_apply, Pi.inv_apply]
  group

private noncomputable def weightedObs (D : GaugeData G d) (β : ℝ) (F : (Link n → G) → ℂ)
    (x : Link n → G) : ℂ := F x * (Real.exp (β * halfAction D x) : ℂ)

omit [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] in
private theorem weightedObs_integrable (D : GaugeData G d) (β : ℝ) (F : (Link n → G) → ℂ)
    (hF : Integrable F (configMeasure μ (Link n))) :
    Integrable (weightedObs D β F) (configMeasure μ (Link n)) :=
  hF.mul_bdd (c := Real.exp (|β| * (Fintype.card (Plaquette n) * d)))
    ((Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_halfAction D).const_mul β))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_bound (b := β) (abs_halfAction_le D x))

omit [μ.IsMulLeftInvariant] in
theorem wilson_product_integrable (D : GaugeData G d) (β : ℝ) (F H : (Link n → G) → ℂ)
    (hF : Integrable F (configMeasure μ (Link n))) (hH : Integrable H (configMeasure μ (Link n))) :
    Integrable (fun u : Box n G => conj (F u.1.1) * H u.1.2 *
      (Real.exp (β * wilsonAction D u) : ℂ)) (boxMeasure μ n) := by
  have hprod := (integrable_conjugate hF).mul_prod hH
  have hlift : Integrable (fun u : Box n G => conj (F u.1.1) * H u.1.2) (boxMeasure μ n) :=
    (measurePreserving_fst (ν := configMeasure μ (BoundarySite n))).integrable_comp_of_integrable hprod
  apply hlift.mul_bdd
  · exact (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_action D).const_mul β))).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_bound (b := β) (abs_action_le D x)

/-- The unnormalized reflected Wilson integral is a nonnegative real. -/
theorem wilson_reflected_integral_nonneg (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (F : (Link n → G) → ℂ) (hF : Integrable F (configMeasure μ (Link n))) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∫ u : Box n G, conj (F u.1.1) * F u.1.2 * (Real.exp (β * wilsonAction D u) : ℂ)
        ∂boxMeasure μ n) = (r : ℂ) := by
  let halfMeasure := configMeasure μ (Link n)
  let seamMeasure := configMeasure μ (BoundarySite n)
  let f : (Link n → G) × (BoundarySite n → G) → ℂ :=
    fun q => weightedObs D β F q.1
  have hf : Integrable f (halfMeasure.prod seamMeasure) :=
    measurePreserving_fst.integrable_comp_of_integrable (weightedObs_integrable μ D β F hF)
  obtain ⟨r, hr, heq⟩ := expGram_diagonal (halfMeasure.prod seamMeasure) (gaugedFeature D)
    (measurable_gaugedFeature D) 1 zero_le_one (abs_gaugedFeature_le D) f hf β hβ
  refine ⟨r, hr, ?_⟩
  rw [show boxMeasure μ n = (halfMeasure.prod halfMeasure).prod seamMeasure from rfl]
  rw [← seam_integral halfMeasure seamMeasure _ (wilson_product_integrable μ D β F F hF hF).aestronglyMeasurable, ← heq]
  apply integral_congr_ae (ae_of_all _ fun q => ?_)
  rw [show star (f q.1) = conj (f q.1) from rfl]
  simp only [wilsonAction, mul_add, Real.exp_add, Complex.ofReal_mul, crossing_eq_gram,
    f, weightedObs, map_mul, Complex.conj_ofReal]
  ring

end Haar

end Omega.LatticeGauge
