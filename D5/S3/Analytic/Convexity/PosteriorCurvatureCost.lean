/- GID: D5/S3/Analytic/Convexity/PosteriorCurvatureCost
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/PosteriorCurvatureCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous curvature truncations and the weak lower semicontinuity of posterior cost. -/
import D5.S3.Analytic.Convexity.CurvaturePerspectiveEndpoints
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.Semicontinuity.Basic

/-! The original curvature supplier is approximated without imposing finite endpoint costs. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Analytic.Convexity.PosteriorCurvatureCost

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation

variable {f : ℝ → ℝ}

private def one : Positive := ⟨1, by norm_num⟩
private def small (n : ℕ) : Positive :=
  ⟨1 / ((n : ℝ) + 1), by change (0 : ℝ) < _; positivity⟩
private def large (n : ℕ) : Positive :=
  ⟨(n : ℝ) + 1, by change (0 : ℝ) < _; positivity⟩

private lemma small_antitone : Antitone small := by
  intro m n hmn
  change 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1)
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

private lemma large_monotone : Monotone large := by
  intro m n hmn
  change (m : ℝ) + 1 ≤ (n : ℝ) + 1
  exact_mod_cast Nat.add_le_add_right hmn 1

private lemma lower_domains_monotone : Monotone (fun n => Icc (small n) one) :=
  fun _ _ h => Icc_subset_Icc (small_antitone h) le_rfl

private lemma upper_domains_monotone : Monotone (fun n => Ioc one (large n)) :=
  fun _ _ h => Ioc_subset_Ioc le_rfl (large_monotone h)

private lemma lower_domains_exhaust : (⋃ n, Icc (small n) one) = Iic one := by
  ext s
  simp only [mem_iUnion, mem_Icc, mem_Iic]
  constructor
  · rintro ⟨n, hn⟩
    exact hn.2
  · intro hs
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds s.property)).exists
    exact ⟨n, hn.le, hs⟩

private lemma upper_domains_exhaust : (⋃ n, Ioc one (large n)) = Ioi one := by
  ext s
  simp only [mem_iUnion, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨n, hn⟩
    exact hn.1
  · intro hs
    obtain ⟨n, hn⟩ := exists_nat_gt (s : ℝ)
    exact ⟨n, hs, (show (s : ℝ) ≤ (n : ℝ) + 1 by linarith)⟩

/-- Finite Bochner truncation of the original two curvature integrals. -/
def curvatureTruncation (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ) (u v : ℝ) : ℝ :=
  (∫ s in Icc (small n) one, max ((s : ℝ) * v - u) 0 ∂curvature hf) +
    ∫ s in Ioc one (large n), max (u - (s : ℝ) * v) 0 ∂curvature hf

private lemma lower_integrable (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ) (u v : ℝ) :
    IntegrableOn (fun s : Positive => max ((s : ℝ) * v - u) 0)
      (Icc (small n) one) (curvature hf) :=
  (((continuous_subtype_val.mul_const v).sub continuous_const).max
    continuous_const).continuousOn.integrableOn_Icc

private lemma upper_integrable (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ) (u v : ℝ) :
    IntegrableOn (fun s : Positive => max (u - (s : ℝ) * v) 0)
      (Ioc one (large n)) (curvature hf) :=
  ((continuous_const.sub (continuous_subtype_val.mul_const v)).max
    continuous_const).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem curvatureTruncation_nonneg (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ) (u v : ℝ) :
    0 ≤ curvatureTruncation hf n u v :=
  add_nonneg (integral_nonneg fun _ => le_max_right _ _)
    (integral_nonneg fun _ => le_max_right _ _)

theorem curvatureTruncation_continuous (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => curvatureTruncation hf n z.1 z.2) := by
  have hl : Continuous (fun z : ℝ × ℝ =>
      ∫ s in Icc (small n) one, max ((s : ℝ) * z.2 - z.1) 0 ∂curvature hf) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have hr : Continuous (fun z : ℝ × ℝ =>
      ∫ s in Icc one (large n), max (z.1 - (s : ℝ) * z.2) 0
        ∂(curvature hf).restrict (Ioi one)) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have he : Icc one (large n) ∩ Ioi one = Ioc one (large n) := by
    ext s
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
  simp only [Measure.restrict_restrict measurableSet_Icc, he] at hr
  exact hl.add hr

theorem curvatureTruncation_monotone (hf : ConvexOn ℝ (Ioi 0) f) (u v : ℝ) :
    Monotone (fun n => curvatureTruncation hf n u v) := by
  intro m n hmn
  apply add_le_add
  · exact setIntegral_mono_set (lower_integrable hf n u v)
      (Eventually.of_forall fun _ => le_max_right _ _)
      (Eventually.of_forall fun _ hx => lower_domains_monotone hmn hx)
  · exact setIntegral_mono_set (upper_integrable hf n u v)
      (Eventually.of_forall fun _ => le_max_right _ _)
      (Eventually.of_forall fun _ hx => upper_domains_monotone hmn hx)

private lemma ofReal_curvatureTruncation (hf : ConvexOn ℝ (Ioi 0) f)
    (n : ℕ) (u v : ℝ) :
    ENNReal.ofReal (curvatureTruncation hf n u v) =
      (∫⁻ s in Icc (small n) one, ENNReal.ofReal ((s : ℝ) * v - u) ∂curvature hf) +
        ∫⁻ s in Ioc one (large n), ENNReal.ofReal (u - (s : ℝ) * v) ∂curvature hf := by
  rw [curvatureTruncation, ENNReal.ofReal_add
    (integral_nonneg fun s : Positive => show 0 ≤ max ((s : ℝ) * v - u) 0
      from le_max_right _ _)
    (integral_nonneg fun s : Positive => show 0 ≤ max (u - (s : ℝ) * v) 0
      from le_max_right _ _),
    ofReal_integral_eq_lintegral_ofReal (lower_integrable hf n u v)
      (Eventually.of_forall fun _ => le_max_right _ _),
    ofReal_integral_eq_lintegral_ofReal (upper_integrable hf n u v)
      (Eventually.of_forall fun _ => le_max_right _ _)]
  simp

/-- The same scalar remainder, including infinite axis values, is the increasing
supremum of these finite continuous truncations. -/
theorem iSup_curvatureTruncation (hf : ConvexOn ℝ (Ioi 0) f) (u v : ℝ) :
    (⨆ n, ENNReal.ofReal (curvatureTruncation hf n u v)) = curvatureRemainder hf u v := by
  simp_rw [ofReal_curvatureTruncation]
  rw [← ENNReal.iSup_add_iSup_of_monotone
    (fun _ _ h => lintegral_mono_set (lower_domains_monotone h))
    (fun _ _ h => lintegral_mono_set (upper_domains_monotone h))]
  change _ = (∫⁻ s in Iic one, ENNReal.ofReal ((s : ℝ) * v - u) ∂curvature hf) +
    ∫⁻ s in Ioi one, ENNReal.ofReal (u - (s : ℝ) * v) ∂curvature hf
  rw [← lower_domains_exhaust, ← upper_domains_exhaust,
    setLIntegral_iUnion_of_directed _ lower_domains_monotone.directed_le,
    setLIntegral_iUnion_of_directed _ upper_domains_monotone.directed_le]

/-- The compact posterior interval carries its Borel measurable structure. -/
abbrev Posterior := ↥(Icc (0 : ℝ) 1)

/-- Actual continuous nonnegative posterior costs, with finite values at both ends. -/
def posteriorTruncation (hf : ConvexOn ℝ (Ioi 0) f) (n : ℕ) : C(Posterior, ℝ≥0) where
  toFun t := ⟨curvatureTruncation hf n t (1 - (t : ℝ)),
    curvatureTruncation_nonneg hf n _ _⟩
  continuous_toFun := Continuous.subtype_mk
    ((curvatureTruncation_continuous hf n).comp
      (continuous_subtype_val.prodMk (continuous_const.sub continuous_subtype_val))) _

/-- Extended posterior cost on the stock weak topology of finite Borel measures. -/
def posteriorCurvatureCost (hf : ConvexOn ℝ (Ioi 0) f) (ν : FiniteMeasure Posterior) : ℝ≥0∞ :=
  ∫⁻ t : Posterior, curvatureRemainder hf (t : ℝ) (1 - (t : ℝ)) ∂(ν : Measure Posterior)

/-- This representation is the live weak-topology proof: countable monotone convergence
in the posterior variable, followed by continuous finite-measure coordinates. -/
theorem posteriorCurvatureCost_eq_iSup (hf : ConvexOn ℝ (Ioi 0) f)
    (ν : FiniteMeasure Posterior) :
    posteriorCurvatureCost hf ν = ⨆ n, ∫⁻ t, (posteriorTruncation hf n t : ℝ≥0∞) ∂ν := by
  have he (t : Posterior) : curvatureRemainder hf (t : ℝ) (1 - (t : ℝ)) =
      ⨆ n, (posteriorTruncation hf n t : ℝ≥0∞) := by
    rw [← iSup_curvatureTruncation hf (t : ℝ) (1 - (t : ℝ))]
    exact iSup_congr fun n => ENNReal.ofReal_eq_coe_nnreal
      (curvatureTruncation_nonneg hf n _ _)
  simp only [posteriorCurvatureCost, he]
  apply lintegral_iSup
  · intro n
    exact (posteriorTruncation hf n).continuous.measurable.coe_nnreal_ennreal
  · intro m n hmn t
    exact ENNReal.coe_le_coe.mpr (curvatureTruncation_monotone hf _ _ hmn)

/-- Lower semicontinuity for all weakly convergent finite measures, hence for nets
without a countable-generation restriction. Both infinite endpoints remain allowed. -/
theorem posteriorCurvatureCost_lowerSemicontinuous (hf : ConvexOn ℝ (Ioi 0) f) :
    LowerSemicontinuous (posteriorCurvatureCost hf) := by
  simp only [show posteriorCurvatureCost hf = fun ν : FiniteMeasure Posterior =>
    ⨆ n, ∫⁻ t, (posteriorTruncation hf n t : ℝ≥0∞) ∂ν from
      funext (posteriorCurvatureCost_eq_iSup hf)]
  exact lowerSemicontinuous_iSup fun n =>
    (FiniteMeasure.continuous_lintegral_continuousMap (posteriorTruncation hf n)).lowerSemicontinuous

#print axioms iSup_curvatureTruncation
#print axioms posteriorCurvatureCost_eq_iSup
#print axioms posteriorCurvatureCost_lowerSemicontinuous

end D5.S3.Analytic.Convexity.PosteriorCurvatureCost
