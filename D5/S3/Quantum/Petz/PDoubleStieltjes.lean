/- GID: D5/S3/Quantum/Petz/PDoubleStieltjes
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The positive diagonal and symmetric product Stieltjes representation of the logarithmic resolvent quotient. -/

import D5.S3.Quantum.Petz.DoubleStieltjesRepresentations
import D5.S3.Quantum.Petz.StieltjesRepresentation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace D5.S3.Quantum.Petz.PDoubleStieltjes

open Set MeasureTheory Filter
open scoped Topology
open D5.S3.Quantum.Petz.DoubleStieltjes
open D5.S3.Quantum.Petz.DoubleStieltjesMarginals
open D5.S3.Quantum.Petz.DoubleStieltjesRepresentations
open D5.S3.Quantum.Petz.StieltjesDensity
open D5.S3.Quantum.Petz.SymmetricKernel
open D5.S3.Quantum.PositiveResolvent.EulerResolvent
open D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference

private theorem Q_single {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) :
    IntegrableOn (fun s => rQ y z s / (x+s)) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), rQ y z s / (x+s)) = Q x y z := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ × ℝ → ℝ := fun p => A z p.1 p.2 / ((x+p.1)*(y+p.2))
  have hA := Q_double_stieltjes hx hy z
  have he : (fun s => ∫ t, f (s,t) ∂μ) =ᵐ[μ] fun s => rQ y z s / (x+s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hfg (t : ℝ) : f (s,t) = (A z s t / (y+t)) / (x+s) := by
      dsimp [f]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [integral_congr_ae (Eventually.of_forall hfg), integral_div,
      (A_marginal_eq_rQ hs hy hz hyz).2]
  refine ⟨hA.1.integral_prod_left.congr he, ?_⟩
  rw [← integral_congr_ae he, ← integral_prod f hA.1]
  exact hA.2

private theorem P_single {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) :
    IntegrableOn (fun s => rP y z s / (x+s)) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), rP y z s / (x+s)) = P x y z := by
  have hQ := Q_single hx hy hz hyz
  have hρ := StieltjesRepresentation.rho_integrable hx hy hz
  have he (s : ℝ) : rP y z s / (x+s) =
      2 * (rQ y z s / (x+s)) - 6 * (rho y z s / (x+s)) := by
    simp only [rho, if_neg hyz]
    ring
  constructor
  · exact ((hQ.1.const_mul 2).sub (hρ.const_mul 6)).congr
      (Eventually.of_forall fun s => (he s).symm)
  · rw [integral_congr_ae (Eventually.of_forall he),
      integral_sub (hQ.1.const_mul 2) (hρ.const_mul 6), integral_const_mul,
      integral_const_mul, hQ.2, StieltjesRepresentation.stieltjes_representation hx hy hz]
    unfold hs
    ring

private theorem P_double_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hyz : y ≠ z) :
    IntegrableOn (fun s => E s z / ((x+s)*(y+s))) (Ioi 0) ∧
    Integrable (fun p : ℝ × ℝ => B z p.1 p.2 / ((x+p.1)*(y+p.2)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) ∧
    (∫ s in Ioi (0 : ℝ), E s z / ((x+s)*(y+s))) +
      (∫ p : ℝ × ℝ, B z p.1 p.2 / ((x+p.1)*(y+p.2))
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) = P x y z := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let e : ℝ → ℝ := fun s => E s z / ((x+s)*(y+s))
  let f : ℝ × ℝ → ℝ := fun p => B z p.1 p.2 / ((x+p.1)*(y+p.2))
  let g : ℝ → ℝ := fun s => ∫ t, f (s,t) ∂μ
  have hP := P_single hx hy hz hyz
  have hfm : Measurable f := (B_measurable z).div (by fun_prop)
  have hem : Measurable e := by unfold e E; fun_prop
  have hrow (s : ℝ) (hs : 0 < s) : Integrable (fun t => f (s,t)) μ := by
    have h := (B_marginal hs hy hz hyz).1.div_const (x+s)
    apply h.congr
    filter_upwards with t
    dsimp [f]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hen : ∀ᵐ s ∂μ, 0 ≤ e s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp [e, E]
    exact div_nonneg (by positivity) (mul_pos (add_pos hx hs) (add_pos hy hs)).le
  have hfn : ∀ s : ℝ, 0 < s → ∀ᵐ t ∂μ, 0 ≤ f (s,t) := by
    intro s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (B_pos hz hs ht).le (mul_pos (add_pos hx hs) (add_pos hy ht)).le
  have hgn : ∀ᵐ s ∂μ, 0 ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact integral_nonneg_of_ae (hfn s hs)
  have heq : (fun s => rP y z s / (x+s)) =ᵐ[μ] fun s => e s + g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [(rP_marginal hs hy hz hyz).2]
    have hfg (t : ℝ) : f (s,t) = (B z s t / (y+t)) / (x+s) := by
      dsimp [f]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    dsimp [g, e, μ]
    rw [integral_congr_ae (Eventually.of_forall hfg), integral_div]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hei : Integrable e μ := by
    apply hP.1.mono_nonneg hem.aestronglyMeasurable hen
    filter_upwards [heq, hgn] with s he hg
    linarith
  have hgi : Integrable g μ := by
    apply hP.1.mono_nonneg hfm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable hgn
    filter_upwards [heq, hen] with s he he0
    linarith
  have hfi : Integrable f (μ.prod μ) := by
    apply (integrable_prod_iff hfm.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hrow s hs
    · apply hgi.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (integral_congr_ae ((hfn s hs).mono fun t ht => Real.norm_of_nonneg ht)).symm
  refine ⟨hei, hfi, ?_⟩
  rw [integral_prod f hfi, ← integral_add hei hgi, ← integral_congr_ae heq]
  exact hP.2

private theorem positive_resolvent_continuous {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {a c : α → ℝ} (ha : Measurable a) (hc : Measurable c)
    (han : ∀ᵐ p ∂μ, 0 ≤ a p) (hcn : ∀ᵐ p ∂μ, 0 ≤ c p)
    {b y : ℝ} (hb : 0 < b) (hby : b < y)
    (hi : Integrable (fun p => a p / (b+c p)) μ) :
    Integrable (fun p => a p / (y+c p)) μ ∧
    ContinuousAt (fun u : ℝ => ∫ p, a p / (u+c p) ∂μ) y := by
  have hdom (u : ℝ) (hu : b < u) : ∀ᵐ p ∂μ, ‖a p / (u+c p)‖ ≤ a p / (b+c p) := by
    filter_upwards [han, hcn] with p hap hcp
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hap (by linarith))]
    exact div_le_div_of_nonneg_left hap (by linarith) (by linarith)
  refine ⟨hi.mono' (ha.div (measurable_const.add hc)).aestronglyMeasurable (hdom y hby), ?_⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun p => a p / (b+c p))
    (Eventually.of_forall fun u => (ha.div (measurable_const.add hc)).aestronglyMeasurable)
    ((eventually_gt_nhds hby).mono fun u hu => hdom u hu) hi
  filter_upwards [hcn] with p hcp
  exact (continuousAt_const.div (continuousAt_id.add continuousAt_const)
    (show y+c p ≠ 0 from (show 0 < y+c p by linarith).ne')).tendsto

/-- Formula (12) holds at all positive nodes, including coincident parameters.
Both its diagonal and product integrals are absolutely convergent. -/
theorem P_double_stieltjes {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s => E s z / ((x+s)*(y+s))) (Ioi 0) ∧
    Integrable (fun p : ℝ × ℝ => B z p.1 p.2 / ((x+p.1)*(y+p.2)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) ∧
    P x y z = (∫ s in Ioi (0 : ℝ), E s z / ((x+s)*(y+s))) +
      (∫ p : ℝ × ℝ, B z p.1 p.2 / ((x+p.1)*(y+p.2))
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) := by
  by_cases hyz : y = z
  · subst y
    let μ : Measure ℝ := volume.restrict (Ioi 0)
    let e : ℝ → ℝ := fun s => E s z / (x+s)
    let a : ℝ × ℝ → ℝ := fun p => B z p.1 p.2 / (x+p.1)
    have hb : 0 < z/2 := by positivity
    have hbz : z/2 < z := by linarith
    have hbase := P_double_ne hx hb hz (by linarith : z/2 ≠ z)
    have hsupport : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, 0 < p.1 ∧ 0 < p.2 := by
      dsimp [μ]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    have hem : Measurable e := by dsimp [e, E]; fun_prop
    have ham : Measurable a := (B_measurable z).div (by fun_prop)
    have hen : ∀ᵐ s ∂μ, 0 ≤ e s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact div_nonneg (by dsimp [E]; positivity) (add_pos hx hs).le
    have han : ∀ᵐ p ∂μ.prod μ, 0 ≤ a p := by
      filter_upwards [hsupport] with p hp
      exact div_nonneg (B_pos hz hp.1 hp.2).le (add_pos hx hp.1).le
    have hcn : ∀ᵐ s ∂μ, 0 ≤ s :=
      (ae_restrict_mem measurableSet_Ioi).mono fun s hs => hs.le
    have hpn : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, 0 ≤ p.2 := hsupport.mono fun p hp => hp.2.le
    have heq (u s : ℝ) : e s / (u+s) = E s z / ((x+s)*(u+s)) := by
      dsimp [e]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    have haq (u : ℝ) (p : ℝ × ℝ) : a p / (u+p.2) =
        B z p.1 p.2 / ((x+p.1)*(u+p.2)) := by
      dsimp [a]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    have hebase : Integrable (fun s => e s / (z/2+s)) μ :=
      hbase.1.congr (Eventually.of_forall fun s => (heq (z/2) s).symm)
    have habase : Integrable (fun p => a p / (z/2+p.2)) (μ.prod μ) :=
      hbase.2.1.congr (Eventually.of_forall fun p => (haq (z/2) p).symm)
    have he := positive_resolvent_continuous μ hem measurable_id hen hcn hb hbz hebase
    have ha := positive_resolvent_continuous (μ.prod μ) ham measurable_snd han hpn hb hbz habase
    have hei : IntegrableOn (fun s => E s z / ((x+s)*(z+s))) (Ioi 0) :=
      he.1.congr (Eventually.of_forall (heq z))
    have hai : Integrable (fun p => B z p.1 p.2 / ((x+p.1)*(z+p.2))) (μ.prod μ) :=
      ha.1.congr (Eventually.of_forall (haq z))
    refine ⟨hei, hai, ?_⟩
    have hL : ContinuousAt (fun u : ℝ => (∫ s, E s z / ((x+s)*(u+s)) ∂μ) +
        ∫ p : ℝ × ℝ, B z p.1 p.2 / ((x+p.1)*(u+p.2)) ∂μ.prod μ) z := by
      convert he.2.add ha.2 using 1
      funext u
      congr 1
      · exact (integral_congr_ae (Eventually.of_forall (heq u))).symm
      · exact (integral_congr_ae (Eventually.of_forall (haq u))).symm
    have hpath : ContinuousAt (fun u : ℝ => (x,u,z)) z := by fun_prop
    have hhs : ContinuousAt (fun u : ℝ => hs x u z) z := by
      change ContinuousAt ((fun p : ℝ × ℝ × ℝ => hs p.1 p.2.1 p.2.2) ∘
        (fun u : ℝ => (x,u,z))) z
      exact (hs_continuousAt hx hz hz).comp (f := fun u : ℝ => (x,u,z)) hpath
    have hQ : ContinuousAt (fun u : ℝ => Q x u z) z := by
      change ContinuousAt ((fun p : ℝ × ℝ × ℝ => Q p.1 p.2.1 p.2.2) ∘
        (fun u : ℝ => (x,u,z))) z
      exact (Q_continuousAt hx hz hz).comp (f := fun u : ℝ => (x,u,z)) hpath
    have hP : ContinuousAt (fun u : ℝ => P x u z) z := by
      convert (hhs.const_mul 6).add (hQ.const_mul 2) using 1
      funext u
      dsimp [hs]
      ring
    have hsame : (fun u : ℝ => (∫ s, E s z / ((x+s)*(u+s)) ∂μ) +
        ∫ p : ℝ × ℝ, B z p.1 p.2 / ((x+p.1)*(u+p.2)) ∂μ.prod μ) =ᶠ[𝓝[≠] z]
        (fun u => P x u z) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hbz).filter_mono nhdsWithin_le_nhds] with u hune hu
      have huz : u ≠ z := by simpa using hune
      exact (P_double_ne hx (lt_trans hb hu) hz huz).2.2
    exact (tendsto_nhds_unique
      ((hL.tendsto.mono_left nhdsWithin_le_nhds).congr' hsame)
      (hP.tendsto.mono_left nhdsWithin_le_nhds)).symm
  · have h := P_double_ne hx hy hz hyz
    exact ⟨h.1, h.2.1, h.2.2.symm⟩

end D5.S3.Quantum.Petz.PDoubleStieltjes
