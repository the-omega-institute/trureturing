/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform original trace logarithms and literal determinant period limits. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
import D5.S3.Quantum.Analysis.TrotterProduct

/-! Uniform limits for the original signed finite trace logarithms and determinants. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant

open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDeterminant

private lemma uniform_iff_error {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℂ → E} {f : ℂ → E} {s : Set ℂ} :
    TendstoUniformlyOn F f atTop s ↔
      Tendsto (fun x : ℕ × ℂ => F x.1 x.2 - f x.2)
        (atTop ×ˢ 𝓟 s) (𝓝 0) := by
  rw [Metric.tendstoUniformlyOn_iff, Metric.tendsto_nhds]
  simp only [eventually_prod_principal_iff, dist_eq_norm, sub_zero, norm_sub_rev]

private lemma uniform_tsum {ι : Type*} {F : ℕ → ι → ℂ → ℂ}
    {f : ι → ℂ → ℂ} {s : Set ℂ} {b : ι → ℝ} (hb : Summable b)
    (hF : ∀ a, TendstoUniformlyOn (fun N z => F N a z) (f a) atTop s)
    (hbound : ∀ N a z, z ∈ s → ‖F N a z‖ ≤ b a) :
    TendstoUniformlyOn (fun N z => ∑' a, F N a z) (fun z => ∑' a, f a z)
      atTop s := by
  have hf (a) (z) (hz : z ∈ s) : ‖f a z‖ ≤ b a :=
    le_of_tendsto ((hF a).tendsto_at hz).norm
      (Eventually.of_forall (fun N => hbound N a z hz))
  have ht := tendsto_tsum_of_dominated_convergence (hb.add hb)
    (fun a => uniform_iff_error.mp (hF a))
    (show ∀ᶠ x : ℕ × ℂ in atTop ×ˢ 𝓟 s,
        ∀ a, ‖F x.1 a x.2 - f a x.2‖ ≤ b a + b a from by
      rw [eventually_prod_principal_iff]
      exact Eventually.of_forall (fun N z hz a =>
        (norm_sub_le _ _).trans (add_le_add (hbound N a z hz) (hf a z hz))))
  simp only [tsum_zero] at ht
  apply uniform_iff_error.mpr
  apply ht.congr'
  rw [Filter.EventuallyEq, eventually_prod_principal_iff]
  refine Eventually.of_forall (fun N z hz => ?_)
  exact (hb.of_norm_bounded (fun a => hbound N a z hz)).tsum_sub
    (hb.of_norm_bounded (fun a => hf a z hz))

private lemma contraction_uniform {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (p : ℕ) (a : ℕ × ℕ) :
    TendstoUniformlyOn (fun N z => unit1ContractN N z p a)
      (fun z => unit1Contract z p a) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  have ht := (uniform_iff_error.mp
    (OriginalGaussianUniformCutoff.sectionOp_tendstoUniformlyOn hρ hρ1)).norm
  apply uniform_iff_error.mpr
  apply squeeze_zero_norm' (a := fun x : ℕ × ℂ =>
    (unit1Geo ρ a * (p : ℝ)) * ‖sectionOp x.1 x.2 - operator x.2‖) ?_
    (by simpa using ht.const_mul (unit1Geo ρ a * (p : ℝ)))
  rw [eventually_prod_principal_iff]
  filter_upwards [eventually_ge_atTop (max a.1 a.2 + 1)] with N hN z hz
  have hi : a.1 < N := by omega
  have hj : a.2 < N := by omega
  have hs : ‖sectionOp N z‖ ≤ 1 := (sectionOp_norm_le N (hz.trans_lt hρ1)).trans
    (le_of_lt (pow_lt_one₀ (norm_nonneg z) (hz.trans_lt hρ1) (by norm_num : (2 : ℕ) ≠ 0)))
  have ho : ‖operator z‖ ≤ 1 := (operator_norm_le (hz.trans_lt hρ1)).trans
    (le_of_lt (pow_lt_one₀ (norm_nonneg z) (hz.trans_lt hρ1) (by norm_num : (2 : ℕ) ≠ 0)))
  have hc : ‖((sectionOp N z ^ p - operator z ^ p) (basis a.1)) a.2‖ ≤
      ‖sectionOp N z ^ p - operator z ^ p‖ := by
    calc
      _ ≤ ‖(sectionOp N z ^ p - operator z ^ p) (basis a.1)‖ :=
        lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ _
      _ ≤ ‖sectionOp N z ^ p - operator z ^ p‖ * ‖basis a.1‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = _ := by simp [basis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simp only [unit1ContractN, unit1EntryN, unit1Contract, hi, hj, and_self, ite_true, ← mul_sub]
  rw [norm_mul]
  calc
    _ ≤ unit1Geo ρ a * ((p : ℝ) * ‖sectionOp N z - operator z‖) :=
      mul_le_mul (unit1Entry_bound hρ hz a.1 a.2)
        (hc.trans (by simpa only [one_pow, mul_one] using
          NormedSpace.norm_pow_sub_pow_le_of_norm_le (C := 1) le_rfl hs ho p))
        (norm_nonneg _)
        (by unfold unit1Geo; positivity)
    _ = _ := by ring

private lemma trace_uniform {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (p : ℕ) :
    TendstoUniformlyOn (fun N z => Matrix.trace (finiteSection N z ^ (p + 1)))
      (fun z => ∑' a : ℕ × ℕ, unit1Contract z p a)
      atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  simpa only [unit1ContractN_tsum] using
    uniform_tsum ((unit1Geo_summable hρ hρ1).mul_right ((ρ ^ 2) ^ p))
      (contraction_uniform hρ hρ1 p)
      (fun N a z hz => unit1ContractN_bound hρ hρ1 hz N p a)

/-- Uniform convergence of the literal finite trace logarithms on each closed subdisk,
including radius zero. -/
theorem finiteLog_tendstoUniformlyOn {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    TendstoUniformlyOn OriginalGaussianDeterminant.finiteLog
      OriginalGaussianDeterminant.gaussianLogDet atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  let b : ℕ → ℝ := fun k => (∑' a : ℕ × ℕ, unit1Geo ρ a) *
    (ρ ^ 2) ^ (2 * k + 1)
  have hb : Summable b := unit1Majorant_summable hρ hρ1
  have hterm (k : ℕ) : TendstoUniformlyOn
      (fun N z => Matrix.trace (finiteSection N z ^ (2 * (k + 1))) / (k + 1 : ℂ))
      (fun z => (∑' a : ℕ × ℕ, unit1Contract z (2 * k + 1) a) / (k + 1 : ℂ))
      atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    have he : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    have ht := (uniform_iff_error.mp (trace_uniform hρ hρ1 (2 * k + 1))).div_const
      (k + 1 : ℂ)
    apply uniform_iff_error.mpr
    simpa only [he, sub_div, zero_div] using ht
  have ht := uniform_tsum hb hterm
    (fun N k z hz => finiteLogTerm_bound hρ hρ1 hz N k)
  have hn := ht.neg
  change TendstoUniformlyOn finiteLog
    (fun z => -(∑' k : ℕ, (∑' a : ℕ × ℕ, unit1Contract z (2 * k + 1) a) /
      (k + 1 : ℂ))) atTop {z : ℂ | ‖z‖ ≤ ρ} at hn
  exact hn.uniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
    (fun z hz => finiteLog_tendsto (hz.trans_lt hρ1))

/-- The actual finite matrix is squared after cutoff, including N=0. Its determinant
converges uniformly to the existing complex period product on every closed subdisk. -/
theorem finite_determinants_tendstoUniformlyOn_period {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    TendstoUniformlyOn
      (fun N z => Matrix.det (1 - OriginalGaussianMatrix.finiteSection N z ^ 2))
      (fun z => Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - z ^ 2)) *
        D5.S3.Analytic.OriginalHalfBinomialPeriod.period (z ^ 2))
      atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  let b : ℕ → ℝ := fun k => (∑' a : ℕ × ℕ, unit1Geo ρ a) *
    (ρ ^ 2) ^ (2 * k + 1)
  let B : ℝ := ∑' k, b k
  have hb : Summable b := unit1Majorant_summable hρ hρ1
  have hfinite (N : ℕ) (z : ℂ) (hz : ‖z‖ ≤ ρ) : ‖finiteLog N z‖ ≤ B := by
    rw [finiteLog, norm_neg]
    exact tsum_of_norm_bounded hb.hasSum (fun k => finiteLogTerm_bound hρ hρ1 hz N k)
  have hlimit (z : ℂ) (hz : ‖z‖ ≤ ρ) : ‖gaussianLogDet z‖ ≤ B :=
    le_of_tendsto (finiteLog_tendsto (hz.trans_lt hρ1)).norm
      (Eventually.of_forall (fun N => hfinite N z hz))
  have hexp : UniformContinuousOn Complex.exp (Metric.closedBall (0 : ℂ) B) :=
    (isCompact_closedBall (0 : ℂ) B).uniformContinuousOn_of_continuous
      Complex.continuous_exp.continuousOn
  have ht : TendstoUniformlyOn (fun N z => Complex.exp (finiteLog N z))
      gaussianDet atTop {z : ℂ | ‖z‖ ≤ ρ} := hexp.comp_tendstoUniformlyOn_eventually
    (Eventually.of_forall (fun N z hz => mem_closedBall_zero_iff.mpr (hfinite N z hz)))
    (fun z hz => mem_closedBall_zero_iff.mpr (hlimit z hz))
    (finiteLog_tendstoUniformlyOn hρ hρ1)
  apply (ht.congr_right (fun z hz =>
    OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity
      (lt_of_le_of_lt hz hρ1))).congr
  exact Eventually.of_forall (fun N z hz =>
    (finite_determinant_identity N z (lt_of_le_of_lt hz hρ1)).symm)

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformDeterminant
