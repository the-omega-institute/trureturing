/- GID: D5/S3/Fourier/GaussianIsometry
   generality: G
   mirror-B: D5/B/S3/Fourier/GaussianIsometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real Hilbert spaces admit a common centered Gaussian L2 isometry. -/

import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace
universe u

namespace D5.S3.Fourier.GaussianIsometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every real Hilbert space has a centered Gaussian linear isometry
on one product probability space. -/
theorem exists_gaussian_isometry (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] :
    ∃ (ι : Type u)
      (W : H →ₗᵢ[ℝ] Lp ℝ 2 (Measure.infinitePi (fun _ : ι => gaussianReal 0 1))),
      (∀ h : H, HasLaw (fun ω => W h ω) (gaussianReal 0 (‖h‖ ^ 2).toNNReal)
        (Measure.infinitePi (fun _ : ι => gaussianReal 0 1))) ∧
      IsGaussianProcess (fun h ω => W h ω)
        (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) ∧
      ∀ h k, cov[fun ω => W h ω, fun ω => W k ω;
        Measure.infinitePi (fun _ : ι => gaussianReal 0 1)] = ⟪h, k⟫ := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℝ H
  have hcoord :
      let P := Measure.infinitePi (fun _ : ι => gaussianReal 0 1)
      ∃ Z : ι → Lp ℝ 2 P, Orthonormal ℝ Z ∧
        (∀ i, HasLaw (fun ω => Z i ω) (gaussianReal 0 1) P) ∧
        iIndepFun (fun i ω => Z i ω) P := by
    classical
    dsimp only
    let P := Measure.infinitePi (fun _ : ι => gaussianReal 0 1)
    have hLaw (i : ι) : HasLaw (fun ω : ι → ℝ => ω i) (gaussianReal 0 1) P :=
      ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
    let Z : ι → Lp ℝ 2 P := fun i => (hLaw i).hasGaussianLaw.memLp_two.toLp (fun ω => ω i)
    have heq (i : ι) : (fun ω => Z i ω) =ᵐ[P] (fun ω => ω i) :=
      MemLp.coeFn_toLp _
    have hz (i : ι) : HasLaw (fun ω => Z i ω) (gaussianReal 0 1) P :=
      (hLaw i).congr (heq i)
    have hind : iIndepFun (fun i (ω : ι → ℝ) => ω i) P :=
      iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
    have hindZ : iIndepFun (fun i ω => Z i ω) P := hind.congr (fun i => (heq i).symm)
    refine ⟨Z, ?_, hz, hindZ⟩
    apply orthonormal_iff_ite.mpr
    intro i j
    have hm (i : ι) : ∫ ω, Z i ω ∂P = 0 := by
      rw [(hz i).integral_eq, integral_id_gaussianReal]
    have hc : ⟪Z i, Z j⟫ = cov[fun ω => Z i ω, fun ω => Z j ω; P] := by
      rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), hm, hm, zero_mul, sub_zero,
        L2.inner_def]
      congr 1
      funext ω
      change Z j ω * Z i ω = Z i ω * Z j ω
      exact mul_comm _ _
    rw [hc]
    split_ifs with h
    · subst j
      rw [covariance_self (hz i).aemeasurable, (hz i).variance_eq, variance_id_gaussianReal]
      rfl
    · exact (hindZ.indepFun h).covariance_eq_zero (Lp.memLp _) (Lp.memLp _)
  let P := Measure.infinitePi (fun _ : ι => gaussianReal 0 1)
  obtain ⟨Z, hZ, hz, hind⟩ := hcoord
  change (∀ i, HasLaw (fun ω => Z i ω) (gaussianReal 0 1) P) at hz
  change iIndepFun (fun i ω => Z i ω) P at hind
  have hclosed : IsClosed {X : Lp ℝ 2 P | HasLaw (fun ω => X ω)
      (gaussianReal 0 (‖X‖ ^ 2).toNNReal) P} := by
    apply isSeqClosed_iff_isClosed.mp
    intro X x hX hx
    have hdist := (tendstoInMeasure_of_tendsto_Lp hx).tendstoInDistribution
      (fun n => (Lp.aestronglyMeasurable (X n)).aemeasurable)
    refine ⟨(Lp.aestronglyMeasurable x).aemeasurable, ?_⟩
    apply Measure.ext_of_charFun
    funext t
    have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hdist.tendsto t
    change Tendsto (fun n => charFun (P.map (fun ω => X n ω)) t) atTop
      (𝓝 (charFun (P.map (fun ω => x ω)) t)) at hcf
    simp_rw [(hX _).map_eq, charFun_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)] at hcf
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub] at hcf
    have hnorm : Tendsto (fun n => ‖X n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := hx.norm.pow 2
    have hexp : Tendsto (fun n => Complex.exp
        (- ((‖X n‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) atTop
        (𝓝 (Complex.exp (- ((‖x‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))) :=
      Complex.continuous_exp.continuousAt.tendsto.comp
        (((Complex.continuous_ofReal.continuousAt.tendsto.comp hnorm).neg.mul
          tendsto_const_nhds).div_const 2)
    simp only [neg_mul, neg_div] at hexp
    simpa only [charFun_gaussianReal, Complex.ofReal_zero, zero_mul, mul_zero,
      zero_sub, Real.coe_toNNReal _ (sq_nonneg _), neg_mul, neg_div] using
        tendsto_nhds_unique hcf hexp
  have hfinite (s : Finset ι) (a : ι → ℝ) :
      HasLaw (fun ω => (∑ i ∈ s, a i • Z i) ω)
        (gaussianReal 0 (‖∑ i ∈ s, a i • Z i‖ ^ 2).toNNReal) P := by
    classical
    let S : Lp ℝ 2 P := ∑ i ∈ s, a i • Z i
    have heq : (fun ω => S ω) =ᵐ[P] (fun ω => ∑ i ∈ s, a i * Z i ω) := by
      refine (Lp.coeFn_fun_finsetSum s (fun i => a i • Z i)).trans ?_
      filter_upwards [ae_all_iff.mpr (fun i : s => Lp.coeFn_smul (a i) (Z i))] with ω hω
      exact Finset.sum_congr rfl (fun i hi => hω ⟨i, hi⟩)
    have hg : HasGaussianLaw (fun ω => ∑ i ∈ s, a i * Z i ω) P := by
      have hh := (hind.restrict s).comp (fun i : s => fun x : ℝ => a i * x)
        (fun _ => measurable_const.mul measurable_id)
      have hs := hh.hasGaussianLaw_fun_sum (fun i : s =>
        (hz i).hasGaussianLaw.fun_smul (a i))
      change HasGaussianLaw (fun ω => ∑ i : s, a i * Z i ω) P at hs
      convert hs using 1
      funext ω
      exact (Finset.sum_attach s (fun i => a i * Z i ω)).symm
    have hgs : HasGaussianLaw (fun ω => S ω) P := hg.congr heq.symm
    have hm : ∫ ω, S ω ∂P = 0 := by
      rw [integral_congr_ae heq, integral_finsetSum]
      · simp only [integral_const_mul, (hz _).integral_eq, integral_id_gaussianReal,
          mul_zero, Finset.sum_const_zero]
      · exact fun i _ => (hz i).hasGaussianLaw.integrable.const_mul (a i)
    have hv : Var[fun ω => S ω; P] = ‖S‖ ^ 2 := by
      rw [variance_of_integral_eq_zero hgs.aemeasurable hm, ← real_inner_self_eq_norm_sq,
        L2.inner_def]
      congr 1
      funext ω
      simp [pow_two]
    exact ⟨hgs.aemeasurable, by rw [hgs.map_eq_gaussianReal, hm, hv]⟩
  let W : H →ₗᵢ[ℝ] Lp ℝ 2 P :=
    hZ.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry
  have hW (h : H) : HasLaw (fun ω => W h ω)
      (gaussianReal 0 (‖h‖ ^ 2).toNNReal) P := by
    have hsum := hZ.orthogonalFamily.hasSum_linearIsometry (b.repr h)
    have hresult : HasLaw (fun ω => W h ω) (gaussianReal 0 (‖W h‖ ^ 2).toNNReal) P := by
      apply hclosed.mem_of_tendsto hsum
      exact .of_forall (fun s => by
        simpa only [Set.mem_ofPred_eq, LinearIsometry.toSpanSingleton_apply] using
          hfinite s (b.repr h))
    simpa only [W.norm_map] using hresult
  refine ⟨ι, W, hW, ?_⟩
  classical
  constructor
  · constructor
    intro I
    constructor
    apply isGaussian_of_isGaussian_map
    intro L
    let a : I → ℝ := fun i => L (fun j => if i = j then 1 else 0)
    have heq : (fun ω => W (∑ i : I, a i • (i : H)) ω) =ᵐ[P]
        (fun ω => L (fun i : I => W i ω)) := by
      have he : W (∑ i : I, a i • (i : H)) = ∑ i : I, a i • W i := by simp only [map_sum, map_smul]
      rw [he]
      refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i : I => a i • W i)).trans ?_
      filter_upwards [ae_all_iff.mpr (fun i : I => Lp.coeFn_smul (a i) (W i))] with ω hω
      change (∑ i : I, (a i • W i) ω) = L.toLinearMap (fun i : I => W i ω)
      rw [L.toLinearMap.pi_apply_eq_sum_univ]
      apply Finset.sum_congr rfl
      intro i _
      rw [hω i]
      change a i * W i ω = W i ω * a i
      exact mul_comm _ _
    have hm : AEMeasurable (fun ω => I.restrict (fun h => W h ω)) P :=
      aemeasurable_pi_iff.mpr (fun i => (hW i).aemeasurable)
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hm]
    exact ((hW _).hasGaussianLaw.congr heq).isGaussian_map
  · intro h k
    have hm (h : H) : ∫ ω, W h ω ∂P = 0 := by
      rw [(hW h).integral_eq, integral_id_gaussianReal]
    rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), hm, hm, zero_mul, sub_zero]
    rw [← W.inner_map_map h k, L2.inner_def]
    congr 1
    funext ω
    change W h ω * W k ω = W k ω * W h ω
    exact mul_comm _ _

#print axioms exists_gaussian_isometry

end D5.S3.Fourier.GaussianIsometry
