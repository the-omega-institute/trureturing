/- GID: D5/S3/Quantum/Analysis/ModulationMaximalDomain
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/ModulationMaximalDomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive physical modulation has exactly the maximal coordinate multiplication derivative graph on actual L2 in every finite Euclidean dimension. -/

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace D5.S3.Quantum.Analysis.ModulationMaximalDomain

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "H" => Lp ℂ 2 (volume : Measure E)

/-- Actual positive physical phase multiplication on the a.e. L2 quotient. -/
def physicalModulation (hbar : ℝ) (b : E) (t : ℝ) (f : H) : H :=
  let phase : E → ℂ := fun x =>
    Complex.exp (((t * (inner ℝ b x / hbar) : ℝ) : ℂ) * Complex.I)
  let hm : MemLp (fun x => phase x * f x) 2 (volume : Measure E) := by
    have hc : Continuous phase := by dsimp [phase]; fun_prop
    apply MemLp.of_le_mul (c := 1) (Lp.memLp f)
      (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards [] with x
    simp [phase, Complex.norm_exp, Complex.mul_re]
  hm.toLp (fun x => phase x * f x)

/-- Exact strong derivative graph of physical modulation, with its maximal
coordinate multiplication domain. Dimension and direction may be zero. -/
theorem physical_modulation_hasDerivAt_iff (hbar : ℝ) (hhbar : 0 < hbar)
    (b : E) (f v : H) :
    HasDerivAt (fun t : ℝ => physicalModulation hbar b t f) v 0 ↔
      ∃ hbx : MemLp (fun x : E => (inner ℝ b x : ℂ) * f x) 2
          (volume : Measure E),
        v = (Complex.I / (hbar : ℂ)) •
          hbx.toLp (fun x : E => (inner ℝ b x : ℂ) * f x) := by
  let a : E → ℝ := fun x => inner ℝ b x / hbar
  let phase : ℝ → E → ℂ := fun t x => Complex.exp ((t * a x : ℝ) * Complex.I)
  let z : E → ℂ := fun x => (inner ℝ b x : ℂ) * f x
  let c : ℂ := Complex.I / (hbar : ℂ)
  let k : E → ℂ := fun x => c * z x
  let q : ℝ → E → ℂ := fun t x => t⁻¹ • ((phase t x - 1) * f x)
  let qLp : ℝ → H := fun t => t⁻¹ • (physicalModulation hbar b t f - f)
  have hhC : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar.ne'
  have hc : c ≠ 0 := div_ne_zero Complex.I_ne_zero hhC
  have hphase : ∀ t x, ‖phase t x‖ = 1 := by
    intro t x
    simp [phase, Complex.norm_exp, Complex.mul_re]
  have hformula : ∀ t, physicalModulation hbar b t f =ᵐ[volume]
      fun x => phase t x * f x := by
    intro t
    dsimp only [physicalModulation]
    exact MemLp.coeFn_toLp _
  have hzero : physicalModulation hbar b 0 f = f := by
    apply Lp.ext
    filter_upwards [hformula 0] with x hx
    simpa [phase] using hx
  have hm : ∀ t, MemLp (fun x => phase t x * f x) 2 (volume : Measure E) := by
    intro t
    have hp : Continuous (phase t) := by dsimp [phase, a]; fun_prop
    apply MemLp.of_le_mul (c := 1) (Lp.memLp f)
      (hp.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards [] with x
    simp [hphase]
  have hq : ∀ t, MemLp (q t) 2 (volume : Measure E) := by
    intro t
    convert ((hm t).sub (Lp.memLp f)).const_smul t⁻¹ using 1
    funext x
    simp only [q, Pi.smul_apply, Pi.sub_apply, sub_mul, one_mul]
  have hqformula : ∀ t, qLp t =ᵐ[volume] q t := by
    intro t
    filter_upwards [Lp.coeFn_smul t⁻¹ (physicalModulation hbar b t f - f),
      Lp.coeFn_sub (physicalModulation hbar b t f) f, hformula t] with x hsm hsub hp
    simp_all [qLp, q, sub_mul]
  have hqeq : ∀ t, (hq t).toLp (q t) = qLp t := by
    intro t
    exact Lp.ext ((hq t).coeFn_toLp.trans (hqformula t).symm)
  have hd : ∀ x t, HasDerivAt (fun r : ℝ => phase r x)
      (phase t x * ((a x : ℂ) * Complex.I)) t := by
    intro x t
    simpa [phase] using (((hasDerivAt_id t).mul_const (a x)).ofReal_comp.mul_const
      Complex.I).cexp
  have hpoint : ∀ x, Tendsto (fun t => q t x) (𝓝[≠] (0 : ℝ)) (𝓝 (k x)) := by
    intro x
    have ht := ((hd x 0).mul_const (f x)).tendsto_slope_zero
    convert ht using 1
    · funext t
      simp [q, phase, sub_mul]
    · congr 1
      simp [phase, k, c, z, a, Complex.ofReal_div]
      ring
  have hderiv_of_mem : ∀ hz : MemLp z 2 (volume : Measure E),
      HasDerivAt (fun t : ℝ => physicalModulation hbar b t f)
        (c • hz.toLp z) 0 := by
    intro hz
    have hk : MemLp k 2 (volume : Measure E) := hz.const_mul c
    have hphase_bound : ∀ t x, ‖phase t x - 1‖ ≤ ‖a x‖ * ‖t‖ := by
      intro t x
      have hl : LipschitzWith ‖a x‖₊ (fun r : ℝ => phase r x) :=
        lipschitzWith_of_nnnorm_deriv_le (fun r => (hd x r).differentiableAt) (by
          intro r
          rw [(hd x r).deriv]
          apply le_of_eq
          apply NNReal.eq
          simp [hphase])
      simpa [dist_eq_norm, phase] using hl.dist_le_mul t 0
    have hknorm : ∀ x, ‖k x‖ = ‖a x‖ * ‖f x‖ := by
      intro x
      simp [k, c, z, a, norm_div, Complex.norm_real]
      ring
    have hqb : ∀ t x, ‖q t x‖ ≤ ‖k x‖ := by
      intro t x
      by_cases ht : t = 0
      · simp [q, ht]
      · have htn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
        calc
          ‖q t x‖ = ‖t‖⁻¹ * (‖phase t x - 1‖ * ‖f x‖) := by
            simp [q]
          _ ≤ ‖t‖⁻¹ * ((‖a x‖ * ‖t‖) * ‖f x‖) := by
            gcongr
            exact hphase_bound t x
          _ = ‖k x‖ := by rw [hknorm]; field_simp
    have herror : ∀ t x, ‖q t x - k x‖ ≤ ‖(2 : ℂ) * k x‖ := by
      intro t x
      calc
        ‖q t x - k x‖ ≤ ‖q t x‖ + ‖k x‖ := norm_sub_le _ _
        _ ≤ ‖k x‖ + ‖k x‖ := add_le_add (hqb t x) le_rfl
        _ = ‖(2 : ℂ) * k x‖ := by simp; ring
    let bound : E → ℝ≥0∞ := fun x => ‖(2 : ℂ) * k x‖ₑ ^ (2 : ℝ)
    have hfin : ∫⁻ x : E, bound x ∂volume ≠ ∞ := by
      have hb := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        (hk.const_mul (2 : ℂ)).eLpNorm_lt_top
      simpa [bound] using hb.ne
    have hi : Tendsto (fun t => ∫⁻ x : E, ‖q t x - k x‖ₑ ^ (2 : ℝ) ∂volume)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hdct := tendsto_lintegral_filter_of_dominated_convergence'
        (μ := (volume : Measure E))
        (F := fun t x => ‖q t x - k x‖ₑ ^ (2 : ℝ)) (f := fun _ => 0) bound
        (Eventually.of_forall fun t => ((hq t).sub hk).aestronglyMeasurable.enorm.pow_const _)
        (Eventually.of_forall fun t => Eventually.of_forall fun x => by
          apply ENNReal.rpow_le_rpow _ (by norm_num)
          exact ENNReal.coe_le_coe.mpr (by exact_mod_cast herror t x))
        hfin (Eventually.of_forall fun x => by
          have ht : Tendsto (fun t => q t x - k x) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
            simpa using (hpoint x).sub (tendsto_const_nhds (x := k x))
          simpa using ht.enorm.ennrpow_const (2 : ℝ))
      simpa using hdct
    have hen : Tendsto (fun t => eLpNorm (q t - k) 2 (volume : Measure E))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa only [fun t => eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        ((hq t).sub hk).aestronglyMeasurable, ENNReal.toReal_ofNat, Pi.sub_apply,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        using hi.ennrpow_const (1 / (2 : ℝ))
    have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' q hq k hk).mpr hen
    have hkeq : hk.toLp k = c • hz.toLp z := by
      apply Lp.ext
      filter_upwards [hk.coeFn_toLp, Lp.coeFn_smul c (hz.toLp z), hz.coeFn_toLp]
        with x hx hs hz'
      simp_all [k]
    have hlim' : Tendsto qLp (𝓝[≠] (0 : ℝ)) (𝓝 (c • hz.toLp z)) := by
      simpa only [hqeq, hkeq] using hlim
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [zero_add, hzero] using hlim'
  constructor
  · intro hv
    have hlim : Tendsto qLp (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
      simpa only [zero_add, hzero] using hv.tendsto_slope_zero
    let tn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have htn : Tendsto tn atTop (𝓝[≠] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ?_⟩
      intro n
      change 1 / ((n : ℝ) + 1) ≠ 0
      positivity
    have hs : Tendsto (fun n => qLp (tn n)) atTop (𝓝 v) := hlim.comp htn
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
    have hrep : ∀ᵐ x : E, ∀ n : ℕ, qLp (tn n) x = q (tn n) x :=
      ae_all_iff.mpr (fun n => hqformula (tn n))
    have hvk : v =ᵐ[volume] k := by
      filter_upwards [hae, hrep] with x hx hxr
      have hqk := (hpoint x).comp (htn.comp hns.tendsto_atTop)
      have hqv : Tendsto (fun n => q (tn (ns n)) x) atTop (𝓝 (v x)) := by
        simpa only [hxr] using hx
      exact tendsto_nhds_unique hqv hqk
    have hk : MemLp k 2 (volume : Measure E) := (Lp.memLp v).ae_eq hvk
    have hz : MemLp z 2 (volume : Measure E) := by
      convert hk.const_mul c⁻¹ using 1
      funext x
      simp [k, hc]
    refine ⟨hz, ?_⟩
    exact hv.unique (hderiv_of_mem hz)
  · rintro ⟨hz, rfl⟩
    exact hderiv_of_mem hz

end D5.S3.Quantum.Analysis.ModulationMaximalDomain
