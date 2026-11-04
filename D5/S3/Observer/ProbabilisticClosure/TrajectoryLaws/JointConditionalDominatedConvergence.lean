/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/JointConditionalDominatedConvergence
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/JointConditionalDominatedConvergence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Dominated varying observables have joint almost-sure and L1 conditional limits. -/

import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.Prod

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.JointConditionalDominatedConvergence

/-- The countable tail errors are bounded, decrease, dominate every later error,
and converge to zero. All supremum order reasoning is under the actual bound. -/
private theorem real_tail_control (a : ℕ → ℝ) (l G : ℝ)
    (ha : Tendsto a atTop (𝓝 l)) (hG : ∀ n, |a n| ≤ G) :
    let b := fun N => ⨆ k : ℕ, |a (N + k) - l|
    (∀ N, 0 ≤ b N ∧ b N ≤ 2 * |G|) ∧ Antitone b ∧
    (∀ N n, N ≤ n → |a n - l| ≤ b N) ∧ Tendsto b atTop (𝓝 0) := by
  dsimp only
  have hl : |l| ≤ G := le_of_tendsto ha.abs (Eventually.of_forall hG)
  have hb (N : ℕ) : BddAbove (range (fun k : ℕ => |a (N + k) - l|)) := by
    refine ⟨2 * |G|, ?_⟩
    rintro _ ⟨k, rfl⟩
    calc
      |a (N + k) - l| ≤ |a (N + k)| + |l| := abs_sub _ _
      _ ≤ G + G := add_le_add (hG _) hl
      _ ≤ 2 * |G| := by nlinarith [le_abs_self G]
  have hdom (N n : ℕ) (hn : N ≤ n) :
      |a n - l| ≤ ⨆ k : ℕ, |a (N + k) - l| := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact le_ciSup (hb N) k
  refine ⟨?_, ?_, hdom, ?_⟩
  · intro N
    refine ⟨(abs_nonneg _).trans (hdom N N le_rfl), ?_⟩
    exact ciSup_le fun k => (abs_sub _ _).trans
      ((add_le_add (hG _) hl).trans (by nlinarith [le_abs_self G]))
  · intro N M hNM
    apply ciSup_le
    intro k
    exact hdom N (M + k) (hNM.trans (Nat.le_add_right _ _))
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ha) (ε / 2) (half_pos hε)
    refine ⟨N, fun M hM => ?_⟩
    have hnonneg : 0 ≤ ⨆ k : ℕ, |a (M + k) - l| :=
      (abs_nonneg _).trans (hdom M M le_rfl)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    calc
      (⨆ k : ℕ, |a (M + k) - l|) ≤ ε / 2 := by
        apply ciSup_le
        intro k
        exact le_of_lt (by simpa [Real.dist_eq] using (hN (M+k)
          (hM.trans (Nat.le_add_right M k))))
      _ < ε := half_lt_self hε



universe u
variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Joint conditional dominated convergence along an increasing filtration. -/
theorem tendsto_condExp_of_dominated_convergence [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (y : ℕ → Ω → ℝ) (yLim g : Ω → ℝ)
    (hy : ∀ n, Measurable (y n)) (hyLim : Measurable yLim)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => y n ω) atTop (𝓝 (yLim ω)))
    (hg : Integrable g μ) (hbound : ∀ n, ∀ᵐ ω ∂μ, |y n ω| ≤ g ω) :
    (∀ᵐ ω ∂μ, Tendsto (fun k : ℕ × ℕ => μ[y k.1 | ℱ k.2] ω) atTop
      (𝓝 (μ[yLim | ⨆ j, ℱ j] ω))) ∧
    Tendsto (fun k : ℕ × ℕ => ∫ ω, |μ[y k.1 | ℱ k.2] ω - μ[yLim | ⨆ j, ℱ j] ω| ∂μ)
      atTop (𝓝 0) := by
  have hcommon : ∀ᵐ ω ∂μ, ∀ n, |y n ω| ≤ g ω := ae_all_iff.mpr hbound
  have hlimbound : ∀ᵐ ω ∂μ, |yLim ω| ≤ g ω := by
    filter_upwards [hlim, hcommon] with ω hω hb
    exact le_of_tendsto hω.abs (Eventually.of_forall hb)
  have hyi (n : ℕ) : Integrable (y n) μ :=
    hg.mono' (hy n).aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hbound n)
  have hyLi : Integrable yLim μ :=
    hg.mono' hyLim.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hlimbound)
  let b : ℕ → Ω → ℝ := fun N ω => ⨆ k : ℕ, |y (N + k) ω - yLim ω|
  have hbm (N : ℕ) : Measurable (b N) := by
    simpa only [b, Real.norm_eq_abs, Pi.sub_apply] using
      (Measurable.iSup fun k : ℕ => ((hy (N+k)).sub hyLim).norm)
  have hbp : ∀ᵐ ω ∂μ,
      (∀ N, 0 ≤ b N ω ∧ b N ω ≤ 2 * |g ω|) ∧
      Antitone (fun N => b N ω) ∧
      (∀ N n, N ≤ n → |y n ω - yLim ω| ≤ b N ω) ∧
      Tendsto (fun N => b N ω) atTop (𝓝 0) := by
    filter_upwards [hlim, hcommon] with ω hl hb
    exact real_tail_control (fun n => y n ω) (yLim ω) (g ω) hl hb
  have hb_bound (N : ℕ) : ∀ᵐ ω ∂μ, ‖b N ω‖ ≤ 2 * |g ω| := by
    filter_upwards [hbp] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hω.1 N).1]
    exact (hω.1 N).2
  have hbi (N : ℕ) : Integrable (b N) μ :=
    (hg.abs.const_mul 2).mono' (hbm N).aestronglyMeasurable (hb_bound N)
  have hb_integrals : Tendsto (fun N => ∫ ω, b N ω ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun ω => 2 * |g ω|)
        (fun N => (hbm N).aestronglyMeasurable) (hg.abs.const_mul 2) hb_bound
        (hbp.mono fun _ h => h.2.2.2))
  let M : MeasurableSpace Ω := ⨆ j, ℱ j
  have hM : M ≤ m0 := iSup_le fun j => ℱ.le j
  let q : ℕ → Ω → ℝ := fun N => μ[b N | M]
  have hqi (N : ℕ) : Integrable (q N) μ := integrable_condExp
  have hq0 (N : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ q N ω :=
    condExp_nonneg (hbp.mono fun _ h => (h.1 N).1)
  have hqs (N : ℕ) : ∀ᵐ ω ∂μ, q (N+1) ω ≤ q N ω :=
    condExp_mono (hbi (N+1)) (hbi N)
      (hbp.mono fun _ h => h.2.1 (Nat.le_succ N))
  have hqa : ∀ᵐ ω ∂μ, Antitone (fun N => q N ω) := by
    filter_upwards [ae_all_iff.mpr hqs] with ω hω
    exact antitone_nat_of_succ_le hω
  have hq_integrals : Tendsto (fun N => ∫ ω, q N ω ∂μ) atTop (𝓝 0) := by
    simpa only [q, integral_condExp hM] using hb_integrals
  have hqlim : ∀ᵐ ω ∂μ, Tendsto (fun N => q N ω) atTop (𝓝 0) := by
    apply tendsto_of_integral_tendsto_of_antitone hqi (integrable_zero Ω ℝ μ)
      (by simpa only [Pi.zero_apply, integral_zero] using hq_integrals) hqa (ae_all_iff.mpr hq0)
  have hbup : ∀ᵐ ω ∂μ, ∀ N, Tendsto (fun j => μ[b N | ℱ j] ω) atTop (𝓝 (q N ω)) :=
    ae_all_iff.mpr fun N => tendsto_ae_condExp (b N)
  have hyup := tendsto_ae_condExp (μ := μ) (ℱ := ℱ) yLim
  have hce (N n j : ℕ) : ∀ᵐ ω ∂μ, N ≤ n →
      |μ[y n | ℱ j] ω - μ[yLim | ℱ j] ω| ≤ μ[b N | ℱ j] ω := by
    by_cases hn : N ≤ n
    · have ho : (fun ω => |y n ω - yLim ω|) ≤ᵐ[μ] b N :=
        hbp.mono fun _ h => h.2.2.1 N n hn
      filter_upwards [condExp_sub (hyi n) hyLi (ℱ j),
        abs_condExp_ae_le_condExp_abs (μ := μ) (m := ℱ j) (y n - yLim),
        condExp_mono (m := ℱ j) ((hyi n).sub hyLi).abs (hbi N) ho] with ω hs ha ho _
      change μ[y n - yLim | ℱ j] ω = μ[y n | ℱ j] ω - μ[yLim | ℱ j] ω at hs
      change |μ[y n - yLim | ℱ j] ω| ≤ μ[|y n - yLim| | ℱ j] ω at ha
      rw [hs] at ha
      exact ha.trans ho
    · exact Eventually.of_forall fun _ h => (hn h).elim
  have hce_all : ∀ᵐ ω ∂μ, ∀ N n j, N ≤ n →
      |μ[y n | ℱ j] ω - μ[yLim | ℱ j] ω| ≤ μ[b N | ℱ j] ω :=
    ae_all_iff.mpr fun N => ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => hce N n j
  constructor
  · filter_upwards [hqlim, hbup, hyup, hce_all] with ω hq hb hy hc
    rw [Metric.tendsto_atTop]
    intro ε hε
    have he : 0 < ε / 3 := by positivity
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hq) (ε/3) he
    obtain ⟨Jb, hJb⟩ := (Metric.tendsto_atTop.mp (hb N)) (ε/3) he
    obtain ⟨Jy, hJy⟩ := (Metric.tendsto_atTop.mp hy) (ε/3) he
    refine ⟨(N, max Jb Jy), ?_⟩
    rintro ⟨n,j⟩ hnj
    change |μ[y n | ℱ j] ω - μ[yLim | M] ω| < ε
    have hn := hc N n j hnj.1
    have hq' : |q N ω| < ε/3 := by simpa [Real.dist_eq] using hN N le_rfl
    have hb' : |μ[b N | ℱ j] ω - q N ω| < ε/3 := by
      simpa [Real.dist_eq] using hJb j ((le_max_left _ _).trans hnj.2)
    have hy' : |μ[yLim | ℱ j] ω - μ[yLim | M] ω| < ε/3 := by
      simpa [Real.dist_eq, M] using hJy j ((le_max_right _ _).trans hnj.2)
    have ht := abs_sub_le (μ[y n | ℱ j] ω) (μ[yLim | ℱ j] ω) (μ[yLim | M] ω)
    have hqb := le_abs_self (μ[b N | ℱ j] ω - q N ω)
    have hqq := le_abs_self (q N ω)
    linarith
  · have hB : Tendsto (fun j => ∫ ω, |μ[yLim | ℱ j] ω - μ[yLim | M] ω| ∂μ)
        atTop (𝓝 0) := by
      have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (tendsto_eLpNorm_condExp (μ := μ) (ℱ := ℱ) yLim)
      have he (j : ℕ) : (eLpNorm (μ[yLim | ℱ j] - μ[yLim | M]) 1 μ).toReal =
          ∫ ω, |μ[yLim | ℱ j] ω - μ[yLim | M] ω| ∂μ := by
        have hi : Integrable (μ[yLim | ℱ j] - μ[yLim | M]) μ :=
          integrable_condExp.sub integrable_condExp
        rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
          ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
        simp only [Real.norm_eq_abs, Pi.sub_apply]
      change Tendsto (fun j => (eLpNorm (μ[yLim | ℱ j] - μ[yLim | M]) 1 μ).toReal)
        atTop (𝓝 0) at ht
      simpa only [he] using ht
    have hA_bound (n : ℕ) :
        (∫ ω, |y n ω - yLim ω| ∂μ) ≤ ∫ ω, b n ω ∂μ :=
      integral_mono_ae ((hyi n).sub hyLi).abs (hbi n)
        (hbp.mono fun _ h => h.2.2.1 n n le_rfl)
    have hD_bound (n j : ℕ) :
        (∫ ω, |μ[y n | ℱ j] ω - μ[yLim | M] ω| ∂μ) ≤
        (∫ ω, b n ω ∂μ) + ∫ ω, |μ[yLim | ℱ j] ω - μ[yLim | M] ω| ∂μ := by
      have h1 : Integrable (fun ω => |μ[y n | ℱ j] ω - μ[yLim | ℱ j] ω|) μ :=
        (integrable_condExp.sub integrable_condExp).abs
      have h2 : Integrable (fun ω => |μ[yLim | ℱ j] ω - μ[yLim | M] ω|) μ :=
        (integrable_condExp.sub integrable_condExp).abs
      have h3 : Integrable (fun ω => |μ[y n | ℱ j] ω - μ[yLim | M] ω|) μ :=
        (integrable_condExp.sub integrable_condExp).abs
      have hcon : (∫ ω, |μ[y n | ℱ j] ω - μ[yLim | ℱ j] ω| ∂μ) ≤
          ∫ ω, |y n ω - yLim ω| ∂μ := by
        calc
          _ = ∫ ω, |μ[y n - yLim | ℱ j] ω| ∂μ := by
            apply integral_congr_ae
            filter_upwards [condExp_sub (hyi n) hyLi (ℱ j)] with ω hω
            exact congrArg abs hω.symm
          _ ≤ _ := integral_abs_condExp_le (y n - yLim)
      calc
        _ ≤ ∫ ω, (|μ[y n | ℱ j] ω - μ[yLim | ℱ j] ω| +
            |μ[yLim | ℱ j] ω - μ[yLim | M] ω|) ∂μ :=
          integral_mono h3 (h1.add h2) (fun ω => abs_sub_le _ _ _)
        _ = _ := integral_add h1 h2
        _ ≤ _ := add_le_add (hcon.trans (hA_bound n)) le_rfl
    have hfst : Tendsto (fun k : ℕ × ℕ => k.1) atTop atTop := by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_fst
    have hsnd : Tendsto (fun k : ℕ × ℕ => k.2) atTop atTop := by
      rw [← prod_atTop_atTop_eq]
      exact tendsto_snd
    have hsum : Tendsto (fun k : ℕ × ℕ => (∫ ω, b k.1 ω ∂μ) +
          ∫ ω, |μ[yLim | ℱ k.2] ω - μ[yLim | M] ω| ∂μ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, add_zero] using
        (hb_integrals.comp hfst).add (hB.comp hsnd)
    exact squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _)
      (fun k => hD_bound k.1 k.2) hsum

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.JointConditionalDominatedConvergence
