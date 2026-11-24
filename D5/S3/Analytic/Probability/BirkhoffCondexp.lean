/- GID: D5/S3/Analytic/Probability/BirkhoffCondexp
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/BirkhoffCondexp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Invariant conditional expectation is the a.e. and L1 time-average limit. -/

/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in
 docs/reports/licenses/birkhoff-condexp/mathlib-PR42078-LICENSE.txt.
Authors: Lua Viana Reis, Oliver Butterley

Adapted from lua-vr/mathlib4 revision ebc0f703f74bec1576e2ca3b078fb173ba11039f,
Mathlib/Dynamics/BirkhoffSum/Pointwise.lean.
Modifications: finite measures, native namespace, private helpers, restricted
maximal-ergodic argument and real L1 convergence.
-/

module

public import D5.S3.Analytic.Probability.BirkhoffPointwise
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Lift

/-!
# Finite-measure conditional-expectation ergodic limits

The invariant sigma algebra identifies the limit of real integrable time averages.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Analytic.Probability.BirkhoffCondexp

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} {g : α → ℝ} {x : α}

private def divergentSet (f : α → α) (g : α → ℝ) : Set α :=
  {x | ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < birkhoffSum f g n x}

private lemma divergentSet_invariant : f x ∈ divergentSet f g ↔ x ∈ divergentSet f g := by
  constructor
  · intro hx M
    obtain ⟨K, hK⟩ := exists_nat_gt ((M : ℝ) - g x)
    obtain ⟨n, hn⟩ := hx K
    refine ⟨n + 1, ?_⟩
    rw [birkhoffSum_succ_apply']
    linarith
  · intro hx M
    obtain ⟨K, hK⟩ := exists_nat_gt (max ((M : ℝ) + g x) 0)
    obtain ⟨n, hn⟩ := hx K
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      simp only [birkhoffSum_zero_apply] at hn
      exact (Nat.cast_nonneg K).not_gt hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨j, ?_⟩
    rw [birkhoffSum_succ_apply'] at hn
    have hMK : (M : ℝ) + g x < K := (le_max_left _ _).trans_lt hK
    linarith

private lemma limsup_birkhoffAverage_nonpos_of_notMem_divergentSet (hx : x ∉ divergentSet f g) :
    limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
  simp only [divergentSet, Set.mem_ofPred_eq, not_forall, not_exists, not_lt] at hx
  obtain ⟨M, hbound⟩ := hx
  refine le_of_le_of_eq
    (limsup_le_limsup (v := fun n : ℕ ↦ (((M : ℝ) / n : ℝ) : EReal)) ?_) ?_
  · refine Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr ?_
    rw [birkhoffAverage, smul_eq_mul, div_eq_inv_mul]
    gcongr
    exact hbound n
  · rw [← EReal.coe_zero]
    exact (EReal.tendsto_coe.mpr
      (tendsto_const_div_atTop_nhds_zero_nat (M : ℝ))).limsup_eq

variable [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

private lemma measurable_divergentSet (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet (divergentSet f g) := by
  have hS : ∀ n : ℕ, Measurable (birkhoffSum f g n) := fun n ↦
    Finset.measurable_sum _ fun j _ ↦ hg.comp (hf.iterate j)
  simpa only [divergentSet, Set.ofPred_forall, Set.ofPred_exists] using
    (MeasurableSet.iInter fun M : ℕ ↦ MeasurableSet.iUnion fun n : ℕ ↦
      measurableSet_lt (measurable_const : Measurable (fun _ : α ↦ (M : ℝ))) (hS n))

private lemma measurable_invariants_divergentSet (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet[invariants f] (divergentSet f g) :=
  ⟨measurable_divergentSet hf hg, funext fun _ ↦ propext divergentSet_invariant⟩

private lemma setIntegral_in_divergentSet_nonneg (g_meas : Measurable g)
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    0 ≤ ∫ x in divergentSet f g, g x ∂μ := by
  have hD := measurable_divergentSet hf.measurable g_meas
  have hres : MeasurePreserving f (μ.restrict (divergentSet f g))
      (μ.restrict (divergentSet f g)) := by
    convert hf.restrict_preimage hD using 1
    congr 1
    exact Set.ext fun x ↦ divergentSet_invariant.symm
  have hmax := BirkhoffPointwise.maximal_ergodic hres g_meas hg.restrict
  have hcover : divergentSet f g ⊆ {x | ∃ n, 0 < birkhoffSum f g n x} := by
    intro x hx
    obtain ⟨n, hn⟩ := hx 0
    exact ⟨n, by simpa using hn⟩
  have heq : (μ.restrict (divergentSet f g)).restrict
      {x | ∃ n, 0 < birkhoffSum f g n x} = μ.restrict (divergentSet f g) := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact ae_restrict_mem₀ hD.nullMeasurableSet |>.mono fun x hx ↦ hcover hx
  rwa [heq] at hmax

private lemma measure_divergentSet_eq_zero_of_condExp_neg (g_meas : Measurable g)
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, μ[g | invariants f] x < 0) :
    μ (divergentSet f g) = 0 := by
  by_contra hm
  apply (setIntegral_in_divergentSet_nonneg μ g_meas hf hg).not_gt
  have pos : 0 ≤ᵐ[μ.restrict (divergentSet f g)] fun x ↦ -μ[g|invariants f] x :=
    ae_restrict_of_ae <| h.mono fun _ hx ↦ (neg_pos.mpr hx).le
  rw [← setIntegral_condExp (invariants_le f) hg
      (measurable_invariants_divergentSet hf.measurable g_meas),
    ← Left.neg_pos_iff, ← integral_neg,
    setIntegral_pos_iff_support_of_nonneg_ae pos integrable_condExp.restrict.neg]
  refine (pos_iff_ne_zero.mpr hm).trans_le (measure_mono_ae ?_)
  filter_upwards [h] with x hx hxd
  exact ⟨by simpa using hx.ne, hxd⟩

private lemma ae_limsup_birkhoffAverage_nonpos_of_condExp_neg
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, μ[g | invariants f] x < 0) :
    ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
  -- Replace `g` by an a.e. equal measurable representative `g'`.
  set g' := hg.aemeasurable.mk g
  have g_eq : g =ᵐ[μ] g' := hg.aemeasurable.ae_eq_mk
  have h' : ∀ᵐ x ∂μ, μ[g' | invariants f] x < 0 := by
    filter_upwards [condExp_congr_ae g_eq, h] with x hx₁ hx₂
    rwa [← hx₁]
  have hae := ae_all_iff.mpr <| hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ g_eq
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_divergentSet_eq_zero_of_condExp_neg
    μ hg.aemeasurable.measurable_mk hf (hg.congr g_eq) h'), hae] with x hx hx'
  exact le_of_eq_of_le (limsup_congr <| Eventually.of_forall fun n ↦ by rw [hx' n])
    (limsup_birkhoffAverage_nonpos_of_notMem_divergentSet hx)

private lemma ae_tendsTo_birkhoffAverage_sub_condExp_nonneg (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ,
    limsup (birkhoffAverage ℝ f g · x - (μ[g|invariants f] x + ε) |>.toEReal) atTop ≤ 0 := by
  let h x := g x - (μ[g|invariants f] x + ε)
  have const_condExp_h : μ[h|invariants f] =ᵐ[μ] - fun _ ↦ ε :=
    calc
      _ =ᵐ[μ] μ[g|invariants f] - μ[μ[g|invariants f] + fun _ ↦ ε|invariants f] :=
        condExp_sub hg (by fun_prop) _
      _ =ᵐ[μ] μ[g|invariants f] - (μ[g|invariants f] + μ[fun _ ↦ ε|invariants f]) := by
        grw [condExp_add integrable_condExp (integrable_const _),
          condExp_condExp_of_le (le_of_eq rfl) (invariants_le f)]
      _ = - μ[fun _ ↦ ε|invariants f] := by
        ring
      _ = - fun _ ↦ ε := by
        rw [condExp_const (invariants_le f)]
  have limsup_nonpos : ∀ᵐ x ∂μ, limsup (birkhoffAverage ℝ f h · x |>.toEReal) atTop ≤ 0 := by
    apply ae_limsup_birkhoffAverage_nonpos_of_condExp_neg μ hf (by fun_prop)
    exact const_condExp_h.mono fun x hx ↦ by simp [hx, hε]
  have hcomp : μ[g|invariants f] ∘ f = μ[g|invariants f] :=
    comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable
  filter_upwards [limsup_nonpos] with x hx
  refine le_of_eq_of_le (limsup_congr ?_) hx
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have havg : birkhoffAverage ℝ f h n x =
      birkhoffAverage ℝ f g n x - (μ[g|invariants f] x + ε) := by
    change birkhoffAverage ℝ f (g - (μ[g|invariants f] + fun _ ↦ ε)) n x = _
    rw [birkhoffAverage_sub_apply, birkhoffAverage_add_apply]
    rw [birkhoffAverage_of_comp_eq ℝ hcomp hnR,
      birkhoffAverage_of_comp_eq ℝ (show (fun _ ↦ ε) ∘ f = fun _ ↦ ε from rfl) hnR]
  exact congrArg (fun r : ℝ ↦ (r : EReal)) havg.symm

private theorem ae_tendsTo_birkhoffAverage_condExp_real (hf : MeasurePreserving f μ μ)
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x)) := by
  have : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ∀ᶠ n in atTop, |birkhoffAverage ℝ f g n x - μ[g|invariants f] x| < (k + 1 : ℝ)⁻¹ := by
    refine ae_all_iff.mpr fun k ↦ ?_
    let δ := (k + 1 : ℝ)⁻¹ / 2
    have hδ : 0 < δ := by positivity
    have hδ' : (0 : EReal) < δ := by norm_cast
    have p₁ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hf hg hδ
    have p₂ := ae_tendsTo_birkhoffAverage_sub_condExp_nonneg μ hf hg.neg hδ
    filter_upwards [p₁, p₂, condExp_neg (μ := μ) g (invariants f)] with x hx₁ hx₂ hx₃
    filter_upwards [eventually_lt_of_limsup_lt (hx₁.trans_lt hδ'),
      eventually_lt_of_limsup_lt (hx₂.trans_lt hδ')] with m hm₁ hm₂
    norm_cast at hm₁ hm₂
    simp only [birkhoffAverage_neg, Pi.neg_apply, hx₃] at hm₂
    grind
  filter_upwards [this] with x hx
  apply Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hx k)
  exact ⟨N, fun n hn ↦ (hN n hn).trans (by rwa [one_div] at hk)⟩

omit [IsFiniteMeasure μ] in
private lemma integrable_average (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)
    (n : ℕ) : Integrable (birkhoffAverage ℝ f g n) μ := by
  unfold birkhoffAverage birkhoffSum
  exact (integrable_finsetSum _ fun j _ ↦
    (hf.iterate j).integrable_comp_of_integrable hg).smul ((n : ℝ)⁻¹)

omit [IsFiniteMeasure μ] in
private lemma integral_average (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)
    {n : ℕ} (hn : n ≠ 0) : ∫ x, birkhoffAverage ℝ f g n x ∂μ = ∫ x, g x ∂μ := by
  have hcomp (j : ℕ) : ∫ x, g (f^[j] x) ∂μ = ∫ x, g x ∂μ := by
    have hm := (hf.iterate j).map_eq
    have hmeas : AEStronglyMeasurable g (μ.map (f^[j])) := hm.symm ▸ hg.1
    exact (integral_map (hf.iterate j).measurable.aemeasurable hmeas).symm.trans
      (congrArg (fun ν ↦ ∫ x, g x ∂ν) hm)
  unfold birkhoffAverage birkhoffSum
  rw [integral_smul, integral_finsetSum (Finset.range n) (f := fun j x ↦ g (f^[j] x)) (fun j _ ↦
    (hf.iterate j).integrable_comp_of_integrable hg)]
  simp_rw [hcomp]
  simp [smul_eq_mul, hn]

private lemma tendsto_integral_abs_average_sub_condExp_of_nonneg
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) (hpos : ∀ x, 0 ≤ g x) :
    Tendsto (fun n ↦ ∫ x, |birkhoffAverage ℝ f g n x - μ[g|invariants f] x| ∂μ)
      atTop (𝓝 0) := by
  let c := μ[g|invariants f]
  have hc : Integrable c μ := integrable_condExp
  have hcpos : ∀ᵐ x ∂μ, 0 ≤ c x := condExp_nonneg (Eventually.of_forall hpos)
  have hApos (n : ℕ) (x : α) : 0 ≤ birkhoffAverage ℝ f g n x := by
    unfold birkhoffAverage birkhoffSum
    exact smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun j _ ↦ hpos (f^[j] x))
  have hmin_int (n : ℕ) : Integrable (fun x ↦ min (birkhoffAverage ℝ f g n x) (c x)) μ := by
    exact (integrable_average μ hf hg n).inf hc
  have hmin : Tendsto (fun n ↦ ∫ x, min (birkhoffAverage ℝ f g n x) (c x) ∂μ)
      atTop (𝓝 (∫ x, c x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence c
      (fun n ↦ (hmin_int n).1) hc
    · intro n
      filter_upwards [hcpos] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hApos n x) hx)]
      exact min_le_right _ _
    · filter_upwards [ae_tendsTo_birkhoffAverage_condExp_real μ hf hg] with x hx
      simpa only [c, min_self] using hx.min (tendsto_const_nhds (x := c x))
  have hlim : Tendsto (fun n ↦ (∫ x, g x ∂μ) + (∫ x, c x ∂μ) -
      2 * ∫ x, min (birkhoffAverage ℝ f g n x) (c x) ∂μ) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (∫ x, g x ∂μ) + (∫ x, c x ∂μ))
      (f := (atTop : Filter ℕ))).sub (hmin.const_mul 2)
    convert h using 1
    congr 1
    change 0 = (∫ x, g x ∂μ) + (∫ x, μ[g|invariants f] x ∂μ) -
      2 * ∫ x, μ[g|invariants f] x ∂μ
    rw [integral_condExp (invariants_le f)]
    ring
  apply hlim.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hid (x : α) : |birkhoffAverage ℝ f g n x - c x| =
      birkhoffAverage ℝ f g n x + c x -
        2 * min (birkhoffAverage ℝ f g n x) (c x) := by
    rcases le_total (birkhoffAverage ℝ f g n x) (c x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [integral_congr_ae (Eventually.of_forall hid),
    integral_sub (f := fun x ↦ birkhoffAverage ℝ f g n x + c x)
      ((integrable_average μ hf hg n).add hc) ((hmin_int n).const_mul 2),
    integral_add (integrable_average μ hf hg n) hc, integral_const_mul,
    integral_average μ hf hg hn]

private lemma tendsto_integral_abs_average_sub_condExp
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    Tendsto (fun n ↦ ∫ x, |birkhoffAverage ℝ f g n x - μ[g|invariants f] x| ∂μ)
      atTop (𝓝 0) := by
  let p := fun x ↦ max (g x) 0
  let q := fun x ↦ max (-g x) 0
  have hp : Integrable p μ := hg.pos_part
  have hq : Integrable q μ := hg.neg_part
  have hrep : g = p - q := by
    ext x
    change g x = max (g x) 0 - max (-g x) 0
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
  have hce : μ[g|invariants f] =ᵐ[μ] μ[p|invariants f] - μ[q|invariants f] := by
    rw [hrep]
    exact condExp_sub hp hq _
  have hplim := tendsto_integral_abs_average_sub_condExp_of_nonneg μ hf hp
    (fun x ↦ le_max_right (g x) 0)
  have hqlim := tendsto_integral_abs_average_sub_condExp_of_nonneg μ hf hq
    (fun x ↦ le_max_right (-g x) 0)
  apply squeeze_zero (fun n ↦ integral_nonneg fun x ↦ abs_nonneg _) _
    (by simpa only [add_zero] using hplim.add hqlim)
  intro n
  have hpi : Integrable (fun x ↦ |birkhoffAverage ℝ f p n x - μ[p|invariants f] x|) μ :=
    ((integrable_average μ hf hp n).sub integrable_condExp).abs
  have hqi : Integrable (fun x ↦ |birkhoffAverage ℝ f q n x - μ[q|invariants f] x|) μ :=
    ((integrable_average μ hf hq n).sub integrable_condExp).abs
  have hgi : Integrable (fun x ↦ |birkhoffAverage ℝ f g n x - μ[g|invariants f] x|) μ :=
    ((integrable_average μ hf hg n).sub integrable_condExp).abs
  rw [← integral_add hpi hqi]
  apply integral_mono_ae hgi (hpi.add hqi)
  filter_upwards [hce] with x hx
  rw [hx, hrep, birkhoffAverage_sub_apply]
  change |birkhoffAverage ℝ f p n x - birkhoffAverage ℝ f q n x -
      (μ[p|invariants f] x - μ[q|invariants f] x)| ≤ _
  calc
    _ = |(birkhoffAverage ℝ f p n x - μ[p|invariants f] x) -
        (birkhoffAverage ℝ f q n x - μ[q|invariants f] x)| := by congr 1; ring
    _ ≤ _ := by
      simpa only [sub_zero, zero_sub, abs_neg, Pi.add_apply] using
        (abs_sub_le (birkhoffAverage ℝ f p n x - μ[p|invariants f] x) 0
          (birkhoffAverage ℝ f q n x - μ[q|invariants f] x))

/-- The finite-measure pointwise and mean ergodic limits, without ergodicity. -/
theorem birkhoff_conditional_expectation (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    (∀ᵐ x ∂μ, Tendsto (birkhoffAverage ℝ f g · x) atTop (𝓝 (μ[g|invariants f] x))) ∧
    Tendsto (fun n ↦ ∫ x, |birkhoffAverage ℝ f g n x - μ[g|invariants f] x| ∂μ)
      atTop (𝓝 0) :=
  ⟨ae_tendsTo_birkhoffAverage_condExp_real μ hf hg,
    tendsto_integral_abs_average_sub_condExp μ hf hg⟩

end D5.S3.Analytic.Probability.BirkhoffCondexp
