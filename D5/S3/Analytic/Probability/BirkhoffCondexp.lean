/- GID: D5/S3/Analytic/Probability/BirkhoffCondexp
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/BirkhoffCondexp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-measure real time averages converge almost everywhere and in L1 to invariant conditional expectation. -/

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

import D5.S3.Analytic.Probability.BirkhoffPointwise
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Probability.BirkhoffCondexp

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α : Type*} {f : α → α} {g : α → ℝ} {x : α}

private noncomputable def sumSup (f : α → α) (g : α → ℝ) (x : α) : EReal :=
  ⨆ n : ℕ, (birkhoffSum f g n x : EReal)

private def divergentSet (f : α → α) (g : α → ℝ) : Set α :=
  {x | sumSup f g x = ⊤}

private lemma divergentSet_invariant : f x ∈ divergentSet f g ↔ x ∈ divergentSet f g := by
  simp only [divergentSet, sumSup, Set.mem_ofPred_eq]
  conv_rhs => rw [← sup_iSup_nat_succ]
  simp only [birkhoffSum_zero_apply, EReal.coe_zero, birkhoffSum_succ_apply', EReal.coe_add,
    max_eq_top, EReal.zero_ne_top, false_or, ← EReal.add_iSup]
  rw [EReal.add_eq_top_iff_eq_top_right (by simp) (by simp)]

private lemma limsup_birkhoffAverage_nonpos_of_notMem_divergentSet (hx : x ∉ divergentSet f g) :
    limsup (birkhoffAverage ℝ f g · x |>.toEReal) atTop ≤ 0 := by
  /- from `hx` hypothesis, the birkhoff sums are bounded above by some real `M` -/
  simp only [divergentSet, sumSup, Set.mem_ofPred_eq, iSup_eq_top, not_forall, not_exists,
    not_lt] at hx
  obtain ⟨M, hM, hbound⟩ := hx
  lift M to ℝ using ⟨hM.ne, ((EReal.bot_lt_coe _).trans_le (hbound 0)).ne'⟩
  /- hence the birkhoff averages are bounded by `M / n`, which tends to `0` -/
  refine le_of_le_of_eq (limsup_le_limsup (v := fun n : ℕ ↦ ((M / n : ℝ) : EReal)) ?_) ?_
  · refine Eventually.of_forall fun n ↦ EReal.coe_le_coe_iff.mpr ?_
    rw [birkhoffAverage, smul_eq_mul, div_eq_inv_mul]
    gcongr
    exact EReal.coe_le_coe_iff.mp (hbound n)
  · rw [← EReal.coe_zero]
    exact (EReal.tendsto_coe.mpr (tendsto_const_div_atTop_nhds_zero_nat M)).limsup_eq

variable [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

private private lemma measurable_divergentSet (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet (divergentSet f g) := by
  have h : Measurable (sumSup f g) := Measurable.iSup fun n ↦
    Measurable.coe_real_ereal <| Finset.measurable_sum _ fun j _ ↦ hg.comp (hf.iterate j)
  exact h (measurableSet_singleton ⊤)

private private lemma measurable_invariants_divergentSet (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet[invariants f] (divergentSet f g) :=
  ⟨measurable_divergentSet hf hg, funext fun _ ↦ propext divergentSet_invariant⟩

private private lemma setIntegral_in_divergentSet_nonneg (g_meas : Measurable g)
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    0 ≤ ∫ x in divergentSet f g, g x ∂μ := by
  have hD := measurable_divergentSet hf.measurable g_meas
  have hres : MeasurePreserving f (μ.restrict (divergentSet f g))
      (μ.restrict (divergentSet f g)) := by
    convert hf.restrict_preimage hD using 1
    congr 1
    exact Set.ext fun x ↦ divergentSet_invariant
  have hmax := BirkhoffPointwise.maximal_ergodic hres g_meas hg.restrict
  have hcover : divergentSet f g ⊆ {x | ∃ n, 0 < birkhoffSum f g n x} := by
    intro x hx
    have hx' := hx
    simp only [divergentSet, sumSup, Set.mem_setOf_eq, iSup_eq_top] at hx'
    obtain ⟨n, hn⟩ := hx' 0 (by simp)
    exact ⟨n, by exact_mod_cast hn⟩
  have heq : (μ.restrict (divergentSet f g)).restrict
      {x | ∃ n, 0 < birkhoffSum f g n x} = μ.restrict (divergentSet f g) := by
    apply Measure.restrict_eq_self.mpr
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
  simp_rw [h, birkhoffAverage_sub, birkhoffAverage_add,
    birkhoffAverage_of_comp_eq ℝ (show (fun _ ↦ ε) ∘ f = fun _ ↦ ε from rfl) (by norm_cast),
    birkhoffAverage_of_comp_eq ℝ hcomp (by norm_cast)]

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


end D5.S3.Analytic.Probability.BirkhoffCondexp
