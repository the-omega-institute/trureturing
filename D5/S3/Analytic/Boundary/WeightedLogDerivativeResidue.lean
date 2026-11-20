/- GID: D5/S3/Analytic/Boundary/WeightedLogDerivativeResidue
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/WeightedLogDerivativeResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite weighted logarithmic derivatives have an exact residue and pole criterion. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue

open Filter
open scoped Topology BigOperators

set_option autoImplicit false

private theorem local_log_deriv {f : ℂ → ℂ} {r : ℂ} {n : ℤ}
    (hf : MeromorphicAt f r) (hn : meromorphicOrderAt f r = n) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h r ∧
      logDeriv f =ᶠ[𝓝[≠] r] fun z => (n : ℂ) / (z - r) + h z := by
  obtain ⟨g, hg, hg0, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  have hfactor : f =ᶠ[𝓝[≠] r] (fun z => (z - r) ^ n * g z) := by
    exact heq.mono fun z hz => by simpa only [smul_eq_mul] using hz
  refine ⟨logDeriv g, hg.deriv.div hg hg0, (logDeriv_congr_nhdsNE hfactor).trans ?_⟩
  filter_upwards [
    eventually_mem_nhdsWithin (a := r) (s := {r}ᶜ),
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds] with z hz hgz hgn
  have hz0 : z - r ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
  have hsub : DifferentiableAt ℂ (fun w : ℂ => w - r) z := by fun_prop
  have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ n) (z - r) :=
    differentiableAt_zpow.mpr (Or.inl hz0)
  have hpowSub : DifferentiableAt ℂ (fun w : ℂ => (w - r) ^ n) z := by
    change DifferentiableAt ℂ ((fun w : ℂ => w ^ n) ∘ (fun w : ℂ => w - r)) z
    exact hpow.comp z hsub
  rw [logDeriv_fun_mul (f := fun w : ℂ => (w - r) ^ n) (g := g) z
    (zpow_ne_zero n hz0) hgn hpowSub hgz.differentiableAt]
  change logDeriv ((fun w : ℂ => w ^ n) ∘ (fun w : ℂ => w - r)) z + _ = _
  rw [logDeriv_comp (g := fun w : ℂ => w - r) (x := z) hpow hsub, logDeriv_zpow]
  simp

/-- The coefficient of the possible simple pole is the weighted sum of the
signed orders. The same coefficient determines whether the germ is removable. -/
theorem weighted_log_deriv_residue {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (a : ι → ℂ)
    (n : ι → ℤ) (r : ℂ) (hf : ∀ i ∈ s, MeromorphicAt (f i) r)
    (hn : ∀ i ∈ s, meromorphicOrderAt (f i) r = n i) :
    let F := fun z => ∑ i ∈ s, a i * logDeriv (f i) z
    let residue := ∑ i ∈ s, a i * (n i : ℂ)
    (∃ h : ℂ → ℂ, AnalyticAt ℂ h r ∧
      F =ᶠ[𝓝[≠] r] fun z => residue / (z - r) + h z) ∧
    (meromorphicOrderAt F r = -1 ↔ residue ≠ 0) ∧
    ((∃ h : ℂ → ℂ, AnalyticAt ℂ h r ∧ F =ᶠ[𝓝[≠] r] h) ↔ residue = 0) := by
  classical
  dsimp
  let F : ℂ → ℂ := fun z => ∑ i ∈ s, a i * logDeriv (f i) z
  let residue : ℂ := ∑ i ∈ s, a i * (n i : ℂ)
  choose h ha he using fun i hi => local_log_deriv (hf i hi) (hn i hi)
  let H : ℂ → ℂ := fun z => ∑ i ∈ s.attach, a i * h i i.property z
  have hH : AnalyticAt ℂ H r := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.mul (ha i i.property)
  have hEq : F =ᶠ[𝓝[≠] r] fun z => residue / (z - r) + H z := by
    have hall : ∀ᶠ z in 𝓝[≠] r, ∀ i : s,
        logDeriv (f i) z = (n i : ℂ) / (z - r) + h i i.property z := by
      exact Filter.eventually_all.mpr (fun i => he i i.property)
    filter_upwards [hall] with z hz
    change (∑ i ∈ s, a i * logDeriv (f i) z) =
      (∑ i ∈ s, a i * (n i : ℂ)) / (z - r) + ∑ i ∈ s.attach, a i * h i i.property z
    rw [← Finset.sum_attach s (fun i => a i * logDeriv (f i) z),
      ← Finset.sum_attach s (fun i => a i * (n i : ℂ)),
      div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hz i, mul_add, div_eq_mul_inv, mul_assoc]
  change (∃ h : ℂ → ℂ, AnalyticAt ℂ h r ∧
      F =ᶠ[𝓝[≠] r] fun z => residue / (z - r) + h z) ∧
    (meromorphicOrderAt F r = -1 ↔ residue ≠ 0) ∧
    ((∃ h : ℂ → ℂ, AnalyticAt ℂ h r ∧ F =ᶠ[𝓝[≠] r] h) ↔ residue = 0)
  refine ⟨⟨H, hH, hEq⟩, ?_⟩
  have hzero (hr : residue = 0) : F =ᶠ[𝓝[≠] r] H := by simpa [hr] using hEq
  have hmer : MeromorphicAt F r := by
    apply MeromorphicAt.congr _ hEq.symm
    have hregular : MeromorphicAt H r := hH.meromorphicAt
    fun_prop
  have hpole (hr : residue ≠ 0) : meromorphicOrderAt F r = -1 := by
    rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast]
    apply (meromorphicOrderAt_eq_int_iff hmer).mpr
    let g : ℂ → ℂ := fun z => residue + (z - r) * H z
    have hg : AnalyticAt ℂ g r := analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hH)
    refine ⟨g, hg, by simpa [g] using hr, ?_⟩
    filter_upwards [hEq, eventually_mem_nhdsWithin (a := r) (s := {r}ᶜ)] with z hz hzr
    have hnz : z - r ≠ 0 := sub_ne_zero.mpr (by simpa using hzr)
    rw [hz, zpow_neg_one, smul_eq_mul]
    dsimp only [g]
    field_simp
  have hnonneg (hr : residue = 0) : 0 ≤ meromorphicOrderAt F r :=
    hmer.meromorphicOrderAt_nonneg_iff.mpr ⟨H, hH, hzero hr⟩
  have hnot : ¬ (0 : WithTop ℤ) ≤ -1 := by
    rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast,
      ← WithTop.coe_zero, WithTop.coe_le_coe]
    decide
  refine ⟨⟨?_, hpole⟩, ⟨?_, fun hr => ⟨H, hH, hzero hr⟩⟩⟩
  · intro hp hr
    apply hnot
    exact hp ▸ hnonneg hr
  · intro hg
    by_contra hr
    apply hnot
    exact hpole hr ▸ hmer.meromorphicOrderAt_nonneg_iff.mpr hg

#print axioms weighted_log_deriv_residue

end D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue
