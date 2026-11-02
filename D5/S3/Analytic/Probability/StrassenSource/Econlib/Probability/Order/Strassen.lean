/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.Approximation
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.WeakLimit
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Strassen's theorem (martingale formulation)

**Strassen's theorem** characterizes the convex order on real-valued probability laws supported on
a compact interval by the existence of a **martingale coupling**: For `μ, ν : ProbDist ℝ` supported
on `[a, b]`, the convex order `μ ≼cx[a,b] ν` holds iff there is a joint law `π : ProbDist (ℝ × ℝ)`
with `Prod.fst`-marginal `μ`, `Prod.snd`-marginal `ν`, and `𝔼π[Y ∣ X] = X` almost surely.

Economically, this is the Blackwell / Rothschild–Stiglitz statement that `ν` is a mean-preserving
spread of `μ` iff `ν` arises from `μ` by adding conditionally mean-zero noise.

## Main statements

* `exists_martingaleCoupling_of_convexOrderOnIcc` — the convex order implies the existence of a
  martingale coupling.
* `strassen_iff` — the full equivalence between the convex order and the existence of a martingale
  coupling.

## References

* Hirsch, Francis, and Bernard Roynette. 2012. “A New Proof of Kellerer’s Theorem.” *ESAIM:
  Probability and Statistics* 16 : 48–60. [https://doi.org/10.1051/ps/2011164](https://doi.org/10.1051/ps/2011164).
* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).
* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).

## Tags

strassen, convex order, martingale coupling, mean-preserving spread, dilation
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Econlib.Probability

/-- **Strassen's theorem (hard direction)** (Strassen 1965). On compact support `[a, b]`, the
convex order `μ ≼cx[a,b] ν` implies the existence of a martingale coupling `π : ProbDist (ℝ × ℝ)`
with `Prod.fst`-marginal `μ`, `Prod.snd`-marginal `ν`, and `𝔼π[Y ∣ X] = X` almost surely. -/
theorem exists_martingaleCoupling_of_convexOrderOnIcc (a b : ℝ) {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) :
    ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling μ ν π := by
  have hμ_supp : μ.supportsOn (Icc a b) := h.support_left
  have hν_supp : ν.supportsOn (Icc a b) := h.support_right
  obtain ⟨p, q, happ⟩ := exists_discrete_approximation h
  rcases happ with ⟨hcx, hn_pos, hsameN, hp_uniform, hq_uniform, hpIcc, hqIcc, hp_lim, hq_lim⟩
  have h_exists : ∀ n, ∃ π : ProbDist (ℝ × ℝ),
      IsMartingaleCoupling (p n).toProbDist (q n).toProbDist π := fun n =>
    DiscreteLaw.exists_martingaleCoupling_uniform (p n) (q n) (hn_pos n) (hsameN n)
      (hp_uniform n) (hq_uniform n) (hcx n)
  classical
  let π : ℕ → ProbDist (ℝ × ℝ) := fun n => (h_exists n).choose
  have hπmart : ∀ n, IsMartingaleCoupling (p n).toProbDist (q n).toProbDist (π n) := fun n =>
    (h_exists n).choose_spec
  have hp_supp : ∀ n, (p n).toProbDist.supportsOn (Icc a b) := fun n =>
    (p n).toProbDist_supportsOn_of_atoms_mem measurableSet_Icc (hpIcc n)
  have hq_supp : ∀ n, (q n).toProbDist.supportsOn (Icc a b) := fun n =>
    (q n).toProbDist_supportsOn_of_atoms_mem measurableSet_Icc (hqIcc n)
  have hπcoup : ∀ n, IsCoupling (p n).toProbDist (q n).toProbDist (π n) := fun n =>
    { fst_marginal := (hπmart n).fst_marginal, snd_marginal := (hπmart n).snd_marginal }
  have hπ_supp : ∀ n, (π n).toMeasure (Icc a b ×ˢ Icc a b) = 1 := fun n =>
    (hπcoup n).supportsOn_Icc_prod (hp_supp n) (hq_supp n)
  obtain ⟨φ, hmono, πInf, hπlim, hInfSupp⟩ :=
    exists_weak_limit_of_supportsOn_Icc_prod a b π hπ_supp
  have hp_lim_sub : Tendsto
      (fun n => ((p (φ n)).toProbDist : ProbabilityMeasure ℝ)) atTop (𝓝 μ) :=
    hp_lim.comp hmono.tendsto_atTop
  have hq_lim_sub : Tendsto
      (fun n => ((q (φ n)).toProbDist : ProbabilityMeasure ℝ)) atTop (𝓝 ν) :=
    hq_lim.comp hmono.tendsto_atTop
  refine ⟨πInf, ?_⟩
  exact IsMartingaleCoupling.of_weak_limit
    (μ_seq := fun n => (p (φ n)).toProbDist) (ν_seq := fun n => (q (φ n)).toProbDist)
    (π_seq := fun n => π (φ n))
    hμ_supp hν_supp (fun n => hπmart (φ n)) (fun n => hπ_supp (φ n)) hInfSupp
    hπlim hp_lim_sub hq_lim_sub

/-- **Strassen's theorem** (Strassen 1965). On compact support `[a, b]`, the convex order
`μ ≼cx[a,b] ν` is equivalent to the existence of a martingale coupling of `μ` and `ν`. -/
theorem strassen_iff (a b : ℝ) {μ ν : ProbDist ℝ}
    (hμ : μ.supportsOn (Icc a b)) (hν : ν.supportsOn (Icc a b)) :
    ConvexOrderOnIcc a b μ ν ↔ ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling μ ν π := by
  refine ⟨exists_martingaleCoupling_of_convexOrderOnIcc a b, ?_⟩
  rintro ⟨π, hπ⟩
  exact hπ.convexOrderOnIcc hμ hν

end Econlib.Probability


namespace Econlib.Probability

lemma IsMartingaleCoupling.condExp_snd_eq_fst {μ ν : ProbDist ℝ}
    {π : ProbDist (ℝ × ℝ)} (h : IsMartingaleCoupling μ ν π) :
    π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] =ᵐ[π.toMeasure] Prod.fst := by
  let m := (borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ)
  have hm : m ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) := measurable_fst.comap_le
  have hxm : StronglyMeasurable[m] (Prod.fst : ℝ × ℝ → ℝ) :=
    (MeasurableSpace.comap_measurable _).stronglyMeasurable
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm h.integrable_snd
    (fun _ _ _ => h.integrable_fst.integrableOn) ?_ hxm.aestronglyMeasurable
  intro s hs _
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  let ψ : ℝ → ℝ := t.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator ht
  have hbψ : ∃ M, ∀ x, |ψ x| ≤ M := by
    refine ⟨1, ?_⟩
    intro x
    by_cases hx : x ∈ t <;> simp [ψ, hx]
  have heq := h.martingale ψ hψ hbψ
  have htest : (fun p : ℝ × ℝ => (p.2 - p.1) * ψ p.1) =
      (Prod.fst ⁻¹' t).indicator (fun p : ℝ × ℝ => p.2 - p.1) := by
    funext p
    by_cases hp : p.1 ∈ t <;> simp [ψ, hp]
  rw [htest, integral_indicator (ht.preimage measurable_fst),
    integral_sub h.integrable_snd.integrableOn h.integrable_fst.integrableOn] at heq
  linarith

lemma isMartingaleCoupling_of_condExp {a b : ℝ} {μ ν : ProbDist ℝ}
    (hμ : μ.toMeasure (Icc a b) = 1) (hν : ν.toMeasure (Icc a b) = 1)
    {π : ProbDist (ℝ × ℝ)}
    (hfst : π.toMeasure.map Prod.fst = μ.toMeasure)
    (hsnd : π.toMeasure.map Prod.snd = ν.toMeasure)
    (hce : π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] =ᵐ[π.toMeasure] Prod.fst) :
    IsMartingaleCoupling μ ν π := by
  have hxi : Integrable (Prod.fst : ℝ × ℝ → ℝ) π.toMeasure := by
    have hμi := ProbDist.integrable_id_of_supportsOn_Icc hμ
    rw [← hfst] at hμi
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mp hμi
  have hyi : Integrable (Prod.snd : ℝ × ℝ → ℝ) π.toMeasure := by
    have hνi := ProbDist.integrable_id_of_supportsOn_Icc hν
    rw [← hsnd] at hνi
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mp hνi
  refine ⟨ProbabilityMeasure.toMeasure_injective hfst,
    ProbabilityMeasure.toMeasure_injective hsnd, hxi, hyi, ?_⟩
  intro ψ hψ hbψ
  obtain ⟨M, hM⟩ := hbψ
  let m := (borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ)
  have hm : m ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) := measurable_fst.comap_le
  have hψm : StronglyMeasurable[m] (fun p : ℝ × ℝ => ψ p.1) :=
    (hψ.comp (MeasurableSpace.comap_measurable _)).stronglyMeasurable
  have hψae : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.1) π.toMeasure :=
    (hψ.comp measurable_fst).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂π.toMeasure, ‖ψ p.1‖ ≤ M :=
    Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hM p.1
  have hprod_y := hyi.mul_bdd hψae hbound
  have hprod_x := hxi.mul_bdd hψae hbound
  have hpull := condExp_mul_of_stronglyMeasurable_right hψm hprod_y hyi
  have hi : (∫ p, p.2 * ψ p.1 ∂π.toMeasure) = ∫ p, p.1 * ψ p.1 ∂π.toMeasure := by
    calc
      _ = ∫ p, (π.toMeasure[(fun q : ℝ × ℝ => q.2 * ψ q.1) | m]) p ∂π.toMeasure :=
        (integral_condExp hm).symm
      _ = ∫ p, p.1 * ψ p.1 ∂π.toMeasure := by
        apply integral_congr_ae
        filter_upwards [hpull, hce] with p hp hc
        exact hp.trans (by change (π.toMeasure[Prod.snd | m]) p * ψ p.1 = _; rw [hc])
  simp_rw [sub_mul]
  rw [integral_sub hprod_y hprod_x, hi, sub_self]

/-- Compact scalar convex order is equivalent to a genuine joint martingale law. -/
theorem compact_convex_order_iff_martingale (a b : ℝ) (μ ν : ProbabilityMeasure ℝ)
    (hμ : μ.toMeasure (Icc a b) = 1) (hν : ν.toMeasure (Icc a b) = 1) :
    ((∫ x, x ∂μ.toMeasure) = ∫ x, x ∂ν.toMeasure) ∧
      (∀ φ : ℝ → ℝ, ConvexOn ℝ (Icc a b) φ → ContinuousOn φ (Icc a b) →
        (∫ x, φ x ∂μ.toMeasure) ≤ ∫ x, φ x ∂ν.toMeasure) ↔
    ∃ π : ProbabilityMeasure (ℝ × ℝ),
      π.toMeasure.map Prod.fst = μ.toMeasure ∧
      π.toMeasure.map Prod.snd = ν.toMeasure ∧
      π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] =ᵐ[π.toMeasure] Prod.fst := by
  constructor
  · rintro ⟨hm, hc⟩
    obtain ⟨π, hπ⟩ := exists_martingaleCoupling_of_convexOrderOnIcc a b
      (μ := μ) (ν := ν) ⟨hμ, hν, hm, hc⟩
    exact ⟨π, hπ.fst_measure, hπ.snd_measure, hπ.condExp_snd_eq_fst⟩
  · rintro ⟨π, hfst, hsnd, hce⟩
    have hπ := isMartingaleCoupling_of_condExp hμ hν hfst hsnd hce
    exact ⟨hπ.mean_eq, fun φ hc ht => hπ.convex_expect_le hμ hν φ hc ht⟩

end Econlib.Probability
