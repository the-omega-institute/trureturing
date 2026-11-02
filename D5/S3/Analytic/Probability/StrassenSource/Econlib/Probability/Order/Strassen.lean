/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.Approximation
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.WeakLimit

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
