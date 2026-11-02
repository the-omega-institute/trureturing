/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.Coupling
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Weak-* topology on `ProbDist`: Tightness, weak-limit extraction, marginal continuity

Generic facts about the weak-* topology on `ProbDist α = ProbabilityMeasure α`, isolated from any
order / Strassen / persuasion context. Three families:

* a sequence of probability measures concentrated on a fixed compact square is automatically
  **tight**, and **Prokhorov**'s theorem gives sequential compactness of the closure;
* marginal pushforward maps `π ↦ π.map Prod.fst` / `Prod.snd` are weak-* continuous;
* a weak limit of couplings is a coupling of the limit marginals, by uniqueness of weak limits.

## Main statements

* `isTight_of_supportsOn_Icc_prod` — `Icc a b × Icc a b`-supported sequences are tight.
* `exists_weak_limit_of_supportsOn_Icc_prod` — extract a weak-limit subsequence with the same
  compact support.
* `ProbabilityMeasure.continuous_map_fst`, `continuous_map_snd` — marginal pushforward continuity.
* `IsCoupling.of_weak_limit` — the coupling property is preserved at weak limits.

## Tags

probability measure, weak-* topology, tightness, prokhorov, coupling
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

@[expose] public section

namespace Econlib.Probability

/-- **Tightness on a compact support.** A sequence of probability measures on `ℝ × ℝ` all
concentrated on the compact set `Icc a b ×ˢ Icc a b` is a tight family. -/
lemma isTight_of_supportsOn_Icc_prod (a b : ℝ) (π : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hπ : ∀ n, (π n).toMeasure (Icc a b ×ˢ Icc a b) = 1) :
    IsTightMeasureSet { ρ : Measure (ℝ × ℝ) | ∃ n, (π n : Measure (ℝ × ℝ)) = ρ } := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  refine ⟨Icc a b ×ˢ Icc a b, isCompact_Icc.prod isCompact_Icc, ?_⟩
  rintro ρ ⟨n, rfl⟩
  have hmeas : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have h0 : (π n : Measure (ℝ × ℝ)) (Icc a b ×ˢ Icc a b)ᶜ = 0 :=
    (MeasureTheory.prob_compl_eq_zero_iff hmeas).mpr (hπ n)
  rw [h0]
  exact le_of_lt hε

/-- **Weak-limit extraction.** A sequence of probability measures on `ℝ × ℝ` all concentrated on a
compact square admits a weakly convergent subsequence. -/
lemma exists_weak_limit_of_supportsOn_Icc_prod (a b : ℝ)
    (π : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hπ : ∀ n, (π n).toMeasure (Icc a b ×ˢ Icc a b) = 1) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (πInf : ProbabilityMeasure (ℝ × ℝ)),
      Tendsto (fun n => π (φ n)) atTop (𝓝 πInf) ∧
      πInf.toMeasure (Icc a b ×ˢ Icc a b) = 1 := by
  -- Step 1: tightness of the range.
  have htight : IsTightMeasureSet
      {x : Measure (ℝ × ℝ) | ∃ μ ∈ Set.range π, (μ : Measure (ℝ × ℝ)) = x} := by
    have h := isTight_of_supportsOn_Icc_prod a b π hπ
    refine h.subset ?_
    rintro x ⟨μ, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  -- Step 2: Prokhorov gives compactness of closure.
  have hcomp : IsCompact (closure (Set.range π)) :=
    isCompact_closure_of_isTightMeasureSet htight
  -- Step 3: Extract convergent subsequence via sequential compactness (metrizable).
  have hmem : ∀ n, π n ∈ closure (Set.range π) := fun n =>
    subset_closure ⟨n, rfl⟩
  obtain ⟨πInf, _hmemInf, φ, hmono, htend⟩ := hcomp.tendsto_subseq (x := π) hmem
  refine ⟨φ, hmono, πInf, htend, ?_⟩
  -- Step 4: the limit still has mass 1 on the compact square (portmanteau closed).
  have hclosed : IsClosed (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    isClosed_Icc.prod isClosed_Icc
  have hmeas : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- By portmanteau: `limsup ((π (φ n)) F) ≤ πInf F` (in ENNReal via toMeasure).
  have hlimsup :=
    MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto htend hclosed
  -- Each `(π (φ n)).toMeasure F = 1` (from `hπ`), so the limsup of the constant-1 sequence is 1.
  have hlimsup_eq : Filter.limsup
      (fun i => (((π ∘ φ) i : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ))
        (Icc a b ×ˢ Icc a b)) Filter.atTop = 1 := by
    have hfun : (fun i => (((π ∘ φ) i : ProbabilityMeasure (ℝ × ℝ)) :
        Measure (ℝ × ℝ)) (Icc a b ×ˢ Icc a b))
        = fun _ => (1 : ENNReal) := funext fun i => hπ (φ i)
    rw [hfun, Filter.limsup_const]
  rw [hlimsup_eq] at hlimsup
  -- We have `1 ≤ πInf F`. Combined with `πInf F ≤ 1` we get equality.
  have hge : (1 : ENNReal) ≤ (πInf : Measure (ℝ × ℝ)) (Icc a b ×ˢ Icc a b) := hlimsup
  exact le_antisymm MeasureTheory.prob_le_one hge

/-- Marginal pushforward is continuous in the weak-* topology on probability measures. -/
lemma ProbabilityMeasure.continuous_map_fst :
    Continuous (fun π : ProbabilityMeasure (ℝ × ℝ) =>
      ProbabilityMeasure.map π measurable_fst.aemeasurable) :=
  MeasureTheory.ProbabilityMeasure.continuous_map (f := (Prod.fst : ℝ × ℝ → ℝ))
    continuous_fst

/-- Marginal pushforward is continuous in the weak-* topology on probability measures. -/
lemma ProbabilityMeasure.continuous_map_snd :
    Continuous (fun π : ProbabilityMeasure (ℝ × ℝ) =>
      ProbabilityMeasure.map π measurable_snd.aemeasurable) :=
  MeasureTheory.ProbabilityMeasure.continuous_map (f := (Prod.snd : ℝ × ℝ → ℝ))
    continuous_snd

/-- **Weak-limit marginals.** If `πₙ → πInf` weakly and each `πₙ` has marginals `(μₙ, νₙ)` with
`μₙ → μ`, `νₙ → ν`, then `πInf` has marginals `(μ, ν)`. -/
lemma IsCoupling.of_weak_limit {μ ν : ProbDist ℝ} {μ_seq ν_seq : ℕ → ProbDist ℝ}
    {π_seq : ℕ → ProbDist (ℝ × ℝ)} {πInf : ProbDist (ℝ × ℝ)}
    (hπcoup : ∀ n, IsCoupling (μ_seq n) (ν_seq n) (π_seq n))
    (hπlim : Tendsto (fun n => (π_seq n : ProbabilityMeasure (ℝ × ℝ))) atTop (𝓝 πInf))
    (hμlim : Tendsto (fun n => (μ_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 μ))
    (hνlim : Tendsto (fun n => (ν_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 ν)) :
    IsCoupling μ ν πInf := by
  -- Use continuity of the marginal pushforward composed with convergence of `πₙ → πInf`.
  have hfst_lim : Tendsto
      (fun n => ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
        measurable_fst.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map (πInf : ProbabilityMeasure (ℝ × ℝ))
        measurable_fst.aemeasurable)) :=
    (ProbabilityMeasure.continuous_map_fst.tendsto _).comp hπlim
  have hsnd_lim : Tendsto
      (fun n => ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
        measurable_snd.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map (πInf : ProbabilityMeasure (ℝ × ℝ))
        measurable_snd.aemeasurable)) :=
    (ProbabilityMeasure.continuous_map_snd.tendsto _).comp hπlim
  -- Each `ProbabilityMeasure.map (π_seq n) ... = μ_seq n` by the coupling hypothesis.
  -- `ProbDist.map (π_seq n) Prod.fst/.snd = μ_seq n / ν_seq n`, and `ProbDist.map` is
  -- definitionally `ProbabilityMeasure.map ... aemeasurable`.
  have hfst_eq : ∀ n, ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
      measurable_fst.aemeasurable = (μ_seq n : ProbabilityMeasure ℝ) :=
    fun n => (hπcoup n).fst_marginal
  have hsnd_eq : ∀ n, ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
      measurable_snd.aemeasurable = (ν_seq n : ProbabilityMeasure ℝ) :=
    fun n => (hπcoup n).snd_marginal
  -- Substitute into the convergence.
  rw [funext hfst_eq] at hfst_lim
  rw [funext hsnd_eq] at hsnd_lim
  -- Now both limits: `μ_seq n → map πInf fst` and `μ_seq n → μ`. Unique limit.
  refine ⟨?_, ?_⟩
  · exact tendsto_nhds_unique hμlim hfst_lim |>.symm
  · exact tendsto_nhds_unique hνlim hsnd_lim |>.symm

end Econlib.Probability
