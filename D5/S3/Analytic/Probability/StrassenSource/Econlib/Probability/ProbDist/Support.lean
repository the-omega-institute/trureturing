/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.Basic
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.Mixture
public import Mathlib.Analysis.Convex.Integral

/-!
# Support of a `ProbDist`

`d.supportsOn s` records that `s` carries probability one under `d`. The predicate is generic over
the measurable space; the lemmas below specialize to `ℝ`, where the order and `Icc` structure are
used to derive integrability of continuous statistics on a compact-interval support and membership
of the mean in that interval.

## Main definitions

* `ProbDist.supportsOn` — the predicate `d.toMeasure s = 1`, generic over the measurable space.

## Main statements

* `ProbDist.ae_mem_of_supportsOn`, `ProbDist.supportsOn_of_ae_mem` — support is equivalent to
  almost-everywhere membership.
* `ProbDist.supportsOn_map`, `ProbDist.supportsOn_mono`, `ProbDist.supportsOn_dirac`,
  `ProbDist.supportsOn_finMixture` — closure of support under pushforward, widening, Dirac masses,
  and finite mixtures.
* `ProbDist.integrable_of_supportsOn_Icc`, `ProbDist.expect_mem_Icc` — integrability and mean
  bounds for a law supported on a compact interval.

## Tags

probability distribution, support, probability measure
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

namespace ProbDist

/-- A probability law is supported on `s` if `s` has probability one. -/
def supportsOn {α : Type*} [MeasurableSpace α] (d : ProbDist α) (s : Set α) : Prop :=
  d.toMeasure s = 1

/-- Every law is supported on the whole line. -/
@[simp] lemma supportsOn_univ (d : ProbDist ℝ) : d.supportsOn Set.univ := by
  simp [supportsOn]

/-- Support on a measurable set `s` gives almost-everywhere membership in `s`. -/
lemma ae_mem_of_supportsOn {d : ProbDist ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : d.supportsOn s) : ∀ᵐ x ∂d.toMeasure, x ∈ s :=
  (ae_mem_iff_measure_eq hs.nullMeasurableSet).mpr (h.trans (measure_univ).symm)

/-- Almost-everywhere membership in a measurable set `s` gives support on `s`. -/
lemma supportsOn_of_ae_mem {d : ProbDist ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ᵐ x ∂d.toMeasure, x ∈ s) : d.supportsOn s :=
  ((ae_mem_iff_measure_eq hs.nullMeasurableSet).mp h).trans (measure_univ)

/-- If `f x ∈ s` almost everywhere under `d`, then the pushforward `map d f` is supported on `s`. -/
lemma supportsOn_map {d : ProbDist ℝ} {f : ℝ → ℝ} (hf : Measurable f) {s : Set ℝ}
    (hs : MeasurableSet s) (h : ∀ᵐ x ∂d.toMeasure, f x ∈ s) :
    (ProbDist.map d f hf).supportsOn s :=
  -- ae membership transfers along the pushforward: y ∈ s under `map f` ⟺ f x ∈ s under `d`.
  supportsOn_of_ae_mem hs <| by
    rw [ProbDist.map_toMeasure]
    exact (ae_map_iff hf.aemeasurable (p := (· ∈ s)) hs).mpr h

/-- Support widens along set inclusion: A law supported on `s` is supported on any `t ⊇ s`. -/
lemma supportsOn_mono {d : ProbDist ℝ} {s t : Set ℝ} (hst : s ⊆ t)
    (hs : d.supportsOn s) : d.supportsOn t :=
  -- 1 = d s ≤ d t ≤ 1 by monotonicity and the probability bound.
  le_antisymm prob_le_one (hs ▸ measure_mono hst)

/-- A point mass is supported on any measurable set containing its point. -/
lemma supportsOn_dirac {s : Set ℝ} (hs : MeasurableSet s) {x : ℝ} (hx : x ∈ s) :
    (ProbDist.dirac x).supportsOn s := by
  unfold supportsOn ProbDist.dirac
  simp [hs, hx]

/-- A finite mixture is supported on `s` if each component law is supported on `s`. -/
lemma supportsOn_finMixture {n : ℕ} (w : FinDist (Fin n))
    (ds : Fin n → ProbDist ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hds : ∀ i, (ds i).supportsOn s) :
    (ProbDist.finMixture w ds).supportsOn s := by
  unfold supportsOn
  have hcomp : ((ProbDist.finMixture w ds : ProbDist ℝ) : Measure ℝ) sᶜ = 0 := by
    rw [show (((ProbDist.finMixture w ds : ProbDist ℝ) : Measure ℝ) sᶜ) =
        ∑ i, ENNReal.ofReal (w.pmf i) * ((ds i : Measure ℝ) sᶜ) by
          simp [ProbDist.finMixture]]
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [mul_eq_zero]
    right
    exact (MeasureTheory.prob_compl_eq_zero_iff hs).mpr (hds i)
  exact (MeasureTheory.prob_compl_eq_zero_iff hs).mp hcomp

/-- A function continuous on `[a, b]` is integrable under a law supported on `[a, b]`. -/
lemma integrable_of_supportsOn_Icc {d : ProbDist ℝ} {a b : ℝ} {f : ℝ → ℝ}
    (h : d.supportsOn (Set.Icc a b)) (hf : ContinuousOn f (Set.Icc a b)) :
    Integrable f d.toMeasure := by
  have hind : Integrable ((Set.Icc a b).indicator f) d.toMeasure :=
    (hf.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hae :
      (fun x ↦ (Set.Icc a b).indicator f x) =ᵐ[d.toMeasure] f := by
    filter_upwards [d.ae_mem_of_supportsOn measurableSet_Icc h] with x hx
    simp [hx]
  exact (integrable_congr hae).mp hind

/-- The identity is integrable under a law supported on a compact interval. -/
lemma integrable_id_of_supportsOn_Icc {d : ProbDist ℝ} {a b : ℝ}
    (h : d.supportsOn (Set.Icc a b)) : Integrable id d.toMeasure :=
  d.integrable_of_supportsOn_Icc h continuousOn_id

/-- The mean of a law supported on `[a, b]` lies in `[a, b]`. -/
lemma expect_mem_Icc {d : ProbDist ℝ} {a b : ℝ}
    (h : d.supportsOn (Set.Icc a b)) : d.expect id ∈ Set.Icc a b := by
  have hmem : ∀ᵐ x ∂d.toMeasure, id x ∈ Set.Icc a b :=
    d.ae_mem_of_supportsOn measurableSet_Icc h
  have hint : Integrable id d.toMeasure := d.integrable_id_of_supportsOn_Icc h
  simpa [expect] using
    Convex.integral_mem (convex_Icc a b) isClosed_Icc hmem hint

end ProbDist

end Econlib.Probability
