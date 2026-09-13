/- GID: D5/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeReal/BisectionCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational midpoint bisection identifies its lower Cauchy class as a least upper bound. -/

import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Rational midpoint bisection for arbitrary sets of rational Cauchy classes.
The upper-bound membership test is classical. The lower endpoint need only
fail to be an upper bound; it need not bound the set below. Both rational
endpoint sequences are Cauchy, and their real images have the lower class
as common limit. This class is a least upper bound.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace D5.S3.ConceptDynamics.SpacetimeReal.CauchyCompletion

abbrev QSeq := CauSeq ℚ abs
abbrev QHat := CauSeq.Completion.Cauchy (abs : ℚ → ℚ)

def toReal : QHat ≃+* ℝ := Real.ringEquivCauchy.symm

instance completionOrder : LinearOrder QHat := LinearOrder.lift' toReal toReal.injective

instance completionOrderedRing : IsStrictOrderedRing QHat :=
  Function.Injective.isStrictOrderedRing toReal toReal.map_zero toReal.map_one
    toReal.map_add toReal.map_mul (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)

instance completionMetric : MetricSpace QHat :=
  MetricSpace.induced toReal toReal.injective inferInstance

end D5.S3.ConceptDynamics.SpacetimeReal.CauchyCompletion

namespace D5.S3.ConceptDynamics.SpacetimeReal.RationalApproximation

open D5.S3.ConceptDynamics.SpacetimeReal.CauchyCompletion

theorem rational_cauchy_iff_real (r : ℕ → ℚ) :
    IsCauSeq abs r ↔ CauchySeq (fun n => (r n : ℝ)) := by
  rw [Real.isCauSeq_iff_lift]
  simpa only [IsCauSeq, Real.norm_eq_abs] using
    (isCauSeq_iff_cauchySeq (u := fun n => (r n : ℝ)))

/-- Constant representatives of a rational Cauchy sequence tend to its own class.
This proof uses the Cauchy condition and the order on representatives only. -/
theorem rational_terms_tendsto (a : QSeq) :
    Tendsto (fun n => (a n : ℝ)) atTop (𝓝 (Real.mk a)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_rat_lt hε
  obtain ⟨N, hN⟩ := a.cauchy₂ hδ
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  apply lt_of_le_of_lt (Real.mk_near_of_forall_near (ε := (δ : ℝ)) ?_) hδε
  exact ⟨N, fun j hj => by exact_mod_cast (hN j hj n hn).le⟩

def dyadicRadius (n : ℕ) : ℝ := ((2 : ℝ)^n)⁻¹

theorem dyadic_radius_tendsto : Tendsto dyadicRadius atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((2 : ℝ)^n)⁻¹) atTop (𝓝 0)
  simpa only [inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1))

end D5.S3.ConceptDynamics.SpacetimeReal.RationalApproximation

namespace D5.S3.ConceptDynamics.SpacetimeReal.BisectionIntervals

open D5.S3.ConceptDynamics.SpacetimeReal.CauchyCompletion

def midpointStep (S : Set QHat) (p : ℚ × ℚ) : ℚ × ℚ := by
  classical
  let m : ℚ := (p.1 + p.2) / 2
  exact if (m : QHat) ∈ upperBounds S then (p.1, m) else (m, p.2)

def bisect (S : Set QHat) (l u : ℚ) : ℕ → ℚ × ℚ
  | 0 => (l, u)
  | n + 1 => midpointStep S (bisect S l u n)

abbrev lower (S : Set QHat) (l u : ℚ) (n : ℕ) := (bisect S l u n).1
abbrev upper (S : Set QHat) (l u : ℚ) (n : ℕ) := (bisect S l u n).2

theorem nonupper_lt_upper {S : Set QHat} {l u : ℚ}
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) : l < u := by
  by_contra h
  apply hl
  intro x hx
  exact (hu hx).trans (Rat.cast_le.mpr (le_of_not_gt h))

theorem midpoint_step_bounds (S : Set QHat) (p : ℚ × ℚ)
    (hl : (p.1 : QHat) ∉ upperBounds S) (hu : (p.2 : QHat) ∈ upperBounds S) :
    ((midpointStep S p).1 : QHat) ∉ upperBounds S ∧
    ((midpointStep S p).2 : QHat) ∈ upperBounds S := by
  dsimp only [midpointStep]
  split_ifs with hm
  · exact ⟨hl, hm⟩
  · exact ⟨hm, hu⟩

theorem midpoint_step_halves (S : Set QHat) (p : ℚ × ℚ) :
    (midpointStep S p).2 - (midpointStep S p).1 = (p.2 - p.1) / 2 := by
  dsimp only [midpointStep]
  split_ifs <;> dsimp <;> ring

/-- The lower endpoint is not an upper bound, the upper endpoint is an
upper bound, and the exact rational width halves at every step. -/
theorem bisection_invariant (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) (n : ℕ) :
    (lower S l u n : QHat) ∉ upperBounds S ∧
    (upper S l u n : QHat) ∈ upperBounds S ∧
    upper S l u n - lower S l u n = (u - l) / (2 : ℚ)^n := by
  induction n with
  | zero =>
    refine ⟨hl, hu, ?_⟩
    change u - l = (u - l) / (2 : ℚ)^0
    simp only [pow_zero, div_one]
  | succ n ih =>
    have hb := midpoint_step_bounds S (bisect S l u n) ih.1 ih.2.1
    refine ⟨hb.1, hb.2, ?_⟩
    change (midpointStep S (bisect S l u n)).2 -
      (midpointStep S (bisect S l u n)).1 = _
    rw [midpoint_step_halves, ih.2.2, pow_succ, div_div]

theorem bisection_nested (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) :
    Monotone (lower S l u) ∧ Antitone (upper S l u) ∧
      ∀ n, lower S l u n < upper S l u n := by
  have hlt : ∀ n, lower S l u n < upper S l u n := fun n =>
    nonupper_lt_upper (bisection_invariant S l u hl hu n).1
      (bisection_invariant S l u hl hu n).2.1
  refine ⟨monotone_nat_of_le_succ ?_, antitone_nat_of_succ_le ?_, hlt⟩
  · intro n
    have h := hlt n
    change (bisect S l u n).1 ≤ (midpointStep S (bisect S l u n)).1
    dsimp only [midpointStep]
    split_ifs <;> dsimp at * <;> linarith
  · intro n
    have h := hlt n
    change (midpointStep S (bisect S l u n)).2 ≤ (bisect S l u n).2
    dsimp only [midpointStep]
    split_ifs <;> dsimp at * <;> linarith

end D5.S3.ConceptDynamics.SpacetimeReal.BisectionIntervals

namespace D5.S3.ConceptDynamics.SpacetimeReal.BisectionCompletion

open D5.S3.ConceptDynamics.SpacetimeReal.CauchyCompletion
open D5.S3.ConceptDynamics.SpacetimeReal.BisectionIntervals
open D5.S3.ConceptDynamics.SpacetimeReal.RationalApproximation

theorem bisection_width_tendsto (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) :
    Tendsto (fun n => ((upper S l u n - lower S l u n : ℚ) : ℝ)) atTop (𝓝 0) := by
  have heq : (fun n => ((upper S l u n - lower S l u n : ℚ) : ℝ)) =
      (fun n => ((u - l : ℚ) : ℝ) * dyadicRadius n) := by
    funext n
    rw [(bisection_invariant S l u hl hu n).2.2]
    change (((u - l) / (2 : ℚ)^n : ℚ) : ℝ) =
      ((u - l : ℚ) : ℝ) * ((2 : ℝ)^n)⁻¹
    simp [div_eq_mul_inv]
  rw [heq]
  simpa using dyadic_radius_tendsto.const_mul ((u - l : ℚ) : ℝ)

theorem bisection_endpoints_cauchy (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) :
    IsCauSeq abs (lower S l u) ∧ IsCauSeq abs (upper S l u) := by
  obtain ⟨hlo, hup, hlt⟩ := bisection_nested S l u hl hu
  have hwidth := bisection_width_tendsto S l u hl hu
  constructor <;> apply (rational_cauchy_iff_real _).mpr
  · apply cauchySeq_of_le_tendsto_0' _ _ hwidth
    intro n m hnm
    have hlm : lower S l u m ≤ upper S l u n := (hlt m).le.trans (hup hnm)
    rw [Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (hlo hnm))]
    exact_mod_cast sub_le_sub_right hlm (lower S l u n)
  · apply cauchySeq_of_le_tendsto_0' _ _ hwidth
    intro n m hnm
    have hum : lower S l u n ≤ upper S l u m := (hlo hnm).trans (hlt m).le
    rw [Real.dist_eq, abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (hup hnm))]
    exact_mod_cast sub_le_sub_left hum (upper S l u n)

def lowerSeq (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) : QSeq :=
  ⟨lower S l u, (bisection_endpoints_cauchy S l u hl hu).1⟩

def upperSeq (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) : QSeq :=
  ⟨upper S l u, (bisection_endpoints_cauchy S l u hl hu).2⟩

theorem bisection_common_limit_real (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) :
    Tendsto (fun n => (lower S l u n : ℝ)) atTop (𝓝 (Real.mk (lowerSeq S l u hl hu))) ∧
    Tendsto (fun n => (upper S l u n : ℝ)) atTop (𝓝 (Real.mk (lowerSeq S l u hl hu))) := by
  have hlow := rational_terms_tendsto (lowerSeq S l u hl hu)
  refine ⟨hlow, hlow.congr_dist ?_⟩
  have heq : (fun n => dist (lower S l u n : ℝ) (upper S l u n : ℝ)) =
      (fun n => ((upper S l u n - lower S l u n : ℚ) : ℝ)) := by
    funext n
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg
      (by exact_mod_cast (sub_nonneg.mpr ((bisection_nested S l u hl hu).2.2 n).le))]
    push_cast
    rfl
  change Tendsto (fun n => dist (lower S l u n : ℝ) (upper S l u n : ℝ)) atTop (𝓝 0)
  rw [heq]
  exact bisection_width_tendsto S l u hl hu

/-- Upperness uses the upper endpoint limit. Leastness uses the lower endpoint
limit and its live non-upper-bound invariant. No IsLUB is assumed or selected. -/
theorem bisection_isLUB (S : Set QHat) (l u : ℚ)
    (hl : (l : QHat) ∉ upperBounds S) (hu : (u : QHat) ∈ upperBounds S) :
    IsLUB S (CauSeq.Completion.mk (lowerSeq S l u hl hu)) := by
  obtain ⟨hlo, hup⟩ := bisection_common_limit_real S l u hl hu
  constructor
  · intro x hx
    change toReal x ≤ Real.mk (lowerSeq S l u hl hu)
    apply ge_of_tendsto hup
    apply Eventually.of_forall
    intro n
    have h := (bisection_invariant S l u hl hu n).2.1 hx
    change toReal x ≤ toReal (upper S l u n : QHat) at h
    simpa only [map_ratCast] using h
  · intro b hb
    change Real.mk (lowerSeq S l u hl hu) ≤ toReal b
    by_contra h
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hlo).1 (toReal b) (lt_of_not_ge h)).exists
    apply (bisection_invariant S l u hl hu n).1
    intro x hx
    apply (hb hx).trans
    change toReal b ≤ toReal (lower S l u n : QHat)
    simpa only [map_ratCast] using hn.le

end D5.S3.ConceptDynamics.SpacetimeReal.BisectionCompletion
