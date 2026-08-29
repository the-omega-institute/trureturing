/- GID: D5/S3/Observer/Dynamics/SuspensionEventDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/SuspensionEventDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive-roof suspension flow splits uniquely into event count and residual phase. -/

import D5.S3.Observer.Dynamics.MinimalSuspensionContinuum
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Topology.Order.Compact

/- Library-search audit trail (2026-08-30):
   * The frozen `MinimalSuspensionContinuum` module owns the suspension carrier,
     its compact fundamental domain, physical-height map, and endpoint setoid.
     This module consumes those declarations and introduces no second public carrier.
   * Pinned Mathlib supplies `birkhoffSum`, its two successor decompositions,
     addition, compact extrema, and quotient lifting.  No packaged suspension-flow
     decomposition theorem was found.
   * Literal time translation is constructed on a private nonnegative-height cover.
     A private normalization transport proves that it descends to the frozen carrier;
     the public theorem and every source clause are stated on that carrier. -/

noncomputable section

namespace D5.S3.Observer.Dynamics.SuspensionEventDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

private abbrev NonnegativeHeight := Set.Ici (0 : Real)

private abbrev ForwardCoverDomain (K : Type*) := K × NonnegativeHeight

private def forwardCoverStep {K : Type*} (T : K -> K) (roof : K -> Real)
    (p q : ForwardCoverDomain K) : Prop :=
  q.1 = T p.1 ∧ q.2.1 = p.2.1 - roof p.1

private abbrev ForwardCover {K : Type*} (T : K -> K) (roof : K -> Real) :=
  Quotient (Relation.EqvGen.setoid (forwardCoverStep T roof))

private theorem birkhoffSum_mono_of_nonnegative
    {K : Type*} (T : K -> K) (roof : K -> Real)
    (hroof : forall k, 0 <= roof k) (k : K) :
    Monotone (fun n => birkhoffSum T roof n k) := by
  intro m n hmn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  change birkhoffSum T roof m k <= birkhoffSum T roof (m + d) k
  rw [birkhoffSum_add]
  apply le_add_of_nonneg_right
  simp only [birkhoffSum]
  exact Finset.sum_nonneg fun i _ => hroof ((T^[i]) ((T^[m]) k))

private theorem crossing_exists
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) :
    ∃ n : Nat, p.2.1 < birkhoffSum T roof (n + 1) p.1 := by
  obtain ⟨lower, lower_positive, lower_le_roof⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_forall_le'
      roof_continuous.continuousOn (fun x _ => roof_positive x)
  have sum_lower : forall n : Nat,
      (n : Real) * lower <= birkhoffSum T roof n p.1 := by
    intro n
    induction n with
    | zero => simp [birkhoffSum_zero]
    | succ n ih =>
        rw [birkhoffSum_succ]
        calc
          ((n + 1 : Nat) : Real) * lower = (n : Real) * lower + lower := by
            push_cast
            ring
          _ <= birkhoffSum T roof n p.1 + roof ((T^[n]) p.1) :=
            add_le_add ih (lower_le_roof _ (Set.mem_univ _))
  obtain ⟨N, hN⟩ := exists_nat_gt (p.2.1 / lower)
  have target_lt_scaled : p.2.1 < (N : Real) * lower := by
    calc
      p.2.1 = (p.2.1 / lower) * lower := by
        rw [div_mul_cancel₀]
        exact lower_positive.ne'
      _ < (N : Real) * lower := mul_lt_mul_of_pos_right hN lower_positive
  refine ⟨N, target_lt_scaled.trans_le ?_⟩
  exact (sum_lower N).trans
    (birkhoffSum_mono_of_nonnegative T roof (fun x => (roof_positive x).le) p.1
      (Nat.le_add_right N 1))

private def crossingIndex
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) : Nat :=
  Nat.find (crossing_exists T roof roof_continuous roof_positive p)

private theorem crossingIndex_upper
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) :
    p.2.1 < birkhoffSum T roof
      (crossingIndex T roof roof_continuous roof_positive p + 1) p.1 :=
  Nat.find_spec (crossing_exists T roof roof_continuous roof_positive p)

private theorem crossingIndex_lower
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) :
    birkhoffSum T roof (crossingIndex T roof roof_continuous roof_positive p) p.1 <=
      p.2.1 := by
  let n := crossingIndex T roof roof_continuous roof_positive p
  by_cases hn : n = 0
  · simpa [n, hn, birkhoffSum_zero] using p.2.2
  · have one_le_n : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn
    have predecessor_lt_find : n - 1 < Nat.find
        (crossing_exists T roof roof_continuous roof_positive p) := by
      simpa [n, crossingIndex] using
        Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) (by decide : 0 < 1)
    have predecessor_not_event := Nat.find_min
      (crossing_exists T roof roof_continuous roof_positive p) predecessor_lt_find
    rw [Nat.sub_add_cancel one_le_n] at predecessor_not_event
    exact le_of_not_gt predecessor_not_event

private theorem crossingIndex_eq_of_bounds
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) (m : Nat)
    (lower : birkhoffSum T roof m p.1 <= p.2.1)
    (upper : p.2.1 < birkhoffSum T roof (m + 1) p.1) :
    crossingIndex T roof roof_continuous roof_positive p = m := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (crossing_exists T roof roof_continuous roof_positive p) upper
  · by_contra hnot
    have index_lt_m :
        crossingIndex T roof roof_continuous roof_positive p < m :=
      Nat.lt_of_not_ge hnot
    have sum_order :
        birkhoffSum T roof
            (crossingIndex T roof roof_continuous roof_positive p + 1) p.1 <=
          birkhoffSum T roof m p.1 :=
      birkhoffSum_mono_of_nonnegative T roof (fun x => (roof_positive x).le) p.1
        (Nat.succ_le_iff.mpr index_lt_m)
    exact (not_lt_of_ge lower)
      ((crossingIndex_upper T roof roof_continuous roof_positive p).trans_le sum_order)

private def crossingResidual
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) : Real :=
  p.2.1 - birkhoffSum T roof
    (crossingIndex T roof roof_continuous roof_positive p) p.1

private theorem crossingResidual_nonnegative
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) :
    0 <= crossingResidual T roof roof_continuous roof_positive p := by
  exact sub_nonneg.mpr
    (crossingIndex_lower T roof roof_continuous roof_positive p)

private theorem crossingResidual_lt_roof
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) :
    crossingResidual T roof roof_continuous roof_positive p <
      roof ((T^[crossingIndex T roof roof_continuous roof_positive p]) p.1) := by
  have upper := crossingIndex_upper T roof roof_continuous roof_positive p
  rw [birkhoffSum_succ] at upper
  dsimp [crossingResidual]
  exact (sub_lt_iff_lt_add).2 (by simpa [add_comm] using upper)

private def normalizedPhase
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) : MinimalSuspensionContinuum.RoofCoordinate :=
  ⟨crossingResidual T roof roof_continuous roof_positive p /
      roof ((T^[crossingIndex T roof roof_continuous roof_positive p]) p.1),
    div_nonneg (crossingResidual_nonnegative T roof roof_continuous roof_positive p)
      (roof_positive _).le,
    (div_le_iff₀ (roof_positive _)).2 (by
      simpa using
        (crossingResidual_lt_roof T roof roof_continuous roof_positive p).le)⟩

private def normalizedDomain
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) : MinimalSuspensionContinuum.SuspensionDomain K :=
  ((T^[crossingIndex T roof roof_continuous roof_positive p]) p.1,
    normalizedPhase T roof roof_continuous roof_positive p)

private theorem physicalHeight_normalizedDomain
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) :
    MinimalSuspensionContinuum.physicalHeight roof
        (normalizedDomain T roof roof_continuous roof_positive p) =
      crossingResidual T roof roof_continuous roof_positive p := by
  simp only [MinimalSuspensionContinuum.physicalHeight, normalizedDomain, normalizedPhase]
  exact div_mul_cancel₀ _ (roof_positive _).ne'

private theorem crossingIndex_step
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    {p q : ForwardCoverDomain K} (hpq : forwardCoverStep T roof p q) :
    crossingIndex T roof roof_continuous roof_positive p =
      crossingIndex T roof roof_continuous roof_positive q + 1 := by
  apply crossingIndex_eq_of_bounds T roof roof_continuous roof_positive p
  · calc
      birkhoffSum T roof
          (crossingIndex T roof roof_continuous roof_positive q + 1) p.1 =
          roof p.1 + birkhoffSum T roof
            (crossingIndex T roof roof_continuous roof_positive q) (T p.1) :=
        birkhoffSum_succ' T roof _ p.1
      _ = roof p.1 + birkhoffSum T roof
            (crossingIndex T roof roof_continuous roof_positive q) q.1 := by
        rw [← hpq.1]
      _ <= roof p.1 + q.2.1 := by
        simpa [add_comm] using add_le_add_left
          (crossingIndex_lower T roof roof_continuous roof_positive q) (roof p.1)
      _ = p.2.1 := by linarith [hpq.2]
  · calc
      p.2.1 = roof p.1 + q.2.1 := by linarith [hpq.2]
      _ < roof p.1 + birkhoffSum T roof
            (crossingIndex T roof roof_continuous roof_positive q + 1) q.1 :=
        by
          simpa [add_comm] using add_lt_add_left
            (crossingIndex_upper T roof roof_continuous roof_positive q) (roof p.1)
      _ = roof p.1 + birkhoffSum T roof
            (crossingIndex T roof roof_continuous roof_positive q + 1) (T p.1) := by
        rw [← hpq.1]
      _ = birkhoffSum T roof
          ((crossingIndex T roof roof_continuous roof_positive q + 1) + 1) p.1 :=
        (birkhoffSum_succ' T roof _ p.1).symm

private theorem normalizedBase_step
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    {p q : ForwardCoverDomain K} (hpq : forwardCoverStep T roof p q) :
    (T^[crossingIndex T roof roof_continuous roof_positive p]) p.1 =
      (T^[crossingIndex T roof roof_continuous roof_positive q]) q.1 := by
  rw [crossingIndex_step T roof roof_continuous roof_positive hpq]
  simpa [hpq.1] using
    (Function.iterate_succ_apply T
      (crossingIndex T roof roof_continuous roof_positive q) p.1)

private theorem crossingResidual_step
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    {p q : ForwardCoverDomain K} (hpq : forwardCoverStep T roof p q) :
    crossingResidual T roof roof_continuous roof_positive p =
      crossingResidual T roof roof_continuous roof_positive q := by
  rw [crossingResidual, crossingResidual,
    crossingIndex_step T roof roof_continuous roof_positive hpq,
    birkhoffSum_succ']
  rw [hpq.1]
  linarith [hpq.2]

private theorem normalizedDomain_step
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    {p q : ForwardCoverDomain K} (hpq : forwardCoverStep T roof p q) :
    normalizedDomain T roof roof_continuous roof_positive p =
      normalizedDomain T roof roof_continuous roof_positive q := by
  apply Prod.ext
  · exact normalizedBase_step T roof roof_continuous roof_positive hpq
  · apply Subtype.ext
    dsimp [normalizedDomain, normalizedPhase]
    rw [crossingResidual_step T roof roof_continuous roof_positive hpq,
      normalizedBase_step T roof roof_continuous roof_positive hpq]

private theorem normalizedDomain_relation
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    {p q : ForwardCoverDomain K}
    (hpq : Relation.EqvGen (forwardCoverStep T roof) p q) :
    normalizedDomain T roof roof_continuous roof_positive p =
      normalizedDomain T roof roof_continuous roof_positive q := by
  induction hpq with
  | rel p q hpq => exact normalizedDomain_step T roof roof_continuous roof_positive hpq
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q z _ _ hpq hqz => exact hpq.trans hqz

private def canonicalCoverPoint
    {K : Type*} [TopologicalSpace K]
    (roof : K -> Real) (roof_positive : forall k, 0 < roof k)
    (p : MinimalSuspensionContinuum.SuspensionDomain K) : ForwardCoverDomain K :=
  (p.1, ⟨MinimalSuspensionContinuum.physicalHeight roof p, by
    change 0 <= p.2.1 * roof p.1
    exact mul_nonneg p.2.2.1 (roof_positive p.1).le⟩)

private def canonicalToForwardCover
    {K : Type*} [TopologicalSpace K]
    (T : K ≃ₜ K) (roof : K -> Real) (roof_positive : forall k, 0 < roof k) :
    MinimalSuspensionContinuum.Suspension T roof roof_positive -> ForwardCover T roof :=
  Quotient.map (canonicalCoverPoint roof roof_positive)
    (by
      intro p q hpq
      change MinimalSuspensionContinuum.suspensionRelation T.toEquiv roof p q at hpq
      change Relation.EqvGen (forwardCoverStep T roof) _ _
      rcases hpq with rfl | hpq | hpq
      · exact Relation.EqvGen.refl _
      · apply Relation.EqvGen.rel
        constructor
        · exact hpq.2.2.symm
        · change MinimalSuspensionContinuum.physicalHeight roof q =
            MinimalSuspensionContinuum.physicalHeight roof p - roof p.1
          rw [hpq.1, hpq.2.1]
          ring
      · apply Relation.EqvGen.symm
        apply Relation.EqvGen.rel
        constructor
        · exact hpq.2.2.symm
        · change MinimalSuspensionContinuum.physicalHeight roof p =
            MinimalSuspensionContinuum.physicalHeight roof q - roof q.1
          rw [hpq.1, hpq.2.1]
          ring)

private theorem canonicalToForwardCover_mk
    {K : Type*} [TopologicalSpace K]
    (T : K ≃ₜ K) (roof : K -> Real) (roof_positive : forall k, 0 < roof k)
    (p : MinimalSuspensionContinuum.SuspensionDomain K) :
    canonicalToForwardCover T roof roof_positive
        (Quotient.mk' (s := MinimalSuspensionContinuum.suspensionSetoid
          T.toEquiv roof roof_positive) p) =
      Quotient.mk' (s := Relation.EqvGen.setoid (forwardCoverStep T roof))
        (canonicalCoverPoint roof roof_positive p) := rfl

private def translateForwardCoverDomain {K : Type*} (t : Real) (t_nonnegative : 0 <= t)
    (p : ForwardCoverDomain K) : ForwardCoverDomain K :=
  (p.1, ⟨p.2.1 + t, add_nonneg p.2.2 t_nonnegative⟩)

private theorem forwardCoverStep_translate
    {K : Type*} (T : K -> K) (roof : K -> Real)
    (t : Real) (t_nonnegative : 0 <= t)
    {p q : ForwardCoverDomain K} (hpq : forwardCoverStep T roof p q) :
    forwardCoverStep T roof
      (translateForwardCoverDomain t t_nonnegative p)
      (translateForwardCoverDomain t t_nonnegative q) := by
  constructor
  · exact hpq.1
  · change q.2.1 + t = p.2.1 + t - roof p.1
    calc
      q.2.1 + t = (p.2.1 - roof p.1) + t := by rw [hpq.2]
      _ = p.2.1 + t - roof p.1 := by ring

private theorem forwardCoverRelation_translate
    {K : Type*} (T : K -> K) (roof : K -> Real)
    (t : Real) (t_nonnegative : 0 <= t)
    {p q : ForwardCoverDomain K}
    (hpq : Relation.EqvGen (forwardCoverStep T roof) p q) :
    Relation.EqvGen (forwardCoverStep T roof)
      (translateForwardCoverDomain t t_nonnegative p)
      (translateForwardCoverDomain t t_nonnegative q) := by
  induction hpq with
  | rel p q hpq =>
      exact Relation.EqvGen.rel _ _
        (forwardCoverStep_translate T roof t t_nonnegative hpq)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q z _ _ hpq hqz => exact Relation.EqvGen.trans _ _ _ hpq hqz

private def forwardCoverFlow
    {K : Type*} (T : K -> K) (roof : K -> Real)
    (t : Real) (t_nonnegative : 0 <= t) :
    ForwardCover T roof -> ForwardCover T roof :=
  Quotient.map (translateForwardCoverDomain t t_nonnegative)
    (by
      intro p q hpq
      change Relation.EqvGen (forwardCoverStep T roof) p q at hpq
      exact forwardCoverRelation_translate T roof t t_nonnegative hpq)

private theorem forwardCoverFlow_mk
    {K : Type*} (T : K -> K) (roof : K -> Real)
    (t : Real) (t_nonnegative : 0 <= t) (p : ForwardCoverDomain K) :
    forwardCoverFlow T roof t t_nonnegative
        (Quotient.mk' (s := Relation.EqvGen.setoid (forwardCoverStep T roof)) p) =
      Quotient.mk' (s := Relation.EqvGen.setoid (forwardCoverStep T roof))
        (translateForwardCoverDomain t t_nonnegative p) := rfl

private def forwardCoverToCanonical
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k) :
    ForwardCover T roof -> MinimalSuspensionContinuum.Suspension T roof roof_positive :=
  Quotient.map (normalizedDomain T roof roof_continuous roof_positive)
    (by
      intro p q hpq
      change Relation.EqvGen (forwardCoverStep T roof) p q at hpq
      have hnormal := normalizedDomain_relation T roof roof_continuous roof_positive hpq
      rw [hnormal])

private theorem forwardCoverToCanonical_mk
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (p : ForwardCoverDomain K) :
    forwardCoverToCanonical T roof roof_continuous roof_positive
        (Quotient.mk' (s := Relation.EqvGen.setoid (forwardCoverStep T roof)) p) =
      Quotient.mk' (s := MinimalSuspensionContinuum.suspensionSetoid
        T.toEquiv roof roof_positive)
        (normalizedDomain T roof roof_continuous roof_positive p) := rfl

/-- Literal forward translation on a private physical-height cover, transported
to the canonical frozen suspension carrier. -/
def suspensionFlow
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (t : Real) (t_nonnegative : 0 <= t) :
    MinimalSuspensionContinuum.Suspension T roof roof_positive ->
      MinimalSuspensionContinuum.Suspension T roof roof_positive :=
  forwardCoverToCanonical T roof roof_continuous roof_positive ∘
    forwardCoverFlow T roof t t_nonnegative ∘
      canonicalToForwardCover T roof roof_positive

/-- Every point of the canonical positive-roof suspension and every nonnegative
time have a unique discrete event count and residual leaf coordinate. -/
theorem continuous_time_discrete_event_decomposition
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (k : K) (u : MinimalSuspensionContinuum.RoofCoordinate)
    (t : Real) (t_nonnegative : 0 <= t) :
    ∃! normal : Nat × MinimalSuspensionContinuum.RoofCoordinate,
      birkhoffSum T roof normal.1 k <=
        MinimalSuspensionContinuum.physicalHeight roof (k, u) + t ∧
      MinimalSuspensionContinuum.physicalHeight roof (k, u) + t <
        birkhoffSum T roof (normal.1 + 1) k ∧
      MinimalSuspensionContinuum.physicalHeight roof ((T^[normal.1]) k, normal.2) =
        MinimalSuspensionContinuum.physicalHeight roof (k, u) + t -
          birkhoffSum T roof normal.1 k ∧
      suspensionFlow T roof roof_continuous roof_positive t t_nonnegative
          (Quotient.mk' (s := MinimalSuspensionContinuum.suspensionSetoid
            T.toEquiv roof roof_positive) (k, u)) =
        Quotient.mk' (s := MinimalSuspensionContinuum.suspensionSetoid
          T.toEquiv roof roof_positive)
          ((T^[normal.1]) k, normal.2) ∧
      MinimalSuspensionContinuum.physicalHeight roof (k, u) + t =
        birkhoffSum T roof normal.1 k +
          MinimalSuspensionContinuum.physicalHeight roof
            ((T^[normal.1]) k, normal.2) := by
  have initial_nonnegative :
      0 <= MinimalSuspensionContinuum.physicalHeight roof (k, u) :=
    mul_nonneg u.2.1 (roof_positive k).le
  let initial : ForwardCoverDomain K :=
    (k, ⟨MinimalSuspensionContinuum.physicalHeight roof (k, u), initial_nonnegative⟩)
  let advanced : ForwardCoverDomain K :=
    translateForwardCoverDomain t t_nonnegative initial
  let n := crossingIndex T roof roof_continuous roof_positive advanced
  let phase := normalizedPhase T roof roof_continuous roof_positive advanced
  have lower : birkhoffSum T roof n k <=
      MinimalSuspensionContinuum.physicalHeight roof (k, u) + t := by
    simpa [n, advanced, initial, translateForwardCoverDomain] using
      crossingIndex_lower T roof roof_continuous roof_positive advanced
  have upper : MinimalSuspensionContinuum.physicalHeight roof (k, u) + t <
      birkhoffSum T roof (n + 1) k := by
    simpa [n, advanced, initial, translateForwardCoverDomain] using
      crossingIndex_upper T roof roof_continuous roof_positive advanced
  have residual_eq :
      MinimalSuspensionContinuum.physicalHeight roof ((T^[n]) k, phase) =
        MinimalSuspensionContinuum.physicalHeight roof (k, u) + t -
          birkhoffSum T roof n k := by
    simpa [n, phase, advanced, initial, translateForwardCoverDomain, crossingResidual,
      normalizedDomain] using
      physicalHeight_normalizedDomain T roof roof_continuous roof_positive advanced
  have flow_eq :
      suspensionFlow T roof roof_continuous roof_positive t t_nonnegative
          (Quotient.mk' (s := MinimalSuspensionContinuum.suspensionSetoid
            T.toEquiv roof roof_positive) (k, u)) =
        Quotient.mk' (s := MinimalSuspensionContinuum.suspensionSetoid
          T.toEquiv roof roof_positive)
          ((T^[n]) k, phase) := by
    rw [suspensionFlow]
    change forwardCoverToCanonical T roof roof_continuous roof_positive
        (forwardCoverFlow T roof t t_nonnegative
          (canonicalToForwardCover T roof roof_positive
            (Quotient.mk' (s := MinimalSuspensionContinuum.suspensionSetoid
              T.toEquiv roof roof_positive) (k, u)))) = _
    rw [canonicalToForwardCover_mk]
    rw [forwardCoverFlow_mk]
    rw [forwardCoverToCanonical_mk]
    rfl
  have time_split : MinimalSuspensionContinuum.physicalHeight roof (k, u) + t =
      birkhoffSum T roof n k +
        MinimalSuspensionContinuum.physicalHeight roof ((T^[n]) k, phase) := by
    linarith
  refine ⟨(n, phase), ⟨lower, upper, residual_eq, flow_eq, time_split⟩, ?_⟩
  intro candidate hcandidate
  rcases candidate with ⟨m, candidatePhase⟩
  have hm : n = m := by
    apply crossingIndex_eq_of_bounds T roof roof_continuous roof_positive advanced
    · simpa [advanced, initial, translateForwardCoverDomain] using hcandidate.1
    · simpa [advanced, initial, translateForwardCoverDomain] using hcandidate.2.1
  subst m
  have phase_height_eq :
      MinimalSuspensionContinuum.physicalHeight roof ((T^[n]) k, candidatePhase) =
        MinimalSuspensionContinuum.physicalHeight roof ((T^[n]) k, phase) :=
    hcandidate.2.2.1.trans residual_eq.symm
  have phase_value_eq : candidatePhase.1 = phase.1 := by
    dsimp [MinimalSuspensionContinuum.physicalHeight] at phase_height_eq
    nlinarith [roof_positive ((T^[n]) k)]
  have phase_eq : candidatePhase = phase := Subtype.ext phase_value_eq
  subst candidatePhase
  rfl

#print axioms continuous_time_discrete_event_decomposition

end D5.S3.Observer.Dynamics.SuspensionEventDecomposition
