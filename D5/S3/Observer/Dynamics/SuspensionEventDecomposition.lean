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
   * Repository searches found the normalized compact suspension construction in
     `MinimalSuspensionContinuum`, but no lifted physical-phase flow, return-time
     sum, event-count decomposition, or theorem containing the five source clauses.
   * Pinned Mathlib supplies the exact `birkhoffSum` primitive and its zero,
     successor, and addition lemmas.  It has no packaged suspension-flow
     decomposition theorem, so those sum lemmas are applied below.
   * Body-shape searches found no existing roof-crossing relation, quotient time
     translation, or least crossing-index construction in D5. -/

noncomputable section

namespace D5.S3.Observer.Dynamics.SuspensionEventDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A single forward roof crossing on the physical-phase cover. -/
def suspensionStep {K : Type*} (T : K -> K) (roof : K -> Real)
    (p q : K × Real) : Prop :=
  q = (T p.1, p.2 - roof p.1)

/-- The lifted roof suspension, obtained by closing roof crossings under equivalence. -/
abbrev Suspension {K : Type*} (T : K -> K) (roof : K -> Real) :=
  Quotient (Relation.EqvGen.setoid (suspensionStep T roof))

private theorem suspension_step_translate
    {K : Type*} (T : K -> K) (roof : K -> Real) (t : Real)
    {p q : K × Real} (hpq : suspensionStep T roof p q) :
    suspensionStep T roof (p.1, p.2 + t) (q.1, q.2 + t) := by
  rcases hpq with rfl
  apply Prod.ext
  · rfl
  · dsimp [suspensionStep]
    ring

private theorem suspension_relation_translate
    {K : Type*} (T : K -> K) (roof : K -> Real) (t : Real)
    {p q : K × Real}
    (hpq : Relation.EqvGen (suspensionStep T roof) p q) :
    Relation.EqvGen (suspensionStep T roof)
      (p.1, p.2 + t) (q.1, q.2 + t) := by
  induction hpq with
  | rel p q hpq =>
      exact Relation.EqvGen.rel _ _ (suspension_step_translate T roof t hpq)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q z _ _ hpq hqz => exact Relation.EqvGen.trans _ _ _ hpq hqz

/-- Time translation on the physical-phase cover descends to the lifted suspension. -/
def suspensionFlow {K : Type*} (T : K -> K) (roof : K -> Real) (t : Real) :
    Suspension T roof -> Suspension T roof :=
  Quotient.map (fun p : K × Real => (p.1, p.2 + t))
    (by
      intro p q hpq
      change Relation.EqvGen (suspensionStep T roof) p q at hpq
      exact suspension_relation_translate T roof t hpq)

private theorem suspension_class_birkhoff
    {K : Type*} (T : K -> K) (roof : K -> Real)
    (k : K) (u : Real) (n : Nat) :
    Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof)) (k, u) =
      Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof))
        ((T^[n]) k, u - birkhoffSum T roof n k) := by
  induction n with
  | zero => simp [birkhoffSum_zero]
  | succ n ih =>
      rw [ih]
      have step :
          Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof))
              ((T^[n]) k, u - birkhoffSum T roof n k) =
            Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof))
              (T ((T^[n]) k),
                (u - birkhoffSum T roof n k) - roof ((T^[n]) k)) := by
        apply Quotient.sound
        apply Relation.EqvGen.rel
        rfl
      rw [step]
      congr 2
      · simp only [Function.iterate_succ_apply']
      · rw [birkhoffSum_succ]
        ring

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

/-- Every nonnegative time in a compact positive-roof suspension has a unique
discrete event count and continuous residual phase. -/
theorem continuous_time_discrete_event_decomposition
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : K ≃ₜ K) (roof : K -> Real)
    (roof_continuous : Continuous roof) (roof_positive : forall k, 0 < roof k)
    (k : K) (s t : Real) (s_nonnegative : 0 <= s) (t_nonnegative : 0 <= t) :
    ∃! normal : Nat × Real,
      birkhoffSum T roof normal.1 k <= s + t ∧
      s + t < birkhoffSum T roof (normal.1 + 1) k ∧
      normal.2 = s + t - birkhoffSum T roof normal.1 k ∧
      s + t = birkhoffSum T roof normal.1 k + normal.2 ∧
      suspensionFlow T roof t
          (Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof)) (k, s)) =
        Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof))
          ((T^[normal.1]) k, normal.2) := by
  obtain ⟨lower, lower_positive, lower_le_roof⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_forall_le'
      roof_continuous.continuousOn (fun x _ => roof_positive x)
  have sum_lower : forall n : Nat,
      (n : Real) * lower <= birkhoffSum T roof n k := by
    intro n
    induction n with
    | zero => simp [birkhoffSum_zero]
    | succ n ih =>
        rw [birkhoffSum_succ]
        calc
          ((n + 1 : Nat) : Real) * lower = (n : Real) * lower + lower := by
            push_cast
            ring
          _ <= birkhoffSum T roof n k + roof ((T^[n]) k) :=
            add_le_add ih (lower_le_roof _ (Set.mem_univ _))
  obtain ⟨N, hN⟩ := exists_nat_gt ((s + t) / lower)
  have target_lt_scaled : s + t < (N : Real) * lower := by
    calc
      s + t = ((s + t) / lower) * lower := by
        rw [div_mul_cancel₀]
        exact lower_positive.ne'
      _ < (N : Real) * lower := mul_lt_mul_of_pos_right hN lower_positive
  have event_exists : ∃ n : Nat,
      s + t < birkhoffSum T roof (n + 1) k := by
    refine ⟨N, target_lt_scaled.trans_le ?_⟩
    exact (sum_lower N).trans
      (birkhoffSum_mono_of_nonnegative T roof (fun x => (roof_positive x).le) k
        (Nat.le_add_right N 1))
  let n := Nat.find event_exists
  have upper : s + t < birkhoffSum T roof (n + 1) k := Nat.find_spec event_exists
  have lower_bound : birkhoffSum T roof n k <= s + t := by
    by_cases hn : n = 0
    · simpa [hn, birkhoffSum_zero] using add_nonneg s_nonnegative t_nonnegative
    · have one_le_n : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn
      have predecessor_lt_find : n - 1 < Nat.find event_exists := by
        simpa [n] using Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) (by decide : 0 < 1)
      have predecessor_not_event := Nat.find_min event_exists predecessor_lt_find
      rw [Nat.sub_add_cancel one_le_n] at predecessor_not_event
      exact le_of_not_gt predecessor_not_event
  let residual := s + t - birkhoffSum T roof n k
  have residual_eq : residual = s + t - birkhoffSum T roof n k := rfl
  have time_split : s + t = birkhoffSum T roof n k + residual := by
    dsimp [residual]
    linarith
  have flow_eq :
      suspensionFlow T roof t
          (Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof)) (k, s)) =
        Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof))
          ((T^[n]) k, residual) := by
    rw [suspensionFlow, Quotient.map_mk]
    calc
      Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof)) (k, s + t) =
          Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof))
            ((T^[n]) k, s + t - birkhoffSum T roof n k) :=
        suspension_class_birkhoff T roof k (s + t) n
      _ = Quotient.mk (Relation.EqvGen.setoid (suspensionStep T roof))
          ((T^[n]) k, residual) := by
        rw [residual_eq]
  refine ⟨(n, residual), ⟨lower_bound, upper, residual_eq, time_split, flow_eq⟩, ?_⟩
  intro candidate hcandidate
  rcases candidate with ⟨m, phase⟩
  have n_le_m : n <= m := Nat.find_min' event_exists hcandidate.2.1
  have m_le_n : m <= n := by
    by_contra hnot
    have n_lt_m : n < m := Nat.lt_of_not_ge hnot
    have sum_order :
        birkhoffSum T roof (n + 1) k <= birkhoffSum T roof m k :=
      birkhoffSum_mono_of_nonnegative T roof (fun x => (roof_positive x).le) k
        (Nat.succ_le_iff.mpr n_lt_m)
    exact (not_lt_of_ge hcandidate.1) (upper.trans_le sum_order)
  have hmn : m = n := Nat.le_antisymm m_le_n n_le_m
  subst m
  have phase_eq : phase = residual := hcandidate.2.2.1.trans residual_eq.symm
  subst phase
  rfl

#print axioms continuous_time_discrete_event_decomposition

end D5.S3.Observer.Dynamics.SuspensionEventDecomposition
