/- GID: D5/S3/Topology/InverseLimit/CofinalTaskSchedule
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/CofinalTaskSchedule
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Fixed ordinal task reservations have cofinal valid execution tails. -/

import D5.S3.Topology.InverseLimit.SignedProperLimit
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Fixed cofinal reservations depend only on ordinal task syntax. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function
open scoped Ordinal Cardinal

namespace D5.S3.Topology.InverseLimit.CofinalTaskSchedule

open SignedProperLimit

/-- Only ordinal syntax is reserved; no space or measure occurs in a task. -/
abbrev Task := (Label × Label) ⊕ (Label × Label × Label × ℕ)

private theorem label_card : Cardinal.mk Label = ℵ₁ := by
  simp [Label, Cardinal.mk_Iio_ordinal, Ordinal.card_omega]

private theorem label_uncountable : ¬ Countable Label := by
  intro h
  have hh := Cardinal.mk_le_aleph0 (α := Label)
  rw [label_card] at hh
  exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hh

private theorem reservation_card : Cardinal.mk (Task × Label) = Cardinal.mk Label := by
  simp only [Task, Cardinal.mk_prod, Cardinal.mk_sum, Cardinal.lift_id,
    Cardinal.mk_nat, Cardinal.lift_aleph0, label_card]
  have h : (ℵ₀ : Cardinal.{1}) ≤ ℵ₁ := Cardinal.aleph0_lt_aleph_one.le
  simp only [Cardinal.lift_uzero, Cardinal.mul_eq_self h,
    Cardinal.mul_aleph0_eq h, Cardinal.add_eq_self h]

/-- One fixed bijection is chosen before all dynamic birth data. -/
noncomputable def reservation : Label ≃ Task × Label :=
  Classical.choice (Cardinal.eq.mp reservation_card.symm)

/-- Every task's reservation fiber is unbounded in the proper ordinals. -/
theorem exists_reservation_above (task : Task) (base : Label) :
    ∃ a : Label, base < a ∧ (reservation a).1 = task := by
  classical
  by_contra h
  have hb : ∀ ξ : Label, (reservation.symm (task, ξ)).1 ≤ base.1 := by
    intro ξ
    by_contra hh
    apply h
    exact ⟨reservation.symm (task, ξ), lt_of_not_ge hh, by simp⟩
  let f : Label → Set.Iio (Order.succ base.1) := fun ξ =>
    ⟨(reservation.symm (task, ξ)).1, (Order.lt_succ_iff).mpr (hb ξ)⟩
  have hf : Injective f := by
    intro x y hxy
    have hv := congrArg (fun z : Set.Iio (Order.succ base.1) => z.1) hxy
    have he : reservation.symm (task, x) = reservation.symm (task, y) :=
      Subtype.ext hv
    exact (Prod.mk.inj (reservation.symm.injective he)).2
  letI : Countable (Set.Iio (Order.succ base.1)) :=
    (Cardinal.countable_Iio_of_lt_omega_one
      ((Cardinal.isSuccLimit_omega 1).succ_lt base.2)).to_subtype
  exact label_uncountable (hf.countable)

/-- A decoded ordinary task can use the new row and the new residual label. -/
def OrdinaryValid (a r d : Label) : Prop := ω ≤ r.1 ∧ r ≤ a ∧ d ≤ a

/-- Delayed tasks use strictly older rows and sequence labels. -/
def DelayedValid (a θ s t : Label) : Prop := ω ≤ θ.1 ∧ θ < a ∧ s < a ∧ t < a

/-- The original legal ordinary fallback. -/
def fallback : Label × Label :=
  (⟨ω, Ordinal.omega0_lt_omega_one⟩,
   ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩)

/-- Semantic validity is checked only when the syntactic reservation is executed.
The predicate may depend on already born data; it is not a decision algorithm. -/
noncomputable def execute (a : Label) (delayed : Label → Label → Label → ℕ → Prop) :
    Label × Label := by
  classical
  exact match (reservation a).1 with
  | .inl (r, d) => if OrdinaryValid a r d then (r, d) else fallback
  | .inr (θ, s, t, k) =>
      if DelayedValid a θ s t ∧ delayed θ s t k then (θ, t) else fallback

/-- Every executed ordinary target has its true birth domains, even after rejection. -/
theorem execute_valid (a : Label) (ha : ω ≤ a.1)
    (delayed : Label → Label → Label → ℕ → Prop) :
    OrdinaryValid a (execute a delayed).1 (execute a delayed).2 := by
  classical
  have hf : OrdinaryValid a fallback.1 fallback.2 :=
    ⟨le_rfl, ha, show (0 : Ordinal.{0}) ≤ a.1 from bot_le⟩
  unfold execute
  split
  · split_ifs with h
    · exact h
    · exact hf
  · split_ifs with h
    · exact ⟨h.1.1, h.1.2.1.le, h.1.2.2.2.le⟩
    · exact hf

/-- Every legal ordinary task executes cofinally, independently of the delayed predicate. -/
theorem ordinary_cofinal (r d base : Label) (hr : ω ≤ r.1)
    (delayed : Label → Label → Label → ℕ → Prop) :
    ∃ a : Label, base < a ∧ OrdinaryValid a r d ∧ (reservation a).1 = Sum.inl (r, d) ∧
      execute a delayed = (r, d) := by
  obtain ⟨a, ha, he⟩ := exists_reservation_above (.inl (r, d)) (max base (max r d))
  have hr' : r ≤ a := (le_trans (le_max_left r d) (le_max_right base (max r d))).trans ha.le
  have hd' : d ≤ a := (le_trans (le_max_right r d) (le_max_right base (max r d))).trans ha.le
  have hx : execute a delayed = (r, d) := by
    simp [execute, he, OrdinaryValid, hr, hr', hd']
  have hv := execute_valid a (hr.trans hr') delayed
  rw [hx] at hv
  exact ⟨a, lt_of_le_of_lt (le_max_left _ _) ha, hv, he, hx⟩

/-- A semantically valid delayed task executes cofinally after all its parameters. -/
theorem delayed_cofinal (θ s t base : Label) (k : ℕ) (hθ : ω ≤ θ.1)
    (delayed : Label → Label → Label → ℕ → Prop) (hd : delayed θ s t k) :
    ∃ a : Label, base < a ∧ DelayedValid a θ s t ∧
      (reservation a).1 = Sum.inr (θ, s, t, k) ∧ execute a delayed = (θ, t) := by
  obtain ⟨a, ha, he⟩ :=
    exists_reservation_above (.inr (θ, s, t, k)) (max base (max θ (max s t)))
  have hθa : θ < a := lt_of_le_of_lt
    ((le_max_left θ (max s t)).trans (le_max_right _ _)) ha
  have hsa : s < a := lt_of_le_of_lt
    ((le_max_left s t).trans ((le_max_right θ (max s t)).trans (le_max_right _ _))) ha
  have hta : t < a := lt_of_le_of_lt
    ((le_max_right s t).trans ((le_max_right θ (max s t)).trans (le_max_right _ _))) ha
  have hv : DelayedValid a θ s t := ⟨hθ, hθa, hsa, hta⟩
  exact ⟨a, lt_of_le_of_lt (le_max_left _ _) ha, hv, he, by simp [execute, he, hv, hd]⟩

end D5.S3.Topology.InverseLimit.CofinalTaskSchedule
