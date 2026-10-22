/- GID: D5/S3/Topology/InverseLimit/CountableJointFusion
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/CountableJointFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Countable finite blocks preserve fixed reservoirs and one-sided cofinite inclusions.
 -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Set.Infinite

/-!
# Countable joint finite-block fusion

This is the set-theoretic selector needed at a proper countable limit.  A block
has only finitely many active labels, while every label is active eventually.
The fixed reservoir `N k e` is never changed.  No distinctness of witnesses
between blocks is assumed; the lower bound by the block index is enough for
the resulting reservoir intersections to be infinite.

The theorem is deliberately independent of ordinals and of the analytic
construction that consumes it.  A cofinal sequence of proper stages supplies
the natural stage index and the `active` predicate in an application.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter

namespace D5.S3.Topology.InverseLimit.CountableJointFusion

/- The finite family of current constraints can be met because every current
pool is infinite and each earlier monotonicity relation has only a finite
exception. -/
private theorem exists_block_witness
    (active : ℕ → ℕ → Prop)
    (I : ℕ → Set ℕ)
    (J : ℕ → ℕ → Set ℕ)
    (N : ℕ → Bool → Set ℕ)
    (hJsubI : ∀ k j, active k j → J k j ⊆ I j)
    (hI_mono : ∀ ⦃h j : ℕ⦄, h ≤ j → I j ≤ᶠ[Filter.cofinite] I h)
    (hJ_mono : ∀ (k : ℕ) ⦃h j : ℕ⦄, active k h → active k j →
      h ≤ j → J k j ≤ᶠ[Filter.cofinite] J k h)
    (k j : ℕ) (e : Bool) (hkj : active k j)
    (hpool : (J k j ∩ N k e).Infinite) :
    ∃ n : ℕ, j < n ∧ n ∈ J k j ∧ n ∈ N k e ∧
      (∀ h ≤ j, n ∈ I h) ∧
      (∀ h ≤ j, active k h → n ∈ J k h) := by
  have hI_eventually : ∀ᶠ n in cofinite,
      ∀ h ∈ Finset.range (j + 1), n ∈ I j → n ∈ I h := by
    apply (Finset.range (j + 1)).eventually_all.mpr
    intro h hh
    exact hI_mono (Nat.le_of_lt_succ (Finset.mem_range.mp hh))
  have hJ_eventually : ∀ᶠ n in cofinite,
      ∀ h ∈ Finset.range (j + 1), active k h → n ∈ J k j → n ∈ J k h := by
    apply (Finset.range (j + 1)).eventually_all.mpr
    intro h hh
    by_cases hkh : active k h
    · exact (hJ_mono k hkh hkj
        (Nat.le_of_lt_succ (Finset.mem_range.mp hh))).mono
          (fun n hn _ => hn)
    · exact Filter.Eventually.of_forall (fun n hn => False.elim (hkh hn))
  have hgt : ∀ᶠ n in cofinite, j < n := by
    simpa only [Set.mem_ofPred_eq, not_le] using
      (Set.finite_le_nat j).eventually_cofinite_notMem
  obtain ⟨n, hnPool, hnGood⟩ :=
    (hpool.frequently_cofinite.and_eventually (hgt.and (hI_eventually.and hJ_eventually))).exists
  refine ⟨n, hnGood.1, hnPool.1, hnPool.2, ?_, ?_⟩
  · intro h hh
    have hmem := hnGood.2.1 h (Finset.mem_range.mpr (Nat.lt_succ_of_le hh))
    exact hmem (hJsubI k j hkj hnPool.1)
  · intro h hh hkh
    have hmem := hnGood.2.2 h (Finset.mem_range.mpr (Nat.lt_succ_of_le hh)) hkh
    exact hmem hnPool.1

/--
For countably many labels, finite active blocks jointly produce a selector and
limit sets.  The selector meets both fixed reservoir pieces for every active
label, and its block-index lower bound makes each resulting intersection
infinite.  All earlier inclusions are one-sided modulo finite sets.

The active predicate records delayed proper-stage domains: a label need not be
defined in an early block, but every label must become active eventually.  The
sets `N k e` are parameters of the conclusion and are never replaced.
-/
theorem exists_countable_joint_finite_block_fusion
    (active : ℕ → ℕ → Prop)
    (hactive_finite : ∀ j, {k | active k j}.Finite)
    (hactive_eventually : ∀ k, ∃ j₀, ∀ j, j₀ ≤ j → active k j)
    (I : ℕ → Set ℕ)
    (J : ℕ → ℕ → Set ℕ)
    (N : ℕ → Bool → Set ℕ)
    (hJsubI : ∀ k j, active k j → J k j ⊆ I j)
    (hI_mono : ∀ ⦃h j : ℕ⦄, h ≤ j → I j ≤ᶠ[Filter.cofinite] I h)
    (hJ_mono : ∀ (k : ℕ) ⦃h j : ℕ⦄, active k h → active k j →
      h ≤ j → J k j ≤ᶠ[Filter.cofinite] J k h)
    (hpool : ∀ k j e, active k j → (J k j ∩ N k e).Infinite) :
    ∃ v : ℕ → ℕ → Bool → ℕ, ∃ Ilim : Set ℕ, ∃ Jlim : ℕ → Set ℕ,
      (∀ j k e, active k j →
        j < v j k e ∧ v j k e ∈ J k j ∧ v j k e ∈ N k e ∧
          (∀ h ≤ j, v j k e ∈ I h) ∧
          (∀ h ≤ j, active k h → v j k e ∈ J k h)) ∧
      (∀ k, Jlim k = {n | ∃ j e, active k j ∧ n = v j k e}) ∧
      Ilim = ⋃ k, Jlim k ∧
      (∀ k e, (Jlim k ∩ N k e).Infinite) ∧
      (∀ h, Ilim ≤ᶠ[Filter.cofinite] I h) ∧
      (∀ k h, active k h → Jlim k ≤ᶠ[Filter.cofinite] J k h) := by
  classical
  have hex : ∀ j k e, active k j → ∃ n : ℕ, j < n ∧ n ∈ J k j ∧ n ∈ N k e ∧
      (∀ h ≤ j, n ∈ I h) ∧ (∀ h ≤ j, active k h → n ∈ J k h) := by
    intro j k e hkj
    exact exists_block_witness active I J N hJsubI hI_mono hJ_mono k j e hkj
      (hpool k j e hkj)
  let v : ℕ → ℕ → Bool → ℕ := fun j k e =>
    if hkj : active k j then Classical.choose (hex j k e hkj) else 0
  have hv : ∀ j k e (hkj : active k j),
      j < v j k e ∧ v j k e ∈ J k j ∧ v j k e ∈ N k e ∧
        (∀ h ≤ j, v j k e ∈ I h) ∧
        (∀ h ≤ j, active k h → v j k e ∈ J k h) := by
    intro j k e hkj
    simp [v, hkj]
    exact Classical.choose_spec (hex j k e hkj)
  let Jlim : ℕ → Set ℕ := fun k => {n | ∃ j e, active k j ∧ n = v j k e}
  let Ilim : Set ℕ := ⋃ k, Jlim k
  refine ⟨v, Ilim, Jlim, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro j k e hkj
    exact hv j k e hkj
  · intro k
    rfl
  · intro k e
    obtain ⟨j₀, hj₀⟩ := hactive_eventually k
    apply Set.infinite_of_forall_exists_gt
    intro b
    let j := max j₀ (b + 1)
    have hjactive : active k j := hj₀ j (le_max_left _ _)
    have hjb : b < j := lt_of_lt_of_le (Nat.lt_succ_self b) (le_max_right _ _)
    have hw := hv j k e hjactive
    refine ⟨v j k e, ?_, ?_⟩
    · exact ⟨⟨j, e, hjactive, rfl⟩, hw.2.2.1⟩
    · exact hjb.trans hw.1
  · intro h
    let early : Set ℕ := ⋃ j ∈ Set.Iio h, ⋃ k ∈ {k | active k j}, ⋃ e : Bool, {v j k e}
    have hearly : early.Finite := by
      apply (Set.finite_lt_nat h).biUnion
      intro j hj
      apply (hactive_finite j).biUnion
      intro k hk
      have hBool : (⋃ e : Bool, {v j k e}).Finite := by
        apply Set.Finite.subset (Set.finite_range (fun e : Bool => v j k e))
        intro n hn
        rcases Set.mem_iUnion.mp hn with ⟨e, he⟩
        exact ⟨e, by simpa using he.symm⟩
      exact hBool
    refine hearly.eventually_cofinite_notMem.mono ?_
    intro n hnEarly hnI
    rcases Set.mem_iUnion.mp hnI with ⟨k, hnJ⟩
    rcases hnJ with ⟨j, e, hkj, rfl⟩
    by_cases hjh : j < h
    · exact False.elim (hnEarly (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjh,
        Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkj,
          Set.mem_iUnion.2 ⟨e, Set.mem_singleton _⟩⟩⟩⟩⟩))
    · exact (hv j k e hkj).2.2.2.1 h (Nat.le_of_not_gt hjh)
  · intro k h hkh
    let early : Set ℕ := ⋃ j ∈ Set.Iio h, ⋃ e : Bool, {v j k e}
    have hearly : early.Finite := by
      apply (Set.finite_lt_nat h).biUnion
      intro j hj
      have hBool : (⋃ e : Bool, {v j k e}).Finite := by
        apply Set.Finite.subset (Set.finite_range (fun e : Bool => v j k e))
        intro n hn
        rcases Set.mem_iUnion.mp hn with ⟨e, he⟩
        exact ⟨e, by simpa using he.symm⟩
      exact hBool
    refine hearly.eventually_cofinite_notMem.mono ?_
    intro n hnEarly hnJ
    rcases hnJ with ⟨j, e, hkj, rfl⟩
    by_cases hjh : j < h
    · exact False.elim (hnEarly (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjh,
        Set.mem_iUnion.2 ⟨e, Set.mem_singleton _⟩⟩⟩))
    · exact (hv j k e hkj).2.2.2.2 h (Nat.le_of_not_gt hjh) hkh

end D5.S3.Topology.InverseLimit.CountableJointFusion
