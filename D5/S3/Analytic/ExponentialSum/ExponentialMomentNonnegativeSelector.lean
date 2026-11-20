/- GID: D5/S3/Analytic/ExponentialSum/ExponentialMomentNonnegativeSelector
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Analytic/ExponentialSum/DescartesRule]
   utility: none
   digest: Exponential sums selecting atoms of finite real support. -/

import D5.S3.Analytic.ExponentialSum.DescartesRule
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Nonnegative exponential selector for finite active support

Keep every selected atom as a root. For each selected atom other than the
minimum, shift its paired root to the right by a common positive amount
that crosses no active atom. At every unselected active atom the two factors
contributed by each pair have the same strict sign. This lets `exact_sign` apply
directly to a single set of distinct roots.
-/

noncomputable section

open D5.S3.Analytic.ExponentialSum.DescartesRule
open Filter
open scoped BigOperators Topology

namespace ExponentialMomentNonnegativeSelector

attribute [local instance] Classical.propDecidable

private theorem signVariations_le {N : ℕ} (a : Fin N → ℝ) :
    (List.ofFn a).signVariations ≤ N - 1 := by
  let signs := (List.ofFn a).map SignType.sign
  have hlength : ((signs.filter (· ≠ 0)).destutter (· ≠ ·)).length ≤ N := by
    calc
      _ ≤ (signs.filter (· ≠ 0)).length := (List.destutter_sublist _ _).length_le
      _ ≤ signs.length := List.length_filter_le _ _
      _ = N := by simp [signs]
  exact Nat.sub_le_sub_right hlength 1

private theorem exists_vanishing_with_positive_lead {N : ℕ} (μ : Fin N → ℝ)
    (Z : Finset ℝ) (hcard : Z.card < N) :
    ∃ a : Fin N → ℝ,
      (∃ i, 0 < a i ∧ ∀ j, j < i → a j = 0) ∧
      (∀ x ∈ Z, exponentialSum a μ x = 0) := by
  let eval : (Fin N → ℝ) →ₗ[ℝ] (↥Z → ℝ) :=
    { toFun := fun a z => exponentialSum a μ z.val
      map_add' := by
        intro a b
        funext z
        simp only [exponentialSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext z
        simp only [exponentialSum, RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
          mul_assoc, Finset.mul_sum] }
  have hdim : Module.finrank ℝ (↥Z → ℝ) < Module.finrank ℝ (Fin N → ℝ) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin]
      using hcard
  have hker : LinearMap.ker eval ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨a, haKer, ha⟩ := (LinearMap.ker eval).ne_bot_iff.mp hker
  have hvanish : ∀ x ∈ Z, exponentialSum a μ x = 0 := by
    intro x hx
    exact congrFun (LinearMap.mem_ker.mp haKer) (⟨x, hx⟩ : ↥Z)
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  let indices := Finset.univ.filter (fun j => a j ≠ 0)
  have hindices : indices.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let i := indices.min' hindices
  have hi : a i ≠ 0 := (Finset.mem_filter.mp (indices.min'_mem hindices)).2
  have hfirst : ∀ j, j < i → a j = 0 := by
    intro j hj
    by_contra h
    have hjmem : j ∈ indices := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    exact (not_lt_of_ge (indices.min'_le j hjmem)) hj
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · refine ⟨-a, ⟨i, ?_, ?_⟩, ?_⟩
    · exact neg_pos.mpr hneg
    · intro j hj
      simp only [Pi.neg_apply, hfirst j hj, neg_zero]
    · intro x hx
      have hnegSum : exponentialSum (-a) μ x = -exponentialSum a μ x := by
        simp only [exponentialSum, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      rw [hnegSum, hvanish x hx, neg_zero]
  · exact ⟨a, ⟨i, hpos, hfirst⟩, hvanish⟩

/-- A common rightward displacement that keeps every strict comparison within the support. -/
private theorem exists_right_shift (active : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ active, ∀ y ∈ active, x < y → x + ε < y := by
  have hnear : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      ∀ x ∈ active, ∀ y ∈ active, x < y → x + ε < y := by
    refine (active.eventually_all).2 fun x _ => (active.eventually_all).2 fun y _ => ?_
    by_cases hxy : x < y
    · have hcont : ContinuousAt (fun ε : ℝ => x + ε) (0 : ℝ) :=
        (continuous_const.add continuous_id).continuousAt
      have hineq : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), x + ε < y :=
        hcont.eventually_lt continuousAt_const (by simpa only [add_zero] using hxy)
      exact hineq.mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hxy h).elim
  have hright : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  exact (hright.and (hnear.filter_mono nhdsWithin_le_nhds)).exists

private theorem selector_of_strictAnti {k : ℕ} (hk : 1 ≤ k)
    (active selected : Finset ℝ) (hsub : selected ⊆ active) (hselected : selected.card = k)
    (xMin : ℝ) (hmin : xMin ∈ selected) (hmin_le : ∀ x ∈ active, xMin ≤ x)
    (μ : Fin (2 * k) → ℝ) (hμ : StrictAnti μ) :
    ∃ a : Fin (2 * k) → ℝ,
      (∃ i, a i ≠ 0) ∧
      (∀ x ∈ selected, exponentialSum a μ x = 0) ∧
      (∀ x ∈ active, x ∉ selected → 0 < exponentialSum a μ x) ∧
      (active.filter (fun x => exponentialSum a μ x = 0)).card ≤ 2 * k - 1 := by
  obtain ⟨ε, hε, hgap⟩ := exists_right_shift active
  let D := selected.erase xMin
  let shift : ℝ → ℝ := fun x => x + ε
  have hshift : Function.Injective shift := fun _ _ h => add_right_cancel h
  have hshift_gt (z : ℝ) : z < shift z := by
    change z < z + ε
    linarith
  have hdisjoint : Disjoint selected (D.image shift) := by
    refine Finset.disjoint_left.mpr ?_
    intro y hy hyShift
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hyShift
    have hzActive : z ∈ active := hsub (Finset.mem_erase.mp hz).2
    exact (lt_irrefl (shift z)) (hgap z hzActive (shift z) (hsub hy) (hshift_gt z))
  let Z := selected ∪ D.image shift
  have hD : D.card = k - 1 := by
    simpa only [D, hselected] using Finset.card_erase_of_mem hmin
  have hZcard : Z.card = 2 * k - 1 := by
    change (selected ∪ D.image shift).card = _
    rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injective D hshift,
      hselected, hD]
    omega
  have hZlt : Z.card < 2 * k := by omega
  obtain ⟨a, hlead, hzero⟩ := exists_vanishing_with_positive_lead μ Z hZlt
  have hne : ∃ i, a i ≠ 0 := by
    obtain ⟨i, hi, _⟩ := hlead
    exact ⟨i, ne_of_gt hi⟩
  have hsat : Z.card = (List.ofFn a).signVariations := by
    apply le_antisymm (zero_bound a μ hμ hne Z hzero)
    rw [hZcard]
    exact signVariations_le a
  have hselectedZero : ∀ x ∈ selected, exponentialSum a μ x = 0 := by
    intro x hx
    exact hzero x (Finset.mem_union.mpr (Or.inl hx))
  refine ⟨a, hne, hselectedZero, ?_, ?_⟩
  · intro x hx hxs
    have hxmin : xMin < x := lt_of_le_of_ne (hmin_le x hx) (fun h => hxs (h ▸ hmin))
    have hpaired : ∀ z ∈ D, 0 < (x - z) * (x - shift z) := by
      intro z hz
      have hzSel : z ∈ selected := (Finset.mem_erase.mp hz).2
      have hxz : x ≠ z := fun h => hxs (h.symm ▸ hzSel)
      rcases lt_or_gt_of_ne hxz with hxz | hzx
      · exact mul_pos_of_neg_of_neg (sub_neg.mpr hxz)
          (sub_neg.mpr (hxz.trans (hshift_gt z)))
      · exact mul_pos (sub_pos.mpr hzx) (sub_pos.mpr (hgap z (hsub hzSel) x hx hzx))
    have hfactor : (∏ z ∈ Z, (x - z)) =
        (x - xMin) * ∏ z ∈ D, ((x - z) * (x - shift z)) := by
      calc
        _ = (∏ z ∈ selected, (x - z)) * ∏ z ∈ D, (x - shift z) := by
          dsimp only [Z]
          rw [Finset.prod_union hdisjoint, Finset.prod_image hshift.injOn]
        _ = _ := by
          rw [← Finset.mul_prod_erase selected (fun z => x - z) hmin]
          change ((x - xMin) * ∏ z ∈ D, (x - z)) * (∏ z ∈ D, (x - shift z)) =
            (x - xMin) * ∏ z ∈ D, ((x - z) * (x - shift z))
          rw [Finset.prod_mul_distrib, mul_assoc]
    have hproduct : 0 < ∏ z ∈ Z, (x - z) := by
      rw [hfactor]
      exact mul_pos (sub_pos.mpr hxmin) (Finset.prod_pos hpaired)
    have hsign := exact_sign a μ hμ hlead Z hzero hsat x
    rw [sign_pos hproduct] at hsign
    exact sign_eq_one_iff.mp hsign
  · let zeros := active.filter (fun x => exponentialSum a μ x = 0)
    have hzeros : ∀ x ∈ zeros, exponentialSum a μ x = 0 :=
      fun _ hx => (Finset.mem_filter.mp hx).2
    exact (zero_bound a μ hμ hne zeros hzeros).trans (signVariations_le a)

/-- A nonzero exponential sum vanishes on the selected atoms and is strictly
positive at every other atom of the finite active support. The exponents may
be ordered in either direction. -/
theorem exists_selector_pos_off_selected {k : ℕ} (hk : 1 ≤ k)
    (active selected : Finset ℝ) (hsub : selected ⊆ active) (hselected : selected.card = k)
    (xMin : ℝ) (hmin : xMin ∈ selected) (hmin_le : ∀ x ∈ active, xMin ≤ x)
    (μ : Fin (2 * k) → ℝ) (hμ : StrictAnti μ ∨ StrictMono μ) :
    ∃ a : Fin (2 * k) → ℝ,
      (∃ i, a i ≠ 0) ∧
      (∀ x ∈ selected, exponentialSum a μ x = 0) ∧
      (∀ x ∈ active, x ∉ selected → 0 < exponentialSum a μ x) ∧
      (active.filter (fun x => exponentialSum a μ x = 0)).card ≤ 2 * k - 1 := by
  rcases hμ with hanti | hmono
  · exact selector_of_strictAnti hk active selected hsub hselected xMin hmin hmin_le μ hanti
  · have hanti : StrictAnti (μ ∘ Fin.rev) := by
      intro i j hij
      exact hmono (Fin.rev_lt_rev.mpr hij)
    obtain ⟨a, hne, hzero, hpos, hcard⟩ :=
      selector_of_strictAnti hk active selected hsub hselected xMin hmin hmin_le
        (μ ∘ Fin.rev) hanti
    have hsum : exponentialSum (a ∘ Fin.rev) μ = exponentialSum a (μ ∘ Fin.rev) := by
      funext x
      unfold exponentialSum
      simpa only [Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev] using
        (Equiv.sum_comp (Fin.revPerm : Fin (2 * k) ≃ Fin (2 * k))
          (fun i => a i * Real.exp (μ (Fin.rev i) * x)))
    refine ⟨a ∘ Fin.rev, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hne
      exact ⟨Fin.rev i, by simpa only [Function.comp_apply, Fin.rev_rev] using hi⟩
    · rw [hsum]
      exact ⟨hzero, hpos, hcard⟩

/-- For any `k ≥ 1` selected active atoms containing the minimum and any `2 * k`
strictly ordered real exponents, a nonzero coefficient vector selects those zeros
and gives nonnegative values on the active support. The final bound counts every
active zero. -/
theorem exists_nonnegative_selector {k : ℕ} (hk : 1 ≤ k)
    (active selected : Finset ℝ) (hsub : selected ⊆ active) (hselected : selected.card = k)
    (xMin : ℝ) (hmin : xMin ∈ selected) (hmin_le : ∀ x ∈ active, xMin ≤ x)
    (μ : Fin (2 * k) → ℝ) (hμ : StrictAnti μ ∨ StrictMono μ) :
    ∃ a : Fin (2 * k) → ℝ,
      (∃ i, a i ≠ 0) ∧
      (∀ x ∈ selected, exponentialSum a μ x = 0) ∧
      (∀ x ∈ active, 0 ≤ exponentialSum a μ x) ∧
      (active.filter (fun x => exponentialSum a μ x = 0)).card ≤ 2 * k - 1 := by
  obtain ⟨a, hne, hzero, hpos, hcard⟩ :=
    exists_selector_pos_off_selected hk active selected hsub hselected xMin hmin hmin_le μ hμ
  refine ⟨a, hne, hzero, ?_, hcard⟩
  intro x hx
  by_cases hxs : x ∈ selected
  · exact le_of_eq (hzero x hxs).symm
  · exact (hpos x hx hxs).le

end ExponentialMomentNonnegativeSelector
