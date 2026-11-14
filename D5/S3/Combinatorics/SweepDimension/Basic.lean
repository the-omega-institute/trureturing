/- GID: D5/S3/Combinatorics/SweepDimension/Basic
   generality: G
   mirror-B: D5/B/S0/Certificates/Combinatorics/SweepDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Antichain, mathlib/module/Mathlib.Order.Defs.Unbundled]
   utility: none
   digest: A finite-poset sweep system has at least as many orders as a maximum three-chain-free set. -/

import Mathlib.Order.Antichain
import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SweepDimension.Basic

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-- A subset has no strict three-chain when it contains no `a < b < c`. -/
def ThreeChainFree (S : Finset α) : Prop :=
  ∀ ⦃a b c : α⦄, a ∈ S → b ∈ S → c ∈ S → ¬(a < b ∧ b < c)

/-- The largest cardinality of a three-chain-free finite subset. -/
noncomputable def theta : ℕ := by
  classical
  let candidates := (Finset.univ : Finset α).powerset.filter ThreeChainFree
  exact (candidates.image Finset.card).max' (by
    have hmem : (∅ : Finset α) ∈ candidates := by simp [candidates, ThreeChainFree]
    exact ⟨0, Finset.mem_image.mpr ⟨∅, hmem, rfl⟩⟩)

/-- The order-convexity predicate used for intervals. Empty and full sets satisfy it. -/
def IsInterval (I : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ I → ∀ ⦃b⦄, b ∈ I → ∀ ⦃z⦄, a ≤ z → z ≤ b → z ∈ I

/-- The order-convex hull of a finite set, written using two endpoints. -/
def convexHull (T : Finset α) : Set α :=
  {z | ∃ a ∈ T, ∃ b ∈ T, a ≤ z ∧ z ≤ b}

/-- A linear order relation carried as data, so a sweep system may contain many orders. -/
structure LinearOrderRel where
  rel : α → α → Prop
  isLinear : IsLinearOrder α rel

/-- The sweep condition for a finite family of arbitrary linear orders. -/
def IsSweepSystem (k : ℕ) (orders : Fin k → LinearOrderRel (α := α)) : Prop :=
  ∀ I : Set α, IsInterval I → ∀ y, y ∉ I →
    ∃ i, ∀ x ∈ I, (orders i).rel y x

private lemma convexHull_interval (T : Finset α) : IsInterval (convexHull T) := by
  intro a ha b hb z haz hzb
  rcases ha with ⟨a₀, ha₀, b₀, hb₀, ha₀a, hab₀⟩
  rcases hb with ⟨a₁, ha₁, b₁, hb₁mem, ha₁b, hb₁le⟩
  exact ⟨a₀, ha₀, b₁, hb₁mem, ha₀a.trans haz, hzb.trans hb₁le⟩

private lemma mem_convexHull {T : Finset α} {x : α} (hx : x ∈ T) : x ∈ convexHull T := by
  exact ⟨x, hx, x, hx, le_rfl, le_rfl⟩

private lemma not_mem_convexHull_erase_of_threeChainFree
    {S : Finset α} (hfree : ThreeChainFree S) {y : α} (hy : y ∈ S) :
    y ∉ convexHull (S.erase y) := by
  intro hyh
  rcases hyh with ⟨a, ha, b, hb, hay, hyb⟩
  have haS : a ∈ S := Finset.mem_of_mem_erase ha
  have hbS : b ∈ S := Finset.mem_of_mem_erase hb
  have hayne : a ≠ y := by
    intro h
    subst a
    exact (Finset.mem_erase.mp ha).1 rfl
  have hybne : y ≠ b := by
    intro h
    subst b
    exact (Finset.mem_erase.mp hb).1 rfl
  have hay' : a < y := lt_of_le_of_ne hay hayne
  have hyb' : y < b := lt_of_le_of_ne hyb hybne
  exact (hfree haS hy hbS) ⟨hay', hyb'⟩

private lemma theta_witness :
    ∃ S : Finset α, ThreeChainFree S ∧ S.card = theta (α := α) := by
  classical
  let candidates := (Finset.univ : Finset α).powerset.filter ThreeChainFree
  have hcand : candidates.Nonempty := by
    have hmem : (∅ : Finset α) ∈ candidates := by simp [candidates, ThreeChainFree]
    exact ⟨∅, hmem⟩
  let values := candidates.image Finset.card
  have hvalues : values.Nonempty := by
    rcases hcand with ⟨S, hS⟩
    exact ⟨S.card, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
  let m := values.max' hvalues
  have hm : m ∈ values := Finset.max'_mem values hvalues
  rcases Finset.mem_image.mp hm with ⟨S, hS, hcard⟩
  have hfree : ThreeChainFree S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hfree, ?_⟩
  change S.card = values.max' hvalues
  exact hcard

/-- Every sweep system needs at least `theta` orders.

This is the lower-bound half of the Boldi--Vigna sweep-dimension problem. The
matching upper construction and endpoint classifications remain separate goals.
-/
theorem theta_le_of_sweep {k : ℕ} (orders : Fin k → LinearOrderRel (α := α))
    (hsweep : IsSweepSystem k orders) : theta (α := α) ≤ k := by
  classical
  obtain ⟨S, hfree, hcard⟩ := theta_witness (α := α)
  let chooseOrder : {y // y ∈ S} → Fin k := fun y =>
    Classical.choose (hsweep (convexHull (S.erase y.1))
      (convexHull_interval (S.erase y.1)) y.1
      (not_mem_convexHull_erase_of_threeChainFree hfree y.2))
  have hchoose : ∀ y : {y // y ∈ S},
      ∀ x ∈ S.erase y.1, (orders (chooseOrder y)).rel y.1 x := by
    intro y
    intro x hx
    exact Classical.choose_spec (hsweep (convexHull (S.erase y.1))
      (convexHull_interval (S.erase y.1)) y.1
      (not_mem_convexHull_erase_of_threeChainFree hfree y.2)) x
      (mem_convexHull hx)
  have hinj : Function.Injective chooseOrder := by
    intro y z heq
    by_contra hne
    have hyz : z.1 ∈ S.erase y.1 := Finset.mem_erase.mpr ⟨by
      intro h
      exact hne (Subtype.ext h.symm), z.2⟩
    have hzy : y.1 ∈ S.erase z.1 := Finset.mem_erase.mpr ⟨by
      intro h
      exact hne (Subtype.ext h), y.2⟩
    have h₁ := hchoose y z.1 hyz
    have h₂ := hchoose z y.1 hzy
    have heqrel : (orders (chooseOrder y)).rel y.1 z.1 := by simpa [heq] using h₁
    have heqrel' : (orders (chooseOrder y)).rel z.1 y.1 := by simpa [heq] using h₂
    exact hne (Subtype.ext ((orders (chooseOrder y)).isLinear.antisymm _ _ heqrel heqrel'))
  have hcardle : Fintype.card {y // y ∈ S} ≤ Fintype.card (Fin k) :=
    Fintype.card_le_of_injective chooseOrder hinj
  simpa [Fintype.card_coe, hcard] using hcardle

end D5.S3.Combinatorics.SweepDimension.Basic
