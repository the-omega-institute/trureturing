/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BalancedComponentExcess
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BalancedComponentExcess
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Sizes of balanced cubic components bound the excess of a subcubic Q9 set. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

/-! Bound the excess over 256 in terms of the minimum size of a balanced cubic component. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BalancedComponentExcess

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open SupportedEigenDimension (supportedEigenSpace mem_supportedEigenSpace_iff)
open TwoBalancedComponents (componentFinset)
open private supportRestriction kerToSupported kerToSupported_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension
open private componentFinset_subset componentFinset_nonempty componentFinset_neighbor_closed
  componentFinset_disjoint nonzero_on_component componentFinset_regular_and_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

/-- The excess over half the cube is bounded by the dimension of the positive
Huang eigenspace supported on the selected vertices. -/
theorem card_le_half_add_finrank (U : Finset (Q 9)) :
    U.card ≤ 256 + Module.finrank Real (supportedEigenSpace U) := by
  classical
  have hsource : Module.finrank Real (Sensitivity.V 8) = 256 := by
    rw [Sensitivity.finrank_V]
    norm_num
  have htarget :
      Module.finrank Real ({x : Q 9 // x ∉ U} → Real) = 512 - U.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
      Sensitivity.Q.card, Fintype.card_coe U]
    norm_num
  have hcard : U.card ≤ 512 := by
    simpa [Sensitivity.Q.card] using Finset.card_le_univ U
  let L := supportRestriction U
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [hsource] at hrank
  have hrange : Module.finrank Real (LinearMap.range L) ≤ 512 - U.card := by
    rw [← htarget]
    exact (LinearMap.range L).finrank_le
  have hker : Module.finrank Real (LinearMap.ker L) ≤
      Module.finrank Real (supportedEigenSpace U) :=
    LinearMap.finrank_le_finrank_of_injective (kerToSupported_injective U)
  omega

/-- If every nonempty, neighbor-closed balanced cubic subset has at least `m` vertices,
the supported eigenspace uses at least `m` vertices per dimension. -/
theorem mul_finrank_le_card (U : Finset (Q 9)) (m : Nat)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hmin : ∀ C : Finset (Q 9), C ⊆ U → C.Nonempty →
      (∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C) →
      ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 → IsBalanced C →
      m ≤ C.card) :
    m * Module.finrank Real (supportedEigenSpace U) ≤ U.card := by
  classical
  let G := (hypercube 9).induce (U : Set (Q 9))
  let K := {k : G.ConnectedComponent //
    ((hypercube 9).induce (componentFinset U k : Set (Q 9))).IsRegularOfDegree 3 ∧
    IsBalanced (componentFinset U k)}
  let _ : Fintype K := Fintype.ofFinite K
  let vertices (k : K) : Finset (Q 9) := componentFinset U k.1
  let vertex (k : K) : Q 9 := (componentFinset_nonempty U k.1).choose
  have vertex_mem (k : K) : vertex k ∈ vertices k :=
    (componentFinset_nonempty U k.1).choose_spec
  let eval : supportedEigenSpace U →ₗ[Real] (K → Real) :=
    { toFun := fun z k => z.1 (vertex k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have eval_injective : Function.Injective eval := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z heval
    obtain ⟨heigen, hsupport⟩ := (mem_supportedEigenSpace_iff U z.1).mp z.2
    apply Subtype.ext
    funext x
    change z.1 x = 0
    by_contra hx
    have hxU : x ∈ U := by
      by_contra hxU
      exact hx (hsupport x hxU)
    let xU : (U : Set (Q 9)) := ⟨x, hxU⟩
    let k := G.connectedComponentMk xU
    have hnonzero : ∀ y ∈ componentFinset U k, z.1 y ≠ 0 :=
      nonzero_on_component U z.1 hdeg hsupport heigen xU hx
    let index : K := ⟨k,
      componentFinset_regular_and_balanced U z.1 hdeg hsupport heigen k hnonzero⟩
    exact hnonzero (vertex index) (vertex_mem index) (congrFun heval index)
  have hdim : Module.finrank Real (supportedEigenSpace U) ≤ Fintype.card K := by
    rw [← Module.finrank_fintype_fun_eq_card Real]
    exact LinearMap.finrank_le_finrank_of_injective eval_injective
  have hdisjoint : (↑(Finset.univ : Finset K) : Set K).PairwiseDisjoint vertices := by
    intro k _ l _ hkl
    exact componentFinset_disjoint U k.1 l.1 (fun h => hkl (Subtype.ext h))
  have hunion : (Finset.univ : Finset K).biUnion vertices ⊆ U := by
    intro x hx
    obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hx
    exact componentFinset_subset U k.1 hxk
  calc
    m * Module.finrank Real (supportedEigenSpace U) ≤ m * Fintype.card K :=
      Nat.mul_le_mul_left m hdim
    _ = ∑ _k : K, m := by simp [Nat.mul_comm]
    _ ≤ ∑ k : K, (vertices k).card := by
      apply Finset.sum_le_sum
      intro k _
      exact hmin (vertices k) (componentFinset_subset U k.1) (componentFinset_nonempty U k.1)
        (componentFinset_neighbor_closed U k.1) k.2.1 k.2.2
    _ = ((Finset.univ : Finset K).biUnion vertices).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ U.card := Finset.card_le_card hunion

/-- A uniform lower bound on the size of closed balanced cubic subsets bounds the excess. -/
theorem mul_card_excess_le_card (U : Finset (Q 9)) (m : Nat)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hmin : ∀ C : Finset (Q 9), C ⊆ U → C.Nonempty →
      (∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C) →
      ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 → IsBalanced C →
      m ≤ C.card) :
    m * (U.card - 256) ≤ U.card := by
  have hcard := card_le_half_add_finrank U
  have hexcess : U.card - 256 ≤ Module.finrank Real (supportedEigenSpace U) := by omega
  exact (Nat.mul_le_mul_left m hexcess).trans (mul_finrank_le_card U m hdeg hmin)

/-- A minimum size of 72 for nonempty closed balanced cubic subsets gives at most 259 vertices. -/
theorem card_le_259_of_seventy_two_le (U : Finset (Q 9))
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hmin : ∀ C : Finset (Q 9), C ⊆ U → C.Nonempty →
      (∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C) →
      ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 → IsBalanced C →
      72 ≤ C.card) :
    U.card ≤ 259 := by
  have h := mul_card_excess_le_card U 72 hdeg hmin
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BalancedComponentExcess
