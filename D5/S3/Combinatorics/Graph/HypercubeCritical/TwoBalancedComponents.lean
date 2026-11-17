/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A degree-three candidate of size 258 has two balanced cubic components. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension
import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Batteries.Tactic.OpenPrivate

/-! Extract actual balanced cubic components from a degree-three restriction of size 258. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

open scoped Classical
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

/-- Project the support of an actual component of the induced graph back to cube vertices. -/
def componentFinset (U : Finset (Q 9))
    (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) : Finset (Q 9) :=
  K.supp.toFinset.image (fun x : (U : Set (Q 9)) => x.1)

@[simp] theorem mem_componentFinset (U : Finset (Q 9))
    (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) (x : Q 9) :
    x ∈ componentFinset U K ↔
      ∃ hx : x ∈ U, (⟨x, hx⟩ : (U : Set (Q 9))) ∈ K.supp := by
  classical
  simp only [componentFinset, Finset.mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hx, hxK⟩
    exact ⟨⟨x, hx⟩, hxK, rfl⟩

private theorem componentFinset_subset (U : Finset (Q 9))
    (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :
    componentFinset U K ⊆ U := by
  intro x hx
  obtain ⟨hxU, _⟩ := (mem_componentFinset U K x).mp hx
  exact hxU

private theorem componentFinset_nonempty (U : Finset (Q 9))
    (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :
    (componentFinset U K).Nonempty := by
  obtain ⟨x, hx⟩ := K.nonempty_supp
  exact ⟨x.1, (mem_componentFinset U K x.1).mpr ⟨x.2, hx⟩⟩

private theorem componentFinset_neighbor_closed (U : Finset (Q 9))
    (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :
    ∀ x ∈ componentFinset U K, ∀ y ∈ U,
      (hypercube 9).Adj x y → y ∈ componentFinset U K := by
  intro x hx y hy hxy
  obtain ⟨hxU, hxK⟩ := (mem_componentFinset U K x).mp hx
  have hxyU : ((hypercube 9).induce (U : Set (Q 9))).Adj
      ⟨x, hxU⟩ ⟨y, hy⟩ := hxy
  exact (mem_componentFinset U K y).mpr
    ⟨hy, (K.mem_supp_congr_adj hxyU).mp hxK⟩

private theorem componentFinset_disjoint (U : Finset (Q 9))
    (K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (hKL : K ≠ L) : Disjoint (componentFinset U K) (componentFinset U L) := by
  apply Finset.disjoint_left.mpr
  intro x hxK hxL
  obtain ⟨hxU, hxK⟩ := (mem_componentFinset U K x).mp hxK
  obtain ⟨hxU', hxL⟩ := (mem_componentFinset U L x).mp hxL
  apply hKL
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hxK hxL

/-- Saturated edge identities propagate vanishing along actual induced walks. -/
private theorem zero_iff_of_reachable (U : Finset (Q 9)) (z : Q 9 → Real)
    (hdeg : ∀ x : (U : Set (Q 9)),
      ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix 9).mulVec z = (3 : Real) • z)
    {x y : (U : Set (Q 9))}
    (hxy : ((hypercube 9).induce (U : Set (Q 9))).Reachable x y) :
    z x.1 = 0 ↔ z y.1 = 0 := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    have hab' : (hypercube 9).Adj a.1 b.1 := hab
    have hstep : z a.1 = 0 ↔ z b.1 = 0 := by
      constructor
      · intro ha
        exact SupportedEigenSaturation.zero_of_adj_zero U z hdeg hsupport heigen
          a.2 b.2 hab' ha
      · intro hb
        exact SupportedEigenSaturation.zero_of_adj_zero U z hdeg hsupport heigen
          b.2 a.2 hab'.symm hb
    exact hstep.trans ih

private theorem nonzero_on_component (U : Finset (Q 9)) (z : Q 9 → Real)
    (hdeg : ∀ x : (U : Set (Q 9)),
      ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix 9).mulVec z = (3 : Real) • z)
    (x : (U : Set (Q 9))) (hx : z x.1 ≠ 0) :
    ∀ y ∈ componentFinset U
      (((hypercube 9).induce (U : Set (Q 9))).connectedComponentMk x), z y ≠ 0 := by
  intro y hy
  obtain ⟨hyU, hyK⟩ := (mem_componentFinset U _ y).mp hy
  have heq :
      ((hypercube 9).induce (U : Set (Q 9))).connectedComponentMk ⟨y, hyU⟩ =
        ((hypercube 9).induce (U : Set (Q 9))).connectedComponentMk x :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hyK
  have hxy : ((hypercube 9).induce (U : Set (Q 9))).Reachable x ⟨y, hyU⟩ :=
    SimpleGraph.ConnectedComponent.exact heq.symm
  intro hyzero
  exact hx ((zero_iff_of_reachable U z hdeg hsupport heigen hxy).mpr hyzero)

private theorem induced_degree_eq_neighbor_card (S : Finset (Q 9))
    (x : (S : Set (Q 9))) :
    ((hypercube 9).induce (S : Set (Q 9))).degree x =
      ((hypercube 9).neighborFinset x.1 ∩ S).card := by
  classical
  exact (selected_neighbor_card (n := 9) (U := S) (x := x.1) x.2).symm

private theorem componentFinset_regular_and_balanced
    (U : Finset (Q 9)) (z : Q 9 → Real)
    (hdeg : ∀ x : (U : Set (Q 9)),
      ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hsupport : ∀ x ∉ U, z x = 0)
    (heigen : (huangMatrix 9).mulVec z = (3 : Real) • z)
    (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (hK : ∀ x ∈ componentFinset U K, z x ≠ 0) :
    ((hypercube 9).induce (componentFinset U K : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced (componentFinset U K) := by
  classical
  constructor
  · intro x
    have hxU : x.1 ∈ U := componentFinset_subset U K x.2
    have hneighbors :
        (hypercube 9).neighborFinset x.1 ∩ componentFinset U K =
          (hypercube 9).neighborFinset x.1 ∩ U := by
      ext y
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hxy, hy⟩
        exact ⟨hxy, componentFinset_subset U K hy⟩
      · rintro ⟨hxy, hy⟩
        exact ⟨hxy, componentFinset_neighbor_closed U K x.1 x.2 y hy hxy⟩
    calc
      ((hypercube 9).induce (componentFinset U K : Set (Q 9))).degree x =
          ((hypercube 9).neighborFinset x.1 ∩ componentFinset U K).card :=
        induced_degree_eq_neighbor_card (componentFinset U K) x
      _ = ((hypercube 9).neighborFinset x.1 ∩ U).card :=
        congrArg Finset.card hneighbors
      _ = ((hypercube 9).induce (U : Set (Q 9))).degree ⟨x.1, hxU⟩ :=
        (induced_degree_eq_neighbor_card U ⟨x.1, hxU⟩).symm
      _ = 3 := SupportedEigenSaturation.degree_eq_of_ne_zero U z hdeg hsupport
        heigen hxU (hK x.1 x.2)
  · obtain ⟨sigma, hsigma⟩ :=
      SupportedEigenSaturation.nonzeroSupport_isBalanced U z hdeg hsupport heigen
    have hsub : componentFinset U K ⊆ SupportedEigenSaturation.nonzeroSupport U z := by
      intro x hx
      exact SupportedEigenSaturation.mem_nonzeroSupport.mpr
        ⟨componentFinset_subset U K hx, hK x hx⟩
    exact ⟨sigma, (fun x hx => hsigma.1 x (hsub hx)),
      fun x hx y hy hxy => hsigma.2 x (hsub hx) y (hsub hy) hxy⟩

/-- A 258-vertex induced subgraph of maximum degree three has two distinct actual
components that are balanced and cubic in Huang's original signing. -/
theorem exists_two_balanced_components (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)),
      ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      K ≠ L ∧ ∃ C D : Finset (Q 9),
        C = componentFinset U K ∧ D = componentFinset U L ∧
        C.Nonempty ∧ D.Nonempty ∧ C ⊆ U ∧ D ⊆ U ∧ Disjoint C D ∧
        (∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C) ∧
        (∀ x ∈ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ D) ∧
        ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
        ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3 ∧
        IsBalanced C ∧ IsBalanced D ∧
        48 ≤ C.card ∧ 48 ≤ D.card ∧ 96 ≤ (C ∪ D).card := by
  classical
  obtain ⟨z, hz, hzeigen, hzsupport⟩ :=
    SupportedEigenDimension.exists_nonzero_supported_eigenvector U hU
  obtain ⟨x, hzx⟩ : ∃ x : Q 9, z x ≠ 0 := by
    by_contra hn
    apply hz
    funext x
    by_contra hx
    exact hn ⟨x, hx⟩
  have hxU : x ∈ U := by
    by_contra hx
    exact hzx (hzsupport x hx)
  let G := (hypercube 9).induce (U : Set (Q 9))
  let xU : (U : Set (Q 9)) := ⟨x, hxU⟩
  let K : G.ConnectedComponent := G.connectedComponentMk xU
  let C := componentFinset U K
  have hzC : ∀ t ∈ C, z t ≠ 0 :=
    nonzero_on_component U z hdeg hzsupport hzeigen xU hzx
  obtain ⟨w, hw, hwx, hweigen, hwsupport⟩ :=
    SupportedEigenDimension.exists_nonzero_supported_eigenvector_vanishing_at U hU x
  have hwC : ∀ t ∈ C, w t = 0 := by
    intro t ht
    obtain ⟨htU, htK⟩ := (mem_componentFinset U K t).mp ht
    have heq : G.connectedComponentMk ⟨t, htU⟩ = G.connectedComponentMk xU :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff K _).mp htK
    have hxt : G.Reachable xU ⟨t, htU⟩ :=
      SimpleGraph.ConnectedComponent.exact heq.symm
    exact (zero_iff_of_reachable U w hdeg hwsupport hweigen hxt).mp hwx
  obtain ⟨y, hwy⟩ : ∃ y : Q 9, w y ≠ 0 := by
    by_contra hn
    apply hw
    funext y
    by_contra hy
    exact hn ⟨y, hy⟩
  have hyU : y ∈ U := by
    by_contra hy
    exact hwy (hwsupport y hy)
  let yU : (U : Set (Q 9)) := ⟨y, hyU⟩
  let L : G.ConnectedComponent := G.connectedComponentMk yU
  let D := componentFinset U L
  have hwD : ∀ t ∈ D, w t ≠ 0 :=
    nonzero_on_component U w hdeg hwsupport hweigen yU hwy
  have hyL : y ∈ componentFinset U L :=
    (mem_componentFinset U L y).mpr ⟨hyU, by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff L yU).mpr rfl⟩
  have hKL : K ≠ L := by
    intro hKL
    have hyC : y ∈ C := by
      change y ∈ componentFinset U K
      rw [hKL]
      exact hyL
    exact hwy (hwC y hyC)
  obtain ⟨hrC, hbC⟩ :=
    componentFinset_regular_and_balanced U z hdeg hzsupport hzeigen K hzC
  obtain ⟨hrD, hbD⟩ :=
    componentFinset_regular_and_balanced U w hdeg hwsupport hweigen L hwD
  have hC : C.Nonempty := componentFinset_nonempty U K
  have hD : D.Nonempty := componentFinset_nonempty U L
  have hdisj : Disjoint C D := componentFinset_disjoint U K L hKL
  have hC48 : 48 ≤ C.card :=
    BalancedCubeLowerBound.forty_eight_le_card C hC hrC hbC
  have hD48 : 48 ≤ D.card :=
    BalancedCubeLowerBound.forty_eight_le_card D hD hrD hbD
  have h96 : 96 ≤ (C ∪ D).card := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  exact ⟨K, L, hKL, C, D, rfl, rfl, hC, hD,
    componentFinset_subset U K, componentFinset_subset U L, hdisj,
    componentFinset_neighbor_closed U K, componentFinset_neighbor_closed U L,
    hrC, hrD, hbC, hbD, hC48, hD48, h96⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
