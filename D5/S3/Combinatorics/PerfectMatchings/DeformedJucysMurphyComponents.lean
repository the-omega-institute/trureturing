/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: none
   digest: Complete native components and live rotation coordinates for the native row. -/

import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCharge
import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Choose.Cast

/-! Complete components retain singleton identity edges. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

open Equiv
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCharge
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The lower endpoint of the h-th literal identity edge. -/
def edgeVertex {k : ℕ} (h : Fin k) : Fin (2 * k) := ⟨2 * h.val, by omega⟩

/-- The identity edge containing a native vertex. -/
def edgeIndex {k : ℕ} (x : Fin (2 * k)) : Fin k := ⟨x.val / 2, by omega⟩

private theorem vertex_on_identity_edge {k : ℕ} (x : Fin (2 * k)) :
    x = edgeVertex (edgeIndex x) ∨ x = (e k).val (edgeVertex (edgeIndex x)) := by
  by_cases hx : x.val % 2 = 0
  · left
    apply Fin.ext
    change x.val = 2 * (x.val / 2)
    omega
  · right
    apply Fin.ext
    change x.val = if (2 * (x.val / 2)) % 2 = 0 then 2 * (x.val / 2) + 1
      else 2 * (x.val / 2) - 1
    simp only [Nat.mul_mod_right, if_true]
    omega

private instance componentSymmetric {k : ℕ} (p : P k) : Std.Symm (Component p) := by
  haveI : Std.Symm (fun u v : Fin (2 * k) =>
      matchingPerm p u = v ∨ matchingPerm (e k) u = v) := ⟨by
    intro u v huv
    rcases huv with hp | he
    · left
      rw [← hp]
      exact p.property.1 u
    · right
      rw [← he]
      exact (e k).property.1 u⟩
  change Std.Symm (Relation.ReflTransGen (fun u v =>
    matchingPerm p u = v ∨ matchingPerm (e k) u = v))
  infer_instance

private theorem vertex_connected_edge {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    Component p x (edgeVertex (edgeIndex x)) := by
  rcases vertex_on_identity_edge x with hx | hx
  · exact (congrArg (fun z => Component p z (edgeVertex (edgeIndex x))) hx).mpr .refl
  · have he : Component p (edgeVertex (edgeIndex x)) x := by
      apply (congrArg (Component p (edgeVertex (edgeIndex x))) hx).mpr
      exact .single (Or.inr rfl)
    exact symm he

theorem component_symm {k : ℕ} (p : P k) {x y : Fin (2 * k)}
    (h : Component p x y) : Component p y x := by
  exact symm h

/-- Native connectivity restricted to the identity edges. -/
def edgeSetoid {k : ℕ} (p : P k) : Setoid (Fin k) where
  r h i := Component p (edgeVertex h) (edgeVertex i)
  iseqv := {
    refl := fun _ => .refl
    symm := by
      intro h i hi
      exact symm hi
    trans := fun hhi hij => hhi.trans hij }

/-- Each part is an actual component's set of identity-edge occurrences. -/
noncomputable def edgeComponents {k : ℕ} (p : P k) :
    Finpartition (Finset.univ : Finset (Fin k)) :=
  Finpartition.ofSetoid (edgeSetoid p)

/-- Complete coset type: count identity edges in every native component.
Doubled edges give singleton parts, so parts of size one are retained. -/
noncomputable def ct {k : ℕ} (p : P k) : Nat.Partition k where
  parts := (edgeComponents p).parts.val.map Finset.card
  parts_pos := by
    intro r hr
    obtain ⟨C, hC, rfl⟩ := Multiset.mem_map.mp hr
    exact Finset.card_pos.mpr ((edgeComponents p).nonempty_of_mem_parts hC)
  parts_sum := by
    have hs := (edgeComponents p).sum_card_parts
    rw [← Finset.sum_eq_multiset_sum]
    simpa only [Finset.card_univ, Fintype.card_fin] using hs

theorem component_iff_edge_components {k : ℕ} (p : P k) (x y : Fin (2 * k)) :
    Component p x y ↔ (edgeSetoid p).r (edgeIndex x) (edgeIndex y) := by
  constructor
  · intro h
    exact (component_symm p (vertex_connected_edge p x)).trans
      (h.trans (vertex_connected_edge p y))
  · intro h
    exact (vertex_connected_edge p x).trans
      (h.trans (component_symm p (vertex_connected_edge p y)))

theorem edge_component_membership {k : ℕ} (p : P k) (h i : Fin k) :
    i ∈ (edgeComponents p).part h ↔ Component p (edgeVertex h) (edgeVertex i) := by
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- Both literal endpoints of an identity edge; the second coordinate is the parity. -/
def edgeEndpoint {k : ℕ} (h : Fin k) (eps : Fin 2) : Fin (2 * k) :=
  ⟨eps.val + 2 * h.val, by omega⟩

private theorem edgeIndex_endpoint {k : ℕ} (h : Fin k) (eps : Fin 2) :
    edgeIndex (edgeEndpoint h eps) = h := by
  apply Fin.ext
  dsimp [edgeIndex, edgeEndpoint]
  omega

theorem edgeIndex_vertex {k : ℕ} (h : Fin k) :
    edgeIndex (edgeVertex h) = h := by
  apply Fin.ext
  dsimp [edgeIndex, edgeVertex]
  omega

private theorem endpoint_surjective {k : ℕ} (x : Fin (2 * k)) :
    ∃ (h : Fin k) (eps : Fin 2), edgeEndpoint h eps = x := by
  refine ⟨edgeIndex x, ⟨x.val % 2, Nat.mod_lt _ (by omega)⟩, ?_⟩
  apply Fin.ext
  dsimp [edgeEndpoint, edgeIndex]
  omega

private theorem identity_endpoint_zero {k : ℕ} (h : Fin k) :
    (e k).val (edgeEndpoint h 0) = edgeEndpoint h 1 := by
  apply Fin.ext
  change (if (0 + 2 * h.val) % 2 = 0 then 0 + 2 * h.val + 1
    else 0 + 2 * h.val - 1) = 1 + 2 * h.val
  simp [Nat.mul_mod_right, Nat.add_comm]

private theorem identity_endpoint_one {k : ℕ} (h : Fin k) :
    (e k).val (edgeEndpoint h 1) = edgeEndpoint h 0 := by
  rw [← identity_endpoint_zero, (e k).property.1]

private def orientedMap {k : ℕ} (sigma : Perm (Fin k)) (x : Fin (2 * k)) : Fin (2 * k) :=
  if x.val % 2 = 0 then edgeEndpoint (sigma (edgeIndex x)) 1
  else edgeEndpoint (sigma.symm (edgeIndex x)) 0

private theorem orientedMap_zero {k : ℕ} (sigma : Perm (Fin k)) (h : Fin k) :
    orientedMap sigma (edgeEndpoint h 0) = edgeEndpoint (sigma h) 1 := by
  simp only [orientedMap, edgeIndex_endpoint]
  have he : (edgeEndpoint h 0).val % 2 = 0 := by
    dsimp [edgeEndpoint]
    omega
  rw [if_pos he]

private theorem orientedMap_one {k : ℕ} (sigma : Perm (Fin k)) (h : Fin k) :
    orientedMap sigma (edgeEndpoint h 1) = edgeEndpoint (sigma.symm h) 0 := by
  simp only [orientedMap, edgeIndex_endpoint]
  have he : ¬ (edgeEndpoint h 1).val % 2 = 0 := by
    dsimp [edgeEndpoint]
    omega
  rw [if_neg he]

/-- An actual native matching attached to an arbitrary edge permutation.
The two orientations use sigma and its inverse, including fixed edges. -/
def oriented {k : ℕ} (sigma : Perm (Fin k)) : P k := ⟨orientedMap sigma, by
  constructor
  · intro x
    obtain ⟨h, eps, rfl⟩ := endpoint_surjective x
    fin_cases eps
    · change orientedMap sigma (orientedMap sigma (edgeEndpoint h 0)) = edgeEndpoint h 0
      rw [orientedMap_zero, orientedMap_one, sigma.symm_apply_apply]
    · change orientedMap sigma (orientedMap sigma (edgeEndpoint h 1)) = edgeEndpoint h 1
      rw [orientedMap_one, orientedMap_zero, sigma.apply_symm_apply]
  · intro x heq
    obtain ⟨h, eps, rfl⟩ := endpoint_surjective x
    fin_cases eps
    · change orientedMap sigma (edgeEndpoint h 0) = edgeEndpoint h 0 at heq
      rw [orientedMap_zero] at heq
      have hv := congrArg Fin.val heq
      dsimp [edgeEndpoint] at hv
      omega
    · change orientedMap sigma (edgeEndpoint h 1) = edgeEndpoint h 1 at heq
      rw [orientedMap_one] at heq
      have hv := congrArg Fin.val heq
      dsimp [edgeEndpoint] at hv
      omega⟩

private theorem oriented_edge_step {k : ℕ} (sigma : Perm (Fin k)) (h : Fin k) :
    Component (oriented sigma) (edgeEndpoint h 0) (edgeEndpoint (sigma h) 0) := by
  apply Relation.ReflTransGen.trans
    (show Component (oriented sigma) (edgeEndpoint h 0) (edgeEndpoint (sigma h) 1) from
      .single (Or.inl (orientedMap_zero sigma h)))
  exact .single (Or.inr (identity_endpoint_one (sigma h)))

private theorem oriented_index_step {k : ℕ} (sigma : Perm (Fin k)) (x : Fin (2 * k)) :
    sigma.SameCycle (edgeIndex x) (edgeIndex ((oriented sigma).val x)) := by
  obtain ⟨h, eps, rfl⟩ := endpoint_surjective x
  fin_cases eps
  · change sigma.SameCycle (edgeIndex (edgeEndpoint h 0))
      (edgeIndex (orientedMap sigma (edgeEndpoint h 0)))
    rw [orientedMap_zero, edgeIndex_endpoint, edgeIndex_endpoint]
    exact (Perm.SameCycle.refl sigma h).apply_right
  · change sigma.SameCycle (edgeIndex (edgeEndpoint h 1))
      (edgeIndex (orientedMap sigma (edgeEndpoint h 1)))
    rw [orientedMap_one, edgeIndex_endpoint, edgeIndex_endpoint]
    exact (Perm.SameCycle.refl sigma h).symm_apply_right

/-- The original class indicator, on literal native partner maps. -/
noncomputable def indicator {K : Type*} [Zero K] [One K] {k : ℕ}
    (lam : Nat.Partition k) (p : P k) : K := if ct p = lam then 1 else 0

/-- The exact sum J_1+...+J_k; Fin k indexes i-1. -/
noncomputable def S {K : Type*} [CommRing K] (b : K) (k : ℕ) :
    (P k → K) →ₗ[K] (P k → K) := ∑ i : Fin k, J b k (i.val + 1)

/-- The two earlier endpoints in the native J_(q+1) summation. -/
def earlierVertex {k : ℕ} (q : Fin k) (h : Fin q.val) (eps : Fin 2) : Fin (2 * k) :=
  ⟨eps.val + 2 * h.val, by omega⟩

theorem earlier_identity_partner {k : ℕ} (q : Fin k) (h : Fin q.val) :
    (e k).val (earlierVertex q h 0) = earlierVertex q h 1 := by
  apply Fin.ext
  change (if (0 + 2 * h.val) % 2 = 0 then 0 + 2 * h.val + 1
    else 0 + 2 * h.val - 1) = 1 + 2 * h.val
  simp [Nat.mul_mod_right, Nat.add_comm]

private theorem J_pair_expansion {K : Type*} [CommRing K] (b : K) {k : ℕ}
    (q : Fin k) (f : P k → K) (p : P k) :
    J b k (q.val + 1) f p = ∑ h : Fin q.val,
      (weight b p (earlierVertex q h 0) (edgeVertex q) *
        f (act (earlierVertex q h 0) (edgeVertex q) p) +
       weight b p (earlierVertex q h 1) (edgeVertex q) *
        f (act (earlierVertex q h 1) (edgeVertex q) p)) := by
  have hi : 0 < q.val + 1 ∧ q.val + 1 ≤ k := by omega
  change (if hi : 0 < q.val + 1 ∧ q.val + 1 ≤ k then
    ∑ a : Fin (2 * (q.val + 1) - 2),
      weight b p ⟨a.val, by omega⟩ ⟨2 * (q.val + 1) - 2, by omega⟩ *
        f (act ⟨a.val, by omega⟩ ⟨2 * (q.val + 1) - 2, by omega⟩ p)
    else 0) = _
  rw [dif_pos hi]
  have hsize : 2 * (q.val + 1) - 2 = 2 * q.val := by omega
  simp only [hsize]
  let F : Fin (2 * q.val) → K := fun a =>
    weight b p ⟨a.val, by omega⟩ (edgeVertex q) *
      f (act ⟨a.val, by omega⟩ (edgeVertex q) p)
  change (∑ a, F a) = _
  let equiv : Fin q.val × Fin 2 ≃ Fin (2 * q.val) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm q.val 2))
  rw [← equiv.sum_comp F, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [Fin.sum_univ_two]
  rfl

private theorem sameCycle_partner_excluded {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    ¬ (matchingPerm p * matchingPerm (e k)).SameCycle x (p.val x) := by
  exact (fixedPointFree_iff_rotation_separation (matchingPerm p) (matchingPerm (e k))
    p.property.1 (e k).property.1).mp ⟨p.property.2, (e k).property.2⟩ x

theorem charge_partner {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    charge p (p.val x) = !(charge p x) := by
  classical
  let R := matchingPerm p * matchingPerm (e k)
  obtain ⟨m, hm, _, hcharge⟩ := charge_maximum_characterization p x
  have hx : Component p x x := .refl
  have hp : Component p x (p.val x) := .single (Or.inl rfl)
  rw [hcharge _ hp, hcharge _ hx]
  have hsplit : R.SameCycle x m ∨ R.SameCycle (p.val x) m :=
    (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
      p.property.1 (e k).property.1 x m).mp hm
  have hsep : ¬ R.SameCycle x (p.val x) := sameCycle_partner_excluded p x
  rcases hsplit with h | h
  · have hn : ¬ R.SameCycle (p.val x) m := fun h' => hsep (h.trans h'.symm)
    simp [R] at h hn ⊢
    simp_all
  · have hn : ¬ R.SameCycle x m := fun h' => hsep (h'.trans h.symm)
    simp_all [R]

theorem charge_identity_partner {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    charge p ((e k).val x) = !(charge p x) := by
  classical
  let R := matchingPerm p * matchingPerm (e k)
  obtain ⟨m, hm, _, hcharge⟩ := charge_maximum_characterization p x
  have hx : Component p x x := .refl
  have he : Component p x ((e k).val x) := .single (Or.inr rfl)
  rw [hcharge _ he, hcharge _ hx]
  have hep : R.SameCycle ((e k).val x) (p.val x) := by
    have h := (Perm.SameCycle.refl R ((e k).val x)).apply_right
    change R.SameCycle ((e k).val x) (p.val ((e k).val ((e k).val x))) at h
    rwa [(e k).property.1 x] at h
  have hsplit : R.SameCycle x m ∨ R.SameCycle (p.val x) m :=
    (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
      p.property.1 (e k).property.1 x m).mp hm
  have hsep : ¬ R.SameCycle x (p.val x) := sameCycle_partner_excluded p x
  rcases hsplit with h | h
  · have hn : ¬ R.SameCycle ((e k).val x) m :=
      fun h' => hsep (h.trans h'.symm |>.trans hep)
    simp_all [R]
  · have hh : R.SameCycle ((e k).val x) m := hep.trans h
    have hn : ¬ R.SameCycle x m := fun h' => hsep (h'.trans h.symm)
    simp_all [R]

theorem charge_of_sameCycle {k : ℕ} (p : P k) {x y : Fin (2 * k)}
    (h : (matchingPerm p * matchingPerm (e k)).SameCycle x y) :
    charge p x = charge p y := by
  have hc : Component p x y :=
    (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
      p.property.1 (e k).property.1 x y).mpr (Or.inl h)
  obtain ⟨m, _, _, hcharge⟩ := charge_maximum_characterization p x
  rw [hcharge x .refl, hcharge y hc]
  have hi : (matchingPerm p * matchingPerm (e k)).SameCycle x m ↔
      (matchingPerm p * matchingPerm (e k)).SameCycle y m :=
    ⟨fun hm => h.symm.trans hm, fun hm => h.trans hm⟩
  simp only [hi]

theorem same_charge_iff {k : ℕ} (p : P k) {x y : Fin (2 * k)}
    (hc : Component p x y) : charge p x = charge p y ↔
      (matchingPerm p * matchingPerm (e k)).SameCycle x y := by
  constructor
  · intro heq
    rcases (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
      p.property.1 (e k).property.1 x y).mp hc with h | h
    · exact h
    · have hy := charge_of_sameCycle p h
      change charge p (p.val x) = charge p y at hy
      rw [charge_partner] at hy
      rw [← heq] at hy
      cases charge p x <;> simp_all
  · exact charge_of_sameCycle p

theorem edgeIndex_identity_partner {k : ℕ} (x : Fin (2 * k)) :
    edgeIndex ((e k).val x) = edgeIndex x := by
  apply Fin.ext
  change (if x.val % 2 = 0 then x.val + 1 else x.val - 1) / 2 = x.val / 2
  split <;> omega

private theorem oriented_components {k : ℕ} (sigma : Perm (Fin k))
    (x y : Fin (2 * k)) : Component (oriented sigma) x y ↔
      sigma.SameCycle (edgeIndex x) (edgeIndex y) := by
  constructor
  · intro hc
    induction hc with
    | refl => exact Perm.SameCycle.refl _ _
    | @tail u v h huv ih =>
      apply ih.trans
      rcases huv with hp | he
      · change (oriented sigma).val u = v at hp
        rw [← hp]
        exact oriented_index_step sigma u
      · change (e k).val u = v at he
        rw [← he, edgeIndex_identity_partner]
  · intro hc
    obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
    have hpath : ∀ m : ℕ, Component (oriented sigma)
        (edgeEndpoint (edgeIndex x) 0)
        (edgeEndpoint ((sigma ^ m) (edgeIndex x)) 0) := by
      intro m
      induction m with
      | zero => exact .refl
      | succ m ih =>
        rw [pow_succ', Perm.mul_apply]
        exact ih.trans (oriented_edge_step sigma ((sigma ^ m) (edgeIndex x)))
    have hp := hpath n
    rw [hn] at hp
    have hp' : Component (oriented sigma)
        (edgeVertex (edgeIndex x)) (edgeVertex (edgeIndex y)) := by
      simpa only [edgeEndpoint, edgeVertex, Fin.val_zero, zero_add] using hp
    exact (vertex_connected_edge (oriented sigma) x).trans
      (hp'.trans (component_symm (oriented sigma) (vertex_connected_edge (oriented sigma) y)))

private theorem oriented_edgeSetoid {k : ℕ} (sigma : Perm (Fin k)) :
    edgeSetoid (oriented sigma) = Perm.SameCycle.setoid sigma := by
  apply Setoid.ext
  intro h i
  change Component (oriented sigma) (edgeVertex h) (edgeVertex i) ↔ sigma.SameCycle h i
  rw [oriented_components, edgeIndex_vertex, edgeIndex_vertex]

theorem ct_oriented {k : ℕ} (sigma : Perm (Fin k)) :
    (ct (oriented sigma)).parts =
      (Finpartition.ofSetoid (Perm.SameCycle.setoid sigma)).parts.val.map Finset.card := by
  change (Finpartition.ofSetoid (edgeSetoid (oriented sigma))).parts.val.map Finset.card = _
  rw [oriented_edgeSetoid]

theorem edgeIndex_charge_injective {k : ℕ} (p : P k) {x y : Fin (2 * k)}
    (hi : edgeIndex x = edgeIndex y) (hc : charge p x = charge p y) : x = y := by
  have he : edgeVertex (edgeIndex x) = edgeVertex (edgeIndex y) := congrArg edgeVertex hi
  rcases vertex_on_identity_edge x with hx | hx <;>
    rcases vertex_on_identity_edge y with hy | hy
  · exact hx.trans (he.trans hy.symm)
  · have hc' : charge p (edgeVertex (edgeIndex x)) =
        charge p ((e k).val (edgeVertex (edgeIndex y))) :=
      (congrArg (charge p) hx).symm.trans (hc.trans (congrArg (charge p) hy))
    rw [he, charge_identity_partner] at hc'
    have hn : ∀ b : Bool, b ≠ !b := by intro b; cases b <;> decide
    exact False.elim (hn _ hc')
  · have hc' : charge p ((e k).val (edgeVertex (edgeIndex x))) =
        charge p (edgeVertex (edgeIndex y)) :=
      (congrArg (charge p) hx).symm.trans (hc.trans (congrArg (charge p) hy))
    rw [he, charge_identity_partner] at hc'
    have hn : ∀ b : Bool, b ≠ !b := by intro b; cases b <;> decide
    exact False.elim (hn _ hc'.symm)
  · exact hx.trans ((congrArg (e k).val he).trans hy.symm)

theorem rotation_connected {k : ℕ} (p : P k) {x y : Fin (2 * k)}
    (hy : (matchingPerm p * matchingPerm (e k)).SameCycle x y) : Component p x y :=
  (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
    p.property.1 (e k).property.1 x y).mpr (Or.inl hy)

def orbitEdge {k : ℕ} (p : P k) (x : Fin (2 * k))
    (y : {y : Fin (2 * k) // (matchingPerm p * matchingPerm (e k)).SameCycle x y}) :
    {h : Fin k // h ∈ (edgeComponents p).part (edgeIndex x)} :=
  ⟨edgeIndex y.val, (edge_component_membership p _ _).mpr
    ((component_iff_edge_components p x y.val).mp (rotation_connected p y.property))⟩

theorem orbitEdge_bijective {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    Function.Bijective (orbitEdge p x) := by
  constructor
  · intro y z heq
    apply Subtype.ext
    apply edgeIndex_charge_injective p (congrArg Subtype.val heq)
    exact charge_of_sameCycle p (y.property.symm.trans z.property)
  · intro h
    have hc : Component p x (edgeVertex h.val) :=
      (component_iff_edge_components p x _).mpr (by
        have hi : edgeIndex (edgeVertex h.val) = h.val := edgeIndex_vertex h.val
        rw [hi]
        exact (edge_component_membership p _ _).mp h.property)
    rcases (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
      p.property.1 (e k).property.1 x (edgeVertex h.val)).mp hc with hr | hr
    · refine ⟨⟨edgeVertex h.val, hr⟩, ?_⟩
      apply Subtype.ext
      exact edgeIndex_vertex h.val
    · change edgeVertex h.val ∈
        RotationOrbit (matchingPerm p * matchingPerm (e k)) ((matchingPerm p) x) at hr
      rw [← (component_split (matchingPerm p) (matchingPerm (e k))
        p.property.1 (e k).property.1 p.property.2 (e k).property.2 x).2.2.2.2.2] at hr
      obtain ⟨z, hz, heq⟩ := hr
      refine ⟨⟨z, hz⟩, ?_⟩
      apply Subtype.ext
      have hi := congrArg edgeIndex heq
      change edgeIndex ((e k).val z) = edgeIndex (edgeVertex h.val) at hi
      rw [edgeIndex_identity_partner] at hi
      exact hi.trans (edgeIndex_vertex h.val)

theorem rotation_card {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    Fintype.card {y : Fin (2 * k) // (matchingPerm p * matchingPerm (e k)).SameCycle x y} =
      ((edgeComponents p).part (edgeIndex x)).card := by
  classical
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (Equiv.ofBijective (orbitEdge p x) (orbitEdge_bijective p x))

theorem rotation_act {k : ℕ} (p : P k) (a b : Fin (2 * k)) :
    matchingPerm (act a b p) * matchingPerm (e k) =
      Equiv.swap a b * Equiv.swap (p.val a) (p.val b) *
        (matchingPerm p * matchingPerm (e k)) := by
  apply Equiv.ext
  intro x
  change Equiv.swap a b (p.val (Equiv.swap a b ((e k).val x))) =
    Equiv.swap a b (Equiv.swap (p.val a) (p.val b) (p.val ((e k).val x)))
  exact congrArg (Equiv.swap a b) (p.property.1.injective.map_swap a b _)

theorem act_partner {k : ℕ} (p : P k) (a : Fin (2 * k)) :
    act a (p.val a) p = p := by
  apply Subtype.ext
  funext x
  change Equiv.swap a (p.val a) (p.val (Equiv.swap a (p.val a) x)) = p.val x
  by_cases hxa : x = a
  · subst x
    rw [Equiv.swap_apply_left, p.property.1 a, Equiv.swap_apply_left]
  · by_cases hxp : x = p.val a
    · subst x
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right, p.property.1 a]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxp]
      exact Equiv.swap_apply_of_ne_of_ne
        (fun h => hxp (by have hh := congrArg p.val h; rwa [p.property.1 x] at hh))
        (fun h => hxa (by
          have hh := congrArg p.val h
          rwa [p.property.1 x, p.property.1 a] at hh))

/-- Select the earlier endpoint whose OUTPUT charge agrees with the fixed endpoint. -/
def equalChargeVertex {k : ℕ} (p : P k) (q : Fin k) (h : Fin q.val) : Fin (2 * k) :=
  if charge p (earlierVertex q h 0) = charge p (edgeVertex q)
    then earlierVertex q h 0 else earlierVertex q h 1

/-- The other earlier endpoint, with the opposite OUTPUT charge. -/
def oppositeChargeVertex {k : ℕ} (p : P k) (q : Fin k) (h : Fin q.val) : Fin (2 * k) :=
  if charge p (earlierVertex q h 0) = charge p (edgeVertex q)
    then earlierVertex q h 1 else earlierVertex q h 0

theorem selected_charges {k : ℕ} (p : P k) (q : Fin k) (h : Fin q.val) :
    charge p (equalChargeVertex p q h) = charge p (edgeVertex q) ∧
      charge p (oppositeChargeVertex p q h) = !(charge p (edgeVertex q)) := by
  have hc : charge p (earlierVertex q h 1) = !(charge p (earlierVertex q h 0)) := by
    rw [← earlier_identity_partner]
    exact charge_identity_partner p _
  unfold equalChargeVertex oppositeChargeVertex
  simp only [apply_ite, hc]
  cases hzero : charge p (earlierVertex q h 0) <;>
    cases hq : charge p (edgeVertex q) <;> simp [hzero, hq]

private theorem paired_term {K : Type*} [CommRing K] (b : K) {k : ℕ}
    (p : P k) (q : Fin k) (h : Fin q.val) (f : P k → K) :
    weight b p (earlierVertex q h 0) (edgeVertex q) *
        f (act (earlierVertex q h 0) (edgeVertex q) p) +
      weight b p (earlierVertex q h 1) (edgeVertex q) *
        f (act (earlierVertex q h 1) (edgeVertex q) p) =
      f (act (equalChargeVertex p q h) (edgeVertex q) p) +
        b * f (act (oppositeChargeVertex p q h) (edgeVertex q) p) := by
  have hc : charge p (earlierVertex q h 1) = !(charge p (earlierVertex q h 0)) := by
    rw [← earlier_identity_partner]
    exact charge_identity_partner p _
  unfold weight equalChargeVertex oppositeChargeVertex
  rw [hc]
  cases hzero : charge p (earlierVertex q h 0) <;>
    cases hq : charge p (edgeVertex q) <;> simp [hzero, hq, add_comm]

theorem native_pair_expansion (b : RatFunc ℂ) {k : ℕ}
    (f : P k → RatFunc ℂ) (p : P k) :
    S b k f p = ∑ q : Fin k, ∑ h : Fin q.val,
      (f (act (equalChargeVertex p q h) (edgeVertex q) p) +
        b * f (act (oppositeChargeVertex p q h) (edgeVertex q) p)) := by
  simp only [S, LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [J_pair_expansion]
  exact Finset.sum_congr rfl (fun h _ => paired_term b p q h f)

end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
