/- GID: D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PlanarMatching/RotationFaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual dart rotations, all facial orbits and their binary edge boundaries. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! Facial incidence uses actual darts and the complete integer-power orbit quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.Combinatorics.Graph.PlanarMatching

open SimpleGraph
open scoped BigOperators

/-- A cyclic order at each actual graph vertex, expressed on its actual darts. -/
structure Rotation {V : Type u} (G : SimpleGraph V) where
  rotor : Equiv.Perm G.Dart
  same_vertex : ∀ d e, rotor.SameCycle d e ↔ d.fst = e.fst

namespace Rotation

variable {V : Type u} {G : SimpleGraph V} (R : Rotation G)

/-- Reverse a dart, then turn at its new initial vertex. -/
def facePerm : Equiv.Perm G.Dart :=
  (Equiv.mk Dart.symm Dart.symm Dart.symm_symm Dart.symm_symm).trans R.rotor

/-- All facial orbits, including any singleton orbit. -/
def Face := Quotient (Equiv.Perm.SameCycle.setoid R.facePerm)

/-- The facial orbit containing an actual dart. -/
def face (d : G.Dart) : R.Face := Quotient.mk _ d

noncomputable instance [Fintype V] [DecidableRel G.Adj] : Fintype R.Face := by
  classical
  exact Quotient.fintype _

private theorem face_eq (d e : G.Dart) : R.face d = R.face e ↔ R.facePerm.SameCycle d e :=
  Quotient.eq

private theorem face_step (d : G.Dart) : R.face (R.facePerm d) = R.face d := by
  exact (R.face_eq _ _).mpr ((Equiv.Perm.sameCycle_apply_left).mpr (.refl _ _))

private theorem rotor_fst (d : G.Dart) : (R.rotor d).fst = d.fst :=
  (R.same_vertex _ _).mp ((Equiv.Perm.sameCycle_apply_left).mpr (.refl _ _))

/-- An arbitrary representative is used only to define an unordered-edge map;
the boundary theorem below proves independence of this choice. -/
noncomputable def edgeRep (G : SimpleGraph V) (e : G.edgeSet) :
    {d : G.Dart // d.edge = e.val} := by
  have h : ∀ e : Sym2 V, e ∈ G.edgeSet → ∃ d : G.Dart, d.edge = e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => exact fun hab => ⟨⟨(a, b), hab⟩, rfl⟩
  exact Classical.indefiniteDescription _ (h e.val e.property)

/-- Binary boundary of a face labelling, evaluated on actual unordered edges. -/
noncomputable def boundary : (R.Face → ZMod 2) →ₗ[ZMod 2] (G.edgeSet → ZMod 2) where
  toFun x e := x (R.face (edgeRep G e).val) + x (R.face (edgeRep G e).val.symm)
  map_add' x y := by funext e; simp only [Pi.add_apply]; ring
  map_smul' a x := by funext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem boundary_dart (x : R.Face → ZMod 2) (d : G.Dart) :
    R.boundary x ⟨d.edge, d.edge_mem⟩ = x (R.face d) + x (R.face d.symm) := by
  have he := (edgeRep G ⟨d.edge, d.edge_mem⟩).property
  rcases (dart_edge_eq_iff _ _).mp he with h | h
  · simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, h]
  · simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, h, Dart.symm_symm, add_comm]

private theorem invariant_rotor (x : R.Face → ZMod 2)
    (h : ∀ d, x (R.face d) = x (R.face d.symm)) (d : G.Dart) :
    x (R.face (R.rotor d)) = x (R.face d) := by
  have hs := congrArg x (R.face_step d.symm)
  change x (R.face (R.rotor d)) = x (R.face d.symm) at hs
  exact hs.trans (h d).symm

private theorem invariant_vertex [Finite G.Dart] (x : R.Face → ZMod 2)
    (h : ∀ d, x (R.face d) = x (R.face d.symm))
    (d e : G.Dart) (hv : d.fst = e.fst) : x (R.face d) = x (R.face e) := by
  obtain ⟨n, hn⟩ := ((R.same_vertex d e).mpr hv).exists_nat_pow_eq
  have hi : ∀ n : ℕ, x (R.face ((R.rotor ^ n) d)) = x (R.face d) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, R.invariant_rotor x h]
      exact ih
  exact ((hi n).symm.trans (congrArg (fun t => x (R.face t)) hn))

/-- In a connected graph, a facial labelling with zero edge boundary is constant.
No Euler or geometric assumption is used for this dual-connectivity fact. -/
private theorem boundary_eq_zero_iff [Fintype V] [DecidableRel G.Adj]
    (hc : G.Connected) (x : R.Face → ZMod 2) :
    R.boundary x = 0 ↔ ∃ c : ZMod 2, x = fun _ => c := by
  classical
  constructor
  · intro hx
    have hs (d : G.Dart) : x (R.face d) = x (R.face d.symm) := by
      have hh := congrFun hx ⟨d.edge, d.edge_mem⟩
      rw [R.boundary_dart] at hh
      have hh' : x (R.face d) + x (R.face d.symm) = 0 := hh
      exact add_eq_zero_iff_eq_neg.mp hh' |>.trans (ZModModule.neg_eq_self _)
    have hw {a b : V} (p : G.Walk a b) (d e : G.Dart)
        (ha : d.fst = a) (hb : e.fst = b) : x (R.face d) = x (R.face e) := by
      induction p generalizing d e with
      | nil => exact R.invariant_vertex x hs d e (ha.trans hb.symm)
      | @cons a b c hab p ih =>
        let t : G.Dart := ⟨(a, b), hab⟩
        exact (R.invariant_vertex x hs d t ha).trans ((hs t).trans (ih t.symm e rfl hb))
    by_cases hf : Nonempty R.Face
    · let f := Classical.choice hf
      refine ⟨x f, funext fun g => ?_⟩
      induction g using Quotient.inductionOn with
      | _ e =>
        induction f using Quotient.inductionOn with
        | _ d => exact hw (hc.preconnected e.fst d.fst).some e d rfl rfl
    · exact ⟨0, funext fun g => (hf ⟨g⟩).elim⟩
  · rintro ⟨c, rfl⟩
    ext e
    exact ZModModule.add_self c

private theorem sum_darts [Fintype V] [DecidableRel G.Adj]
    {K : Type*} [AddCommMonoid K] (f : G.Dart → K) :
    (∑ e : G.edgeSet, (f (edgeRep G e).val + f (edgeRep G e).val.symm)) =
      ∑ d : G.Dart, f d := by
  classical
  let pick : G.edgeSet × Bool → G.Dart := fun t =>
    if t.2 then (edgeRep G t.1).val.symm else (edgeRep G t.1).val
  have hedge (t : G.edgeSet × Bool) : (pick t).edge = t.1.val := by
    simp only [pick]
    split <;> simp only [Dart.edge_symm, (edgeRep G t.1).property]
  have hi : Function.Injective pick := by
    rintro ⟨e, b⟩ ⟨e', b'⟩ h
    have he : e = e' := Subtype.ext ((hedge _).symm.trans ((congrArg Dart.edge h).trans (hedge _)))
    subst e'
    congr 1
    cases b <;> cases b' <;> simp only [pick, Bool.false_eq_true, ↓reduceIte] at h ⊢
    · exact ((Dart.symm_ne _ ) h.symm).elim
    · exact ((Dart.symm_ne _ ) h).elim
  have hs : Function.Surjective pick := by
    intro d
    let e : G.edgeSet := ⟨d.edge, d.edge_mem⟩
    have he := (edgeRep G e).property
    rcases (dart_edge_eq_iff _ _).mp he with h | h
    · exact ⟨(e, false), h⟩
    · refine ⟨(e, true), ?_⟩
      change (edgeRep G e).val.symm = d
      rw [h, Dart.symm_symm]
  have hh := Fintype.sum_bijective pick ⟨hi, hs⟩ (f ∘ pick) f (fun _ => rfl)
  simpa [Function.comp_def, Fintype.sum_prod_type, pick, add_comm] using hh

private theorem boundary_relation [Fintype V] [DecidableRel G.Adj]
    (x : R.Face → ZMod 2) :
    R.boundary x ∈
      D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality.characterRelationSpace
        (ZMod 2)
        (D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.endpointCharacters G) := by
  classical
  apply LinearMap.ext_iff.mpr
  intro a
  change (∑ e : G.edgeSet, (R.boundary x e) •
    D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.endpointCharacters G e) a = 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have he (e : G.edgeSet) :
      D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.endpointCharacters G e a =
        a (edgeRep G e).val.fst + a (edgeRep G e).val.snd := by
    unfold D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.endpointCharacters
    conv_lhs => rw [← (edgeRep G e).property]
    rfl
  simp_rw [he]
  have hsum := sum_darts (fun d : G.Dart => x (R.face d) * (a d.fst + a d.snd))
  have heq : (∑ e : G.edgeSet,
      R.boundary x e * (a (edgeRep G e).val.fst + a (edgeRep G e).val.snd)) =
      ∑ d : G.Dart, x (R.face d) * (a d.fst + a d.snd) := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro e _
    change (x (R.face (edgeRep G e).val) + x (R.face (edgeRep G e).val.symm)) * _ = _
    dsimp only [Dart.symm, Prod.swap]
    ring
  rw [heq]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hturn : (∑ d : G.Dart, x (R.face d) * a d.snd) =
      ∑ d : G.Dart, x (R.face d) * a d.fst := by
    apply Fintype.sum_equiv R.facePerm
    intro d
    rw [R.face_step]
    change _ = x (R.face d) * a (R.rotor d.symm).fst
    rw [R.rotor_fst]
    rfl
  rw [hturn]
  exact ZModModule.add_self _

/-- Every facial boundary is a binary combination of actual simple cycles. -/
private theorem boundary_mem_cycle_space [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (x : R.Face → ZMod 2) :
    R.boundary x ∈
      D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.simpleCycleSpace G := by
  classical
  letI : MeasurableSpace (ZMod 2) := ⊤
  letI : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [(D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.finite_graph_cycle_space G).1.1]
  exact R.boundary_relation x

/-- In the signed-Euler-two model every binary simple-cycle combination is a
facial boundary. The kernel consists exactly of constant face functions. -/
theorem face_cycle_exact [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (he : Nonempty G.Dart)
    (hEuler : (Fintype.card V : ℤ) - (Nat.card G.edgeSet : ℤ) +
      (Nat.card R.Face : ℤ) = 2) :
    (∀ (x : R.Face → ZMod 2) (d : G.Dart),
      R.boundary x ⟨d.edge, d.edge_mem⟩ = x (R.face d) + x (R.face d.symm)) ∧
    (∀ x : R.Face → ZMod 2, R.boundary x = 0 ↔ ∃ c, x = fun _ => c) ∧
    LinearMap.range R.boundary =
      D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.simpleCycleSpace G := by
  classical
  refine ⟨R.boundary_dart, R.boundary_eq_zero_iff hc, ?_⟩
  letI : Nonempty R.Face := ⟨R.face (Classical.choice he)⟩
  let C : ZMod 2 →ₗ[ZMod 2] (R.Face → ZMod 2) := LinearMap.pi fun _ => LinearMap.id
  have hC : LinearMap.range C = LinearMap.ker R.boundary := by
    ext x
    simp only [LinearMap.mem_ker, R.boundary_eq_zero_iff hc, LinearMap.mem_range]
    exact exists_congr fun c => Eq.comm
  have hCi : Function.Injective C := by
    intro a b h
    exact congrFun h (Classical.choice (inferInstance : Nonempty R.Face))
  have hker : Module.finrank (ZMod 2) (LinearMap.ker R.boundary) = 1 := by
    rw [← hC, LinearMap.finrank_range_of_inj hCi]
    exact Module.finrank_self _
  have hrank := R.boundary.finrank_range_add_finrank_ker
  rw [hker, Module.finrank_pi] at hrank
  have hle : LinearMap.range R.boundary ≤
      D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.simpleCycleSpace G := by
    rintro _ ⟨x, rfl⟩
    exact R.boundary_mem_cycle_space x
  letI : MeasurableSpace (ZMod 2) := ⊤
  letI : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
  letI : Nonempty V := ⟨(Classical.choice he).fst⟩
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  letI : Subsingleton G.ConnectedComponent := hc.preconnected.subsingleton_connectedComponent
  have hcomp : Fintype.card G.ConnectedComponent = 1 := Fintype.card_eq_one_iff.mpr ⟨G.connectedComponentMk (Classical.choice he).fst, fun _ => Subsingleton.elim _ _⟩
  have h := D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.finite_graph_cycle_space G
  obtain ⟨T, ht, ha, hr⟩ := h.2.1
  obtain ⟨cs, hcs, hp, hd, bs, hb, htree, hbound, hD, hD', hDz, hdim, rest⟩ :=
    h.2.2 T ht ha hr
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hdim]
  simp only [Nat.card_eq_fintype_card, hcomp] at hEuler hDz
  omega

#print axioms face_cycle_exact

private theorem binary_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have h : z.val = 0 ∨ z.val = 1 := by have := z.val_lt; omega
  rcases h with h | h
  · left; apply ZMod.val_injective; simpa using h
  · right; apply ZMod.val_injective; norm_num at *; exact h

private theorem invariant_vertex_local [Finite G.Dart] (x : R.Face → ZMod 2)
    (d e : G.Dart) (hv : d.fst = e.fst)
    (h : ∀ t : G.Dart, t.fst = d.fst → x (R.face t) = x (R.face t.symm)) :
    x (R.face d) = x (R.face e) := by
  obtain ⟨n, hn⟩ := ((R.same_vertex d e).mpr hv).exists_nat_pow_eq
  have hfst (n : ℕ) : ((R.rotor ^ n) d).fst = d.fst :=
    (R.same_vertex _ _).mp ((Equiv.Perm.sameCycle_pow_left).mpr (.refl _ _))
  have hi : ∀ n : ℕ, x (R.face ((R.rotor ^ n) d)) = x (R.face d) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have hs := congrArg x (R.face_step ((R.rotor ^ n) d).symm)
      change x (R.face (R.rotor ((R.rotor ^ n) d))) =
        x (R.face ((R.rotor ^ n) d).symm) at hs
      exact hs.trans ((h _ (hfst n)).symm.trans ih)
  exact (hi n).symm.trans (congrArg (fun t => x (R.face t)) hn)

private theorem cycle_edge_endpoint {a : V} (p : G.Walk a a) (d : G.Dart)
    (h : d.edge ∈ p.edges) : d.fst ∈ p.support :=
  Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨d.edge, h, by simp [Dart.edge]⟩)

private theorem restrict_matching {W : Type*} (H : SimpleGraph W) (S : Set W)
    (hclosed : ∀ v ∈ S, ∀ w, H.Adj v w → w ∈ S)
    (M : H.Subgraph) (hm : M.IsPerfectMatching) :
    ∃ N : (H.induce S).Subgraph, N.IsPerfectMatching ∧
      ∀ v w, N.Adj v w ↔ M.Adj v.val w.val := by
  let N : (H.induce S).Subgraph := {
    verts := Set.univ
    Adj := fun v w => M.Adj v.val w.val
    adj_sub := fun h => M.adj_sub h
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ h => M.adj_symm h⟩ }
  refine ⟨N, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_, fun _ _ => Iff.rfl⟩
  intro v
  obtain ⟨w, hw, hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hm v.val
  refine ⟨⟨w, hclosed v.val v.property w (M.adj_sub hw)⟩, hw, ?_⟩
  intro t ht
  exact Subtype.ext (hu t.val ht)

private theorem region_subgraph [Fintype V] [DecidableEq V]
    (hc : G.Connected) {a : V} (p : G.Walk a a)
    (x : R.Face → ZMod 2) (S : Set V) (b : ZMod 2)
    (hoff : ∀ d : G.Dart, d.fst ∉ p.support → x (R.face d) = x (R.face d.symm))
    (hS : ∀ d : G.Dart, d.fst ∉ p.support → (d.fst ∈ S ↔ x (R.face d) = b)) :
    ∃ H : G.Subgraph,
      H.verts = {v | v ∈ p.support ∨ v ∈ S} ∧
      (∀ d : G.Dart, H.Adj d.fst d.snd ↔
        d.edge ∈ p.edges ∨ (x (R.face d) = b ∧ x (R.face d.symm) = b)) ∧ H.Connected := by
  classical
  let H : G.Subgraph := {
    verts := {v | v ∈ p.support ∨ v ∈ S}
    Adj := fun v w => ∃ h : G.Adj v w,
      s(v,w) ∈ p.edges ∨ (x (R.face ⟨(v,w),h⟩) = b ∧ x (R.face ⟨(w,v),h.symm⟩) = b)
    adj_sub := fun ⟨h, _⟩ => h
    edge_vert := by
      rintro v w ⟨h, he | he⟩
      · exact Or.inl (cycle_edge_endpoint p ⟨(v,w),h⟩ he)
      · by_cases hv : v ∈ p.support
        · exact Or.inl hv
        · exact Or.inr ((hS ⟨(v,w),h⟩ hv).mpr he.1)
    symm := ⟨by
      rintro v w ⟨h, he | he⟩
      · exact ⟨h.symm, Or.inl (by simpa only [Sym2.eq_swap] using he)⟩
      · exact ⟨h.symm, Or.inr ⟨he.2, he.1⟩⟩⟩ }
  have hadj (d : G.Dart) : H.Adj d.fst d.snd ↔
      d.edge ∈ p.edges ∨ (x (R.face d) = b ∧ x (R.face d.symm) = b) := by
    change (∃ h : G.Adj d.fst d.snd, _) ↔ _
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨d.adj, h⟩⟩
  have hpH : p.toSubgraph ≤ H := by
    constructor
    · intro v hv; exact Or.inl (p.mem_verts_toSubgraph.mp hv)
    · intro v w hvw
      exact ⟨p.toSubgraph.adj_sub hvw,
        Or.inl (p.adj_toSubgraph_iff_mem_edges.mp hvw)⟩
  let root : H.verts := ⟨a, Or.inl p.start_mem_support⟩
  have hcycle (v : H.verts) (hv : v.val ∈ p.support) : H.coe.Reachable v root := by
    exact (p.toSubgraph_connected ⟨v.val, p.mem_verts_toSubgraph.mpr hv⟩
      ⟨a, p.start_mem_verts_toSubgraph⟩).map (Subgraph.inclusion hpH)
  have hwalk {v : V} (q : G.Walk v a) :
      ∀ hv : v ∈ H.verts, H.coe.Reachable ⟨v,hv⟩ root := by
    induction q with
    | nil => intro hv; exact Reachable.rfl
    | @cons v w a hvw q ih =>
      intro hv
      by_cases hvc : v ∈ p.support
      · exact hcycle ⟨v,hv⟩ hvc
      · have hvs : v ∈ S := hv.resolve_left hvc
        let d : G.Dart := ⟨(v,w),hvw⟩
        have hdx : x (R.face d) = b := (hS d hvc).mp hvs
        have hdy : x (R.face d.symm) = b := (hoff d hvc).symm.trans hdx
        have hw : w ∈ H.verts := by
          by_cases hwc : w ∈ p.support
          · exact Or.inl hwc
          · exact Or.inr ((hS d.symm hwc).mpr hdy)
        have hdH : H.coe.Adj ⟨v,hv⟩ ⟨w,hw⟩ :=
          (hadj d).mpr (Or.inr ⟨hdx,hdy⟩)
        exact hdH.reachable.trans (ih p hoff hS hadj hpH hcycle hw)
  refine ⟨H, rfl, hadj, ⟨?_⟩⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable H.coe).mpr
  refine ⟨root, fun v => ?_⟩
  exact (hwalk (hc.preconnected v.val a).some v.property).symm

/-- A simple cycle has a nontrivial binary facial side, and all off-cycle
vertices belong to one of two actual sides with no original edge between them.
Every perfect matching of the actual vertex-deleted complement restricts to
both sides, so each side has even cardinality. -/
theorem cycle_face_sides [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (he : Nonempty G.Dart)
    (hEuler : (Fintype.card V : ℤ) - (Nat.card G.edgeSet : ℤ) +
      (Nat.card R.Face : ℤ) = 2)
    (a : V) (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ (x : R.Face → ZMod 2) (I J : Set V),
      (∃ f, x f = 1) ∧ (∃ f, x f = 0) ∧
      R.boundary x = (fun e : G.edgeSet => if e.val ∈ p.edges then 1 else 0) ∧
      (∀ v, v ∉ p.support ↔ v ∈ I ∨ v ∈ J) ∧ Disjoint I J ∧
      (∀ d : G.Dart, d.fst ∉ p.support →
        (d.fst ∈ I ↔ x (R.face d) = 1) ∧ (d.fst ∈ J ↔ x (R.face d) = 0)) ∧
      (∀ v ∈ I, ∀ w ∈ J, ¬G.Adj v w) ∧
      (∀ (S : Set V) (b : ZMod 2), (S = I ∧ b = 1) ∨ (S = J ∧ b = 0) →
        ∃ H : G.Subgraph,
          H.verts = {v | v ∈ p.support ∨ v ∈ S} ∧
          (∀ d : G.Dart, H.Adj d.fst d.snd ↔
            d.edge ∈ p.edges ∨ (x (R.face d) = b ∧ x (R.face d.symm) = b)) ∧ H.Connected) ∧
      (∀ (M : (G.induce {v | v ∉ p.support}).Subgraph), M.IsPerfectMatching →
        (∀ S ∈ ({I, J} : Set (Set V)),
          ∃ N : ((G.induce {v | v ∉ p.support}).induce {v | v.val ∈ S}).Subgraph,
            N.IsPerfectMatching ∧ ∀ v w, N.Adj v w ↔ M.Adj v.val w.val) ∧
        Even (Nat.card I) ∧ Even (Nat.card J)) := by
  classical
  let z : G.edgeSet → ZMod 2 := fun e => if e.val ∈ p.edges then 1 else 0
  have hz : z ∈ D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.simpleCycleSpace G :=
    Submodule.subset_span ⟨a, p, hp, rfl⟩
  rw [← (R.face_cycle_exact hc he hEuler).2.2] at hz
  obtain ⟨x, hx⟩ := hz
  have hzn : z ≠ 0 := by
    intro h
    cases p with
    | nil => exact hp.ne_nil rfl
    | @cons a b c hab q =>
      have hh := congrFun h ⟨s(a,b), hab⟩
      simp [z, Walk.edges_cons] at hh
  have h1 : ∃ f, x f = 1 := by
    by_contra h
    have hzero : x = 0 := by
      funext f
      exact (binary_zero_or_one (x f)).resolve_right (fun hf => h ⟨f, hf⟩)
    exact hzn (hx.symm.trans (by rw [hzero, map_zero]))
  have h0 : ∃ f, x f = 0 := by
    by_contra h
    have hone : x = fun _ => 1 := by
      funext f
      exact (binary_zero_or_one (x f)).resolve_left (fun hf => h ⟨f, hf⟩)
    exact hzn (hx.symm.trans ((R.boundary_eq_zero_iff hc x).mpr ⟨1, hone⟩))
  have hoff (d : G.Dart) (hd : d.fst ∉ p.support) :
      x (R.face d) = x (R.face d.symm) := by
    have hed : d.edge ∉ p.edges := fun h => hd (cycle_edge_endpoint p d h)
    have hh := congrFun hx ⟨d.edge, d.edge_mem⟩
    rw [R.boundary_dart] at hh
    have hh' : x (R.face d) + x (R.face d.symm) = 0 := by simpa [z, hed] using hh
    exact (add_eq_zero_iff_eq_neg.mp hh').trans (ZModModule.neg_eq_self _)
  let I : Set V := {v | v ∉ p.support ∧ ∃ d : G.Dart, d.fst = v ∧ x (R.face d) = 1}
  let J : Set V := {v | v ∉ p.support ∧ ∃ d : G.Dart, d.fst = v ∧ x (R.face d) = 0}
  have hconst (d e : G.Dart) (hv : d.fst = e.fst) (hd : d.fst ∉ p.support) :
      x (R.face d) = x (R.face e) := by
    apply R.invariant_vertex_local x d e hv
    intro t ht
    exact hoff t (by simpa only [ht] using hd)
  have hI (d : G.Dart) (hd : d.fst ∉ p.support) : d.fst ∈ I ↔ x (R.face d) = 1 := by
    constructor
    · rintro ⟨_, t, ht, hx1⟩
      exact (hconst d t ht.symm hd).trans hx1
    · intro hx1; exact ⟨hd, d, rfl, hx1⟩
  have hJ (d : G.Dart) (hd : d.fst ∉ p.support) : d.fst ∈ J ↔ x (R.face d) = 0 := by
    constructor
    · rintro ⟨_, t, ht, hx0⟩
      exact (hconst d t ht.symm hd).trans hx0
    · intro hx0; exact ⟨hd, d, rfl, hx0⟩
  have hpart : ∀ v, v ∉ p.support ↔ v ∈ I ∨ v ∈ J := by
    intro v
    constructor
    · intro hv
      letI : Nontrivial V := nontrivial_of_ne (Classical.choice he).fst (Classical.choice he).snd
        (Classical.choice he).fst_ne_snd
      obtain ⟨w, hvw⟩ := hc.preconnected.exists_adj_of_nontrivial v
      let d : G.Dart := ⟨(v,w),hvw⟩
      rcases binary_zero_or_one (x (R.face d)) with h | h
      · exact Or.inr ((hJ d hv).mpr h)
      · exact Or.inl ((hI d hv).mpr h)
    · rintro (h | h) <;> exact h.1
  have hdis : Disjoint I J := by
    apply Set.disjoint_left.mpr
    rintro v ⟨hv, d, hd, hxd⟩ ⟨_, e, he', hxe⟩
    have hh := hconst d e (hd.trans he'.symm) (by simpa only [hd] using hv)
    rw [hxd, hxe] at hh
    exact one_ne_zero hh
  have hnc : ∀ v ∈ I, ∀ w ∈ J, ¬G.Adj v w := by
    intro v hv w hw hvw
    let d : G.Dart := ⟨(v,w),hvw⟩
    have hdx : x (R.face d) = 1 := (hI d hv.1).mp hv
    have hdy : x (R.face d.symm) = 0 := (hJ d.symm hw.1).mp hw
    have hh := hoff d hv.1
    rw [hdx, hdy] at hh
    exact one_ne_zero hh
  have hregions (S : Set V) (b : ZMod 2)
      (hb : (S = I ∧ b = 1) ∨ (S = J ∧ b = 0)) := by
    apply R.region_subgraph hc p x S b hoff
    intro d hd
    rcases hb with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hI d hd
    · exact hJ d hd
  refine ⟨x, I, J, h1, h0, hx, hpart, hdis, fun d hd => ⟨hI d hd, hJ d hd⟩,
    hnc, hregions, ?_⟩
  intro M hm
  have hclosed (S : Set V) (hS : S ∈ ({I, J} : Set (Set V))) :
      ∀ v : {v | v ∉ p.support}, v.val ∈ S →
        ∀ w : {v | v ∉ p.support}, G.Adj v.val w.val → w.val ∈ S := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS
    rcases hS with rfl | rfl
    · intro v hv w hvw
      rcases (hpart w.val).mp w.property with hw | hw
      · exact hw
      · exact (hnc v.val hv w.val hw hvw).elim
    · intro v hv w hvw
      rcases (hpart w.val).mp w.property with hw | hw
      · exact (hnc w.val hw v.val hv hvw.symm).elim
      · exact hw
  have hrestrict (S : Set V) (hS : S ∈ ({I, J} : Set (Set V))) :=
    restrict_matching (G.induce {v | v ∉ p.support}) {v | v.val ∈ S} (hclosed S hS) M hm
  have heven (S : Set V) (hS : S ∈ ({I, J} : Set (Set V)))
      (hsub : ∀ v ∈ S, v ∉ p.support) : Even (Nat.card S) := by
    obtain ⟨N, hN, _⟩ := hrestrict S hS
    have hcard := hN.even_card
    let e : {v : {v | v ∉ p.support} // v.val ∈ S} ≃ S := {
      toFun := fun v => ⟨v.val.val, v.property⟩
      invFun := fun v => ⟨⟨v.val, hsub v.val v.property⟩, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [← Nat.card_eq_fintype_card] at hcard
    exact (Nat.card_congr e) ▸ hcard
  exact ⟨hrestrict, heven I (by simp) (fun _ h => h.1),
    heven J (by simp) (fun _ h => h.1)⟩

#print axioms cycle_face_sides

end Rotation
end D5.S3.Combinatorics.Graph.PlanarMatching
