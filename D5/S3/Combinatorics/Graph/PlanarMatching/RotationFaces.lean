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
theorem boundary_eq_zero_iff [Fintype V] [DecidableRel G.Adj] (hc : G.Connected) (x : R.Face → ZMod 2) :
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

#print axioms boundary_eq_zero_iff

end Rotation
end D5.S3.Combinatorics.Graph.PlanarMatching
