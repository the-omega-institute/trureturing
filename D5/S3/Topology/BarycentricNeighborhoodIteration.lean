/- GID: D5/S3/Topology/BarycentricNeighborhoodIteration
   generality: G
   mirror-B: D5/B/S3/Topology/BarycentricNeighborhoodIteration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Closed graph neighborhoods in full subcomplexes propagate under ordinary subdivision. -/

module

public import D5.S3.Topology.BarycentricGraphDistance
public import Mathlib.Order.Preorder.Chain
import OmegaBuild.Commands

/-! # Graph neighborhoods under iterated barycentric subdivision

The simplices of the ordinary subdivision are nonempty chains of faces.
Each subdivided subcomplex is realized inside this order complex, so its
neighborhood is measured in the subdivided ambient one-skeleton.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Topology.BarycentricNeighborhoodIteration

open BarycentricGraphDistance SimpleGraph
open scoped ENat

universe u

variable {V : Type u}

/-- The subdivision of `P` inside the order complex of the nonempty faces of `J`.
Taking `P = J` gives the entire ordinary barycentric subdivision. -/
def subdivision (J P : PreAbstractSimplicialComplex V) : PreAbstractSimplicialComplex (Face J) where
  faces := {s | s.Nonempty ∧ IsChain (· < ·) (s : Set (Face J)) ∧ ∀ f ∈ s, f.val ∈ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, hs.2.1.mono (Finset.coe_subset.mpr hts), fun f hf => hs.2.2 f (hts hf)⟩

variable {J P W : PreAbstractSimplicialComplex V}

private theorem singleton_mem_subdivision {f : Face J} :
    ({f} : Finset (Face J)) ∈ subdivision J P ↔ f.val ∈ P := by
  constructor
  · intro hf
    exact hf.2.2 f (Finset.mem_singleton_self f)
  · intro hf
    refine ⟨Finset.singleton_nonempty f, ?_, ?_⟩
    · simpa only [Finset.coe_singleton] using (IsChain.singleton (r := (· < ·)) (a := f))
    · intro g hg
      rwa [Finset.mem_singleton.mp hg]

/-- A full subcomplex contains every ambient face whose vertices lie in the subcomplex. -/
def FullIn (W J : PreAbstractSimplicialComplex V) : Prop :=
  W ≤ J ∧ ∀ s : Face J, (∀ v ∈ s.val, ({v} : Finset V) ∈ W) → s.val ∈ W

/-- Subdividing a subcomplex gives the full subcomplex on its face vertices. -/
theorem subdivision_full (J P : PreAbstractSimplicialComplex V) :
    FullIn (subdivision J P) (subdivision J J) := by
  constructor
  · intro s hs
    exact ⟨hs.1, hs.2.1, fun f _ => f.property⟩
  · intro s hs
    exact ⟨s.property.1, s.property.2.1, fun f hf => singleton_mem_subdivision.mp (hs f hf)⟩

/-- The subcomplex `W` contains the closed radius-`D` vertex neighborhood of `P` in `J`. -/
def ContainsBall (J P W : PreAbstractSimplicialComplex V) (D : ℕ) : Prop :=
  ∀ x : Vertex J,
    graphSetEdist (@oneSkeleton V (Classical.decEq V) J) {x} (vertexSet J P) ≤ (D : ℕ∞) →
      x ∈ vertexSet J W

private def subdivisionGraphHom (J : PreAbstractSimplicialComplex V) :
    @oneSkeleton (Face J) (Classical.decEq (Face J)) (subdivision J J) →g subdivisionGraph J := by
  letI : DecidableEq (Face J) := Classical.decEq (Face J)
  refine { toFun := Subtype.val, map_rel' := ?_ }
  intro x y h
  exact h.2.2.1 (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (fun he => h.1 (Subtype.ext he))

/-- One ordinary subdivision doubles the radius of the neighborhood containment. -/
theorem containsBall_subdivision (hPJ : P ≤ J) (hW : FullIn W J) {D : ℕ}
    (hnear : ContainsBall J P W D) :
    ContainsBall (subdivision J J) (subdivision J P) (subdivision J W) (2 * D) := by
  let : DecidableEq V := Classical.decEq V
  intro x hx
  have hlt := hx.trans_lt (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self (2 * D)))
  simp only [graphSetEdist, SimpleGraph.edist, iInf_lt_iff] at hlt
  obtain ⟨a, b, p, hp⟩ := hlt
  have ha : a.val = x := Set.mem_singleton_iff.mp a.property
  have hb : b.val.val.val ∈ P := singleton_mem_subdivision.mp b.property
  have hlen : p.length ≤ 2 * D := Nat.lt_succ_iff.mp (ENat.natCast_lt_natCast.mp hp)
  let f := subdivisionGraphHom J
  have hmaplen : (p.map f).length ≤ 2 * D := (Walk.length_map f p).le.trans hlen
  have hmem := mem_full_subcomplex_of_face_walk hPJ hW.2 hnear hb (p.map f) hmaplen
  apply singleton_mem_subdivision.mpr
  change a.val.val.val ∈ W at hmem
  simpa only [ha] using hmem

/-- The vertex carrier and ambient complex after `r` ordinary subdivisions. -/
def iteratedAmbient (J : PreAbstractSimplicialComplex V) :
    ℕ → Σ X : Type u, PreAbstractSimplicialComplex X
  | 0 => ⟨V, J⟩
  | r + 1 =>
    let previous := iteratedAmbient J r
    ⟨Face previous.2, subdivision previous.2 previous.2⟩

/-- The ordinary subdivisions of `P` realized inside the corresponding subdivisions of `J`. -/
def iteratedSubcomplex (J P : PreAbstractSimplicialComplex V) :
    (r : ℕ) → PreAbstractSimplicialComplex (iteratedAmbient J r).1
  | 0 => P
  | r + 1 => subdivision (iteratedAmbient J r).2 (iteratedSubcomplex J P r)

/-- After `r` ordinary barycentric subdivisions, the radius-`D * 2^r` vertex neighborhood
of the subdivided `P` lies in the subdivided full subcomplex `W`. -/
theorem containsBall_iteratedSubdivision (hPJ : P ≤ J) (hW : FullIn W J) {D : ℕ}
    (hnear : ContainsBall J P W D) (r : ℕ) :
    ContainsBall (iteratedAmbient J r).2 (iteratedSubcomplex J P r)
      (iteratedSubcomplex J W r) (D * 2 ^ r) := by
  suffices ∀ n : ℕ,
      iteratedSubcomplex J P n ≤ (iteratedAmbient J n).2 ∧
      FullIn (iteratedSubcomplex J W n) (iteratedAmbient J n).2 ∧
      ContainsBall (iteratedAmbient J n).2 (iteratedSubcomplex J P n)
        (iteratedSubcomplex J W n) (D * 2 ^ n) from (this r).2.2
  intro n
  induction n with
  | zero =>
    refine ⟨hPJ, hW, ?_⟩
    change ContainsBall J P W (D * 2 ^ 0)
    simpa only [pow_zero, mul_one] using hnear
  | succ n ih =>
    obtain ⟨hP, hW', hball⟩ := ih
    refine ⟨(subdivision_full _ _).1, subdivision_full _ _, ?_⟩
    rw [pow_succ, ← Nat.mul_assoc, Nat.mul_comm (D * 2 ^ n) 2]
    exact containsBall_subdivision hP hW' hball

end D5.S3.Topology.BarycentricNeighborhoodIteration
