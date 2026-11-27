/- GID: D5/S3/Topology/GraphSubdivisionNullhomotopy
   generality: G
   mirror-B: D5/B/S3/Topology/GraphSubdivisionNullhomotopy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Finite edge-path witnesses give a contiguity contraction after subdividing the source graph. -/

import D5.S3.Topology.GraphSubdivisionIntervals
import D5.S3.Topology.GraphSubdivisionHalves
import D5.S3.Topology.FixedTargetGraphTermination
import OmegaBuild.Commands

/-! Finite edge-path witnesses give a contiguity contraction after subdividing the source graph. -/

compile_only_with_mathlib


namespace D5.S3.Topology.GraphSubdivisionNullhomotopy

open BarycentricBaseRigidity (Contiguous faceImage retainedVertex)
open BarycentricGraphDistance (Face Vertex)
open BarycentricNeighborhoodIteration (iteratedAmbient iteratedSubcomplex)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open FixedTargetGraphTermination
open GraphSubdivisionIntervals
open PathContiguity (intervalComplex)
open Relation (ReflTransGen SymmGen)

set_option autoImplicit false

noncomputable section

local instance (X : Type*) : DecidableEq X := Classical.decEq X

variable {X Y : Type} {K : PreAbstractSimplicialComplex Y}

private theorem finite_subdivision_carrier (A : PreAbstractSimplicialComplex X) [Finite X]
    (m : ℕ) : Finite (iteratedAmbient A m).1 := by
  induction m with
  | zero => exact ‹Finite X›
  | succ m ih =>
    change Finite (Face (iteratedAmbient A m).2)
    letI := ih
    infer_instance

/-- A graph map with finite triangle-move witnesses contracts after sufficiently
many ordinary subdivisions of its source alone. The contractibility is uniform
over all vertex selections belonging to the original support of each vertex. -/
theorem supported_graph_map_contracts (A : PreAbstractSimplicialComplex X) [Finite X]
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2)
    (left right : {e : Face A // e.val.val.card = 2} → Vertex A)
    (horient : ∀ e, e.val.val = {(left e).val, (right e).val} ∧ left e ≠ right e)
    (f : Vertex A → Vertex K)
    (hedge : ∀ e, ({(f (left e)).val, (f (right e)).val} : Finset Y) ∈ K)
    (base : Vertex K) (paths : Vertex A → EdgePath K)
    (hstart : ∀ v, (paths v).read 0 = base)
    (hfinish : ∀ v, (paths v).read (paths v).length = f v)
    (hmoves : ∀ e, ReflTransGen (SymmGen TriangleInsert)
      (EdgePath.single (f (left e)) (f (right e)) (hedge e))
      (joinAtStart (paths (left e)) (paths (right e))
        ((hstart _).trans (hstart _).symm))) :
    ∃ d : ℕ, ∀ m, d ≤ m →
      ∀ select : Vertex (iteratedAmbient A (m + 1)).2 → Vertex A,
        (∀ x, (select x).val ∈ originalSupport A (m + 1) {x.val}) →
        ReflTransGen Contiguous (f ∘ select) (fun _ => base) := by
  let E := {e : Face A // e.val.val.card = 2}
  letI : Fintype (Vertex A) := Fintype.ofFinite _
  let p (e : E) := EdgePath.single (f (left e)) (f (right e)) (hedge e)
  obtain ⟨B, hreplace⟩ := replace_by_centered_paths p paths base hstart left right hmoves
  let C := Finset.univ.sup fun v : Vertex A => (paths v).length
  refine ⟨max B C, ?_⟩
  intro m hm select hselect
  let P := (iteratedAmbient A (m + 1)).2
  letI : Finite (iteratedAmbient A (m + 1)).1 := finite_subdivision_carrier A _
  let M := 2 ^ m
  have hBM : B ≤ M := (le_max_left B C).trans (hm.trans m.lt_two_pow_self.le)
  have hpaths (v : Vertex A) : (paths v).length ≤ M :=
    (Finset.le_sup (f := fun v : Vertex A => (paths v).length) (Finset.mem_univ v)).trans
      ((le_max_right B C).trans (hm.trans m.lt_two_pow_self.le))
  have hretain (v : Vertex A) : select (retainedVertex (m + 1) v) = v := by
    apply Subtype.ext
    simpa only [originalSupport_retained, Finset.mem_singleton] using
      hselect (retainedVertex (m + 1) v)
  have charts := graph_subdivision_intervals_oriented A hdim (m + 1) left right horient
  dsimp only at charts
  rw [pow_succ'] at charts
  obtain ⟨chart, hinj, hend, hfaces, hdisjoint, hcover⟩ := charts
  have hcarrier (e : E) (i : Vertex (intervalComplex (2 * M))) :
      (select (chart e i)).val ∈ e.val.val := by
    have hs := (hfaces e _).2 ⟨{i.val}, i.property, faceImage_singleton (chart e) i⟩
    exact ((mem_iteratedSubcomplex_iff (m + 1) (chart e i).property).1 hs).2
      (hselect (chart e i))
  obtain ⟨owner, distance, howner, hheight, hface, hmetric, hmid, houtside⟩ :=
    GraphSubdivisionHalves.split_charts A m left right chart hinj hend hdisjoint
      (fun s hs => (hcover s hs).imp
        (fun ⟨v, _, heq, _⟩ => ⟨v, heq⟩)
        (fun ⟨e, t, ht, _, honto⟩ => ⟨e, t, ht, honto⟩))
  let g (x : Vertex P) := (owner x).elim base (fun v => (paths v).read (distance x))
  have htrace (e : E) (i : Vertex (intervalComplex (2 * M))) :
      g (chart e i) = if i.val ≤ M then (paths (left e)).read (M - i.val)
        else (paths (right e)).read (i.val - M) := by
    rw [show g (chart e i) = (owner (chart e i)).elim base
      (fun v => (paths v).read (distance (chart e i))) from rfl, howner, hheight]
    change (if i.val < M then some (left e) else if M < i.val then some (right e)
      else none).elim base (fun v => (paths v).read (max (M - i.val) (i.val - M))) = _
    rcases lt_trichotomy i.val M with hlt | heq | hgt
    · simp [hlt, hlt.le, Nat.sub_eq_zero_of_le hlt.le]
    · simp [heq, hstart]
    · simp [hgt, hgt.not_ge, hgt.not_gt, Nat.sub_eq_zero_of_le hgt.le]
  have hfixed (x : Vertex P) (hx : ¬ ∃ e i, chart e i = x) : g x = (f ∘ select) x := by
    obtain ⟨v, rfl, hv, hd⟩ := houtside x hx
    simp only [g, hv, hd, Option.elim_some, Function.comp_apply, hretain]
    have hlen := hpaths v
    have clamp : (paths v).read M = (paths v).read (paths v).length := by
      simp only [EdgePath.read, min_eq_right hlen, min_self]
    exact clamp.trans (hfinish v)
  have hpre : ReflTransGen Contiguous (f ∘ select) g := by
    refine hreplace M hBM hpaths chart hinj hdisjoint ?_ _ _ ?_ ?_ htrace hfixed
    · intro s hs
      rcases hcover s hs with ⟨v, _, heq, hno⟩ | ⟨e, t, ht, _, honto⟩
      · exact Or.inl ⟨retainedVertex _ v, heq, hno⟩
      · exact Or.inr ⟨e, t, ht, honto⟩
    · intro e
      refine ⟨_, hedge e, ?_, ?_⟩
      · intro i
        have hmem := hcarrier e i
        rw [(horient e).1, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · rw [Function.comp_apply, show select (chart e i) = left e from Subtype.ext h]
          exact Finset.mem_insert_self _ _
        · rw [Function.comp_apply, show select (chart e i) = right e from Subtype.ext h]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · intro i
        simp only [p, EdgePath.read_single]
        split <;> simp
    · intro e i
      constructor
      · intro hi
        rw [Function.comp_apply, (hend e i).1 hi, hretain]
        simp [p]
      · intro hi
        rw [Function.comp_apply, (hend e i).2 hi, hretain]
        change f (right e) = (p e).read 1
        simp [p]
  exact hpre.trans (contract_padded_half_paths base paths hstart owner hface M
    distance hmetric hmid)

end

end D5.S3.Topology.GraphSubdivisionNullhomotopy
