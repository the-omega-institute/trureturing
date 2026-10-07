/- GID: D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual signed transport on an arbitrary selected named spanning tree. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Tactic.Group
import Mathlib.Tactic.FunProp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport

open SimpleGraph

universe u v

/-- The simple support of selected named edges, retaining the original edge type elsewhere. -/
def treeSupport {V : Type u} {E : Type v} (s t : E → V) (T : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range fun e : T => s(s e, t e))

/-- A spanning tree selects distinct nonloop named edges and has connected acyclic support. -/
structure NamedSpanningTree {V : Type u} {E : Type v} (s t : E → V) (T : Set E) : Prop where
  nonloop : ∀ e ∈ T, s e ≠ t e
  distinct : Function.Injective (fun e : T => s(s e, t e))
  isTree : (treeSupport s t T).IsTree

variable {V : Type u} {E : Type v} {s t : E → V} {T : Set E}

/-- The original named edge underlying a selected-tree adjacency. -/
noncomputable def namedEdge {a b : V} (h : (treeSupport s t T).Adj a b) : T :=
  Classical.choose (((SimpleGraph.fromEdgeSet_adj _).mp h).1)

/-- Positive traversal uses the named phase; negative traversal uses its formal inverse. -/
noncomputable def stepPhase {a b : V} (h : (treeSupport s t T).Adj a b)
    (u : E → Circle) : Circle := by
  classical
  exact if s (namedEdge h) = a then u (namedEdge h) else (u (namedEdge h))⁻¹

/-- Original directed generators retain their named edge, including loops and parallel edges. -/
def NamedVertex (_s _t : E → V) := V

instance namedQuiver (s t : E → V) : Quiver (NamedVertex s t) where
  Hom a b := {e : E // s e = a ∧ t e = b}

/-- Transfer each selected-tree adjacency to a signed original generator. -/
noncomputable def signedTreeStep {a b : V} (h : (treeSupport s t T).Adj a b) :
    @Quiver.Hom (Quiver.Symmetrify (NamedVertex s t)) _ a b := by
  classical
  let e := namedEdge h
  have he : s(s e,t e) = s(a,b) :=
    Classical.choose_spec ((SimpleGraph.fromEdgeSet_adj _).mp h).1
  by_cases hs : s e = a
  · have hb : t e = b := ((Sym2.eq_iff.mp he).resolve_right (by
      intro he'; exact h.ne (hs.symm.trans he'.1))).2
    exact Sum.inl ⟨e,hs,hb⟩
  · have hh := (Sym2.eq_iff.mp he).resolve_left (fun hh => hs hh.1)
    exact Sum.inr ⟨e,hh.1,hh.2⟩

/-- The actual typed path in the symmetrification of the original directed multigraph. -/
noncomputable def signedTreePath {a : V} : ∀ {b : V}, (treeSupport s t T).Walk a b →
    @Quiver.Path (Quiver.Symmetrify (NamedVertex s t)) _ a b
  | _, .nil => .nil
  | _, .cons h p => (signedTreeStep h).toPath.comp (signedTreePath p)

/-- The original edge coordinate projection as a continuous phase homomorphism. -/
noncomputable def edgeProjection (e : E) : (E → Circle) →ₜ* Circle where
  toFun := fun u => u e
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  continuous_toFun := continuous_apply e

/-- Formal inverses invert the same named generator projection. -/
noncomputable def signedPhaseHom {a b : Quiver.Symmetrify (NamedVertex s t)}
    (e : a ⟶ b) : (E → Circle) →ₜ* Circle :=
  match e with
  | .inl f => edgeProjection f.1
  | .inr f => (edgeProjection f.1)⁻¹

/-- Public path-weight evaluation in the group of continuous phase homomorphisms. -/
noncomputable def pathPhaseHom {a b : V} (p : (treeSupport s t T).Walk a b) :
    (E → Circle) →ₜ* Circle :=
  Quiver.Path.weight (fun e => signedPhaseHom e) (signedTreePath p)

/-- Evaluation of the actual tree walk, with one signed original generator per step. -/
noncomputable def transport (u : E → Circle) {a : V} :
    ∀ {b : V}, (treeSupport s t T).Walk a b → Circle
  | _, .nil => 1
  | _, .cons h p => stepPhase h u * transport u p

/-- The unique simple path in this selected tree, never uniqueness of raw walks. -/
noncomputable def rootPath (ht : NamedSpanningTree s t T) (r a : V) :
    (treeSupport s t T).Walk r a :=
  (ht.isTree.existsUnique_path r a).choose

/-- Actual phase from the reference root along its selected tree path. -/
noncomputable def rootPhase (ht : NamedSpanningTree s t T) (r : V)
    (u : E → Circle) (a : V) : Circle := transport u (rootPath ht r a)

/-- The original vertex gauge acts on each original named edge. -/
noncomputable def gauge (s t : E → V) (g : V → Circle) (u : E → Circle) : E → Circle :=
  fun e => g (t e) * u e * (g (s e))⁻¹

/-- Selected named edges correspond exactly to the support edges; actual evaluation is
continuous and multiplicative, obeys endpoint covariance, and reconstructs tree edges. -/
theorem selected_tree_transport (ht : NamedSpanningTree s t T) (r : V) :
    (∀ u : E → Circle, rootPhase ht r u r = 1) ∧
    (∀ e ∈ T, ∀ u : E → Circle,
      rootPhase ht r u (t e) = u e * rootPhase ht r u (s e)) ∧
    (∀ g : V → Circle, ∀ u : E → Circle, ∀ a : V,
      rootPhase ht r (gauge s t g u) a =
        g a * rootPhase ht r u a * (g r)⁻¹) ∧
    (∀ a : V, Continuous (fun u : E → Circle => rootPhase ht r u a)) ∧
    (∀ u w : E → Circle, ∀ a : V,
      rootPhase ht r (u * w) a = rootPhase ht r u a * rootPhase ht r w a) ∧
    (∀ a : V, rootPhase ht r (1 : E → Circle) a = 1) := by
  classical
  have edge_spec {a b : V} (h : (treeSupport s t T).Adj a b) :
      s(s (namedEdge h), t (namedEdge h)) = s(a,b) :=
    Classical.choose_spec (((SimpleGraph.fromEdgeSet_adj _).mp h).1)
  have edge_forward (e : T) : (treeSupport s t T).Adj (s e) (t e) :=
    (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, rfl⟩, ht.nonloop e e.property⟩
  have edge_id {a b : V} (h : (treeSupport s t T).Adj a b) (e : T)
      (he : s(s e, t e) = s(a,b)) : namedEdge h = e :=
    ht.distinct ((edge_spec h).trans he.symm)
  have step_reverse {a b : V} (h : (treeSupport s t T).Adj a b) (u : E → Circle) :
      stepPhase h.symm u = (stepPhase h u)⁻¹ := by
    have hid : namedEdge h.symm = namedEdge h :=
      edge_id h.symm (namedEdge h) ((edge_spec h).trans (Sym2.eq_swap ..))
    rcases Sym2.eq_iff.mp (edge_spec h) with ⟨hs, ht'⟩ | ⟨hs, ht'⟩
    · simp [stepPhase, hid, hs, h.ne]
    · simp [stepPhase, hid, hs, h.ne.symm]
  have concat_weight {a b c : V} (p : (treeSupport s t T).Walk a b)
      (h : (treeSupport s t T).Adj b c) (u : E → Circle) :
      transport u (p.concat h) = transport u p * stepPhase h u := by
    induction p with
    | nil => simp [SimpleGraph.Walk.concat, transport, mul_comm]
    | cons h' p ih =>
      change stepPhase h' u * transport u (p.concat h) = _
      rw [ih]; simp [transport, mul_assoc]
  have path_spec (a : V) : (rootPath ht r a).IsPath :=
    (ht.isTree.existsUnique_path r a).choose_spec.1
  have edge_law {a b : V} (h : (treeSupport s t T).Adj a b) (u : E → Circle) :
      rootPhase ht r u b = stepPhase h u * rootPhase ht r u a := by
    by_cases ha : a ∈ (rootPath ht r b).support
    · have hp := ht.isTree.isAcyclic.path_concat (path_spec a) (path_spec b) h ha
      simpa [rootPhase, hp, mul_comm] using concat_weight (rootPath ht r a) h u
    · have hb := ht.isTree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (path_spec a) (path_spec b) h ha
      have hp := ht.isTree.isAcyclic.path_concat (path_spec b) (path_spec a) h.symm hb
      have hw : rootPhase ht r u a = rootPhase ht r u b * (stepPhase h u)⁻¹ := by
        simpa only [rootPhase, hp, step_reverse h u] using
          concat_weight (rootPath ht r b) h.symm u
      rw [hw]; simp [mul_comm, mul_left_comm]
  have covariance {a b : V} (p : (treeSupport s t T).Walk a b)
      (g : V → Circle) (u : E → Circle) :
      transport (gauge s t g u) p = g b * transport u p * (g a)⁻¹ := by
    induction p with
    | nil => simp [transport]
    | @cons a b c h p ih =>
      have hs : stepPhase h (gauge s t g u) = g b * stepPhase h u * (g a)⁻¹ := by
        rcases Sym2.eq_iff.mp (edge_spec h) with ⟨ha, hb⟩ | ⟨hb, ha⟩
        · simp [stepPhase, gauge, ha, hb]
        · simp [stepPhase, gauge, ha, hb, h.ne.symm]; group
      simp only [transport, hs, ih]
      calc
        _ = (g b * (g b)⁻¹) * (g c * stepPhase h u * transport u p * (g a)⁻¹) := by
          ac_rfl
        _ = _ := by simp [mul_assoc]
  have step_evaluation {a b : V} (h : (treeSupport s t T).Adj a b)
      (u : E → Circle) : signedPhaseHom (signedTreeStep h) u = stepPhase h u := by
    by_cases hs : s (namedEdge h) = a
    · simp only [signedTreeStep, dif_pos hs, signedPhaseHom, stepPhase, if_pos hs]
      rfl
    · simp only [signedTreeStep, dif_neg hs, signedPhaseHom, stepPhase, if_neg hs]
      rfl
  have path_evaluation {a b : V} (p : (treeSupport s t T).Walk a b)
      (u : E → Circle) : pathPhaseHom p u = transport u p := by
    induction p with
    | nil => simp [pathPhaseHom, signedTreePath, transport]
    | cons h p ih =>
      simp only [pathPhaseHom, signedTreePath, Quiver.Path.weight_comp,
        Quiver.Hom.toPath, Quiver.Path.weight_cons, Quiver.Path.weight_nil, one_mul]
      change signedPhaseHom (signedTreeStep h) u * pathPhaseHom p u = _
      rw [step_evaluation, ih]; rfl
  have continuous_weight {a b : V} (p : (treeSupport s t T).Walk a b) :
      Continuous (fun u : E → Circle => transport u p) :=
    (pathPhaseHom p).continuous.congr (path_evaluation p)
  have mul_weight {a b : V} (p : (treeSupport s t T).Walk a b)
      (u w : E → Circle) : transport (u * w) p = transport u p * transport w p := by
    rw [← path_evaluation p, map_mul, path_evaluation, path_evaluation]
  have one_weight {a b : V} (p : (treeSupport s t T).Walk a b) :
      transport (1 : E → Circle) p = 1 := by
    rw [← path_evaluation p, map_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    have hp : rootPath ht r r = .nil :=
      (SimpleGraph.Walk.isPath_iff_nil.mp (path_spec r)).eq_nil
    simp [rootPhase, hp, transport]
  · intro e he u
    have hi := edge_id (edge_forward ⟨e,he⟩) ⟨e,he⟩ rfl
    simpa [stepPhase, hi] using edge_law (edge_forward ⟨e,he⟩) u
  · intro g u a; exact covariance (rootPath ht r a) g u
  · intro a; exact continuous_weight (rootPath ht r a)
  · intro u w a; exact mul_weight (rootPath ht r a) u w
  · intro a; exact one_weight (rootPath ht r a)

#print axioms selected_tree_transport

end D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport
