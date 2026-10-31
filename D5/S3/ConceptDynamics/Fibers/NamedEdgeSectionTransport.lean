/- GID: D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Named multigraph incidence transport and root section comparison. -/

import D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
import D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Algebra.Module.Submodule.Ker

/-! Exact named-edge incidence transport and its root-fibre consumers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport

open ConfigurationPathTransport
open D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport

universe u v w

variable {V : Type u} {E : Type v} (s t : E → V)

/-- Two distinct ports keep a named loop and its inverse distinct. -/
inductive IncidenceVertex (V : Type u) (E : Type v)
  | vertex : V → IncidenceVertex V E
  | source : E → IncidenceVertex V E
  | target : E → IncidenceVertex V E

open IncidenceVertex

/-- Projection of the ports to their original endpoints. -/
def endpoint : IncidenceVertex V E → V
  | .vertex a => a
  | .source e => s e
  | .target e => t e

/-- Each original edge is a three-segment path through its own two ports. -/
def incidenceAdj : IncidenceVertex V E → IncidenceVertex V E → Prop
  | .vertex a, .source e => a = s e
  | .source e, .vertex a => s e = a
  | .source e, .target f => e = f
  | .target e, .source f => e = f
  | .target e, .vertex a => t e = a
  | .vertex a, .target e => a = t e
  | _, _ => False

private theorem incidence_symm {a b : IncidenceVertex V E}
    (h : incidenceAdj s t a b) : incidenceAdj s t b a := by
  cases a <;> cases b <;> try contradiction
  all_goals exact h.symm

/-- Prop adjacency is used only after each named edge has separate ports. -/
def incidenceGraph : BiGraph (IncidenceVertex V E) where
  Adj := incidenceAdj s t
  symm := incidence_symm s t

abbrev NamedPath (a b : V) :=
  @Quiver.Path (Quiver.Symmetrify (NamedVertex s t)) _ a b

variable {s t} {F : V → Type w} (U : ∀ e, F (s e) ≃ F (t e))

/-- The same edge map or its inverse on each signed named generator. -/
def signedEdge {a b : Quiver.Symmetrify (NamedVertex s t)} (e : a ⟶ b) : F a ≃ F b := by
  rcases e with ⟨e, hs, ht⟩ | ⟨e, hs, ht⟩
  · subst a; subst b; exact U e
  · subst a; subst b; exact (U e).symm

/-- Actual finite path composition; the last named generator acts last. -/
def namedTransport (U : ∀ e, F (s e) ≃ F (t e)) {a : V} : ∀ {b : V}, NamedPath s t a b → F a ≃ F b
  | _, .nil => Equiv.refl _
  | _, .cons p e => (namedTransport U p).trans (signedEdge U e)

private theorem namedTransport_comp {a b c : V}
    (p : NamedPath s t a b) (q : NamedPath s t b c) :
    namedTransport U (p.comp q) = (namedTransport U p).trans (namedTransport U q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change (namedTransport U (p.comp q)).trans (signedEdge U e) = _
    rw [ih]; rfl

/-- The actual edge transport on the subdivision, with identity port segments. -/
def incidenceEdge : ∀ {a b : IncidenceVertex V E},
    incidenceAdj s t a b → F (endpoint s t a) ≃ F (endpoint s t b)
  | .vertex a, .source e, h => Equiv.cast (congrArg F h)
  | .source e, .vertex a, h => Equiv.cast (congrArg F h)
  | .target e, .vertex a, h => Equiv.cast (congrArg F h)
  | .vertex a, .target e, h => Equiv.cast (congrArg F h)
  | .source e, .target f, h => (U e).trans (Equiv.cast (congrArg (fun e => F (t e)) h))
  | .target e, .source f, h => (U e).symm.trans (Equiv.cast (congrArg (fun e => F (s e)) h))
  | .vertex _, .vertex _, h => False.elim h
  | .source _, .source _, h => False.elim h
  | .target _, .target _, h => False.elim h

private theorem incidenceEdge_reverse {a b : IncidenceVertex V E}
    (h : incidenceAdj s t a b) :
    incidenceEdge U (incidence_symm s t h) = (incidenceEdge U h).symm := by
  cases a <;> cases b <;> try contradiction
  all_goals cases h; simp [incidenceEdge, endpoint]

/-- The native graph transport is built from the same original edge maps. -/
def incidenceTransport : EdgeTransport (incidenceGraph s t) (fun a => F (endpoint s t a)) :=
  EdgeTransport.ofEdges (incidenceEdge U) (incidenceEdge_reverse U)

/-- Project an incidence step to an actual signed original edge or the empty path. -/
def projectStep : ∀ {a b : IncidenceVertex V E},
    incidenceAdj s t a b → NamedPath s t (endpoint s t a) (endpoint s t b)
  | .vertex a, .source e, h => Eq.ndrec (motive := fun b => NamedPath s t a b) .nil h
  | .source e, .vertex a, h => Eq.ndrec (motive := fun b => NamedPath s t (s e) b) .nil h
  | .target e, .vertex a, h => Eq.ndrec (motive := fun b => NamedPath s t (t e) b) .nil h
  | .vertex a, .target e, h => Eq.ndrec (motive := fun b => NamedPath s t a b) .nil h
  | .source e, .target f, h => Eq.ndrec
      (motive := fun f => NamedPath s t (s e) (t f))
      (Quiver.Path.cons .nil (Sum.inl ⟨e, rfl, rfl⟩)) h
  | .target e, .source f, h => Eq.ndrec
      (motive := fun f => NamedPath s t (t e) (s f))
      (Quiver.Path.cons .nil (Sum.inr ⟨e, rfl, rfl⟩)) h
  | .vertex _, .vertex _, h => False.elim h
  | .source _, .source _, h => False.elim h
  | .target _, .target _, h => False.elim h

/-- All finite subdivided walks project, including walks beginning at ports. -/
def projectWalk : ∀ {a b : IncidenceVertex V E},
    Walk (incidenceGraph s t) a b → NamedPath s t (endpoint s t a) (endpoint s t b)
  | _, _, .nil _ => .nil
  | _, _, .cons h p => (projectStep h).comp (projectWalk p)

/-- The three-step lift of one positive original generator. -/
def positiveLift (e : E) : Walk (incidenceGraph s t) (.vertex (s e)) (.vertex (t e)) :=
  Walk.cons (G := incidenceGraph s t) (w := .source e) (z := .vertex (t e))
    (show (incidenceGraph s t).Adj (.vertex (s e)) (.source e) from rfl)
    (Walk.cons (G := incidenceGraph s t) (w := .target e) (z := .vertex (t e))
      (show (incidenceGraph s t).Adj (.source e) (.target e) from rfl)
      (Walk.cons (G := incidenceGraph s t) (w := .vertex (t e)) (z := .vertex (t e))
        (show (incidenceGraph s t).Adj (.target e) (.vertex (t e)) from rfl) (.nil _)))

/-- Each negative traversal uses the reverse of that same three-step lift. -/
def liftStep {a b : Quiver.Symmetrify (NamedVertex s t)} (e : a ⟶ b) :
    Walk (incidenceGraph s t) (.vertex a) (.vertex b) := by
  rcases e with ⟨e, hs, ht⟩ | ⟨e, hs, ht⟩
  · subst a; subst b; exact positiveLift (s := s) (t := t) e
  · subst a; subst b; exact (positiveLift (s := s) (t := t) e).reverse

/-- Lift every actual signed named path into the native graph carrier. -/
def liftPath {a : V} : ∀ {b : V}, NamedPath s t a b →
    Walk (incidenceGraph s t) (.vertex a) (.vertex b)
  | _, .nil => .nil _
  | _, .cons p e => (liftPath p).append (liftStep e)

private theorem projectStep_transport {a b : IncidenceVertex V E}
    (h : incidenceAdj s t a b) :
    namedTransport U (projectStep h) = incidenceEdge U h := by
  cases a <;> cases b <;> try contradiction
  all_goals cases h; simp [incidenceEdge, projectStep, namedTransport, signedEdge]

private theorem projectWalk_append {a b c : IncidenceVertex V E}
    (p : Walk (incidenceGraph s t) a b) (q : Walk (incidenceGraph s t) b c) :
    projectWalk (p.append q) = (projectWalk p).comp (projectWalk q) := by
  induction p with
  | nil => simp [Walk.append, projectWalk]
  | cons h p ih =>
    change (projectStep h).comp (projectWalk (p.append q)) = _
    rw [ih]
    exact (Quiver.Path.comp_assoc _ _ _).symm

private theorem project_lift {a b : V} (p : NamedPath s t a b) :
    projectWalk (liftPath p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change projectWalk ((liftPath p).append (liftStep e)) = _
    rw [projectWalk_append, ih]
    rcases e with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ <;>
      simp [liftStep, positiveLift, projectWalk, projectStep, Walk.reverse, Walk.append,
        Quiver.Hom.toPath, endpoint]
    all_goals rfl

/-- Projection and lifting preserve the actual composite of every named edge occurrence. -/
theorem incidence_path_transport :
    (∀ {a b : IncidenceVertex V E} (p : Walk (incidenceGraph s t) a b),
      namedTransport U (projectWalk p) = (incidenceTransport U).walk p) ∧
    (∀ {a b : V} (p : NamedPath s t a b),
      (incidenceTransport U).walk (liftPath p) = namedTransport U p) ∧
    (∀ {a b : V} (p : NamedPath s t a b), projectWalk (liftPath p) = p) := by
  constructor
  · intro a b p
    induction p with
    | nil => rfl
    | cons h p ih =>
      change namedTransport U ((projectStep h).comp (projectWalk p)) = _
      rw [namedTransport_comp, ih, projectStep_transport]
      rfl
  · refine ⟨?_, fun p => project_lift p⟩
    intro a b p
    induction p with
    | nil => rfl
    | cons p e ih =>
      change (incidenceTransport U).walk ((liftPath p).append (liftStep e)) = _
      rw [(incidenceTransport U).walk_append, ih]
      change (namedTransport U p).trans ((incidenceTransport U).walk (liftStep e)) =
        (namedTransport U p).trans (signedEdge U e)
      congr 1
      rcases e with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      · simp [liftStep, positiveLift, incidenceTransport, EdgeTransport.ofEdges,
          edgeWalk, incidenceEdge, signedEdge]
      · rw [liftStep, (incidenceTransport U).walk_reverse]
        simp [positiveLift, incidenceTransport, EdgeTransport.ofEdges,
          edgeWalk, incidenceEdge, signedEdge]


/-- Every actual original named edge equation, without collapsing parallel edges. -/
def NamedSection := {x : ∀ a, F a // ∀ e, U e (x (s e)) = x (t e)}

/-- All actual finite signed root loops of the same connection. -/
def NamedFixedPoint (r : V) := {x : F r // ∀ p : NamedPath s t r r, namedTransport U p x = x}

private def extendSection (x : NamedSection U) : Section (incidenceTransport U) := by
  refine ⟨fun a => x.1 (endpoint s t a), ?_⟩
  intro a b h
  cases a <;> cases b <;> try contradiction
  all_goals cases h
  all_goals first | exact x.2 _ | exact (Equiv.symm_apply_eq _).mpr (x.2 _).symm | rfl

private def restrictSection (x : Section (incidenceTransport U)) : NamedSection U := by
  refine ⟨fun a => x.1 (.vertex a), ?_⟩
  intro e
  have hs := x.2 (v := .vertex (s e)) (w := .source e) rfl
  have hu := x.2 (v := .source e) (w := .target e) rfl
  have ht := x.2 (v := .target e) (w := .vertex (t e)) rfl
  change x.1 (.vertex (s e)) = x.1 (.source e) at hs
  change U e (x.1 (.source e)) = x.1 (.target e) at hu
  change x.1 (.target e) = x.1 (.vertex (t e)) at ht
  exact (congrArg (U e) hs).trans (hu.trans ht)

private def sectionEquiv : NamedSection U ≃ Section (incidenceTransport U) where
  toFun := extendSection U
  invFun := restrictSection U
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    funext a
    cases a with
    | vertex a => rfl
    | source e => exact x.2 (v := .vertex (s e)) (w := .source e) rfl
    | target e => exact (x.2 (v := .target e) (w := .vertex (t e)) rfl).symm

private def fixedEquiv (r : V) :
    NamedFixedPoint U r ≃ RootFixedPoint (incidenceTransport U) (.vertex r) where
  toFun x := ⟨x.1, fun p => by
    rw [← (incidence_path_transport U).1 p]
    exact x.2 (projectWalk p)⟩
  invFun x := ⟨x.1, fun p => by
    have h := x.2 (liftPath p)
    rw [← (incidence_path_transport U).1 (liftPath p),
      (incidence_path_transport U).2.2 p] at h
    exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem incidenceConnected (r : V) (hc : ∀ a, Nonempty (NamedPath s t r a)) :
    GraphConnectedFrom (incidenceGraph s t) (.vertex r) := by
  intro a
  cases a with
  | vertex a => exact ⟨liftPath (Classical.choice (hc a))⟩
  | source e => exact ⟨(liftPath (Classical.choice (hc (s e)))).append
      (Walk.cons (G := incidenceGraph s t) (w := .source e) rfl (.nil _))⟩
  | target e => exact ⟨(liftPath (Classical.choice (hc (t e)))).append
      (Walk.cons (G := incidenceGraph s t) (w := .target e) rfl (.nil _))⟩

/-- The original native classification is the only root-section bijection used. -/
noncomputable def fromFixed (r : V) (hc : ∀ a, Nonempty (NamedPath s t r a)) :
    NamedFixedPoint U r ≃ NamedSection U :=
  (fixedEquiv U r).trans
    ((Equiv.ofBijective (rootSectionMap (incidenceTransport U) (.vertex r)
      (incidenceConnected r hc))
      (rootSectionMap_bijective (incidenceTransport U) (.vertex r)
        (incidenceConnected r hc))).trans (sectionEquiv U).symm)

private theorem fromFixed_root (r : V) (hc : ∀ a, Nonempty (NamedPath s t r a))
    (x : NamedFixedPoint U r) : (fromFixed U r hc x).1 r = x.1 := by
  change (incidenceTransport U).walk
    (Classical.choice (incidenceConnected r hc (.vertex r))) x.1 = x.1
  exact (fixedEquiv U r x).2 _

private theorem fromFixed_path (r : V) (hc : ∀ a, Nonempty (NamedPath s t r a))
    (x : NamedFixedPoint U r) {a : V} (p : NamedPath s t r a) :
    (fromFixed U r hc x).1 a = namedTransport U p x.1 := by
  let T := incidenceTransport U
  let q := Classical.choice (incidenceConnected r hc (.vertex a))
  have h := (fixedEquiv U r x).2 ((liftPath p).append q.reverse)
  change T.walk ((liftPath p).append q.reverse) x.1 = x.1 at h
  have hh := congrArg (fun z => T.walk q z) h
  simp only [T.walk_append, T.walk_reverse, Equiv.trans_apply,
    Equiv.apply_symm_apply] at hh
  rw [(incidence_path_transport U).2.1 p] at hh
  exact hh.symm

section Unitary

variable [∀ a, NormedAddCommGroup (F a)] [∀ a, NormedSpace ℂ (F a)]
variable (U : ∀ e, F (s e) ≃ₗᵢ[ℂ] F (t e))

/-- Underlying equivalences keep exactly the same unitary connection. -/
def underlying (e : E) : F (s e) ≃ F (t e) := (U e).toLinearEquiv.toEquiv

def signedUnitary {a b : Quiver.Symmetrify (NamedVertex s t)} (e : a ⟶ b) :
    F a ≃ₗᵢ[ℂ] F b := by
  rcases e with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  · exact U e
  · exact (U e).symm

/-- Unitary composition of the actual finite signed original edge path. -/
def unitaryTransport (U : ∀ e, F (s e) ≃ₗᵢ[ℂ] F (t e)) {a : V} :
    ∀ {b : V}, NamedPath s t a b → F a ≃ₗᵢ[ℂ] F b
  | _, .nil => LinearIsometryEquiv.refl ℂ _
  | _, .cons p e => (unitaryTransport U p).trans (signedUnitary U e)

private theorem transport_underlying {a b : V} (p : NamedPath s t a b) :
    namedTransport (underlying U) p = (unitaryTransport U p).toLinearEquiv.toEquiv := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (namedTransport (underlying U) p).trans (signedEdge (underlying U) e) = _
    rw [ih]
    rcases e with ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ <;> rfl

/-- The intersection uses every finite root-loop operator of this same connection. -/
def holonomyKernel (r : V) : Submodule ℂ (F r) :=
  ⨅ p : NamedPath s t r r,
    LinearMap.ker ((unitaryTransport U p).toLinearEquiv.toLinearMap - LinearMap.id)

private def fixedKernelEquiv (r : V) : NamedFixedPoint (underlying U) r ≃ holonomyKernel U r where
  toFun x := ⟨x.1, by
    rw [holonomyKernel, Submodule.mem_iInf]
    intro p
    change unitaryTransport U p x.1 - x.1 = 0
    apply sub_eq_zero.mpr
    have h := x.2 p
    rw [transport_underlying U p] at h
    exact h⟩
  invFun x := ⟨x.1, fun p => by
    have h := (Submodule.mem_iInf _).mp x.2 p
    change unitaryTransport U p x.1 - x.1 = 0 at h
    rw [transport_underlying U p]
    exact sub_eq_zero.mp h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Root evaluation, inverse path transport, root norm and the all-vector criterion
on the original arbitrary connected named multigraph. -/
theorem named_unitary_root_classification (r : V)
    (hc : ∀ a, Nonempty (NamedPath s t r a)) :
    ∃ ev : NamedSection (underlying U) ≃ holonomyKernel U r,
      (∀ σ, (ev σ).1 = σ.1 r) ∧
      (∀ x a (p : NamedPath s t r a), (ev.symm x).1 a = unitaryTransport U p x.1) ∧
      (∀ (σ : NamedSection (underlying U)) a, ‖σ.1 a‖ = ‖σ.1 r‖) ∧
      (∀ σ τ, ‖(ev σ).1 - (ev τ).1‖ = ‖σ.1 r - τ.1 r‖) ∧
      ((∀ a (p q : NamedPath s t r a) (x : F r),
          unitaryTransport U p x = unitaryTransport U q x) ↔
        ∀ p : NamedPath s t r r, unitaryTransport U p = LinearIsometryEquiv.refl ℂ (F r)) := by
  classical
  let e := fromFixed (underlying U) r hc
  let ev := e.symm.trans (fixedKernelEquiv U r)
  have heval (σ : NamedSection (underlying U)) : (ev σ).1 = σ.1 r := by
    have h := congrArg (fun z : NamedSection (underlying U) => z.1 r) (e.apply_symm_apply σ)
    exact (fromFixed_root (underlying U) r hc (e.symm σ)).symm.trans h
  have hpath (x : holonomyKernel U r) (a : V) (p : NamedPath s t r a) :
      (ev.symm x).1 a = unitaryTransport U p x.1 := by
    exact (fromFixed_path (underlying U) r hc ((fixedKernelEquiv U r).symm x) p).trans
      (congrArg (fun f : F r ≃ F a => f x.1) (transport_underlying U p))
  refine ⟨ev, heval, hpath, ?_, ?_, ?_⟩
  · intro σ a
    have h := hpath (ev σ) a (Classical.choice (hc a))
    rw [ev.symm_apply_apply] at h
    rw [h, (unitaryTransport U _).norm_map, heval]
  · intro σ τ
    rw [heval, heval]
  · constructor
    · intro h p
      ext x
      exact h r p .nil x
    · intro h a p q x
      let z : NamedFixedPoint (underlying U) r := ⟨x, fun l => by
        rw [transport_underlying U l, h l]
        rfl⟩
      have hp := fromFixed_path (underlying U) r hc z p
      have hq := fromFixed_path (underlying U) r hc z q
      rw [transport_underlying U p] at hp
      rw [transport_underlying U q] at hq
      exact hp.symm.trans hq

#print axioms incidence_path_transport
#print axioms named_unitary_root_classification

end Unitary

end D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
