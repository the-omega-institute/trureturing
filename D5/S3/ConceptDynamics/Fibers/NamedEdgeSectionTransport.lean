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

set_option autoImplicit false
set_option relaxedAutoImplicit false

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
  cases a <;> cases b <;> exact h.symm

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
def namedTransport {a : V} : ∀ {b : V}, NamedPath s t a b → F a ≃ F b
  | _, .nil => Equiv.refl _
  | _, .cons p e => (namedTransport U p).trans (signedEdge U e)

private theorem namedTransport_comp {a b c : V}
    (p : NamedPath s t a b) (q : NamedPath s t b c) :
    namedTransport U (p.comp q) = (namedTransport U p).trans (namedTransport U q) := by
  induction q with
  | nil => rfl
  | cons q e ih => simp only [Quiver.Path.comp_cons, namedTransport, ih, Equiv.trans_assoc]

/-- The actual edge transport on the subdivision, with identity port segments. -/
def incidenceEdge : ∀ {a b : IncidenceVertex V E},
    incidenceAdj s t a b → F (endpoint s t a) ≃ F (endpoint s t b)
  | .vertex a, .source e, h => Equiv.cast (congrArg F h)
  | .source e, .vertex a, h => Equiv.cast (congrArg F h)
  | .target e, .vertex a, h => Equiv.cast (congrArg F h)
  | .vertex a, .target e, h => Equiv.cast (congrArg F h)
  | .source e, .target f, h => by cases h; exact U e
  | .target e, .source f, h => by cases h; exact (U e).symm
  | .vertex _, .vertex _, h => False.elim h
  | .source _, .source _, h => False.elim h
  | .target _, .target _, h => False.elim h

private theorem incidenceEdge_reverse {a b : IncidenceVertex V E}
    (h : incidenceAdj s t a b) :
    incidenceEdge U (incidence_symm s t h) = (incidenceEdge U h).symm := by
  cases a <;> cases b <;> try contradiction
  all_goals cases h; rfl

/-- The native graph transport is built from the same original edge maps. -/
def incidenceTransport : EdgeTransport (incidenceGraph s t) (fun a => F (endpoint s t a)) :=
  EdgeTransport.ofEdges (incidenceEdge U) (incidenceEdge_reverse U)

/-- Project an incidence step to an actual signed original edge or the empty path. -/
def projectStep : ∀ {a b : IncidenceVertex V E},
    incidenceAdj s t a b → NamedPath s t (endpoint s t a) (endpoint s t b)
  | .vertex a, .source e, h => by cases h; exact .nil
  | .source e, .vertex a, h => by cases h; exact .nil
  | .target e, .vertex a, h => by cases h; exact .nil
  | .vertex a, .target e, h => by cases h; exact .nil
  | .source e, .target f, h => by
      cases h; exact (Sum.inl ⟨e, rfl, rfl⟩).toPath
  | .target e, .source f, h => by
      cases h; exact (Sum.inr ⟨e, rfl, rfl⟩).toPath
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
  .cons rfl (.cons rfl (.cons rfl (.nil _)))

/-- Each negative traversal uses the reverse of that same three-step lift. -/
def liftStep {a b : Quiver.Symmetrify (NamedVertex s t)} (e : a ⟶ b) :
    Walk (incidenceGraph s t) (.vertex a) (.vertex b) := by
  rcases e with ⟨e, hs, ht⟩ | ⟨e, hs, ht⟩
  · subst a; subst b; exact positiveLift s t e
  · subst a; subst b; exact (positiveLift s t e).reverse

/-- Lift every actual signed named path into the native graph carrier. -/
def liftPath {a : V} : ∀ {b : V}, NamedPath s t a b →
    Walk (incidenceGraph s t) (.vertex a) (.vertex b)
  | _, .nil => .nil _
  | _, .cons p e => (liftPath p).append (liftStep e)

private theorem projectStep_transport {a b : IncidenceVertex V E}
    (h : incidenceAdj s t a b) :
    namedTransport U (projectStep h) = incidenceEdge U h := by
  cases a <;> cases b <;> try contradiction
  all_goals cases h; rfl

/-- Projection and lifting preserve the actual composite of every named edge occurrence. -/
theorem incidence_path_transport :
    (∀ {a b : IncidenceVertex V E} (p : Walk (incidenceGraph s t) a b),
      namedTransport U (projectWalk p) = (incidenceTransport U).walk p) ∧
    (∀ {a b : V} (p : NamedPath s t a b),
      (incidenceTransport U).walk (liftPath p) = namedTransport U p) := by
  constructor
  · intro a b p
    induction p with
    | nil => rfl
    | cons h p ih =>
      rw [projectWalk, namedTransport_comp, ih, projectStep_transport]
      rfl
  · intro a b p
    induction p with
    | nil => rfl
    | cons p e ih =>
      rw [liftPath, (incidenceTransport U).walk_append, ih]
      congr 1
      rcases e with ⟨e, hs, ht⟩ | ⟨e, hs, ht⟩
      · subst a; subst b; rfl
      · subst a; subst b
        rw [liftStep, (incidenceTransport U).walk_reverse]
        rfl

end D5.S3.ConceptDynamics.Fibers.NamedEdgeSectionTransport
