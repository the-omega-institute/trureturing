import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.EdgeColouring.TwoColours

/-! Exact full-telescope source reconstruction for the two-colour theorem.
The four-slot family certificate is explicitly unfinished. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.EdgeColouring.TwoColours

open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Graph.EdgeColouring.TwoColours

universe u v

abbrev sourceScope := type_of% (@exists_iff_no_odd_component.{u,v})

structure SourceData (V : Type u) (E : Type v) where
  finiteV : Fintype V
  finiteE : Fintype E
  decV : DecidableEq V
  decE : DecidableEq E
  left : E → V
  right : E → V
  constrained : Finset V

abbrev signature : DependentFamily.Signature where
  Params := (Type u) × (Type v)
  State p := SourceData p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : DependentFamily.Realization signature.{u,v} :=
  DependentFamily.realize signature
    (fun _ _ s => by
      letI := s.finiteV
      letI := s.finiteE
      letI := s.decV
      letI := s.decE
      exact OddComponent s.left s.right s.constrained)
    (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature.{u,v}
  Law R := ∀ (p : (Type u) × (Type v)) (s : SourceData p.1 p.2),
    letI := s.finiteV
    letI := s.finiteE
    letI := s.decV
    letI := s.decE
    (∀ e, s.left e ≠ s.right e) →
    (∀ x ∈ s.constrained, 2 ≤ (star s.left s.right x).card) →
    ((∃ c : p.2 → Bool, ∀ x ∈ s.constrained, Mixed s.left s.right c x) ↔
      ¬R.readout () p s)

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual.{u,v} := by
  constructor
  · intro h p s
    exact @h p.1 p.2 s.finiteV s.finiteE s.decV s.decE s.left s.right s.constrained
  · intro h V E fV fE dV dE l r C
    exact h (V, E) ⟨fV, fE, dV, dE, l, r, C⟩

theorem actual_positive : arena.{u,v}.Law actual.{u,v} :=
  source_bridge.mp (@exists_iff_no_odd_component.{u,v})

/-- No completed registration is claimed: whole-family intervention, sensitivity,
observational-dependence and source-selection certificates remain missing. -/
def familyCertificate : Option (DependentFamily.Registration arena.{u,v} sourceScope.{u,v}) := none

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Combinatorics.Graph.EdgeColouring.TwoColours
