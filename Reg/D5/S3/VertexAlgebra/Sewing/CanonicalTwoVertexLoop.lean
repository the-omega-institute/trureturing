import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.CanonicalOccupationSewing
open _root_.D5.S3.VertexAlgebra.CanonicalTwoVertexLoop

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop

/-- The source predicate is summability of an unrestricted real family. -/
abbrev signature : Signature where
  Params := Type
  State σ := σ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize _ (fun _ _ f => Summable f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ℕ, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) :=
    Eq.mp h (show Summable (fun _ : ℕ => (0 : ℝ)) from summable_zero)
  simpa only [summable_const_iff, one_ne_zero] using hs

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (D : LatticeData) (a b : Charge D)
    (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ)
    (_ : ‖q1‖ < 1) (_ : ‖q2‖ < 1),
    F.readout () (Occ D × Occ D) (fun z =>
      ‖q1^level D z.1 * q2^level D z.2 *
        (_root_.D5.S3.VertexAlgebra.LatticeSectorIntertwiner.canonical D a (-a+b) u
          (r+(level D z.2 : ℤ)-(level D z.1 : ℤ)) (CanonicalOccupationSewing.b D z.2)).coeff z.1 *
        (_root_.D5.S3.VertexAlgebra.LatticeSectorIntertwiner.canonical D (-a) b v
          (s+(level D z.1 : ℤ)-(level D z.2 : ℤ)) (CanonicalOccupationSewing.b D z.1)).coeff z.2‖)

private theorem source_bridge :
    (type_of% (@canonical_two_vertex_loop_summable)) ↔ arena.Law actual := Iff.rfl

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0 0 0 0 0 0 0 (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@canonical_two_vertex_loop_summable)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp canonical_two_vertex_loop_summable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_two_vertex_loop_summable) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop
