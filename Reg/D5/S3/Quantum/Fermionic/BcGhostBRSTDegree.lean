import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare

open scoped BigOperators TensorProduct
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostCharge
open _root_.D5.S3.Quantum.Fermionic
open _root_.D5.S3.VertexAlgebra.LatticeBRST
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostDegree
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostBRSTDegree

namespace ghost_number_Qg
abbrev signature : Signature where
  Params := Unit
  State p := Module.End ℂ Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  ghostNumber * BcGhostBRST.Qg - BcGhostBRST.Qg * ghostNumber
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (BcGhostBRST.Qg)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h
def family : Registration arena (type_of% @BcGhostBRST.ghost_number_Qg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨BcGhostBRST.ghost_number_Qg, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    have := state_nontrivial zeroLattice
    let p : signature.Params := ()
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@BcGhostBRST.ghost_number_Qg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostBRSTDegree.ghost_number_Qg.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostBRSTDegree.ghost_number_Qg.family
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
    owner := `D5.S3.Quantum.Fermionic.BcGhostBRSTDegree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ghost_number_Qg

end Reg.D5.S3.Quantum.Fermionic.BcGhostBRSTDegree
