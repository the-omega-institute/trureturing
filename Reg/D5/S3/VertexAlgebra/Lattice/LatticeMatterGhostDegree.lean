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
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree

namespace tensorNumber_T
abbrev signature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  tensorNumber p.1 * (T p.1 p.2) - (T p.1 p.2) * tensorNumber p.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    R.readout () ⟨D,H⟩ (T D H)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0
def family : Registration arena (type_of% @tensorNumber_T) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensorNumber_T, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tensorNumber_T) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_T.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_T.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end tensorNumber_T

namespace tensorNumber_G
abbrev signature : Signature where
  Params := LatticeData
  State p := Module.End ℂ (State p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  tensorNumber p * (G p) - (G p) * tensorNumber p
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData),
    R.readout () D (G D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice
def family : Registration arena (type_of% @tensorNumber_G) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensorNumber_G, rejected, rejected_law⟩
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
    let p : signature.Params := zeroLattice
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tensorNumber_G) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_G.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_G.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end tensorNumber_G

namespace tensorNumber_Q
abbrev signature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  tensorNumber p.1 * (Q p.1 p.2) - (Q p.1 p.2) * tensorNumber p.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    R.readout () ⟨D,H⟩ (Q D H)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0
def family : Registration arena (type_of% @tensorNumber_Q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensorNumber_Q, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tensorNumber_Q) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_Q.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_Q.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end tensorNumber_Q

namespace tensorNumber_E
abbrev signature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  tensorNumber p.1 * (E p.1 p.2) - (E p.1 p.2) * tensorNumber p.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    R.readout () ⟨D,H⟩ ((2 : ℂ) • E D H)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0
def family : Registration arena (type_of% @tensorNumber_E) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensorNumber_E, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tensorNumber_E) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_E.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree.tensorNumber_E.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end tensorNumber_E

end Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
