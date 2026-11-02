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
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard

namespace total_ward_b
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  totalCharge p.1 p.2.1 * ghostB p.1 p.2.2 + ghostB p.1 p.2.2 * totalCharge p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (matterMode D H r + ghostVirasoro D r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @total_ward_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_ward_b, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@total_ward_b) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_ward_b.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_ward_b.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_ward_b

namespace total_ward_c
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  totalCharge p.1 p.2.1 * ghostC p.1 p.2.2 + ghostC p.1 p.2.2 * totalCharge p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (ghostR D r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @total_ward_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_ward_c, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@total_ward_c) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_ward_c.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_ward_c.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_ward_c

namespace ghostCharge_square
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
  ghostCharge p * ghostCharge p
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData),
    R.readout () D (ghostSquareAnomaly D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice
def family : Registration arena (type_of% @ghostCharge_square) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ghostCharge_square, rejected, rejected_law⟩
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
    (@ghostCharge_square) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.ghostCharge_square.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.ghostCharge_square.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
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
end ghostCharge_square

namespace ghostSquareAnomaly_b
abbrev signature : Signature where
  Params := Σ _ : LatticeData, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  ghostSquareAnomaly p.1 * ghostB p.1 p.2 - ghostB p.1 p.2 * ghostSquareAnomaly p.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (r : ℤ),
    R.readout () ⟨D,r⟩ (BcGhostBRST.anomalyCoefficient r • ghostC D r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0
def family : Registration arena (type_of% @ghostSquareAnomaly_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ghostSquareAnomaly_b, rejected, rejected_law⟩
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
    (@ghostSquareAnomaly_b) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.ghostSquareAnomaly_b.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.ghostSquareAnomaly_b.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
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
end ghostSquareAnomaly_b

namespace ghostSquareAnomaly_c
abbrev signature : Signature where
  Params := Σ _ : LatticeData, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  ghostSquareAnomaly p.1 * ghostC p.1 p.2 - ghostC p.1 p.2 * ghostSquareAnomaly p.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (r : ℤ),
    R.readout () ⟨D,r⟩ (0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0
def family : Registration arena (type_of% @ghostSquareAnomaly_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ghostSquareAnomaly_c, rejected, rejected_law⟩
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
    (@ghostSquareAnomaly_c) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.ghostSquareAnomaly_c.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.ghostSquareAnomaly_c.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
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
end ghostSquareAnomaly_c

namespace T_R
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  T p.1 p.2.1 * ghostR p.1 p.2.2 - ghostR p.1 p.2.2 * T p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @T_R) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨T_R, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@T_R) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.T_R.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.T_R.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end T_R

namespace total_R
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  totalCharge p.1 p.2.1 * ghostR p.1 p.2.2 - ghostR p.1 p.2.2 * totalCharge p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @total_R) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_R, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@total_R) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_R.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_R.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_R

namespace total_covariance
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  totalCharge p.1 p.2.1 * (matterMode p.1 p.2.1 p.2.2 + ghostVirasoro p.1 p.2.2) - (matterMode p.1
    p.2.1 p.2.2 + ghostVirasoro p.1 p.2.2) * totalCharge p.1 p.2.1
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (_ : H * gramComplex D =
    1) (_ : gramComplex D * H = 1) (r : ℤ),
    R.readout () ⟨D,H,r⟩ ((((26-(D.rank : ℂ))/12) * ((r : ℂ)^3-r)) • ghostC D r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i) 0
def family : Registration arena (type_of% @total_covariance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_covariance, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@total_covariance) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_covariance.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_covariance.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_covariance

namespace total_square_b
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  (totalCharge p.1 p.2.1 * totalCharge p.1 p.2.1) * ghostB p.1 p.2.2 - ghostB p.1 p.2.2 *
    (totalCharge p.1 p.2.1 * totalCharge p.1 p.2.1)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (_ : H * gramComplex D =
    1) (_ : gramComplex D * H = 1) (r : ℤ),
    R.readout () ⟨D,H,r⟩ ((((26-(D.rank : ℂ))/12) * ((r : ℂ)^3-r)) • ghostC D r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i) 0
def family : Registration arena (type_of% @total_square_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_square_b, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@total_square_b) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_square_b.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_square_b.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_square_b

namespace total_square_c
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  (totalCharge p.1 p.2.1 * totalCharge p.1 p.2.1) * ghostC p.1 p.2.2 - ghostC p.1 p.2.2 *
    (totalCharge p.1 p.2.1 * totalCharge p.1 p.2.1)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @total_square_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_square_c, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@total_square_c) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_square_c.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.total_square_c.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_square_c

namespace squareResidual_b
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  squareResidual p.1 p.2.1 * ghostB p.1 p.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (_ : H * gramComplex D =
    1) (_ : gramComplex D * H = 1) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (ghostB D r * squareResidual D H)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i) 0
def family : Registration arena (type_of% @squareResidual_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨squareResidual_b, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@squareResidual_b) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.squareResidual_b.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.squareResidual_b.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end squareResidual_b

namespace squareResidual_c
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, ℤ
  State p := Module.End ℂ (State p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  squareResidual p.1 p.2.1 * ghostC p.1 p.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ),
    R.readout () ⟨D,H,r⟩ (ghostC D r * squareResidual D H)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 0
def family : Registration arena (type_of% @squareResidual_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨squareResidual_c, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@squareResidual_c) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.squareResidual_c.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard.squareResidual_c.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end squareResidual_c

end Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
