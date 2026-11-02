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
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare

namespace total_square_anomaly
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
  totalCharge p.1 p.2 ^ 2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (_ : H * gramComplex D =
    1) (_ : gramComplex D * H = 1),
    R.readout () ⟨D,H⟩ (((26-(D.rank : ℂ))/26) • ghostSquareAnomaly D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i)
def family : Registration arena (type_of% @total_square_anomaly) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_square_anomaly, rejected, rejected_law⟩
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
    (@total_square_anomaly) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare.total_square_anomaly.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare.total_square_anomaly.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_square_anomaly

namespace total_square_apply
abbrev signature : Signature where
  Params := Σ D : LatticeData, Σ _ : Matrix (Fin D.rank) (Fin D.rank) ℂ, State D
  State p := State p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def lhs (p : signature.Params) : signature.State p :=
  (totalCharge p.1 p.2.1 ^ 2) p.2.2
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (_ : H * gramComplex D =
    1) (_ : gramComplex D * H = 1) (x : State D),
    R.readout () ⟨D,H,x⟩ (∑ᶠ n : ℤ, (((D.rank : ℂ)-26)/24 * ((n : ℂ)^3-n)) • ((ghostC D (-n) *
      ghostC D n) x))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0 (by funext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i) 0
def family : Registration arena (type_of% @total_square_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_square_apply, rejected, rejected_law⟩
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
    (@total_square_apply) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare.total_square_apply.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare.total_square_apply.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
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
end total_square_apply

namespace total_square_finite
abbrev signature : Signature where
  Params := LatticeData
  State D := ℤ → State D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ f => Function.HasFiniteSupport f) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (x : State D), R.readout () D
    (fun n : ℤ => (((D.rank : ℂ)-26)/24 * ((n : ℂ)^3-n)) •
      ((ghostC D (-n) * ghostC D n) x))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroLattice 0
def family : Registration arena (type_of% @total_square_finite) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_square_finite, rejected, rejected_law⟩
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
    obtain ⟨z, hz⟩ := exists_ne (0 : State zeroLattice)
    refine ⟨zeroLattice, (fun _ => 0), (fun _ => z), ?_⟩
    intro h
    change Function.HasFiniteSupport (fun _ : ℤ => (0 : State zeroLattice)) =
      Function.HasFiniteSupport (fun _ : ℤ => z) at h
    have hf : Function.HasFiniteSupport (fun _ : ℤ => z) :=
      Eq.mp h (by simp [Function.HasFiniteSupport, Function.support])
    change (Function.support (fun _ : ℤ => z)).Finite at hf
    have he : Function.support (fun _ : ℤ => z) = Set.univ := by ext; simp [hz]
    rw [he] at hf
    exact Set.infinite_univ hf
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@total_square_finite) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare.total_square_finite.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare.total_square_finite.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end total_square_finite

end Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
