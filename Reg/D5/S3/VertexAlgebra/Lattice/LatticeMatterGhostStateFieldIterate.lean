import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateFieldIterate

/-! A faithful dependent-family attempt for the original unrestricted law.
The source occurrence selector and enrolled readout remain unresolved. -/
open scoped VertexOperator
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostStateField
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostStateFieldIterate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateFieldIterate

abbrev signature : Signature where
  Params := Σ D : LatticeData, State D × State D × State D × ℤ × ℤ
  State p := _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.State p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (p : signature.Params) : signature.State p :=
  (((Y p.1 (((Y p.1 p.2.1) [[p.2.2.2.2.1]]) p.2.2.1)) [[p.2.2.2.2.2]]) p.2.2.2.1)
def actual : Realization signature := realize signature
  (fun _ p y => lhs p = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (a b c : State D) (r n : ℤ),
    let a0 := (2 : ℂ)⁻¹ • (a + parity D a)
    let a1 := (2 : ℂ)⁻¹ • (a - parity D a)
    let w : ℕ → ℂ := fun i => ((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)
    let left : ℕ → State D := fun i =>
      w i • (((Y D a) [[r - (i : ℤ)]]) (((Y D b) [[n + (i : ℤ)]]) c))
    let right0 : ℕ → State D := fun i =>
      w i • (((Y D b) [[r + n - (i : ℤ)]]) (((Y D a0) [[(i : ℤ)]]) c))
    let right1 : ℕ → State D := fun i =>
      w i • (((Y D (parity D b)) [[r + n - (i : ℤ)]]) (((Y D a1) [[(i : ℤ)]]) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right0 ∧
      Function.HasFiniteSupport right1 ∧
      R.readout () ⟨D,a,b,c,r,n⟩
        ((∑ᶠ i : ℕ, left i) - ((-1 : ℂ) ^ r) •
          ((∑ᶠ i : ℕ, right0 i) + (∑ᶠ i : ℕ, right1 i)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h zeroLattice 0 0 0 0 0).2.2.2

def family : Registration arena (type_of% @stateField_iterate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stateField_iterate, rejected, rejected_law⟩
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
    let p : signature.Params := ⟨zeroLattice,0,0,0,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs p)
    refine ⟨p, lhs p, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stateField_iterate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateFieldIterate.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateFieldIterate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => lhs p = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeMatterGhostStateFieldIterate
