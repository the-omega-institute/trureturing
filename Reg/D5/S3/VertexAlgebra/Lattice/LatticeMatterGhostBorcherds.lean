import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBorcherds

/-! Faithful full-telescope dependent-family registration attempt.
The original-source occurrence selector remains unprovided; no validated
certificate is claimed by this source. -/
open scoped BigOperators VertexOperator
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostStateField
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostSignedBorcherds
  (mu_D jacobiLeftTerm jacobiRightFirstTerm)
open _root_.D5.S3.VertexAlgebra.LatticeMatterGhostBorcherds
open _root_.D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice state_nontrivial)
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBorcherds

abbrev signature : Signature where
  Params := Σ D : LatticeData, State D × State D × State D × ℤ × ℤ × ℤ
  State p := _root_.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.State p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def lhs (x : signature.Params) : signature.State x :=
  ∑ᶠ i : ℕ, jacobiLeftTerm x.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2
    x.2.1 x.2.2.1 x.2.2.2.1 i

def actual : Realization signature := realize signature
  (fun _ x y => lhs x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (a b c : State D) (p q r : ℤ),
    let a0 := (2 : ℂ)⁻¹ • (a + parity D a)
    let a1 := (2 : ℂ)⁻¹ • (a - parity D a)
    let w : ℕ → ℂ := fun i => ((-1 : ℂ)^i) * integerBinomial r i
    Function.HasFiniteSupport (jacobiLeftTerm D p q r a b c) ∧
    Function.HasFiniteSupport (jacobiRightFirstTerm D p q r a b c) ∧
    Function.HasFiniteSupport (fun i : ℕ =>
      w i • mu_D D b (q + r - i) (mu_D D a0 (p + i) c)) ∧
    Function.HasFiniteSupport (fun i : ℕ =>
      w i • mu_D D (parity D b) (q + r - i) (mu_D D a1 (p + i) c)) ∧
    R.readout () ⟨D,a,b,c,p,q,r⟩
      (∑ᶠ i : ℕ, w i •
        (mu_D D a (p + r - i) (mu_D D b (q + i) c) -
          epsilon r •
            (mu_D D b (q + r - i) (mu_D D a0 (p + i) c) +
              mu_D D (parity D b) (q + r - i) (mu_D D a1 (p + i) c))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h zeroLattice 0 0 0 0 0 0).2.2.2.2

def family : Registration arena (type_of% @borcherds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨borcherds, rejected, rejected_law⟩
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
    let x : signature.Params := ⟨zeroLattice,0,0,0,0,0,0⟩
    obtain ⟨y, hy⟩ := exists_ne (lhs x)
    refine ⟨x, lhs x, y, ?_⟩
    intro h
    exact hy (Eq.mp h rfl).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@borcherds) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBorcherds.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBorcherds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => lhs x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeMatterGhostBorcherds
