import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration

/-!
The readout is the actual signed degree on the original StateIndex family.
Only its lower-bound occurrence is varied; the upper-bound clause is retained
literally in the complete Law. The supplied zeroLattice support is used only
for audit witnesses, never as a restriction on the original theorem.
-/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeQuartetContraction
open _root_.D5.S3.VertexAlgebra.LatticeBRSTModeFiltration
open _root_.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
open Reg.D5.S3.VertexAlgebra.LatticeMatterGhostCoupling (zeroLattice)

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration

namespace degree_bounds
abbrev signature : Signature where
  Params := Sigma (fun _ : LatticeData => ℕ)
  State p := StateIndex p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ i => degree i) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ i => -indexLevel i - 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} {t : ℕ} (i : StateIndex D t),
    -indexLevel i ≤ R.readout () ⟨D,t⟩ i ∧ degree i ≤ indexLevel i + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let i : StateIndex zeroLattice 0 := (⟨0,0⟩, {1})
  have hl := (h (D := zeroLattice) (t := 0) i).1
  change -indexLevel i ≤ -indexLevel i - 1 at hl
  omega

def family : Registration arena (type_of% @degree_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@degree_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    refine ⟨⟨zeroLattice,0⟩,
      ((⟨0,0⟩, {1}) : StateIndex zeroLattice 0),
      ((⟨0,0⟩, {1,3}) : StateIndex zeroLattice 0), ?_⟩
    norm_num [actual, realize, degree, exponentDegree,
      _root_.D5.S3.Quantum.Fermionic.BcGhostCharge.charge,
      Finset.filter_insert, Finset.filter_singleton]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@degree_bounds) (Realization signature) (LatticeData → ℕ → Type) Unit where
  unitName :=
    `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration.degree_bounds.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration.degree_bounds.family
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
  escapeFrom := some StateIndex
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end degree_bounds

end Reg.D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration

/-!
The degree_bounds source audit above is retained and compiled; validation is
reported only from the current binding-evidence checker. All other public
theorem audits, including
D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFiniteTransfer.actual_normalized_perturbation_termination,
remain unfinished under https://github.com/the-omega-institute/trureturing/issues/30101.
For the termination theorem, the faithful Law must retain D/F/t/B/H, both
inverse-Gram identities, beta, every integer level, the actual v, and its two
charge/energy premises. Varying only the final zero equation loses the
original operator readout; varying the original operator requires full-family
intervention/sensitivity and source reconstruction. Those typed proofs and
current source-selection evidence are not supplied here. No validated audit
is claimed merely from compilation or the mathematical escape witness.
-/
