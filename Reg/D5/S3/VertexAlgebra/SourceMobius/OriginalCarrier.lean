import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
/-! Faithful dependent-family source registration for the original theorem telescope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open _root_.D5.S3.VertexAlgebra.SourceMobius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
private abbrev emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i
private theorem empty_unit : IsUnit emptyLattice.G.det := by
  simp [emptyLattice]

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ D : LatticeData, ℂ) (fun t => Carrier t.1) (fun t => Carrier t.1)
def actual : Realization signature := realize signature
  (fun _ t v => sourceFlow t.1 t.2 v) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ t v => sourceFlow t.1 t.2 v + Finsupp.single 0 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (u : ℂ) (v : Carrier D),
    R.readout () ⟨D,u⟩ v =
      ∑ n ∈ Finset.range (v.support.sup
        (fun a => weightedTotalDegree (sourceWeight D) (v a)) + 1),
        (u ^ n / (n.factorial : ℂ)) • (sugawaraMode D (gramComplex D)⁻¹ 1 ^ n) v
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun v : Carrier emptyLattice => v 0)
    (h emptyLattice empty_unit 0 0)
  simpa [rejected, realize] using hh

set_option maxHeartbeats 2000000 in
def sourceProof : Registration arena (type_of% (@actual_sourceFlow_eq_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_sourceFlow_eq_sum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨emptyLattice,0⟩, (0 : Carrier emptyLattice),
      (Finsupp.single 0 1 : Carrier emptyLattice), ?_⟩
    change sourceFlow emptyLattice 0 0 ≠ sourceFlow emptyLattice 0 (Finsupp.single 0 1)
    simp only [map_zero, sourceFlow, Finsupp.lsum_single]
    intro h
    have hh := congrArg (fun v : Carrier emptyLattice => v 0) h
    simpa using hh

def actual_sourceFlow_eq_sum_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.VertexAlgebra.SourceMobius.actual_sourceFlow_eq_sum)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier.actual_sourceFlow_eq_sum
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier.sourceProof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t v => sourceFlow t.1 t.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
    definition := none
    coordinates := #[0,2]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 3,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }

  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
