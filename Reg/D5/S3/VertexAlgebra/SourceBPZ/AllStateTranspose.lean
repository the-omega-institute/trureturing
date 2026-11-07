import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticePositiveEnergy MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open _root_.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem empty_unit : IsUnit emptyLattice.G.det := by simp [emptyLattice]

/-- Parameters retain the original lattice, mode, source and first input;
the observed state is the original second carrier input. -/
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ D : LatticeData, Σ _ : ℤ, Σ _ : Carrier D, Carrier D)
  (fun t => Carrier t.1) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ t v => sourcePairing t.1 (((Y t.1 t.2.2.1)[[t.2.1]]) t.2.2.2) v)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ t v => sourcePairing t.1 (((Y t.1 t.2.2.1)[[t.2.1]]) t.2.2.2) v + 1)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (d m : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (u v : Carrier D),
    R.readout () ⟨D,m,a,u⟩ v =
      (-1 : ℂ)^d * ∑ j ∈ Finset.range (a.support.sup
        (fun α => weightedTotalDegree (sourceWeight D) (a α)) + 1),
        (j.factorial : ℂ)⁻¹ * sourcePairing D u
          (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ j) a))
            [[2*d-(j : ℤ)-m-2]]) v)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h emptyLattice empty_unit 0 0 0 (Submodule.zero_mem _) 0 0
  simpa [rejected, realize] using hh

def family : Registration arena (type_of% (@sourcePairing_allState)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sourcePairing_allState, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨emptyLattice,-1,vacuum emptyLattice,vacuum emptyLattice⟩,
      (0 : Carrier emptyLattice), vacuum emptyLattice, ?_⟩
    change sourcePairing emptyLattice
        (((Y emptyLattice (vacuum emptyLattice))[[-1]]) (vacuum emptyLattice)) 0 ≠
      sourcePairing emptyLattice
        (((Y emptyLattice (vacuum emptyLattice))[[-1]]) (vacuum emptyLattice))
        (vacuum emptyLattice)
    simp only [map_zero, LinearMap.zero_apply, stateField_creation, sourcePairing_vacuum,
      ne_eq, zero_ne_one, not_false_eq_true]

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose.sourcePairing_allState)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose.sourcePairing_allState
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
    definition := none
    coordinates := #[0,3,4,6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
