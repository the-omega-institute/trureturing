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

namespace FlowVariableSupport

abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ => False) (fun e => nomatch e)

private def oneLattice : LatticeData where
  rank := 1
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact ⟨0, rfl⟩

def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (α : Charge D) (i : Fin D.rank) (p : ℕ),
    R.readout () () (SourceMobius.flowPolynomial D α (X (i,p)) =
      (∑ s ∈ Finset.range (p+1), Polynomial.monomial (p-s)
        (((p+1).choose (s+1) : ℂ) • (X (i,s) : Oscillator D))) +
      Polynomial.monomial (p+1) (C (bilinear D (unitCharge D i) α : ℂ)))

private theorem source_bridge :
    (type_of% (@flow_X_polynomial)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h oneLattice 0 ⟨0, by decide⟩ 0

def family : Registration arena (type_of% (@flow_X_polynomial)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp flow_X_polynomial, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), True, False, ?_⟩
    intro h
    exact Eq.mp h True.intro

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@flow_X_polynomial)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose.flow_X_polynomial "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose.FlowVariableSupport.family
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
  escapeFrom := some Prop
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end FlowVariableSupport

end Reg.D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
