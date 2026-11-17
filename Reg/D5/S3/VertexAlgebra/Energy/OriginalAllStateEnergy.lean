import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
import D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.OriginalGram
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
open _root_.D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private testLattice test_positive actual_dependence from
  Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
open scoped VertexOperator Matrix

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy

abbrev signature : Signature :=
  _root_.Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.signature

abbrev actual : Realization signature :=
  _root_.Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.actual

abbrev rejected : Realization signature :=
  _root_.Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.rejected

def homogeneousArena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData}, (gramReal D).PosDef →
    ∀ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    H*gramComplex D=1 → gramComplex D*H=1 →
    ∀ (W : ℕ) (s : Carrier D), s ∈ grade D (W : ℤ) →
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (v : Carrier D),
      R.readout () D (((Y D s)[[m+(W : ℤ)-1]]) v) ≤
        C*(1+|(m : ℝ)|)^(2*W)*normD (((1+sugawaraMode D H 0)^(2*W)) v)

def finiteArena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData}, (gramReal D).PosDef →
    ∀ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    H*gramComplex D=1 → gramComplex D*H=1 →
    ∀ s : Carrier D,
    let Wmax := (stateEnergies D s).sup (fun E => E.toNat)
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (v : Carrier D),
      R.readout () D (((Y D s)[[n]]) v) ≤
        C*(1+|(n : ℝ)|)^(2*Wmax)*
          normD (((1+sugawaraMode D H 0)^(2*Wmax)) v)

private theorem homogeneous_rejected : ¬ homogeneousArena.Law rejected := by
  intro h
  obtain ⟨H,hHG,hGH⟩ := complex_inverse_exists testLattice test_positive
  obtain ⟨C,hC,hb⟩ := h test_positive H hHG hGH 0 0 (grade testLattice 0).zero_mem
  have hz := hb 0 0
  norm_num [rejected,
    _root_.Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.rejected, realize, normD] at hz

private theorem finite_rejected : ¬ finiteArena.Law rejected := by
  intro h
  obtain ⟨H,hHG,hGH⟩ := complex_inverse_exists testLattice test_positive
  obtain ⟨C,hC,hb⟩ := h test_positive H hHG hGH 0
  have hz := hb 0 0
  norm_num [rejected,
    _root_.Reg.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy.rejected, realize, normD] at hz

def homogeneousEvidence : Registration homogeneousArena (type_of% (@homogeneous_energy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@homogeneous_energy_bound, rejected, homogeneous_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    homogeneousArena.Law actual rejected homogeneous_rejected
  dependence := actual_dependence

def finiteEvidence : Registration finiteArena (type_of% (@finite_energy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_energy_bound, rejected, finite_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    finiteArena.Law actual rejected finite_rejected
  dependence := actual_dependence

def homogeneousAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@homogeneous_energy_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy.homogeneousUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy.homogeneousEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨homogeneousArena⟩
  objectArena := .source ⟨homogeneousArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source homogeneousArena ⟨homogeneousEvidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def finiteAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_energy_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy.finiteUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy.finiteEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteEvidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms homogeneousEvidence
#print axioms finiteEvidence
end Reg.D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy
