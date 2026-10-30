import Reg.Support.SingleDependentReadout
import Reg.Support.LatticeSectorIntertwiner
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.LatticeSectorIntertwiner

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeAllStateField
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.FieldNormalProduct
open scoped VertexOperator

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeSectorIntertwiner.charge_homogeneity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner.unit
  realizationName := `Reg.Support.LatticeSectorIntertwiner.ChargeHomogeneity.family
  realizationSource := none
  generated := false
  arena := .source ⟨ChargeHomogeneity.arena⟩
  objectArena := .source ⟨ChargeHomogeneity.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ChargeHomogeneity.arena ⟨ChargeHomogeneity.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature equality.readout equality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

namespace WordCharge
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
def bad : Realization signature := realize _ (fun _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (α β : Charge D) (w : List (Index D))
    (n : ℤ) (v : Oscillator D), R.readout () ()
      (((wordField D α w)[[n]]) (Finsupp.single β v) ∈ chargeSpace D (α + β))

private theorem source_bridge : (type_of% (@word_charge)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact h zeroLattice 0 0 [] 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro h
  exact Eq.mp h True.intro

def family : Registration arena (type_of% (@word_charge)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp word_charge, bad, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@word_charge)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeSectorIntertwiner.word_charge "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner.WordCharge.family
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
end WordCharge

end Reg.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
