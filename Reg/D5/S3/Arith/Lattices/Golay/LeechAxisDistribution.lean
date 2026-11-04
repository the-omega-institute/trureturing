import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
import Reg.Support.SingleDependentReadout

/-! # Source audit of the full unbounded axis distribution -/

noncomputable section
namespace Reg.D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
open _root_.D5.S3.Arith.Lattices.Golay.GolayEncoder
open _root_.D5.S3.Arith.Lattices.Golay.IntegerLeech
open _root_.D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
attribute [local instance] Classical.propDecidable

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => IntVector) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ x => squareSum x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (i j : Fin 24), i ≠ j → ∀ t : ℤ,
    Finite {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32 ∧
      dotProduct (Pi.single i 4 + Pi.single j 4) x = 8*t} ∧
    Nat.card {x : Fin 24 → ℤ // Admissible code x ∧ R.readout () () x = 32 ∧
      dotProduct (Pi.single i 4 + Pi.single j 4) x = 8*t} =
      if t = 4 ∨ t = -4 then 1 else
      if t = 2 ∨ t = -2 then 4600 else
      if t = 1 ∨ t = -1 then 47104 else
      if t = 0 then 93150 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h 0 1 (by decide +kernel) 4).2
  let X := {x : Fin 24 → ℤ // Admissible code x ∧ rejected.readout () () x = 32 ∧
    dotProduct (Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4) x = 8*(4 : ℤ)}
  haveI : IsEmpty X := ⟨fun x => by
    have hx := x.property.2.1
    norm_num [rejected, realize] at hx⟩
  have hz : Nat.card X = 0 := Nat.card_of_isEmpty
  change Nat.card X = _ at hc
  rw [hz] at hc
  norm_num at hc

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨(), 0, (fun _ => 1), ?_⟩
  change squareSum (0 : IntVector) ≠ squareSum (fun _ => 1)
  norm_num [squareSum]

def evidence : Registration arena (type_of% (@axis_distribution)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨axis_distribution, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@axis_distribution)
    (type_of% (realize signature (fun _ _ x => squareSum x) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Arith.Lattices.Golay.LeechAxisDistribution.axis_distribution.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.Golay.LeechAxisDistribution.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => squareSum x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg",
        "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence

end Reg.D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
