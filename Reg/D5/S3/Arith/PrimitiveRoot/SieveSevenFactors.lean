import D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exceptional supports are read at their actual first coordinate and integer. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
open _root_.D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Shapes
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 7 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => q 0) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Fin 7 → ℕ,
    (StrictMono q ∧ (∀ i, (q i).Prime) ∧
      (73 / 137 : ℝ) < ∑ i : Fin 5, (q (Fin.natAdd 2 i) : ℝ)⁻¹) ↔
    R.readout () () q = 2 ∧ q 1 = 3 ∧ q 2 = 5 ∧ q 3 = 7 ∧ q 4 = 11 ∧
      ((q 5 = 13 ∧ q 6 ∈ ({17, 19, 23, 29, 31, 37, 41, 43} : Finset ℕ)) ∨
        (q 5 = 17 ∧ (q 6 = 19 ∨ q 6 = 23)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h ![2, 3, 5, 7, 11, 13, 17]).mp
    ⟨by decide, by decide, by norm_num [Fin.sum_univ_succ]⟩
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), (fun _ => 0), (fun _ => 1), by norm_num [actual, realize]⟩

def family : Registration arena (type_of% seven_shapes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨seven_shapes, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    seven_shapes (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SieveSevenFactors.seven_shapes.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveSevenFactors.Shapes.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => q 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Shapes

namespace Candidates
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℕ,
    (3483482 ≤ x ∧ x < 4144141 ∧
      ∃ hc : (x - 1).primeFactors.card = 7,
        (73 / 137 : ℝ) < ∑ i : Fin 5,
          ((x - 1).primeFactors.orderEmbOfFin hc (Fin.natAdd 2 i) : ℝ)⁻¹) ↔
    R.readout () () x ∈ ({3573571, 4084081, 3993991, 3723721,
      3693691, 3873871, 3730651, 3612841} : Finset ℕ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 3573571).mp ((seven_candidates 3573571).mpr (by decide))
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% seven_candidates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨seven_candidates, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    seven_candidates (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SieveSevenFactors.seven_candidates.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveSevenFactors.Candidates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Candidates

end Reg.D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
