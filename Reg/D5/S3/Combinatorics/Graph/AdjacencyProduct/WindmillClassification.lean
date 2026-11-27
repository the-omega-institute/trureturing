import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the blade-order residue used in the classification. -/

namespace Reg.D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification

open _root_.D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ t => t % 4) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d t : ℕ), 1 ≤ d → 3 ≤ t →
    ((∃ B C : SimpleGraph (Option (Fin d × Fin (t - 1))),
      B.adjMatrix ℤ * C.adjMatrix ℤ = (windmill d t).adjMatrix ℤ) ↔
      d = 1 ∧ R.readout () () t = 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have factorization := (result 1 5 (by decide) (by decide)).mpr ⟨rfl, rfl⟩
  have he := ((h 1 5 (by decide) (by decide)).mp factorization).2
  change (0 : ℕ) = 1 at he
  exact Nat.zero_ne_one he

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 4, 5, by decide⟩

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (type_of% actual) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t % 4) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification
