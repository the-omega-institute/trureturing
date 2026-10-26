import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.MazorchukXu

namespace Triangle

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => Prop)

noncomputable def actual : Realization signature := realize signature
  (fun _ p a => (a, p.2) ∈ triangle p.1) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n a b : ℕ}, R.readout () ⟨n, b⟩ a ↔ a ≤ b ∧ b ≤ n

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  exact (h (n := 0) (a := 0) (b := 0)).mpr ⟨le_rfl, le_rfl⟩

noncomputable def family : Registration arena (type_of% (@mem_triangle)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_triangle, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
    intro heq
    have htrue : actual.readout role ⟨0, 0⟩ 0 := by
      change (0, 0) ∈ triangle 0
      exact mem_triangle.mpr ⟨le_rfl, le_rfl⟩
    have hfalse : ¬ actual.readout role ⟨0, 0⟩ 1 := by
      change (1, 0) ∉ triangle 0
      simp [mem_triangle]
    exact hfalse (Eq.mp heq htrue)

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mem_triangle) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.MazorchukXu.mem_triangle.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure.Triangle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a => (a, p.2) ∈ triangle p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Triangle
end Reg.D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
