import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
import Reg.Support.DependentFamily

/-! Source-family audit of the complete Hermite absolute-tie enumeration. -/

namespace Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
open _root_.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ n : ℕ, 1 ≤ n → 0 < r.readout () () n) ∧
    (∀ n m : ℕ, 1 ≤ n → n < m → r.readout () () n < r.readout () () m) ∧
    ∀ k : ℕ, HasExactlyTwo k ↔
      ∃! n : ℕ, 1 ≤ n ∧ (k : ℤ) = r.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1 1 (by decide)
  change (0 : ℤ) < 0 at hh
  omega

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change a 1 ≠ a 2
    exact ne_of_lt (result.2.1 1 2 (by decide) (by decide))

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.unit
  realizationName := `Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
    definition := some {
      owner := `D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
      name := `D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders
