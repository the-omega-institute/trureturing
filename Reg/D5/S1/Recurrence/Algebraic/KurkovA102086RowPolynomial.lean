import D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open Polynomial
open scoped BigOperators
open _root_.D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ((ℕ → ℕ → ℤ) × ℕ) (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ p k => p.1 p.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The entire original claim, with only its matrix-coefficient readout varied.
The existence conjuncts and both source predicates are retained verbatim. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    (∃ T, IsSourceTriangle T) ∧
    (∃ P, IsSourcePolynomialTable P) ∧
    ∀ (T : ℕ → ℕ → ℤ) (P : ℕ → ℤ → Polynomial ℤ),
      IsSourceTriangle T → IsSourcePolynomialTable P → ∀ n : ℕ,
        (∑ k ∈ Finset.range (n + 1), C (r.readout () (T, n) k) * X ^ k) =
          P (n + 1) (n : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨T, hT⟩ := result.1
  obtain ⟨P, hP⟩ := result.2.1
  have he := h.2.2 T P hT hP 0
  have hz := hP.2.1 1
  have : (0 : Polynomial ℤ) = 1 := by simpa [rejected, realize, hz] using he
  exact zero_ne_one this

/-- Kernel-checked full-claim equivalence, whole-family intervention and dependence. -/
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨((fun _ k => (k : ℤ)), 0), 0, 1, ?_⟩
    change (0 : ℤ) ≠ 1
    exact zero_ne_one

/-- Typed audit attempt. Exact scoped source-occurrence reconstruction remains unresolved. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial.resultUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => p.1 p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Algebraic.KurkovA102086RowPolynomial
