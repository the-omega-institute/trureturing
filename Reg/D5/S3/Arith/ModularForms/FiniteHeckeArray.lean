import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ModularForms.FiniteHeckeArray
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.ModularForms.FiniteHeckeArray

open _root_.D5.S3.Arith.ModularForms
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ (_ : ℕ), Σ (_ : ℕ), ℕ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Array (Array ℤ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => millerDepthArrays p.1 p.2.1 p.2.2 d)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m s N d : ℕ), m < N → d ≤ m →
    ∀ e : ℕ, e < d →
      ((R.readout 0 ⟨m, s, N⟩ d).getD e #[]).size = N ∧
        ∀ n : ℕ, n < N →
          ((R.readout 1 ⟨m, s, N⟩ d).getD e #[]).getD n 0 =
            millerCoefficientDepth m s e n

def rejected (role : Fin 2) : Realization signature :=
  realize signature (fun i p d => if i = role then #[] else actual.readout i p d)
    (fun e => nomatch e)

theorem rejected_law (role : Fin 2) : ¬ arena.Law (rejected role) := by
  intro h
  fin_cases role
  · have hsize := (h 1 0 2 1 (by decide) (by decide) 0 (by decide)).1
    change (0 : ℕ) = 2 at hsize
    omega
  · have hentry := (h 1 0 2 1 (by decide) (by decide) 0 (by decide)).2 1 (by decide)
    change (0 : ℤ) = millerCoefficientDepth 1 0 0 1 at hentry
    have hc : millerCoefficientDepth 1 0 0 1 = 1 := by
      simpa using millerCoefficientDepth_normalized 1 0 (by left; rfl)
        0 (by decide) 1 (by decide)
    rw [hc] at hentry
    omega

def family : Registration arena (type_of% @millerDepthArrays_correct) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨millerDepthArrays_correct, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro other hne
      funext p d
      simp only [actual, rejected, realize, if_neg hne]
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨⟨1, 0, 2⟩, 0, 1, ?_⟩
    intro heq
    have hsize := congrArg Array.size heq
    simp [actual, realize, millerDepthArrays] at hsize

/-- Kernel-checked whole-family obligations retain the original unbounded telescope,
including zero and empty cases. Both raw table occurrences have exact source selections.
The current source-binding assessor rejects the external Array.size operand with
IE-C050 source.unsafe_or_external. This is declared_unresolved, not declared_validated;
the missing admissible observation bridge is recorded in issue #5214. -/
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@millerDepthArrays_correct) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.ModularForms.FiniteHeckeArray.tableUnit
  realizationName := `Reg.D5.S3.Arith.ModularForms.FiniteHeckeArray.family
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
    (fun _ p d => millerDepthArrays p.1 p.2.1 p.2.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ModularForms.FiniteHeckeArray
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "fn", "arg", "arg", "fn", "fn", "arg"]
        stateBinder := 3
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "body", "body", "fn", "arg", "fn", "fn", "arg", "fn", "fn", "arg"]
        stateBinder := 3
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.ModularForms.FiniteHeckeArray

