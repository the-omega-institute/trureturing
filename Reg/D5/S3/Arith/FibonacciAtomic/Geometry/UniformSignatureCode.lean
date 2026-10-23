import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode
import Reg.Support.DependentFamily

/-! The whole uniform static decoder statement, with its original address readout. -/

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ × List (ZMod p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ p s => signature p.1 p.2 s) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _ s => if s = [false, false] then (0, []) else (1, []))
    (fun e => nomatch e)

/-- Every original quantifier is retained, including both existential maps before all p. -/
@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (m : ℕ), 3 ≤ m → ∀ h : ℕ,
    ∃ alpha : Address → Fin (alphabetSize h),
      ∃ D : ((ZMod m × ℕ) × Fin (alphabetSize h)) → (ℕ × List (ZMod m)),
        ∀ p : Address, D (observation m p, alpha p) = R.readout () ⟨m, h⟩ p

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  obtain ⟨alpha, D, hD⟩ := he 3 (by decide) 0
  have hobs : observation 3 [false, false] = observation 3 [true, false] := by
    decide
  have halpha : alpha [false, false] = alpha [true, false] := by
    apply Fin.ext
    have hp : (alpha [false, false]).val < 1 := (alpha [false, false]).isLt
    have ht : (alpha [true, false]).val < 1 := (alpha [true, false]).isLt
    omega
  have hin : (observation 3 [false, false], alpha [false, false]) =
      (observation 3 [true, false], alpha [true, false]) := Prod.ext hobs halpha
  have hh := congrArg D hin
  rw [hD, hD] at hh
  have hdepth := congrArg Prod.fst hh
  have hne : ([true, false] : Address) ≠ [false, false] := by decide
  norm_num [bad, realize, hne] at hdepth

private theorem signature_distinct : signature 3 0 [] ≠ signature 3 0 [false] := by
  intro he
  have hh := congrArg Prod.fst he
  norm_num [signature] at hh

def familyRegistration : Registration arena
    (∀ (m : ℕ), 3 ≤ m → ∀ h : ℕ,
      ∃ alpha : Address → Fin (alphabetSize h),
        ∃ D : ((ZMod m × ℕ) × Fin (alphabetSize h)) → (ℕ × List (ZMod m)),
          ∀ p : Address, D (observation m p, alpha p) = signature m h p) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_signature_code, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    exact ⟨⟨3, 0⟩, [], [false], signature_distinct⟩
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_signature_code)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode.uniform_signature_code
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize sourceSignature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "arg"],
      stateBinder := 5, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode
