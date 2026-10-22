import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
import Reg.Support.DependentFamily

/-! Source-bound registration of the complete finite endpoint classification. -/

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Both operand occurrences are retained for the two actual readouts. -/
@[reducible] def sourceSignature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := Address
  Role := Bool × Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output i p := match i.1 with
    | false => ℕ × List (ZMod p.1)
    | true => ℕ → (ZMod p.1 × ℕ → ℝ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun i p s => match i with
    | (false, _) => signature p.1 p.2 s
    | (true, _) => B p.1 s) (fun e => nomatch e)

def signatureLeftBad : Realization sourceSignature :=
  realize sourceSignature (fun i p s => match i with
    | (false, false) => signature p.1 p.2 []
    | (false, true) => signature p.1 p.2 s
    | (true, _) => B p.1 s) (fun e => nomatch e)

def signatureRightBad : Realization sourceSignature :=
  realize sourceSignature (fun i p s => match i with
    | (false, false) => signature p.1 p.2 s
    | (false, true) => signature p.1 p.2 []
    | (true, _) => B p.1 s) (fun e => nomatch e)

def endpointLeftBad : Realization sourceSignature :=
  realize sourceSignature (fun i p s => match i with
    | (false, _) => signature p.1 p.2 s
    | (true, false) => B p.1 []
    | (true, true) => B p.1 s) (fun e => nomatch e)

def endpointRightBad : Realization sourceSignature :=
  realize sourceSignature (fun i p s => match i with
    | (false, _) => signature p.1 p.2 s
    | (true, false) => B p.1 s
    | (true, true) => B p.1 []) (fun e => nomatch e)

/-- The original telescope, including modulus, budget, both addresses and bounded tests. -/
@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (m : ℕ), 3 ≤ m → ∀ (h : ℕ) (p t : Address),
    R.readout (false, false) ⟨m,h⟩ p = R.readout (false, true) ⟨m,h⟩ t ↔
      ∀ j : ℕ, j ≤ h → ∀ f : ZMod m × ℕ → ℝ, Bounded f →
        R.readout (true, false) ⟨m,h⟩ p j f = R.readout (true, true) ⟨m,h⟩ t j f

private def rootTest (e : ZMod 3 × ℕ) : ℝ := if e.2 = 0 then 1 else 0

private theorem rootTest_bounded : Bounded rootTest := by
  refine ⟨1, fun e => ?_⟩
  unfold rootTest
  split_ifs <;> norm_num

private theorem B_zero (m : ℕ) (f : ZMod m × ℕ → ℝ) (p : Address) :
    B m p 0 f = f (observation m p) := by
  simp [B, law, PMF.toMeasure_pure]

private theorem signature_distinct (m h : ℕ) : signature m h [] ≠ signature m h [false] := by
  intro he
  have hd := congrArg Prod.fst he
  norm_num [signature] at hd

private theorem endpoints_distinct :
    B 3 [] 0 rootTest ≠ B 3 [false] 0 rootTest := by
  rw [B_zero, B_zero]
  norm_num [rootTest, observation]

private theorem signatureLeftBad_law : ¬ arena.Law signatureLeftBad := by
  intro he
  have hh := (he 3 (by decide) 0 [false] []).mp rfl 0 (by decide) rootTest rootTest_bounded
  exact endpoints_distinct hh.symm

private theorem signatureRightBad_law : ¬ arena.Law signatureRightBad := by
  intro he
  have hh := (he 3 (by decide) 0 [] [false]).mp rfl 0 (by decide) rootTest rootTest_bounded
  exact endpoints_distinct hh

private theorem endpointLeftBad_law : ¬ arena.Law endpointLeftBad := by
  intro he
  have hh := (he 3 (by decide) 0 [false] []).mpr (fun _ _ _ _ => rfl)
  exact signature_distinct 3 0 hh.symm

private theorem endpointRightBad_law : ¬ arena.Law endpointRightBad := by
  intro he
  have hh := (he 3 (by decide) 0 [] [false]).mpr (fun _ _ _ _ => rfl)
  exact signature_distinct 3 0 hh

def familyRegistration : Registration arena
    (∀ (m : ℕ), 3 ≤ m → ∀ (h : ℕ) (p t : Address),
      signature m h p = signature m h t ↔
        ∀ j : ℕ, j ≤ h → ∀ f : ZMod m × ℕ → ℝ, Bounded f → B m p j f = B m t j f) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_endpoints_iff_signature, signatureLeftBad, signatureLeftBad_law⟩
  sensitivity := ⟨by
    intro i
    rcases i with ⟨a,b⟩
    cases a <;> cases b
    · refine ⟨signatureLeftBad, ?_, rfl, signatureLeftBad_law⟩
      intro j hj
      rcases j with ⟨a,b⟩
      cases a <;> cases b <;> try rfl
      exact (hj rfl).elim
    · refine ⟨signatureRightBad, ?_, rfl, signatureRightBad_law⟩
      intro j hj
      rcases j with ⟨a,b⟩
      cases a <;> cases b <;> try rfl
      exact (hj rfl).elim
    · refine ⟨endpointLeftBad, ?_, rfl, endpointLeftBad_law⟩
      intro j hj
      rcases j with ⟨a,b⟩
      cases a <;> cases b <;> try rfl
      exact (hj rfl).elim
    · refine ⟨endpointRightBad, ?_, rfl, endpointRightBad_law⟩
      intro j hj
      rcases j with ⟨a,b⟩
      cases a <;> cases b <;> try rfl
      exact (hj rfl).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    rcases i with ⟨a,b⟩
    cases a with
    | false => exact ⟨⟨3,0⟩, [], [false], signature_distinct 3 0⟩
    | true =>
      refine ⟨⟨3,0⟩, [], [false], ?_⟩
      intro he
      exact endpoints_distinct (congrFun (congrFun he 0) rootTest)
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_endpoints_iff_signature)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.bounded_endpoints_iff_signature
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.familyRegistration,
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
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints,
    definition := none,
    coordinates := #[0,2],
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","body","body","body","arg","fn","fn"],
      stateBinder := 4, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","arg","body","body","body","body","fn","arg","fn","fn"],
      stateBinder := 3, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","fn","arg","arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
