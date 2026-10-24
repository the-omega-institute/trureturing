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

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.DeltaChild

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := ℕ
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := Increment
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ _p s => delta _p s) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _p _s => Increment.minus) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (m : ℕ) (p : Address) (b : Bool),
    R.readout () m (child p b) = childIncrement (delta m p) b

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  have hh := he 3 [] false
  simp [bad, realize, delta, code, childIncrement] at hh

def familyRegistration : Registration arena
    (∀ (m : ℕ) (p : Address) (b : Bool),
    delta m (child p b) = childIncrement (delta m p) b) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨delta_child, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨3, [], [false], ?_⟩
    simp [actual, realize, delta, code, update, childIncrement]
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@delta_child)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.delta_child
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.DeltaChild.familyRegistration,
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
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.DeltaChild

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorZero

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := Unit
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := Address
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ _p s => ancestor s 0) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _p _s => ([] : Address)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ p : Address, R.readout () () p = p

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  have hh := congrArg List.length (he [false])
  norm_num [bad, realize] at hh

def familyRegistration : Registration arena
    (∀ p : Address, ancestor p 0 = p) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ancestor_zero, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), [], [false], ?_⟩
    intro he
    have hh := congrArg List.length he
    norm_num [actual, realize, ancestor] at hh
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ancestor_zero)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.ancestor_zero
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorZero.familyRegistration,
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
    coordinates := #[],
    readouts := #[{
      path := #["body","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorZero

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.ParentChild

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := Unit
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := Address
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ _p s => parent s) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _p _s => ([] : Address)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (p : Address) (b : Bool), R.readout () () (child p b) = p

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  have hh := congrArg List.length (he [false] false)
  norm_num [bad, realize] at hh

def familyRegistration : Registration arena
    (∀ (p : Address) (b : Bool), parent (child p b) = p) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨parent_child, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), [], [false,false], ?_⟩
    intro he
    have hh := congrArg List.length he
    norm_num [actual, realize, parent] at hh
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@parent_child)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.parent_child
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.ParentChild.familyRegistration,
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
    coordinates := #[],
    readouts := #[{
      path := #["body","body","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.ParentChild

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.Incoming

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := ℕ
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := ZMod _p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ _p s => q _p s) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _p _s => (0 : ZMod _p)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (m : ℕ) (p : Address), p ≠ [] →
    R.readout () m p = q m (parent p) + ((delta m p).value : ZMod m)

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  have hh := he 3 [false] (by simp)
  norm_num [bad, realize, q, parent, delta, code, update, childIncrement, Increment.value] at hh

def familyRegistration : Registration arena
    (∀ (m : ℕ) (p : Address), p ≠ [] →
    q m p = q m (parent p) + ((delta m p).value : ZMod m)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨incoming, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨3, [], [false], ?_⟩
    norm_num [actual, realize, q, code, update, childIncrement, Increment.value]
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@incoming)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.incoming
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.Incoming.familyRegistration,
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
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.Incoming

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorPast

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := Address
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := Address
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ _p s => ancestor _p s) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _p _s => ([false] : Address)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (p : Address) (k : ℕ), p.length ≤ k → R.readout () p k = []

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  have hh := he [] 0 (by decide)
  change ([false] : Address) = [] at hh
  cases hh

def familyRegistration : Registration arena
    (∀ (p : Address) (k : ℕ), p.length ≤ k → ancestor p k = []) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ancestor_past, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨[false], 0, 1, ?_⟩
    intro he
    have hh := congrArg List.length he
    norm_num [actual, realize, ancestor] at hh
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ancestor_past)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.ancestor_past
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorPast.familyRegistration,
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
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorPast

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.SignatureEqIff

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := ℕ × List (ZMod _p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ _p s => signature _p.1 _p.2 s) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _p _s => signature _p.1 _p.2 []) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (m h : ℕ) (p t : Address),
    R.readout () ⟨m,h⟩ p = signature m h t ↔ Same m h p t

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  have hh := (he 3 0 [false] []).mp rfl
  have hd : ([false] : Address).length = ([] : Address).length := hh.1
  norm_num at hd

def familyRegistration : Registration arena
    (∀ (m h : ℕ) (p t : Address),
    signature m h p = signature m h t ↔ Same m h p t) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signature_eq_iff, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨⟨3,0⟩, [], [false], ?_⟩
    intro he
    have hh := congrArg Prod.fst he
    norm_num [actual, realize, signature] at hh
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signature_eq_iff)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.signature_eq_iff
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.SignatureEqIff.familyRegistration,
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
    coordinates := #[0,1],
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.SignatureEqIff

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorParent

open D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def sourceSignature : Signature where
  Params := Address
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _p := Address
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization sourceSignature :=
  realize sourceSignature (fun _ _p s => ancestor (parent _p) s) (fun e => nomatch e)

def bad : Realization sourceSignature :=
  realize sourceSignature (fun _ _p _s => ([] : Address)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := sourceSignature
  Law R := ∀ (p : Address) (k : ℕ), R.readout () p k = ancestor p (k + 1)

private theorem bad_law : ¬ arena.Law bad := by
  intro he
  have hh := congrArg List.length (he [false,false] 0)
  norm_num [bad, realize, ancestor] at hh

def familyRegistration : Registration arena
    (∀ (p : Address) (k : ℕ), ancestor (parent p) k = ancestor p (k + 1)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ancestor_parent, bad, bad_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨[false,false], 0, 1, ?_⟩
    intro he
    have hh := congrArg List.length he
    norm_num [actual, realize, ancestor, parent] at hh
}

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ancestor_parent)
    (type_of% (realize sourceSignature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.ancestor_parent
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorParent.familyRegistration,
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
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","fn","arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints.AncestorParent
