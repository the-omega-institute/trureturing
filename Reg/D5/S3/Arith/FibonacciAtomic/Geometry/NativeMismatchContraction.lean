import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

/-- A source is observed through its mass function against every second source. -/
@[reducible] def signature : Signature where
  Params := ℚ
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source → ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q s => mass q s) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

@[reducible] def rootArena : Arena where
  signature := signature
  Law R := ∀ (q : ℚ), 0 < q → q ≤ 1 / 2 →
    (∀ s t : Source, s = t → R.readout () q (substitution^[2] s) (substitution^[2] t) = 0) ∧
    (∀ b c : Bool, b ≠ c →
      mass q (substitution^[2] (.of b)) (substitution^[2] (.of c)) = 2 * q) ∧
    (∀ (b : Bool) (u v : Source),
      mass q (substitution^[2] (.of b)) (substitution^[2] (.mul u v)) ≤ 2 * q ∧
      mass q (substitution^[2] (.mul u v)) (substitution^[2] (.of b)) ≤ 2 * q) ∧
    (∀ s u t v : Source,
      mass q (substitution^[2] (.mul s u)) (substitution^[2] (.mul t v)) =
        q * (mass q (substitution^[2] s) (substitution^[2] t) +
          mass q (substitution^[2] u) (substitution^[2] v)))

@[reducible] def contractionArena : Arena where
  signature := signature
  Law R := ∀ (q : ℚ), 0 < q → q ≤ 1 / 2 → ∀ s t : Source,
    R.readout () q (substitution^[2] s) (substitution^[2] t) ≤ 2 * q * mass q s t

@[reducible] def iterateArena : Arena where
  signature := signature
  Law R := ∀ (q : ℚ), 0 < q → q ≤ 1 / 2 → ∀ (n : ℕ) (s t : Source),
    R.readout () q (substitution^[2 * n] s) (substitution^[2 * n] t) ≤
      (2 * q) ^ n * mass q s t

private theorem root_bad : ¬ rootArena.Law bad := by
  intro h
  have hh := (h (1 / 4) (by norm_num) (by norm_num)).1 (.of true) (.of true) rfl
  change (1 : ℚ) = 0 at hh
  norm_num at hh

private theorem contraction_bad : ¬ contractionArena.Law bad := by
  intro h
  have hh := h (1 / 4) (by norm_num) (by norm_num) (.of true) (.of true)
  norm_num [bad, realize, mass,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier] at hh

private theorem iterate_bad : ¬ iterateArena.Law bad := by
  intro h
  have hh := h (1 / 4) (by norm_num) (by norm_num) 1 (.of true) (.of true)
  norm_num [bad, realize, mass,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1 / 4, .of true, .of false, ?_⟩
  intro he
  have hh := congrFun he (.of true)
  have hn : (FreeMagma.of false : Source) ≠ .of true := by decide
  norm_num [actual, realize, mass,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, hn] at hh

private theorem sensitivity (law : Realization signature → Prop)
    (h : ¬ law bad) : Sensitivity ⟨signature, law⟩ actual := by
  exact ⟨fun i => ⟨bad, fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, h⟩,
    fun e => nomatch e⟩

def rootFamilyRegistration : Registration rootArena (type_of% root_cases) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨root_cases, bad, root_bad⟩
  sensitivity := sensitivity rootArena.Law root_bad
  dependence := dependence }

def contractionFamilyRegistration :
    Registration contractionArena (type_of% two_step_contraction) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_step_contraction, bad, contraction_bad⟩
  sensitivity := sensitivity contractionArena.Law contraction_bad
  dependence := dependence }

def iterateFamilyRegistration : Registration iterateArena (type_of% even_iterates) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨even_iterates, bad, iterate_bad⟩
  sensitivity := sensitivity iterateArena.Law iterate_bad
  dependence := dependence }

noncomputable def rootRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@root_cases) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction.root_cases "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction.rootFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rootArena⟩
  objectArena := .source ⟨rootArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootArena ⟨rootFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def contractionRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_step_contraction)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction.two_step_contraction
    "__information_unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
    "contractionFamilyRegistration"
  realizationSource := none
  generated := false
  arena := .source ⟨contractionArena⟩
  objectArena := .source ⟨contractionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source contractionArena ⟨contractionFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def iterateRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@even_iterates) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction.even_iterates
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction.iterateFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨iterateArena⟩
  objectArena := .source ⟨iterateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source iterateArena ⟨iterateFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

@[reducible] def leafSignature : Signature where
  Params := ℚ
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source → ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def leafActual : Realization leafSignature :=
  realize leafSignature (fun _ q b => mass q (.of b)) (fun e => nomatch e)

def leafBad : Realization leafSignature :=
  realize leafSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

@[reducible] def leafArena : Arena where
  signature := leafSignature
  Law R := ∀ (q : ℚ) (b c : Bool), b ≠ c → R.readout () q b (.of c) = 1

private theorem leaf_bad : ¬ leafArena.Law leafBad := by
  intro h
  have hh := h 0 false true (by decide)
  change (0 : ℚ) = 1 at hh
  norm_num at hh

private theorem leaf_dependence : ObservationalDependence leafSignature leafActual := by
  intro i
  refine ⟨1 / 4, false, true, ?_⟩
  intro he
  have hh := congrFun he (FreeMagma.of false : Source)
  have hn : (FreeMagma.of true : Source) ≠ .of false := by decide
  norm_num [leafActual, realize, mass,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, hn] at hh

def leafFamilyRegistration : Registration leafArena (type_of% mass_of_of) := {
  actual := leafActual
  bridge := Iff.rfl
  variation := ⟨mass_of_of, leafBad, leaf_bad⟩
  sensitivity := ⟨fun i => ⟨leafBad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, leaf_bad⟩,
    fun e => nomatch e⟩
  dependence := leaf_dependence }

noncomputable def leafRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mass_of_of) (type_of% (realize leafSignature leafActual.readout leafActual.anchor))
    Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction.mass_of_of
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction.leafFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨leafArena⟩
  objectArena := .source ⟨leafArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source leafArena ⟨leafFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leafSignature leafActual.readout leafActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 1, functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms leafFamilyRegistration
#print axioms leafRegistration
#print axioms rootFamilyRegistration
#print axioms contractionFamilyRegistration
#print axioms iterateFamilyRegistration
#print axioms rootRegistration
#print axioms contractionRegistration
#print axioms iterateRegistration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
