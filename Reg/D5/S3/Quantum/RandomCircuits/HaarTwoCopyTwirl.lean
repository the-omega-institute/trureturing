import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import Reg.Support.DependentFamily

/-! Source-bound audit of the trace of the tensor-factor swap. -/

namespace Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

open _root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe the complex cardinality appearing in the swap trace identity. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => (k : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The trace identity keeps the complete polymorphic telescope. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n],
    Matrix.trace (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) =
      r.readout () () (Fintype.card n)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := @h (ULift.{u} (Fin 1)) inferInstance inferInstance
  change Matrix.trace (Equiv.Perm.permMatrix ℂ
    (Equiv.prodComm (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)))) = 0 at hbad
  rw [traceSwap] at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena.{u} (type_of% @traceSwap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceSwap, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.traceSwap.{u})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.traceSwap.unit
  realizationName :=
    `Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => (k : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

namespace Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.PureQuadratic
open _root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix
open MeasureTheory TopologicalSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- A source coordinate with one observed role and no fixed anchors. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z ^ 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} [NeZero d] (a : Matrix (Fin d) (Fin d) ℂ),
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
      Matrix.trace ((u.1 * Matrix.single 0 0 1 * u.1ᴴ) * a *
        (u.1 * Matrix.single 0 0 1 * u.1ᴴ) * a) ∂(Measure.haarMeasure
          (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
      (r.readout () () a.trace + (a * a).trace) / ((d : ℂ) * (d + 1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (d := 1) 0
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩


def source_registration : Registration arena (type_of% (@pure_quadratic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pure_quadratic, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@pure_quadratic) (Realization signature) Unit Unit := {
  unitName := .str ``source_registration "unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.PureQuadratic

namespace Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.TraceOneSandwich
open _root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix
open MeasureTheory TopologicalSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- A source coordinate with one observed role and no fixed anchors. -/
abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.trace) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (p x : Matrix (Fin d) (Fin d) ℂ),
    p * p = p → p.trace = 1 → p * x * p = r.readout () d (p * x) • p

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (d := 1) 1 1 (by simp) (by simp)
  simp [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1, 0, 1, by simp [actual, realize]⟩


def source_registration : Registration arena (type_of% (@trace_one_sandwich)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_one_sandwich, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_one_sandwich) (Realization signature) Unit Unit := {
  unitName := .str ``source_registration "unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.trace) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.TraceOneSandwich

namespace Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.TwirlFormula
open _root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix
open MeasureTheory TopologicalSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- A source coordinate with one observed role and no fixed anchors. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => (k : ℂ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (Y : Matrix (n×n) (n×n) ℂ), 2 ≤ Fintype.card n →
    Matrix.of (Function.curry (((haarAverage n).mulVec (Matrix.vec Y)) ∘ Prod.swap)) =
      ((Matrix.trace Y - Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) /
          r.readout () () (Fintype.card n)) /
        ((Fintype.card n : ℂ)^2 - 1)) • (1 : Matrix (n×n) (n×n) ℂ) +
      ((Matrix.trace ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) * Y) -
          Matrix.trace Y / (Fintype.card n : ℂ)) /
        ((Fintype.card n : ℂ)^2 - 1)) • (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n))

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} (Fin 2)) inferInstance inferInstance 1 (by simp)
  rw [twirlFormula _ (by simp)] at hb
  have hc := congrArg (fun M => Matrix.trace M) hb
  norm_num [rejected, realize, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, traceSwap] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩


def source_registration : Registration arena.{u} (type_of% (@twirlFormula.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@twirlFormula.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@twirlFormula.{u}) (Realization signature) Unit Unit := {
  unitName := .str ``source_registration "unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => (k : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg",
        "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.TwirlFormula

namespace Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.SwapHermitian
open _root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix
open MeasureTheory TopologicalSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- A source coordinate with one observed role and no fixed anchors. -/
abbrev signature : Signature where
  Params := Type u
  State n := Matrix (n × n) (n × n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => @decide M.IsHermitian (Classical.propDecidable _))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n],
    r.readout () n (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) = true

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} Unit) inferInstance inferInstance
  change false = true at hb
  exact Bool.false_ne_true hb

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let n := ULift.{u} Unit
  let j : n × n := (⟨()⟩, ⟨()⟩)
  have hn : ¬ (Complex.I • (1 : Matrix (n×n) (n×n) ℂ)).IsHermitian := by
    intro h
    have he := congrFun (congrFun h.eq j) j
    have hi := congrArg Complex.im he
    norm_num [Matrix.conjTranspose_apply] at hi
  refine ⟨n, 0, Complex.I • 1, ?_⟩
  simp [actual, realize, Matrix.isHermitian_zero, hn]


def source_registration : Registration arena.{u} (type_of% (@swapHermitian.{u})) where
  actual := actual
  bridge := by
    simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro n inst de
    exact @decide_eq_true _ (Classical.propDecidable _) (swapHermitian (n := n)),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@swapHermitian.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := .str ``source_registration "unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ M => @decide M.IsHermitian (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.SwapHermitian

namespace Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.SwapSquare
open _root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix
open MeasureTheory TopologicalSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- A source coordinate with one observed role and no fixed anchors. -/
abbrev signature : Signature where
  Params := Σ n : Type u, Σ _ : Fintype n, DecidableEq n
  State p := Matrix (p.1 × p.1) (p.1 × p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.1) (p.1 × p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M =>
    letI := p.2.1
    letI := p.2.2
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm p.1 p.1) * M) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u} [fi : Fintype n] [de : DecidableEq n],
    r.readout () ⟨n, fi, de⟩ (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) = 1

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} Unit) inferInstance inferInstance
  change (0 : Matrix _ _ ℂ) = 1 at hb
  exact zero_ne_one hb

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let n := ULift.{u} Unit
  refine ⟨⟨n, inferInstance, inferInstance⟩, 0,
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n), ?_⟩
  change _ * 0 ≠ _ * _
  rw [Matrix.mul_zero, swapSquare]
  exact zero_ne_one


def source_registration : Registration arena.{u} (type_of% (@swapSquare.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@swapSquare.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@swapSquare.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := .str ``source_registration "unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p M =>
    letI := p.2.1
    letI := p.2.2
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm p.1 p.1) * M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.SwapSquare
