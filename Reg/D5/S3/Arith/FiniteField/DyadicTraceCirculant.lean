import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FiniteField.DyadicTraceCirculant
import Reg.Support.DependentFamily

/-! The full dyadic matrix is the observation of the natural translation parameter. -/

namespace Reg.D5.S3.Arith.FiniteField.DyadicTraceCirculant

open _root_.D5.S3.Arith.FiniteField.DyadicTraceCirculant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ k => Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) (ZMod 2)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => dyadicTraceCirculant k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law readout := ∀ {k t : ℕ}, 2 ≤ k → Nat.Coprime t (2 ^ k - 1) →
    Matrix.det (readout.readout () k t) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (k := 2) (t := 1) (by decide) (by decide)
  change Matrix.det (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 at hbad
  simp at hbad

def registration : Registration arena
    (∀ {k t : ℕ}, 2 ≤ k → Nat.Coprime t (2 ^ k - 1) →
      Matrix.det (dyadicTraceCirculant k t) = 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dyadic_trace_circulant_det_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change dyadicTraceCirculant 2 0 ≠ dyadicTraceCirculant 2 1
    decide

noncomputable def registration_1 : Contract.Registration
    (@_root_.D5.S3.Arith.FiniteField.DyadicTraceCirculant.dyadic_trace_circulant_det_one)
    (type_of% (realize signature (fun _ k t => dyadicTraceCirculant k t)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FiniteField.DyadicTraceCirculant.determinant_information_unit,
  realizationName := `Reg.D5.S3.Arith.FiniteField.DyadicTraceCirculant.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ k t => dyadicTraceCirculant k t)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FiniteField.DyadicTraceCirculant,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FiniteField.DyadicTraceCirculant
