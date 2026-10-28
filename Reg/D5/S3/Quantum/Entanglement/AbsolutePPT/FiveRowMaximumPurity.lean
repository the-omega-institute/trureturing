/-
The Nat-indexed state family is
State n := Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ,
with real output and purity readout rho ↦ (rho * rho).trace.re.
Each state fiber is a monomorphic Type. Role 0 is the universal purity
observation and role 1 is the existential purity observation. Both share n,
but each observes its own lexically bound rho. The arena retains both clauses.
-/

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity

set_option autoImplicit false
set_option Elab.async false

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Change one whole readout family and keep the other one actual. -/
def rejectedAt (i : Fin 2) : Realization signature :=
  realize signature (fun j n rho =>
    if j = i then (1 : ℝ) else actual.readout j n rho) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨5, 0, 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]

abbrev maximumArena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ), 5 ≤ n →
    (∀ rho : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ,
      rho.PosSemidef → rho.trace = 1 → APPT rho →
        O.readout 0 n rho ≤ bound n) ∧
    (∃ rho : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        O.readout 1 n rho = bound n)

private theorem rejected_law : ¬ maximumArena.Law rejected := by
  intro h
  rcases (h 5 (by decide)).2 with ⟨rho, _, _, heq⟩
  have hbad : (1 : ℝ) = bound 5 := by
    simpa [rejected, realize] using heq
  norm_num [bound] at hbad

private theorem rejectedAt_law (i : Fin 2) : ¬ maximumArena.Law (rejectedAt i) := by
  intro h
  fin_cases i
  · obtain ⟨rho, hd, ha, _hp⟩ :=
      (_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity.result
        5 (by decide)).2
    have hb := (h 5 (by decide)).1 rho hd.1 hd.2 ha
    have hbad : (1 : ℝ) ≤ bound 5 := by
      simpa [rejectedAt, realize] using hb
    norm_num [bound] at hbad
  · rcases (h 5 (by decide)).2 with ⟨rho, _hd, _ha, heq⟩
    have hbad : (1 : ℝ) = bound 5 := by
      simpa [rejectedAt, realize] using heq
    norm_num [bound] at hbad

private theorem actual_sensitivity : Sensitivity maximumArena actual := by
  constructor
  · intro i
    refine ⟨rejectedAt i, ?_, ?_, rejectedAt_law i⟩
    · intro j hji
      funext n rho
      simp [rejectedAt, realize, hji]
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration maximumArena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity.result,
    rejected, rejected_law⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

/-- The dependent-family registration for the full maximum law,
with purity in its universal upper bound and existential equality. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity.result)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity.family
  realizationSource := none
  generated := false
  arena := .source ⟨maximumArena⟩
  objectArena := .source ⟨maximumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source maximumArena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ rho => (rho * rho).trace.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- UNVALIDATED: enter the exact same-owner nullary `claim` at definition.path #[],
  -- keeping `result : claim` as the binding root. CompiledSourceScope.validateFields
  -- requires two selected occurrences for these two roles. No original-expression
  -- data for this claim is supplied, so neither raw path is guessed here.
  -- Later: derive both paths in claim.value, project the common n coordinate,
  -- retain each rho binder's own scope, and run full reconstruction/field checks.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowMaximumPurity
