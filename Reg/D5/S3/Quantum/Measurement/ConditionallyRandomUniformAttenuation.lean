import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
import Reg.Support.DependentFamily

/-! Source-bound audit of conditional randomness and uniform attenuation. -/

namespace Reg.D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation

open _root_.D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
open _root_.D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality (luders)
open _root_.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe an outcome effect of the second observable. -/
abbrev signature : Signature where
  Params := Σ d : ℕ, Σ m : ℕ, Σ n : ℕ,
    Σ _A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      Fin n → Matrix (Fin d) (Fin d) ℂ
  State p := Fin p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p y => p.2.2.2.2 y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep every original parameter and hypothesis, observing the complete conclusion. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d m n : ℕ) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ),
    0 < m → 0 < n → IsPOVM A → IsPOVM B →
    ConditionallyRandom A B →
      UniformAttenuation A (fun y => r.readout () ⟨d, m, n, A, B⟩ y)

private theorem singleton_povm :
    IsPOVM (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  constructor
  · intro _
    exact Matrix.PosSemidef.one
  · simp

private theorem singleton_random :
    ConditionallyRandom
      (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  constructor <;> intro _ <;>
    simp [conditioned, _root_.D5.S3.Observer.Conditioning.unreadState]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 1 1 (fun _ => 1) (fun _ => 1)
    (by decide) (by decide) singleton_povm singleton_povm singleton_random 0 0).1
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hbad
  norm_num [rejected, realize, luders] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 2, (fun _ => 1), (fun y => if y = 0 then 1 else 0)⟩, 0, 1, ?_⟩
  change (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0
  exact one_ne_zero

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p y => p.2.2.2.2 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
    definition := some {
      owner := `D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
      name := `D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.claim
      path := #[] }
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg"]
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
end Reg.D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
