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

/-- Observe the uniform-attenuation predicate as the second observable varies. -/
abbrev signature : Signature where
  Params := Σ d : ℕ, Σ m : ℕ, Σ _n : ℕ,
    Fin m → Matrix (Fin d) (Fin d) ℂ
  State p := Fin p.2.2.1 → Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
def actual : Realization signature :=
  realize signature (fun _ p B => decide (UniformAttenuation p.2.2.2 B))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Keep every original parameter and hypothesis, observing the complete conclusion. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d m n : ℕ) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ),
    0 < m → 0 < n → IsPOVM A → IsPOVM B →
    ConditionallyRandom A B → r.readout () ⟨d, m, n, A⟩ B = true

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
  have hbad := h 1 1 1 (fun _ => 1) (fun _ => 1)
    (by decide) (by decide) singleton_povm singleton_povm singleton_random
  change false = true at hbad
  cases hbad

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨⟨1, 1, 1, fun _ => 1⟩, (fun _ => 1), (fun _ => 0), ?_⟩
  have hgood : UniformAttenuation
      (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ : Fin 1 => 1) := by
    intro x y
    simp [luders]
  have hbad : ¬ UniformAttenuation
      (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ : Fin 1 => 0) := by
    intro h
    have he := (h 0 0).1
    have he' := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) he
    norm_num [luders] at he'
  change decide (UniformAttenuation
      (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ : Fin 1 => 1)) ≠
    decide (UniformAttenuation
      (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ : Fin 1 => 0))
  simp [hgood, hbad]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    classical
    constructor
    · intro h d m n A B hm hn hA hB hr
      exact decide_eq_true (h d m n A B hm hn hA hB hr)
    · intro h d m n A B hm hn hA hB hr
      exact of_decide_eq_true (h d m n A B hm hn hA hB hr)
  variation := ⟨by
    classical
    intro d m n A B hm hn hA hB hr
    exact decide_eq_true (result d m n A B hm hn hA hB hr), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

open Classical in
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
    (fun _ p B => decide (UniformAttenuation p.2.2.2 B)) (fun e => nomatch e))
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
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body"]
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
end Reg.D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
