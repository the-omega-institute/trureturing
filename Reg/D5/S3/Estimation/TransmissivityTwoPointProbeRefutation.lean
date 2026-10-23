import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
open D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
noncomputable section

abbrev sqrtSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def sqrtActual : Realization sqrtSignature :=
  realize sqrtSignature (fun _ _ t => Real.sqrt t) (fun e => nomatch e)

def sqrtRejected : Realization sqrtSignature :=
  realize sqrtSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev powerArena : Arena where
  signature := sqrtSignature
  Law R := ∀ (t : ℝ) (_ht : 0 ≤ t) (k : ℕ),
    R.readout () () (t ^ k) = Real.sqrt t ^ k

abbrev coefficientArena : Arena where
  signature := sqrtSignature
  Law R := ∀ (n l : ℕ) (τ : ℝ) (_hτ : τ ∈ Set.Icc 0 1),
    R.readout () () ((Nat.choose n l : ℝ) * τ ^ (n - l) * (1 - τ) ^ l) =
      Real.sqrt (Nat.choose n l) * Real.sqrt τ ^ (n - l) * Real.sqrt (1 - τ) ^ l

private theorem power_rejected_law : ¬ powerArena.Law sqrtRejected := by
  intro h
  have impossible := h 0 le_rfl 0
  norm_num [sqrtRejected, realize] at impossible

private theorem coefficient_rejected_law : ¬ coefficientArena.Law sqrtRejected := by
  intro h
  have impossible := h 0 0 0 (by norm_num)
  norm_num [sqrtRejected, realize] at impossible

private theorem sqrt_dependence : ObservationalDependence sqrtSignature sqrtActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [sqrtActual, realize]

def powerProof : Registration powerArena (type_of% (@sqrt_power)) where
  actual := sqrtActual
  bridge := Iff.rfl
  variation := ⟨sqrt_power, sqrtRejected, power_rejected_law⟩
  sensitivity := ⟨fun i => ⟨sqrtRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, power_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := sqrt_dependence

def coefficientProof : Registration coefficientArena (type_of% (@source_coefficient)) where
  actual := sqrtActual
  bridge := Iff.rfl
  variation := ⟨source_coefficient, sqrtRejected, coefficient_rejected_law⟩
  sensitivity := ⟨fun i => ⟨sqrtRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, coefficient_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := sqrt_dependence

abbrev krausSignature : Signature where
  Params := Σ N : ℕ, Fin (N + 1)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin (p.1 + 1)) (Fin (p.1 + 1)) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def krausActual : Realization krausSignature :=
  realize krausSignature (fun _ p η => amplitudeKraus p.2 η) (fun e => nomatch e)

def krausRejected : Realization krausSignature :=
  realize krausSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev krausArena : Arena where
  signature := krausSignature
  Law R := ∀ {N : ℕ} (l : Fin (N + 1)) (τ : ℝ) (_hτ : τ ∈ Set.Icc 0 1),
    R.readout () ⟨N, l⟩ (1 - τ) = Matrix.of (fun r c : Fin (N + 1) =>
      if r.val + l.val = c.val then
        if l.val ≤ c.val then
          (Real.sqrt ((Nat.choose c.val l.val : ℝ) *
            τ ^ (c.val - l.val) * (1 - τ) ^ l.val) : ℂ)
        else 0
      else 0)

private theorem kraus_rejected_law : ¬ krausArena.Law krausRejected := by
  intro h
  have impossible := congrFun (congrFun (@h 0 0 1 (by norm_num)) 0) 0
  norm_num [krausRejected, realize, Matrix.of_apply] at impossible

def krausProof : Registration krausArena (type_of% (@sourceKraus)) where
  actual := krausActual
  bridge := Iff.rfl
  variation := ⟨@sourceKraus, krausRejected, kraus_rejected_law⟩
  sensitivity := ⟨fun i => ⟨krausRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, kraus_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
    intro equality
    have impossible := congrFun (congrFun equality 1) 1
    norm_num [krausActual, realize, amplitudeKraus, Matrix.of_apply] at impossible

def sqrt_power_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.sqrt_power)
    (Realization sqrtSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.sqrt_power
  realizationName := `Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.powerProof
  realizationSource := none
  generated := false
  arena := .source ⟨powerArena⟩
  objectArena := .source ⟨powerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source powerArena ⟨powerProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sqrtSignature sqrtActual.readout sqrtActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms powerProof
#print axioms sqrt_power_registration

def source_coefficient_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.source_coefficient)
    (Realization sqrtSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.source_coefficient
  realizationName := `Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.coefficientProof
  realizationSource := none
  generated := false
  arena := .source ⟨coefficientArena⟩
  objectArena := .source ⟨coefficientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coefficientArena ⟨coefficientProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sqrtSignature sqrtActual.readout sqrtActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms coefficientProof
#print axioms source_coefficient_registration

def sourceKraus_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.sourceKraus)
    (Realization krausSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.sourceKraus
  realizationName := `Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation.krausProof
  realizationSource := none
  generated := false
  arena := .source ⟨krausArena⟩
  objectArena := .source ⟨krausArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source krausArena ⟨krausProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize krausSignature krausActual.readout krausActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms krausProof
#print axioms sourceKraus_registration

end
end Reg.D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
