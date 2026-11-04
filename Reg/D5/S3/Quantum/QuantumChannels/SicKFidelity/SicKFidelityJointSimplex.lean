import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex
import Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Joint SIC k-Fidelity Simplex Geometry -/

namespace Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex

open scoped BigOperators Matrix
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
open _root_.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex
open _root_.Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

def pauliId1Weight : PauliLabel 1 → ℝ := fun β => if β = 0 then 1 else 0

def pauliId1 : QubitMap 1 := pauliChannel pauliId1Weight

theorem pauliId1_props :
    pauliId1.IsCompletelyPositive ∧ pauliId1.IsTracePreserving ∧
    processFidelity pauliId1 = 1 ∧ realProcessFidelity pauliId1 = 1 ∧
    jointKFidelityVec (canonicalSICFamily 1) pauliId1 0 = 1 := by
  have hch := pauli_process_matrix_and_fidelity_characterization 1
  have hpc := hch.2.2.2.2 pauliId1Weight
  have hCP : pauliId1.IsCompletelyPositive :=
    hpc.2.1 fun β => by dsimp [pauliId1Weight]; split_ifs <;> norm_num
  have hTP : pauliId1.IsTracePreserving := hpc.2.2 (by simp [pauliId1Weight])
  have htw (β : PauliLabel 1) : pauliTwirlWeight pauliId1 β = (pauliId1Weight β : ℂ) := by
    simpa [pauliTwirlWeight, pauliId1] using hpc.1 β β
  have hpf1 : processFidelity pauliId1 = 1 := by
    rw [(hch.2.1 pauliId1).1, htw 0]; simp [pauliId1Weight]
  have hrpf1 : realProcessFidelity pauliId1 = 1 := by simp [realProcessFidelity, hpf1]
  have hkf1 : kFidelity (canonicalSICFamily 1) 0 pauliId1 = 1 := by
    rw [(kFidelity_eq_pauliWeight_alternating_sum 1 0 (canonicalSICFamily 1)
      (canonicalSICFamily_isQubitSICProjector 1) pauliId1).2.2.1]
    simp_rw [htw]
    rw [Fintype.sum_eq_single (0 : PauliLabel 1) fun β hβ => by simp [pauliId1Weight, hβ]]
    have hhw0 : hammingWeight (0 : PauliLabel 1) = 0 := by decide
    simp [pauliId1Weight, hhw0]
  have hjv : jointKFidelityVec (canonicalSICFamily 1) pauliId1 0 = 1 := by
    simp [jointKFidelityVec, realKFidelity, hkf1]
  exact ⟨hCP, hTP, hpf1, hrpf1, hjv⟩

namespace TpReconstruct

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n : ℕ) (ρ : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
    ∀ (Λ : QubitMap n), Λ.IsTracePreserving →
      3 * ∑ k ∈ Finset.range (O.readout () () n), (-2 : ℂ) ^ k * kFidelity ρ k Λ +
          (-2 : ℂ) ^ n * processFidelity Λ = 1 ∧
      processFidelity Λ =
        ((-2 : ℂ) ^ n)⁻¹ * (1 - 3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * kFidelity ρ k Λ) ∧
      (Λ.IsCompletelyPositive →
        3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k * realKFidelity ρ k Λ +
            (-2 : ℝ) ^ n * realProcessFidelity Λ = 1 ∧
        realProcessFidelity Λ =
          ((-2 : ℝ) ^ n)⁻¹ * (1 - 3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k * realKFidelity ρ k Λ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hTP, hpf1, _, _⟩ := pauliId1_props
  have hr := (h 1 (canonicalSICFamily 1)
    (canonicalSICFamily_isQubitSICProjector 1) pauliId1 hTP).1
  rw [show rejected.readout () () 1 = 0 from rfl, Finset.range_zero, Finset.sum_empty,
    mul_zero, zero_add, pow_one, hpf1, mul_one] at hr
  norm_num at hr

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@tp_exact_fidelity_reconstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tp_exact_fidelity_reconstruction, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@tp_exact_fidelity_reconstruction)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex.TpReconstruct.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex.TpReconstruct.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg",
        "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TpReconstruct

namespace SimplexRange

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n : ℕ),
    ∀ (ρ : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
      AffineIndependent ℝ (simplexVertex n) ∧
      jointKFidelityRange n ρ = convexHull ℝ (Set.range (simplexVertex n)) ∧
      (∀ Λ : QubitMap n, Λ.IsCompletelyPositive → Λ.IsTracePreserving →
        (∀ i : Fin (n + 1), 0 ≤ realWeightSum Λ i.val) ∧
        ∑ i : Fin (n + 1), realWeightSum Λ i.val = 1 ∧
        ∑ i : Fin (n + 1), realWeightSum Λ i.val • simplexVertex n i = jointKFidelityVec ρ Λ ∧
        ∀ c : Fin (n + 1) → ℝ, ∑ i : Fin (n + 1), c i = 1 →
          ∑ i : Fin (n + 1), c i • simplexVertex n i = jointKFidelityVec ρ Λ →
            ∀ i : Fin (n + 1), c i = realWeightSum Λ i.val) ∧
      (∀ Λ : QubitMap n, Λ.IsCompletelyPositive → Λ.IsTracePreserving →
        realProcessFidelity Λ = realWeightSum Λ 0 ∧
        realProcessFidelity Λ =
          ((-2 : ℝ) ^ O.readout () () n)⁻¹ *
            (1 - 3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val * jointKFidelityVec ρ Λ k))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hCP, hTP, _, hrpf1, hjv⟩ := pauliId1_props
  have hr := ((h 1 (canonicalSICFamily 1)
    (canonicalSICFamily_isQubitSICProjector 1)).2.2.2 pauliId1 hCP hTP).2
  rw [show rejected.readout () () 1 = 0 from rfl, hrpf1, Fin.sum_univ_one, Fin.val_zero, hjv] at hr
  norm_num at hr

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@cptp_joint_kFidelity_simplex_range)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cptp_joint_kFidelity_simplex_range, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cptp_joint_kFidelity_simplex_range)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex.SimplexRange.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex.SimplexRange.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SimplexRange

end

end Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex
