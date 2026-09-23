/- GID: D5/S3/ConceptDynamics/InformationEscape/IffRegistrations
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/IffRegistrations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dual_lawSensitive; instance=D5/S3/ConceptDynamics/InformationEscape/IffRegistrations.dualRealization
   digest: Two frozen iff theorems retain their predicates in one Boolean readout template. -/

import D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates
import D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
import D5.S0.Certificates.SelfInterestConventionDeviationGain
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.IffRegistrations

open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit

register_information_template iffRealization

section OpenClaim
open D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

def unsettledCode : Fin 5 :=
  (⟨Nat.zero, (let h : Nat.lt 0 5 := (by change 0 < 5; omega); h)⟩ :
    Fin (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))

def openPermissionReadout (i : Fin 5) : Bool :=
  @decide (i = unsettledCode) (instDecidableEqFin 5 i unsettledCode)
def openUnsettledReadout (i : Fin 5) : Bool :=
  @decide (i = unsettledCode) (instDecidableEqFin 5 i unsettledCode)
def openCodeArena := iffArena (Arena.ofFintype (Fin 5))
def openRealization := iffRealization
  (fun i : Fin 5 => openPermissionReadout i) (fun i => openUnsettledReadout i)
theorem open_bridge : LegacyPrimitiveRealization openCodeArena
    (∀ c : Claim, permits .open c = true ↔ c = .unsettled) openRealization := by
  constructor
  change (∀ c : Claim, permits .open c = true ↔ c = .unsettled) ↔
    ∀ i : Fin 5, openPermissionReadout i = openUnsettledReadout i
  let encode : Claim → Fin 5
    | .unsettled => 0 | .nonformalJudgment => 1 | .consequentUnderConditions => 2
    | .assertP => 3 | .assertNegP => 4
  let decode (i : Fin 5) : Claim :=
    if i = 0 then .unsettled else if i = 1 then .nonformalJudgment
    else if i = 2 then .consequentUnderConditions else if i = 3 then .assertP else .assertNegP
  have decodeEncode (c) : decode (encode c) = c := by cases c <;> decide
  have encodeDecode (i) : encode (decode i) = i := by fin_cases i <;> decide
  let coordinates : Claim ≃ Fin 5 := ⟨encode, decode, decodeEncode, encodeDecode⟩
  have leftDecoded (i) : openPermissionReadout i =
      decide (permits .open (coordinates.symm i) = true) := by
    change openPermissionReadout i = decide (permits .open (decode i) = true)
    fin_cases i <;> decide
  have rightDecoded (i) : openUnsettledReadout i =
      decide (coordinates.symm i = .unsettled) := by
    change openUnsettledReadout i = decide (decode i = .unsettled)
    fin_cases i <;> decide
  have pointwise (i) : openPermissionReadout i = openUnsettledReadout i ↔
      (permits .open (coordinates.symm i) = true ↔ coordinates.symm i = .unsettled) := by
    rw [leftDecoded, rightDecoded, Bool.eq_iff_iff]
    simp
  constructor
  · intro h i
    exact (pointwise i).mpr (h (coordinates.symm i))
  · intro h c
    have atCode := (pointwise (coordinates c)).mp (h (coordinates c))
    simpa only [coordinates.symm_apply_apply] using atCode

theorem open_lawSensitive : openCodeArena.Law openRealization ∧
    ¬ openCodeArena.Law (iffRealization (fun _ : Fin 5 => true) (fun _ => false)) := by
  refine ⟨open_bridge.equivalence.mp (fun c => open_permits_only_unsettled c), ?_⟩
  intro h
  exact Bool.noConfusion (h (0 : Fin 5))
theorem open_slotSensitive : FiniteSlotSensitivity openCodeArena :=
  iff_sensitivity _ (0 : Fin 5)
register_information_theorem open_permits_only_unsettled in openCodeArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    (Fin 5) (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  primitives openRealization.toPrimitiveBundle realization open_bridge
  variation open_lawSensitive sensitivity open_slotSensitive
example : open_permits_only_unsettled.__information_unit.Statement =
    (∀ c : Claim, permits .open c = true ↔ c = .unsettled) := rfl
#print axioms open_bridge
#print axioms open_lawSensitive
#print axioms open_slotSensitive
expect_information_occurrence open_permits_only_unsettled in openCodeArena
  from "D5.S3.ConceptDynamics.InformationEscape.IffRegistrations"
end OpenClaim

section DualConvention
open D5.S0.Certificates.SelfInterestConventionDeviationGain

def dualFixedReadout (c : Convention) : Bool :=
  @decide (c.1 = c.2) (instDecidableEqBool c.1 c.2)
def dualAlternativesReadout (c : Convention) : Bool :=
  Bool.rec (@decide (c.2 = false) (instDecidableEqBool c.2 false))
    (@decide (c.2 = true) (instDecidableEqBool c.2 true)) c.1
def dualArena := iffArena (Arena.ofFintype Convention)
def dualRealization := iffRealization
  (fun convention : Convention => dualFixedReadout convention)
  (fun convention => dualAlternativesReadout convention)
theorem dual_bridge : LegacyPrimitiveRealization dualArena
    (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) dualRealization := by
  constructor
  change (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) ↔
    ∀ c : Convention, dualFixedReadout c = dualAlternativesReadout c
  have leftIff (c : Convention) : dualFixedReadout c = true ↔ dual c = c := by
    rcases c with ⟨a, b⟩
    cases a <;> cases b <;> decide
  have rightIff (c : Convention) : dualAlternativesReadout c = true ↔ c = FvF ∨ c = AvA := by
    rcases c with ⟨a, b⟩
    cases a <;> cases b <;> decide
  have pointwise (c : Convention) :
      (dual c = c ↔ c = FvF ∨ c = AvA) ↔ dualFixedReadout c = dualAlternativesReadout c := by
    rw [← leftIff, ← rightIff]
    exact Bool.eq_iff_iff.symm
  exact ⟨fun h c => (pointwise c).mp (h c), fun h c => (pointwise c).mpr (h c)⟩
theorem dual_lawSensitive : dualArena.Law dualRealization ∧
    ¬ dualArena.Law (iffRealization (fun _ : Convention => true) (fun _ => false)) := by
  refine ⟨dual_bridge.equivalence.mp (fun convention => dual_fixed_iff convention), ?_⟩
  intro h
  exact Bool.noConfusion (h FvF)
theorem dual_slotSensitive : FiniteSlotSensitivity dualArena :=
  iff_sensitivity _ FvF
register_information_theorem dual_fixed_iff in dualArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention))
  primitives dualRealization.toPrimitiveBundle realization dual_bridge
  variation dual_lawSensitive sensitivity dual_slotSensitive
example : dual_fixed_iff.__information_unit.Statement =
    (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) := rfl
#print axioms dual_bridge
#print axioms dual_lawSensitive
#print axioms dual_slotSensitive
expect_information_occurrence dual_fixed_iff in dualArena
  from "D5.S3.ConceptDynamics.InformationEscape.IffRegistrations"
end DualConvention

#seal_information_theory

open Lean in
run_meta do
  let env ← getEnv
  for entry in InformationRegistry.entries env do
    if entry.registrationModuleName == env.header.mainModule then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName env.header.mainModule)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
      else
        logWarning diagnostic

end D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
