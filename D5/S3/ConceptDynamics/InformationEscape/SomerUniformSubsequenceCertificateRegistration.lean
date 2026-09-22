/- GID: D5/S3/ConceptDynamics/InformationEscape/SomerUniformSubsequenceCertificateRegistration
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/SomerUniformSubsequenceCertificateRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Six CUT readouts register the complete Somer-Krizek counterexample certificate. -/

import D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation
import D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation
open D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates
open LeanInformationAudit

namespace D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration

def certificateArena : PrimitiveLawArena where
  toArena := Arena.ofFintype CertificateWord
  signature := certificateSignature CertificateWord
  Law realization :=
    let readWord : CertificateWord := fun index => realization.readout index actualWord
    readWord = actualWord /\ CounterexampleCertificate readWord

local instance : DecidableEq CertificateWord := inferInstance
local instance : DecidableEq certificateArena.State := certificateArena.toArena.stateDecidableEq

def certificateRealization :=
  certificateWordRealization (X := CertificateWord)
    (fun (word : CertificateWord) (index : Fin 6) => word index)

def bumpCode (code : Fin 5) : Fin 5 :=
  ⟨(code.1 + 1) % 5, Nat.mod_lt _ (by omega)⟩

private theorem bumpCode_ne (code : Fin 5) : bumpCode code ≠ code := by
  fin_cases code <;> decide

def alteredRealization (changed : Fin 6) : PrimitiveRealization certificateArena.signature :=
  certificateWordRealization fun word index =>
    if index = changed then bumpCode (word index) else word index

private theorem certificateLaw : certificateArena.Law certificateRealization := by
  exact ⟨rfl, actualRefutationEvidence.certificate⟩

private theorem altered_not_law (changed : Fin 6) :
    ¬ certificateArena.Law (alteredRealization changed) := by
  rintro ⟨equality, _⟩
  have atChanged := congrFun equality changed
  apply bumpCode_ne (actualWord changed)
  simpa [alteredRealization, certificateWordRealization, certificateSignature] using atChanged

private theorem certificateBridge : LegacyPrimitiveRealization certificateArena
    (let counterexample := actualWord; Not fullClaim) certificateRealization := by
  constructor
  constructor
  · intro _
    exact certificateLaw
  · rintro ⟨_, certificate⟩
    exact actualRefutationEvidence.refutes certificate

private theorem certificateVariation : FiniteLawVariation certificateArena := by
  exact ⟨certificateRealization, alteredRealization 0, certificateLaw, altered_not_law 0⟩

private theorem certificateSensitivity : FiniteSlotSensitivity certificateArena := by
  classical
  constructor
  · intro i
    refine ⟨certificateRealization, alteredRealization i, ?_, ?_, ?_⟩
    · intro j hne
      change Fin 6 at i j
      funext word
      change CertificateWord at word
      change word j = if j = i then bumpCode (word j) else word j
      split
      · next h => exact (hne h).elim
      · rfl
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => altered_not_law i, fun _ => certificateLaw⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem result in certificateArena
  readout via (@certificateWordRealization CertificateWord (fun word index => word index))
  primitives certificateRealization.toPrimitiveBundle realization certificateBridge
  variation certificateVariation sensitivity certificateSensitivity
  escape from (actualWord) escape continues (open)

end D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration
