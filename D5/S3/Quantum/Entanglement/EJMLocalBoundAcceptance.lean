import D5.S3.Quantum.Entanglement.EJMContractionCertificates
import D5.S3.Quantum.Entanglement.EJMStructureCertificates
import D5.S3.Quantum.Entanglement.EJMTerminalCertificates
import D5.S3.Quantum.Entanglement.EJMTerminalBoundSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJMLocalBoundAcceptance
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJMScoreSymmetry (triangleCentered singletonCentered)

/-! Every actual local row is accepted only after checking its complete
structure, exact terminal event, actual coefficient inequality and actual
contraction value. No numerical receipt is assumed in these consumers. -/

theorem triangle_accepted :
    ∀ j, checkRow (triangleCentered F1) trianglePartialAct triangleRows j = true := by
  apply checked_structure_and_terminals
  · exact EJMStructureCertificates.triangle_structure
  · exact EJMTerminalBoundSoundness.triangle_all_terminal_bounds
      EJMContractionCertificates.triangle_contractions
      EJMTerminalCertificates.triangle_terminals EJMTerminalCertificates.triangle_tags

theorem singleton_accepted :
    ∀ j, checkRow (singletonCentered F2) singletonPartialAct singletonRows j = true := by
  apply checked_structure_and_terminals
  · exact EJMStructureCertificates.singleton_structure
  · exact EJMTerminalBoundSoundness.singleton_all_terminal_bounds
      EJMContractionCertificates.singleton_contractions
      EJMTerminalCertificates.singleton_terminals EJMTerminalCertificates.singleton_tags

#print axioms triangle_accepted
#print axioms singleton_accepted
end D5.S3.Quantum.Entanglement.EJMLocalBoundAcceptance
