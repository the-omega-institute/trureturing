/- GID: D5/S3/Quantum/Entanglement/EJM/EJMLocalBoundAcceptance
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMLocalBoundAcceptance
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMStructureCertificates.triangle_structure,D5/S3/Quantum/Entanglement/EJM/EJMStructureCertificates.singleton_structure,D5/S3/Quantum/Entanglement/EJM/EJMContractionCertificates.triangle_contractions,D5/S3/Quantum/Entanglement/EJM/EJMContractionCertificates.singleton_contractions,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_tags,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_tags
   digest: All actual local coefficient-bound rows earn complete checkRow acceptance. -/

/-
admission_basis: escape-witness
This delivery supplies the complete actual numerical premises for local
row and cache soundness. The consumed receipts are not independent
positive finite-instance results. Numerical
normalization and consumed binding helpers supply no separate escape.
Public targets: triangle_accepted, singleton_accepted.
proof_shape: bind-only; these consumed assembly helpers apply
checked_structure_and_terminals, whose complete/split case analysis combines
the exact structural and terminal premises without recursive score evaluation.
They supply no independent escape content. The actual cache lower-bound proof
uses checked_rows_lower_bound's strong induction over earlier child rows.
Every actual structural, terminal-tag,
terminal-inequality and contraction premise is supplied by the named kernel
receipts without an assumed acceptance proposition. These complete local
acceptance theorems feed EJMCacheSoundness.associated_lower_le_score. They assert local row acceptance, not acceptance
of the global DAG or its positive margin; the final consumer must separately
earn its actual global_accepted computation.
The concrete numeric premises listed in the utility header must be
kernel-checked in this delivery, with the same original functions,
finite domains, partial rows and inequality direction. Pending sources
or external producer validations do not fulfill those premises.
Four-slot registration remains unfinished under issue #16309. The
specific public targets below lack a compiled original-source
realization bridge, enrolled readout and variation/sensitivity evidence;
this is a missing-registration statement, not a template-support claim.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMContractionCertificates
import D5.S3.Quantum.Entanglement.EJM.EJMStructureCertificates
import D5.S3.Quantum.Entanglement.EJM.EJMTerminalCertificates
import D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMLocalBoundAcceptance
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry (triangleCentered singletonCentered)

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
end D5.S3.Quantum.Entanglement.EJM.EJMLocalBoundAcceptance
