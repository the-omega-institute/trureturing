/- GID: D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundSoundness
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMTerminalBoundSoundness
   mirror-E: none(waiver:actual-exact-certificate-premise)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; premises=D5/S3/Quantum/Entanglement/EJM/EJMContractionCertificates.triangle_contractions,D5/S3/Quantum/Entanglement/EJM/EJMContractionCertificates.singleton_contractions,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_tags,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_terminals,D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_tags
   digest: Actual terminal checks and earned contractions imply the required centered-score bounds. -/

/-
admission_basis: escape-witness
This delivery supplies the complete actual numerical premises for local
row and cache soundness. The consumed receipts are not independent
positive finite-instance results. Numerical
normalization and consumed binding helpers supply no separate escape.
Public targets: triangle_terminal_sound, singleton_terminal_sound,
triangle_all_terminal_bounds, singleton_all_terminal_bounds.
proof_shape: bind-only relative to the earned contraction symmetries, original
check interpretation and logical transport. These are consumed conditional
helpers, not independent escape claims. The contraction and terminal-check
premises stay explicit in their theorem types. EJMLocalBoundAcceptance supplies
all of them from the actual full-domain kernel receipts in this same delivery.
The singleton formula retains its factor 64, and every bound is on the
original triangleCentered F1 or singletonCentered F2 at the actual event.
The tag receipts identify every complete row's event; no terminal event or
external numerical minimum is substituted without that checked equality.
The concrete numeric premises listed in the utility header must be
kernel-checked in this delivery, with the same original functions,
finite domains, partial rows and inequality direction. Pending sources
or external producer validations do not fulfill those premises.
Four-slot registration remains unfinished under issue #16309. The
specific public targets below lack a compiled original-source
realization bridge, enrolled readout and variation/sensitivity evidence;
this is a missing-registration statement, not a template-support claim.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundSoundness
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMContractionSymmetry
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry
open D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundData

theorem triangle_terminal_sound
    (contractions : ∀ i, triangleContraction F1 (EJMContractionData.triangleTail i) =
      EJMContractionData.triangleValue i)
    (j : Fin 4588) (checked : triangleTerminalCheck j = true) :
    (triangleRows ⟨j.val, lt_trans j.isLt (by decide : 4588 < 41294)⟩).lower ≤
      triangleCentered F1 (triangleTerminalEvent j) := by
  let e := triangleTerminalEvent j
  let w := triangleWitness j
  have transport : EJMContractionData.triangleTail w.2 =
      outcome w.1.2 ∘ (fun i : Fin 7 => e (Fin.natAdd 3 i)) ∘ triangleTailPerm w.1.1 ∧
      (triangleRows ⟨j.val, lt_trans j.isLt (by decide : 4588 < 41294)⟩).lower ≤
        256 * F1 e - EJMContractionData.triangleValue w.2 := by
    unfold triangleTerminalCheck at checked
    cases rule : (triangleRows
      ⟨j.val, lt_trans j.isLt (by decide : 4588 < 41294)⟩).rule with
    | complete actual =>
      simp only [rule] at checked
      simpa only [one_mul] using (of_decide_eq_true checked).2
    | split i child sym => simp only [rule, Bool.false_eq_true] at checked
  have hc : EJMContractionData.triangleValue w.2 =
      triangleContraction F1 (fun i : Fin 7 => e (Fin.natAdd 3 i)) := by
    rw [← contractions, transport.1]
    change triangleContraction F1
      ((outcomeEquiv w.1.2) ∘ ((fun i : Fin 7 => e (Fin.natAdd 3 i)) ∘
        triangleTailPerm w.1.1)) = _
    rw [actual_triangleContraction_relabel, actual_triangleContraction_coordinate]
  have bound := transport.2
  rw [hc] at bound
  exact bound

theorem singleton_terminal_sound
    (contractions : ∀ i, singletonContraction F2 (EJMContractionData.singletonTail i) =
      EJMContractionData.singletonValue i)
    (j : Fin 1192) (checked : singletonTerminalCheck j = true) :
    (singletonRows ⟨j.val, lt_trans j.isLt (by decide : 1192 < 8689)⟩).lower ≤
      singletonCentered F2 (singletonTerminalEvent j) := by
  let e := singletonTerminalEvent j
  let w := singletonWitness j
  have transport : EJMContractionData.singletonTail w.2 =
      outcome w.1.2 ∘ (fun i : Fin 8 => e (Fin.natAdd 1 i)) ∘ singletonTailPerm w.1.1 ∧
      (singletonRows ⟨j.val, lt_trans j.isLt (by decide : 1192 < 8689)⟩).lower ≤
        256 * F2 e - 64 * EJMContractionData.singletonValue w.2 := by
    unfold singletonTerminalCheck at checked
    cases rule : (singletonRows
      ⟨j.val, lt_trans j.isLt (by decide : 1192 < 8689)⟩).rule with
    | complete actual =>
      simp only [rule] at checked
      exact (of_decide_eq_true checked).2
    | split i child sym => simp only [rule, Bool.false_eq_true] at checked
  have hc : EJMContractionData.singletonValue w.2 =
      singletonContraction F2 (fun i : Fin 8 => e (Fin.natAdd 1 i)) := by
    rw [← contractions, transport.1]
    change singletonContraction F2
      ((outcomeEquiv w.1.2) ∘ ((fun i : Fin 8 => e (Fin.natAdd 1 i)) ∘
        singletonTailPerm w.1.1)) = _
    rw [actual_singletonContraction_relabel, actual_singletonContraction_coordinate]
  have bound := transport.2
  rw [hc] at bound
  exact bound

#print axioms triangle_terminal_sound
#print axioms singleton_terminal_sound

theorem triangle_all_terminal_bounds
    (contractions : ∀ i, triangleContraction F1 (EJMContractionData.triangleTail i) =
      EJMContractionData.triangleValue i)
    (terminalChecks : ∀ j, triangleTerminalCheck j = true)
    (tagChecks : ∀ j, triangleTerminalTagCheck j = true)
    (j : Fin 41294) (e : Fin 10 → Fin 4) (hrule : (triangleRows j).rule = .complete e) :
    (triangleRows j).lower ≤ triangleCentered F1 e := by
  have checked := tagChecks j
  unfold triangleTerminalTagCheck at checked
  rw [hrule] at checked
  split_ifs at checked with hj
  · have he : e = triangleTerminalEvent ⟨j.val, hj⟩ := of_decide_eq_true checked
    rw [he]
    exact triangle_terminal_sound contractions ⟨j.val, hj⟩ (terminalChecks _)

theorem singleton_all_terminal_bounds
    (contractions : ∀ i, singletonContraction F2 (EJMContractionData.singletonTail i) =
      EJMContractionData.singletonValue i)
    (terminalChecks : ∀ j, singletonTerminalCheck j = true)
    (tagChecks : ∀ j, singletonTerminalTagCheck j = true)
    (j : Fin 8689) (e : Fin 9 → Fin 4) (hrule : (singletonRows j).rule = .complete e) :
    (singletonRows j).lower ≤ singletonCentered F2 e := by
  have checked := tagChecks j
  unfold singletonTerminalTagCheck at checked
  rw [hrule] at checked
  split_ifs at checked with hj
  · have he : e = singletonTerminalEvent ⟨j.val, hj⟩ := of_decide_eq_true checked
    rw [he]
    exact singleton_terminal_sound contractions ⟨j.val, hj⟩ (terminalChecks _)

#print axioms triangle_all_terminal_bounds
#print axioms singleton_all_terminal_bounds
end D5.S3.Quantum.Entanglement.EJM.EJMTerminalBoundSoundness
