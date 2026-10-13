import D5.S3.Quantum.Entanglement.EJMTerminalBoundData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJMTerminalBoundSoundness
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJMContractionSymmetry
open D5.S3.Quantum.Entanglement.EJMScoreSymmetry
open D5.S3.Quantum.Entanglement.EJMTerminalBoundData

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
      exact (of_decide_eq_true checked).2
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
  · cases checked

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
  · cases checked

#print axioms triangle_all_terminal_bounds
#print axioms singleton_all_terminal_bounds
end D5.S3.Quantum.Entanglement.EJMTerminalBoundSoundness
