import D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation
import Reg.Support.CounterexampleRecord

namespace Reg.D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

private theorem cert_sound :
    ∀ fuel s cert, certValid fuel s cert = true → PresenterWins fuel s := by
  intro fuel
  induction fuel with
  | zero =>
    intro s cert h
    cases cert with
    | stop => exact PresenterWins.stop h
    | step edge children => simp [certValid] at h
  | succ fuel ih =>
    intro s cert h
    cases cert with
    | stop => exact PresenterWins.stop h
    | step edge children =>
      simp only [certValid, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hbound, hfree⟩, hchildren⟩ := h
      exact PresenterWins.step edge
        (by simpa only [decide_eq_true_eq] using hbound) hfree
        (fun c => ih _ _ ((List.all_eq_true.mp hchildren) c.val
          (List.mem_range.mpr c.isLt)))

private theorem five_not_wins : ¬ AlgorithmWins 10 initial := by
  have incompatible : ∀ fuel s, PresenterWins fuel s → ¬ AlgorithmWins fuel s := by
    intro fuel s hw ha
    induction fuel generalizing s with
    | zero =>
      cases hw with
      | stop h =>
        change terminalBad s = false at ha
        simp [h] at ha
    | succ fuel ih =>
      cases hw with
      | stop h =>
        have hf := ha.1
        change terminalBad s = false at hf
        simp [h] at hf
      | step e hbound hfree h =>
        obtain ⟨_, hresp⟩ := ha
        obtain ⟨c, hc⟩ := hresp e hbound hfree
        exact ih _ (h c) hc
  have checked : certValid 10 initial certificate = true := by decide
  exact incompatible 10 initial (cert_sound 10 initial certificate checked)

private def predicate (n : Nat) : Prop :=
  n ∈ [5, 6, 7] → AlgorithmWinsFor n (edgesFor n).length (initialFor n)

private def embed : Fin 1 → Nat := fun _ => 5

private def decision : ∀ w : Fin 1, Decidable (predicate (embed w)) :=
  fun w => .isFalse (by
    intro h
    have five : AlgorithmWins 10 initial := by
      have member : embed w ∈ [5, 6, 7] := by simp [embed]
      simpa [predicate, embed, AlgorithmWins, initial, initialFor,
        edgesFor, edges] using h member
    exact five_not_wins five)

private def arena := WitnessArena.ofCarrier (Fin 1) Nat predicate embed decision
private def reads := counterexampleRealization (fun _ : Fin 1 => false)

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

register_information_theorem
  _root_.D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation.result in arena
  readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (Nat) escape continues (open)

end Reg.D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation
