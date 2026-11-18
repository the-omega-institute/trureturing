import D5.S1.Recurrence.Raney.ExactRunRecordSpectrum
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound registration of the complete all-prime R31 theorem. -/

namespace Reg.D5.S1.Recurrence.Raney.ExactRunRecordSpectrum

open TrureTuring.Raney
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Nat (fun _ => Nat) (fun p => ZMod p)

def actual : Realization signature :=
  realize signature (fun _ p n => (raneyNumber 3 1 n : ZMod p)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Nat) (_hp : p.Prime),
    let ρ : Nat → ZMod p := R.readout () p
    let values : Set Nat := {l | ∃ m j, runSpectrumRetained p m j ∧ l = runSpectrumLength p m j}
    positiveZeroRunLengths ρ = values ∧
    positiveZeroRunRecordValues ρ = values ∧
    (∀ m j, runSpectrumRetained p m j →
      IsMaximalDeltaInterval {0} ρ (runSpectrumStart p m j) (runSpectrumLast p m j) ∧
      0 < runSpectrumLength p m j ∧
      runSpectrumLast p m j + 1 - runSpectrumStart p m j = runSpectrumLength p m j ∧
      IsFirstZeroRunLength ρ (runSpectrumStart p m j) (runSpectrumLast p m j) ∧
      IsWeakZeroRunRecord ρ (runSpectrumStart p m j) (runSpectrumLast p m j)) ∧
    (∀ m h j k, runSpectrumRetained p m j → runSpectrumRetained p h k →
      (m < h ∨ (m = h ∧ j < k)) → runSpectrumLength p m j < runSpectrumLength p h k) ∧
    (∀ m h j k, runSpectrumRetained p m j → runSpectrumRetained p h k →
      runSpectrumLength p m j = runSpectrumLength p h k → m = h ∧ j = k) ∧
    (5 ≤ p → ∀ m j, 1 ≤ m → (j = 1 ∨ j = 2) →
      ((j * p ^ m + 2) / 3 ≤ (if j = 1 then (p ^ m - 3) / 2 else p ^ m - 1) ↔
        j = 2 ∨ (p ^ m ≠ 5 ∧ p ^ m ≠ 7)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hw := (h 2 Nat.prime_two).2.2.1 2 1 (by norm_num [runSpectrumRetained])
  have hz := hw.1.2.1 3 (by decide) (by decide)
  change (1 : ZMod 2) ∈ ({0} : Finset (ZMod 2)) at hz
  exact one_ne_zero (Finset.mem_singleton.mp hz)

def family : Registration arena (type_of% @raney_all_prime_exact_run_record_spectrum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨raney_all_prime_exact_run_record_spectrum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 0, 3, ?_⟩
    change (raneyNumber 3 1 0 : ZMod 2) ≠ (raneyNumber 3 1 3 : ZMod 2)
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@raney_all_prime_exact_run_record_spectrum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Raney.ExactRunRecordSpectrum.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Raney.ExactRunRecordSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => (raneyNumber 3 1 n : ZMod p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Raney.ExactRunRecordSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Raney.ExactRunRecordSpectrum
