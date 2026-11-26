import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.KarttunenA401714
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Divisors.KarttunenA401714

open _root_.D5.S3.Arith.Divisors.KarttunenA401714
open _root_.D5.S3.Arith.EulerFormDivisorSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ N => unitarySum N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (hn : 0 < N),
    N / (∏ p ∈ N.primeFactors, p) < leastMissingPrime N hn →
    2 * N ≤ R.readout () () N + squarefreeSum N

private theorem leastMissingPrime_ge_two (N : ℕ) (hn : 0 < N) :
    2 ≤ leastMissingPrime N hn := by
  unfold leastMissingPrime
  generalize_proofs h
  have hp : Nat.Prime (Nat.find (p := fun p => Nat.Prime p ∧ ¬ p ∣ N) h) :=
    (Nat.find_spec (p := fun p => Nat.Prime p ∧ ¬ p ∣ N) h).1
  exact hp.two_le

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : 0 < (1 : ℕ) := by decide
  have hm : 1 / (∏ p ∈ (1 : ℕ).primeFactors, p) < leastMissingPrime 1 hn :=
    (by norm_num : 1 / (∏ p ∈ (1 : ℕ).primeFactors, p) < 2) |>.trans_le
      (leastMissingPrime_ge_two 1 hn)
  have hz := h 1 hn hm
  change 2 * 1 ≤ 0 + squarefreeSum 1 at hz
  have hs : squarefreeSum 1 = 1 := by
    simp [squarefreeSum, Finset.filter_singleton]
  rw [hs] at hz
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change unitarySum 1 ≠ unitarySum 2
  decide

def sourceRegistration : Registration arena
    (∀ (N : ℕ) (hn : 0 < N),
      N / (∏ p ∈ N.primeFactors, p) < leastMissingPrime N hn →
      2 * N ≤ unitarySum N + squarefreeSum N) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.KarttunenA401714.result)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Divisors.KarttunenA401714.unit
  realizationName := `Reg.D5.S3.Arith.Divisors.KarttunenA401714.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => unitarySum N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.KarttunenA401714
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Divisors.KarttunenA401714
