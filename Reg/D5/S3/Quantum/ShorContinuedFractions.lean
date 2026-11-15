import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.ShorContinuedFractions

namespace Reg.D5.S3.Quantum.ShorContinuedFractions.Membership
open QuantumShorContinuedFractions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : Parameters, ℕ)
    (fun p => Fin (2 ^ p.2)) (fun _ => List ℚ)
def actual : Realization signature :=
  realize signature (fun _ p y => candidates y.val (2 ^ p.2) p.1.modulus) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (c : Parameters) (n : ℕ), c.modulus ^ 2 ≤ 2 ^ n →
    ∀ (s : Fin c.period) (y : Fin (2 ^ n)),
    Nearest (2 ^ n) (s.val / (c.period : ℝ)) y →
    reduced s.val c.period ∈ R.readout () ⟨c,n⟩ y ∧ (reduced s.val c.period).den ∣ c.period
private def sample : Parameters := ⟨2, by norm_num, 1, by norm_num, 1, by norm_num⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : sample.period = 1 := by
    change orderOf (1 : ZMod 2) = 1
    exact orderOf_one
  have hh := h sample 2 (by norm_num [sample]) ⟨0, by omega⟩ ⟨0, by decide⟩
    (by exact ⟨0, by norm_num⟩)
  simpa [rejected, realize] using hh.1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let c : Parameters := ⟨3, by decide, 2, by decide, 2, by decide⟩
  refine ⟨⟨c, 4⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ?_⟩
  change candidates 0 16 3 ≠ candidates 8 16 3
  have hd : (1 / 2 : ℚ).den = 2 := by
    change (reduced 1 2).den = 2
    rw [reduced_den _ _ (by decide)]
    norm_num
  norm_num [candidates, convergents, Int.fract, hd]

def source_registration : Registration arena (type_of% @QuantumShorContinuedFractions.shor_nearest_candidate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@QuantumShorContinuedFractions.shor_nearest_candidate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumShorContinuedFractions.shor_nearest_candidate) (Realization signature) Unit Unit := {
  unitName := `QuantumShorContinuedFractions.shor_nearest_candidate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.ShorContinuedFractions.Membership.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => candidates y.val (2 ^ p.2) p.1.modulus) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.ShorContinuedFractions
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Quantum.ShorContinuedFractions.Membership

namespace Reg.D5.S3.Quantum.ShorContinuedFractions.Coprime
open QuantumShorContinuedFractions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : Parameters, ℕ)
    (fun p => Fin (2 ^ p.2)) (fun _ => List ℕ)
def actual : Realization signature :=
  realize signature (fun _ p y => (candidates y.val (2 ^ p.2) p.1.modulus).map Rat.den)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (c : Parameters) (n : ℕ), c.modulus ^ 2 ≤ 2 ^ n →
    ∀ (s : Fin c.period) (y : Fin (2 ^ n)),
    Nearest (2 ^ n) (s.val / (c.period : ℝ)) y → Nat.Coprime s.val c.period →
    c.period ∈ R.readout () ⟨c,n⟩ y
private def sample : Parameters := ⟨2, by norm_num, 1, by norm_num, 1, by norm_num⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : sample.period = 1 := by
    change orderOf (1 : ZMod 2) = 1
    exact orderOf_one
  have hh := h sample 2 (by norm_num [sample]) ⟨0, by omega⟩ ⟨0, by decide⟩
    (by exact ⟨0, by norm_num⟩) (by simpa [hp] using Nat.coprime_zero_left.mpr rfl)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let c : Parameters := ⟨3, by decide, 2, by decide, 2, by decide⟩
  refine ⟨⟨c, 4⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ?_⟩
  change (candidates 0 16 3).map Rat.den ≠ (candidates 8 16 3).map Rat.den
  have hd : (1 / 2 : ℚ).den = 2 := by
    change (reduced 1 2).den = 2
    rw [reduced_den _ _ (by decide)]
    norm_num
  norm_num [candidates, convergents, Int.fract, hd]

def source_registration : Registration arena (type_of% @QuantumShorContinuedFractions.shor_coprime_candidate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@QuantumShorContinuedFractions.shor_coprime_candidate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumShorContinuedFractions.shor_coprime_candidate) (Realization signature) Unit Unit := {
  unitName := `QuantumShorContinuedFractions.shor_coprime_candidate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.ShorContinuedFractions.Coprime.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => (candidates y.val (2 ^ p.2) p.1.modulus).map Rat.den) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.ShorContinuedFractions
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Quantum.ShorContinuedFractions.Coprime
