import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate
import Reg.Support.DependentFamily

/-! Source-bound audit of the binomial bound on a nonsimulability certificate. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate

open _root_.D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds (IsRowStochastic)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the binomial certificate bound as the simulated dimension varies. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k d => k.choose d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve every hypothesis and both qualitative certificate conditions. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m k d : ℕ) (_hd : 1 ≤ d) (_hk : d < k)
    (p : Fin m → Fin k → ℝ) (_hp : IsRowStochastic p) (_h : ¬ IsSimulable d p),
      ∃ i : Finset (Fin m), i.Nonempty ∧ i.card ≤ R.readout () k d ∧
        ¬ IsSimulable d ((i : Set _).domRestrict p)

private def binaryChannel (x y : Fin 2) : ℝ := if x = y then 1 else 0

private theorem binaryChannel_stochastic : IsRowStochastic binaryChannel := by
  constructor
  · intro x y
    simp only [binaryChannel]
    split <;> norm_num
  · intro x
    simp [binaryChannel]

private theorem binaryChannel_not_simulable : ¬ IsSimulable 1 binaryChannel := by
  rintro ⟨n, q, t, r, _, _, ht, _, hrec⟩
  have htone (l : Fin n) (x : Fin 2) : t l x 0 = 1 := by
    simpa using (ht l).2 x
  have hzero := hrec 0 0
  have hone := hrec 1 0
  simp only [Fin.sum_univ_one, htone, mul_one] at hzero hone
  have heq : binaryChannel 0 0 = binaryChannel 1 0 := hzero.trans hone.symm
  norm_num [binaryChannel] at heq

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨i, hi, hcard, _⟩ :=
    h 2 2 1 (by norm_num) (by norm_num) binaryChannel binaryChannel_stochastic
      binaryChannel_not_simulable
  change i.card ≤ 0 at hcard
  exact (Nat.not_lt_of_ge hcard) hi.card_pos

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨4, 1, 2, ?_⟩
  change Nat.choose 4 1 ≠ Nat.choose 4 2
  decide

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k d => k.choose d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate
