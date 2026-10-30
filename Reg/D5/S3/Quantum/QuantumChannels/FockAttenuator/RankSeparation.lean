import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteRankClassification
import Reg.Support.DependentFamily

/-! A dependent-family audit of the completed operator-rank readout. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.QuantumChannels.FockAttenuator
open _root_.D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open _root_.D5.S3.Analytic.Entire
open BeamSplitter DisplacementCovariance Attenuator

noncomputable section
namespace Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.RankSeparation

abbrev rankSignature : Signature where
  Params := Unit
  State _ := TwoMode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Cardinal
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rankActual : Realization rankSignature :=
  realize rankSignature (fun _ _ V => rangeRank (purePartialTrace V)) (fun e => nomatch e)

abbrev rankRejected : Realization rankSignature :=
  realize rankSignature (fun _ _ _ => (1 : Cardinal)) (fun e => nomatch e)

abbrev rankArena : Arena where
  signature := rankSignature
  Law R := ∀ (V : TwoMode) (k : ℕ),
    R.readout () () V ≤ (k : Cardinal) ↔ SeparatedLE k (kernel V)

private theorem rank_zero : rangeRank (purePartialTrace (0 : TwoMode)) = 0 := by
  have hC : coefficientOperator (0 : TwoMode) = 0 := by
    symm
    apply coefficient_operator_unique
    intro j
    rfl
  rw [pure_partial_trace_eq, hC, zero_mul]
  change Module.rank ℂ (LinearMap.range (0 : Fock →ₗ[ℂ] Fock)) = 0
  rw [LinearMap.range_zero]
  exact rank_bot ℂ Fock

private theorem rejected : ¬ rankArena.Law rankRejected := by
  intro h
  have hz : SeparatedLE 0 (kernel (0 : TwoMode)) :=
    (reduced_rank_le_iff_separated 0 0).mp (by rw [rank_zero]; exact le_rfl)
  have hh := (h 0 0).mpr hz
  change (1 : Cardinal) ≤ 0 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence rankSignature rankActual := by
  intro i
  have hHalf : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  let a : Fock := lp.single 2 0 (1 : ℂ)
  have ha : a ≠ 0 := by
    intro h
    have hc := congrArg (fun v : Fock => v 0) h
    simp only [a, lp.single_apply_self, lp.coeFn_zero, Pi.zero_apply] at hc
    exact one_ne_zero hc
  let V : TwoMode := beamSplitter (1/2) hHalf (tensor a (lp.single 2 2 (1 : ℂ)))
  have hpos : (3 : Cardinal) ≤ rangeRank (purePartialTrace V) := by
    have h := actual_rank_lower_bound a ha hHalf
    rwa [point_mass_pure_attenuator] at h
  refine ⟨(), (0 : TwoMode), V, ?_⟩
  intro h
  change rangeRank (purePartialTrace (0 : TwoMode)) = rangeRank (purePartialTrace V) at h
  rw [rank_zero] at h
  rw [← h] at hpos
  norm_num at hpos

def rankEvidence : Registration rankArena
    (∀ (V : TwoMode) (k : ℕ),
      rangeRank (purePartialTrace V) ≤ (k : Cardinal) ↔ SeparatedLE k (kernel V)) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨reduced_rank_le_iff_separated, rankRejected, rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rankRejected, ?_, ?_, rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def rankRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann.reduced_rank_le_iff_separated)
    (type_of% (realize rankSignature (fun _ _ V => rangeRank (purePartialTrace V))
      (fun e => nomatch e))) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.RankSeparation.rankUnit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.RankSeparation.rankEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena⟩
  objectArena := .source ⟨rankArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena ⟨rankEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature (fun _ _ V => rangeRank (purePartialTrace V))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (↥TwoMode)
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.FockAttenuator.RankSeparation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.RankSeparation
