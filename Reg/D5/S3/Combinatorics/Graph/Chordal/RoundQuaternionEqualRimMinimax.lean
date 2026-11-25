import D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionEqualRimMinimax
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the attained radius and its normalized ratio. -/

open scoped Quaternion Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionEqualRimMinimax

open _root_.RoundQuaternionK4Bounds _root_.RoundQuaternionEqualRimMinimax
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

local notation "U" => unitary ℍ[ℝ]

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ a => equalRimOptRadius a) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, π / 3, ?_⟩
  simp [actual, realize, equalRimOptRadius, show 0 ≤ π / 3 by positivity]
  linarith [Real.pi_pos]

namespace Exact

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (I : ℍ[ℝ]) (hI : I.re = 0) (hN : ‖I‖ = 1) (a : ℝ),
    a ∈ Set.Icc 0 π →
    DefectLE (equalRimGains I hI hN a) (equalRimDefect a) ∧
    (∀ ε, DefectLE (equalRimGains I hI hN a) ε → equalRimDefect a ≤ ε) ∧
    (∃ φ : Fin 4 → U, Fits (equalRimGains I hI hN a) φ (R.readout () () a)) ∧
    (∀ (φ : Fin 4 → U) (r : ℝ), Fits (equalRimGains I hI hN a) φ r →
      equalRimOptRadius a ≤ r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hI : (unitI : ℍ[ℝ]).re = 0 := rfl
  have hN : ‖(unitI : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary unitI
  obtain ⟨_, _, ⟨φ, hf⟩, _⟩ := h (unitI : ℍ[ℝ]) hI hN 0
    ⟨le_rfl, Real.pi_pos.le⟩
  have he := hf 0 1 (by decide)
  change roundDist _ _ ≤ -1 at he
  exact (not_le_of_gt (lt_of_lt_of_le (by norm_num) (Real.arccos_nonneg _))) he

def family : Registration arena (type_of% (@equalRim_exact_defect_and_minimax)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@equalRim_exact_defect_and_minimax, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@equalRim_exact_defect_and_minimax) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionEqualRimMinimax.equalRim_exact_defect_and_minimax.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionEqualRimMinimax.Exact.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionEqualRimMinimax
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg",
        "fn", "arg", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Exact

namespace Ratio

def rejected : Realization signature :=
  realize signature (fun _ _ a => ((2 / π) * quarterError + 1) * equalRimDefect a)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ), a ∈ Set.Ioc 0 π →
    R.readout () () a / equalRimDefect a ≤ (2 / π) * quarterError ∧
      (equalRimOptRadius a / equalRimDefect a = (2 / π) * quarterError ↔ a = π / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (π / 3) ⟨by positivity, by linarith [Real.pi_pos]⟩).1
  change ((2 / π) * quarterError + 1) * equalRimDefect (π / 3) /
    equalRimDefect (π / 3) ≤ _ at he
  rw [mul_div_cancel_right₀ _ (show equalRimDefect (π / 3) ≠ 0 by
    simp [equalRimDefect, Real.pi_pos.ne'])] at he
  linarith

def family : Registration arena (type_of% (@equalRim_ratio_unique_maximum_at_quarter_turn)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@equalRim_ratio_unique_maximum_at_quarter_turn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@equalRim_ratio_unique_maximum_at_quarter_turn) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionEqualRimMinimax.equalRim_ratio_unique_maximum_at_quarter_turn.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionEqualRimMinimax.Ratio.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionEqualRimMinimax
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Ratio

end Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionEqualRimMinimax
