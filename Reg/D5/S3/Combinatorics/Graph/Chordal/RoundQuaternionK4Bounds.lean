import D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the reconstruction radius and relative edge potential. -/

open scoped Quaternion Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds

open _root_.RoundQuaternionK4Bounds

local notation "U" => unitary ℍ[ℝ]

namespace Upper

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => 4 * ε / 5) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (g : Fin 4 → Fin 4 → U) (ε : ℝ), 0 ≤ ε → ε ≤ π → DefectLE g ε →
    ∃ φ : Fin 4 → U, Fits g φ (R.readout () () ε)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let g : Fin 4 → Fin 4 → U := fun _ _ => 1
  have hg : DefectLE g 0 := by
    refine ⟨by simp [g], by simp [g], ?_⟩
    intro i j k _ _ _
    simp [g, roundDist]
  obtain ⟨φ, hφ⟩ := h g 0 le_rfl Real.pi_pos.le hg
  have herr := hφ 0 1 (by decide)
  change roundDist _ _ ≤ -1 at herr
  exact (not_le_of_gt (show (-1 : ℝ) < roundDist (g 0 1) ((φ 0)⁻¹ * φ 1) from
    lt_of_lt_of_le (by norm_num) (Real.arccos_nonneg _))) herr

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]


def family : Registration arena (type_of% (@reconstruction_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reconstruction_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reconstruction_bound) (Realization signature) Unit Unit where
  unitName := `_root_.RoundQuaternionK4Bounds.reconstruction_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds.Upper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ε => 4*ε/5) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Upper

namespace Lower

abbrev Params := (Fin 4 → U) × Fin 4
abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Params
  (fun _ => Fin 4) (fun _ => U)

def actual : Realization signature :=
  realize signature (fun _ p j => (p.1 p.2)⁻¹ * p.1 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p j => quarterGains p.2 j) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    DefectLE quarterGains (π/2) ∧
    (∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      roundDist (quarterGains i j * quarterGains j k) (quarterGains i k) = π/2) ∧
    (∀ φ : Fin 4 → U, ∃ i j : Fin 4, i ≠ j ∧
      quarterError ≤ roundDist (quarterGains i j) (R.readout () (φ, i) j)) ∧
    (∃ φ : Fin 4 → U, ∀ i j : Fin 4, i ≠ j →
      roundDist (quarterGains i j) ((φ i)⁻¹ * φ j) = quarterError) ∧
    3/5 < 2*quarterError/π

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨i, j, _, hij⟩ := h.2.2.1 (fun _ => 1)
  have hzero (q : U) : roundDist q q = 0 := by simp [roundDist]
  change quarterError ≤ roundDist (quarterGains i j) (quarterGains i j) at hij
  rw [hzero] at hij
  have hr := (lt_div_iff₀ Real.pi_pos).mp h.2.2.2.2
  linarith [Real.pi_pos]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let φ : Fin 4 → U := ![1, -1, 1, 1]
  refine ⟨(φ, 0), 0, 1, ?_⟩
  have h : (1 : U) ≠ -1 := by
    intro h
    have hh := congrArg (fun q : U => (q : ℍ[ℝ]).re) h
    norm_num at hh
  simpa [actual, realize, φ] using h


def family : Registration arena (type_of% (@quarter_turn_sharp)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quarter_turn_sharp, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quarter_turn_sharp) (Realization signature) Unit Unit where
  unitName := `_root_.RoundQuaternionK4Bounds.quarter_turn_sharp.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds.Lower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p j => (p.1 p.2)⁻¹ * p.1 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Lower

end Reg.D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Bounds

