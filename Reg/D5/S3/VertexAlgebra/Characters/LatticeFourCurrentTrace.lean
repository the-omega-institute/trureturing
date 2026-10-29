import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFourCurrentTrace
open LatticePositiveEnergy LatticeThetaCharacter

open private original_four_zero_charge_trace bounded_coefficient_ordered ordered_positive_channels
  channelEnergyCoefficient channelMate channelRest currentMode contraction pairEnergyCoefficient
  from D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace

namespace Reg.D5.S3.VertexAlgebra.LatticeFourCurrentTrace

structure Params where
  D : LatticeData
  positive : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  i : Four → Fin D.rank

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun _ => Four → ℕ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p n => actualFourCurrentCycleTrace p.D p.positive p.i n)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ),
    a.readout () ⟨D, hD, i⟩ n = boundedFourCurrentCoefficient D hD i n


private theorem bridge : (type_of% (@actual_four_current_grade_trace)) ↔ arena.Law actual := Iff.rfl

def rejected : Realization signature := realize signature
  (fun _ p n => actualFourCurrentCycleTrace p.D p.positive p.i n + 1)
  (fun e => nomatch e)

private abbrev probe : LatticeData where
  rank := 1
  G := Matrix.diagonal (fun _ => 2)
  symmetric := by intro i j; fin_cases i; fin_cases j; rfl
  even_diagonal := by intro i; simp

private theorem probePositive : Matrix.PosDef (probe.G.map (Int.cast : ℤ → ℝ)) := by
  have he : probe.G.map (Int.cast : ℤ → ℝ) = Matrix.diagonal (fun _ => (2 : ℝ)) := by
    ext i j; fin_cases i; fin_cases j; norm_num [probe]
  rw [he, Matrix.posDef_diagonal_iff]
  intro i
  norm_num

private theorem cutoff_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    positiveChargeCutoff D hD 0 = {0} := by
  classical
  ext β
  simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    Int.toNat_zero, Nat.cast_zero, Finset.mem_singleton]
  constructor
  · intro h
    exact (chargeEnergy_eq_zero_iff D hD β).mp (le_antisymm h (chargeEnergy_nonneg D hD β))
  · rintro rfl
    simp

private theorem multiplicity_zero (D : LatticeData) : Nat.card (IntegerFiber D 0) = 1 := by
  letI : Unique (IntegerFiber D 0) := {
    default := ⟨0, by simp [oscillatorEnergy]⟩
    uniq := fun a => Subtype.ext ((oscillatorEnergy_eq_zero_iff D a.1).mp a.2) }
  exact Nat.card_unique

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h probe probePositive (fun _ => 0) (fun _ => 0)
  have ha := actual_four_current_grade_trace probe probePositive (fun _ => 0) (fun _ => 0)
  change actualFourCurrentCycleTrace probe probePositive (fun _ => 0) (fun _ => 0) + 1 = _ at hb
  rw [ha] at hb
  exact one_ne_zero (add_left_cancel (hb.trans (add_zero _).symm))

private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  refine ⟨⟨probe, probePositive, fun _ => 0⟩, (fun _ => 0), ![0, 1, 0, 1], ?_⟩
  change actualFourCurrentCycleTrace probe probePositive (fun _ => 0) (fun _ => 0) ≠
    actualFourCurrentCycleTrace probe probePositive (fun _ => 0) ![0, 1, 0, 1]
  have hz : actualFourCurrentCycleTrace probe probePositive (fun _ => 0) (fun _ => 0) = 0 := by
    rw [original_four_zero_charge_trace]
    simp [cutoff_zero, bilinear]
  have h4 : actualFourCurrentCycleTrace probe probePositive (fun _ => 0) ![0, 1, 0, 1] = 4 := by
    rw [actual_four_current_grade_trace, bounded_coefficient_ordered,
      ordered_positive_channels probe probePositive (fun _ => 0) ![0, 1, 0, 1] (by decide)]
    norm_num [Fin.sum_univ_succ, channelEnergyCoefficient, channelMate, channelRest,
      currentMode, contraction, pairEnergyCoefficient, cutoff_zero, multiplicity_zero,
      bilinear, probe]
  rw [hz, h4]
  norm_num

def family : Registration arena (type_of% (@actual_four_current_grade_trace)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_four_current_grade_trace, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_four_current_grade_trace) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentTrace.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentTrace.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_four_current_grade_trace
#print axioms family

end Reg.D5.S3.VertexAlgebra.LatticeFourCurrentTrace
