import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
import D5.S3.VertexAlgebra.Characters.LatticeFourCurrentThermal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeFourCurrentTrace
open LatticeFourCurrentThermal CanonicalOccupationSewing

open private probe probePositive cutoff_zero multiplicity_zero
  from Reg.D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace
open private original_four_zero_charge_trace bounded_coefficient_ordered ordered_positive_channels
  channelEnergyCoefficient channelMate channelRest currentMode contraction pairEnergyCoefficient
  from D5.S3.VertexAlgebra.Characters.LatticeFourCurrentTrace

namespace Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal

structure Params where
  D : LatticeData
  positive : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  i : Fin 4 → Fin D.rank
  z : Fin 4 → ℂ
  disk : ∀ j, ‖z j‖ < 1

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun _ => Fin 4 → ℕ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p n => (∏ j, p.z j ^ n j) * actualFourCurrentCycleTrace p.D p.positive p.i n)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  refine ⟨⟨probe, probePositive, fun _ => 0, fun _ => 1/2, by intro j; norm_num⟩,
    (fun _ => 0), ![0, 1, 0, 1], ?_⟩
  have hz : actualFourCurrentCycleTrace probe probePositive (fun _ => 0) (fun _ => 0) = 0 := by
    rw [original_four_zero_charge_trace]
    simp [cutoff_zero, bilinear]
  have h4 : actualFourCurrentCycleTrace probe probePositive (fun _ => 0) ![0, 1, 0, 1] = 4 := by
    rw [actual_four_current_grade_trace, bounded_coefficient_ordered,
      ordered_positive_channels probe probePositive (fun _ => 0) ![0, 1, 0, 1] (by decide)]
    norm_num [Fin.sum_univ_succ, channelEnergyCoefficient, channelMate, channelRest,
      currentMode, contraction, pairEnergyCoefficient, cutoff_zero, multiplicity_zero,
      bilinear, probe, Finset.filter_singleton,
      LatticePositiveEnergy.chargeEnergy_zero]
  change (∏ j : Fin 4, (1/2 : ℂ) ^ (0 : ℕ)) * _ ≠
    (∏ j : Fin 4, (1/2 : ℂ) ^ (![0,1,0,1] : Fin 4 → ℕ) j) * _
  rw [hz, h4]
  norm_num [Fin.prod_univ_succ]

namespace Absolute
abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin 4 → Fin D.rank) (z : Fin 4 → ℂ) (hz : ∀ j, ‖z j‖ < 1),
    Summable (fun n : Fin 4 → ℕ => ‖a.readout () ⟨D,hD,i,z,hz⟩ n‖)
private theorem bridge : (type_of% (@original_four_current_thermal_normSummable)) ↔
    arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h probe probePositive (fun _ => 0) (fun _ => 0) (by intro j; norm_num)
  change Summable (fun _ : Fin 4 → ℕ => ‖(1 : ℂ)‖) at hs
  simpa only [norm_one, summable_const_iff, one_ne_zero] using hs
def family : Registration arena (type_of% (@original_four_current_thermal_normSummable)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp original_four_current_thermal_normSummable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_four_current_thermal_normSummable) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Absolute.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Absolute.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeFourCurrentThermal
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","body","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Absolute

namespace Evaluation
abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin 4 → Fin D.rank) (z : Fin 4 → ℂ) (hz : ∀ j, ‖z j‖ < 1),
    HasSum (fun n : Fin 4 → ℕ => a.readout () ⟨D,hD,i,z,hz⟩ n) (thermalValue D i z)
private theorem bridge : (type_of% (@original_four_current_thermal_hasSum)) ↔
    arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := (h probe probePositive (fun _ => 0) (fun _ => 0)
    (by intro j; norm_num)).summable.norm
  change Summable (fun _ : Fin 4 → ℕ => ‖(1 : ℂ)‖) at hs
  simpa only [norm_one, summable_const_iff, one_ne_zero] using hs
def family : Registration arena (type_of% (@original_four_current_thermal_hasSum)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp original_four_current_thermal_hasSum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_four_current_thermal_hasSum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Evaluation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Evaluation.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeFourCurrentThermal
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","fn","fn","arg","body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Evaluation

namespace Oscillator
structure Params where
  D : LatticeData
  q : ℂ
  disk : ‖q‖ < 1
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun _ => ℕ) (fun _ => ℂ)
def actual : Realization signature := realize signature
  (fun _ p m => ((1-p.q^(m+1))⁻¹)^p.D.rank) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData) (q : ℂ) (hq : ‖q‖ < 1),
    HasProd (fun m : ℕ => a.readout () ⟨D,q,hq⟩ m)
      (∑' d : Occ D, q ^ oscillatorEnergy d)
private theorem bridge : (type_of% (@ordinary_oscillator_hasProd)) ↔
    arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h probe 0 (by norm_num)
  have ha := ordinary_oscillator_hasProd probe 0 (by norm_num)
  have hone : HasProd (fun _ : ℕ => (1 : ℂ)) 1 := by simpa using hasProd_one
  have hv : (∑' d : Occ probe, (0 : ℂ)^oscillatorEnergy d) = 1 := by
    apply HasProd.unique ha
    simpa [probe] using hone
  rw [hv] at hs
  change HasProd (fun _ : ℕ => (0 : ℂ)) 1 at hs
  have hzero : HasProd (fun _ : ℕ => (0 : ℂ)) 0 := by
    exact hasProd_zero_zero
  exact zero_ne_one (hzero.unique hs)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probe, 1/2, by norm_num⟩, 0, 1, ?_⟩
  change ((1-(1/2 : ℂ)^1)⁻¹)^probe.rank ≠ ((1-(1/2 : ℂ)^2)⁻¹)^probe.rank
  norm_num [probe]
def family : Registration arena (type_of% (@ordinary_oscillator_hasProd)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp ordinary_oscillator_hasProd, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_oscillator_hasProd) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Oscillator.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Oscillator.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeFourCurrentThermal
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","fn","fn","arg","body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Oscillator

namespace Origin
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature := realize signature
  (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (i : Fin 4 → Fin D.rank),
    a.readout () () (thermalValue D i (fun _ => 0)) 0
private theorem bridge : (type_of% (@thermal_value_all_zero)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h probe probePositive (fun _ => 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% (@thermal_value_all_zero)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp thermal_value_all_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thermal_value_all_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Origin.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal.Origin.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeFourCurrentThermal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Origin

end Reg.D5.S3.VertexAlgebra.LatticeFourCurrentThermal
