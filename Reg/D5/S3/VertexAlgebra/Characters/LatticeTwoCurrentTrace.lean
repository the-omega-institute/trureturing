import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace

/-! The actual finite current cycle is observed over the complete source parameter family. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeThetaCharacter LatticeTwoCurrentTrace

namespace Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentTrace

structure Params where
  D : LatticeData
  positive : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  i : Fin D.rank
  j : Fin D.rank
  n : ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p m => actualCurrentCycleTrace p.D p.positive p.i p.j p.n m)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ p m => actualCurrentCycleTrace p.D p.positive p.i p.j p.n m + 1)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (n m : ℕ),
    a.readout () ⟨D, hD, i, j, n⟩ m =
      if n = m then
        ∑ β ∈ positiveChargeCutoff D hD (n : ℤ),
          (bilinear D (unitCharge D i) β : ℂ) *
            (bilinear D (unitCharge D j) β : ℂ) *
              occupationMultiplicity D (n - (chargeEnergy D β).toNat)
      else
        (Nat.dist n m : ℂ) * (D.G i j : ℂ) *
          ∑ β ∈ positiveChargeCutoff D hD ((min n m : ℕ) : ℤ),
            ∑ k ∈ Finset.range ((min n m - (chargeEnergy D β).toNat) / Nat.dist n m + 1),
              occupationMultiplicity D (min n m - (chargeEnergy D β).toNat - k * Nat.dist n m)

private theorem bridge : (type_of% (@actual_two_current_grade_trace)) ↔ arena.Law actual := Iff.rfl

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

private theorem multiplicity_zero (D : LatticeData) : occupationMultiplicity D 0 = 1 := by
  letI : Unique (IntegerFiber D 0) := {
    default := ⟨0, by simp [oscillatorEnergy]⟩
    uniq := fun a => Subtype.ext ((oscillatorEnergy_eq_zero_iff D a.1).mp a.2) }
  simp [occupationMultiplicity, Nat.card_unique]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h probe probePositive 0 0 0 0
  have ha := actual_two_current_grade_trace probe probePositive 0 0 0 0
  change actualCurrentCycleTrace probe probePositive 0 0 0 0 + 1 = _ at hb
  rw [ha] at hb
  exact one_ne_zero (add_left_cancel (hb.trans (add_zero _).symm))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨probe, probePositive, 0, 0, 0⟩, 0, 1, ?_⟩
  change actualCurrentCycleTrace probe probePositive 0 0 0 0 ≠
    actualCurrentCycleTrace probe probePositive 0 0 0 1
  rw [actual_two_current_grade_trace, actual_two_current_grade_trace]
  norm_num [cutoff_zero, multiplicity_zero, bilinear, probe, chargeEnergy, Nat.dist,
    LatticePositiveEnergy.chargeEnergy_zero]

def family : Registration arena (type_of% (@actual_two_current_grade_trace)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_two_current_grade_trace, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_two_current_grade_trace) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentTrace.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentTrace.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.VertexAlgebra.LatticeTwoCurrentTrace
