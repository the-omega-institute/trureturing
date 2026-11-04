import D5.S3.Quantum.Matrix.HsfQubitMixedCubic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit attempts for the original mixed coefficient supplier. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic
open _root_.D5.S3.Quantum.Matrix.HsfQubitCoupledCubic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic
noncomputable section

private theorem zero_hermitian : hermitian 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian]

private theorem one_hermitian : hermitian 1 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitian]

namespace Positive

abbrev signature : Signature where
  Params := Unit
  State _ := Mat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b u v : ℝ) (w z : ℂ), 0 < a → 0 < b →
    R.readout () () (mixedMatrix a b u v w z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 0 0 0 0 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, -1, ?_⟩
  intro h
  have hf : (-1 : Mat).PosSemidef := Eq.mp h Matrix.PosSemidef.zero
  have hn := (Complex.nonneg_iff.mp (hf.diag_nonneg (i := 0))).1
  norm_num at hn

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.mixedMatrix_posSemidef)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.mixedMatrix_posSemidef, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.mixedMatrix_posSemidef) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Positive.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (Mat)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positive

namespace CoordinateEnergy

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b u v r s : ℝ) (w z : ℂ), a+b ≠ 0 →
    R.readout () ()
      (coefficient2 (hermitian a b 0)
        (hermitian u v w + weightedImage a b
          (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z))
      (3*(Matrix.trace (hermitian a b 0*(hermitian u v w)^2)).re +
        ((a-b)^2*(a^2+3*a*b+b^2)/(3*(a+b)))*‖z‖^2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 0 0 0 0 0 0 (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hf

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coordinate_energy_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coordinate_energy_identity, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coordinate_energy_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.CoordinateEnergy.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.CoordinateEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoordinateEnergy

namespace CoordinateBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b u v r s : ℝ) (w z : ℂ), 0 < a → 0 < b →
    (1+hermitian r s z).PosSemidef → (1-hermitian r s z).PosSemidef →
    R.readout () ()
      (|3*(Matrix.trace ((hermitian u v w)^3)).re -
        3*coefficient3 (hermitian a b 0)
          (hermitian u v w + weightedImage a b
            (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z)|)
      (3*coefficient2 (hermitian a b 0)
        (hermitian u v w + weightedImage a b
          (2*(a^2+a*b+b^2)/(3*(a+b))) (hermitian r s z)) (hermitian r s z))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h 1 1 0 0 0 0 0 0 (by norm_num) (by norm_num)
  · simpa only [zero_hermitian, add_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)
  · simpa only [zero_hermitian, sub_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at hf

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coordinate_mixed_cubic_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coordinate_mixed_cubic_bound, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coordinate_mixed_cubic_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.CoordinateBound.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.CoordinateBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoordinateBound

namespace MixedBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℝ) (H K : Mat), 0 < a → 0 < b → H.IsHermitian → K.IsHermitian →
    (1+K).PosSemidef → (1-K).PosSemidef →
    R.readout () ()
      (|3*(Matrix.trace ((H-weightedImage a b
          (2*(a^2+a*b+b^2)/(3*(a+b))) K)^3)).re -
        3*coefficient3 (hermitian a b 0) H K|)
      (3*coefficient2 (hermitian a b 0) H K)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h 1 1 0 0 (by norm_num) (by norm_num) Matrix.isHermitian_zero Matrix.isHermitian_zero
  · simpa only [add_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)
  · simpa only [sub_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at hf

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.mixed_cubic_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.mixed_cubic_bound, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.mixed_cubic_bound) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.MixedBound.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.MixedBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MixedBound

namespace Energy

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℝ) (H K : Mat), a+b ≠ 0 → H.IsHermitian → K.IsHermitian →
    R.readout () () (coefficient2 (hermitian a b 0) H K)
      (3*(Matrix.trace (hermitian a b 0*(H-weightedImage a b
          (2*(a^2+a*b+b^2)/(3*(a+b))) K)^2)).re +
        ((a-b)^2*(a^2+3*a*b+b^2)/(3*(a+b)))*‖K 0 1‖^2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 0 0 (by norm_num) Matrix.isHermitian_zero Matrix.isHermitian_zero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hf

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.energy_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.energy_identity, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.energy_identity) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Energy.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Energy

namespace Compatibility

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => 0 ≤ p.1 ∧ 3*|p.2| ≤ 5*p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℝ) (H K : Mat), 0 < a → 0 < b → H.IsHermitian → K.IsHermitian →
    (hermitian a b 0+H).PosSemidef → (hermitian a b 0-H).PosSemidef →
    (1+K).PosSemidef → (1-K).PosSemidef →
    R.readout () () (coefficient2 (hermitian a b 0) H K,
      coefficient3 (hermitian a b 0) H K)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h 1 1 0 0 (by norm_num) (by norm_num) Matrix.isHermitian_zero Matrix.isHermitian_zero
  · simpa only [one_hermitian, add_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)
  · simpa only [one_hermitian, sub_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)
  · simpa only [add_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)
  · simpa only [sub_zero] using (Matrix.PosSemidef.one : (1 : Mat).PosSemidef)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (0, 1), ?_⟩
  intro h
  have ht : actual.readout () () (0, 0) := by norm_num [actual, realize]
  have hf : actual.readout () () (0, 1) := Eq.mp h ht
  norm_num [actual, realize] at hf

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coefficient_compatibility)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coefficient_compatibility, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.coefficient_compatibility) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Compatibility.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Compatibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => 0 ≤ p.1 ∧ 3*|p.2| ≤ 5*p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ × ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Compatibility


universe u

namespace Jet2

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (X H K : Matrix n n ℂ),
    let L := H-(2/3 : ℝ) • (X*K)
    let M := -(4/3 : ℝ) • (H*K)+(10/9 : ℝ) • (X*K^2)
    R.readout () () (Matrix.trace ((3 : ℝ) • (M*X*X)+(6 : ℝ) • (L*L*X))) (2*traceCoefficient2 X H K)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hf

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.trace_jet_coefficient2.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.trace_jet_coefficient2.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.trace_jet_coefficient2.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Jet2.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Jet2.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Jet2

namespace Jet3

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (X H K : Matrix n n ℂ),
    let L := H-(2/3 : ℝ) • (X*K)
    let M := -(4/3 : ℝ) • (H*K)+(10/9 : ℝ) • (X*K^2)
    let N := (10/3 : ℝ) • (H*K^2)-(80/27 : ℝ) • (X*K^3)
    R.readout () () (Matrix.trace ((3 : ℝ) • (N*X*X)+(9 : ℝ) • (M*L*X)+
        (9 : ℝ) • (M*X*L)+(6 : ℝ) • (L*L*L))) (6*traceCoefficient3 X H K)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (n := ULift.{u} Unit) 0 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  norm_num at hf

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.trace_jet_coefficient3.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.trace_jet_coefficient3.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.trace_jet_coefficient3.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Jet3.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic.Jet3.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfQubitMixedCubic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Jet3


end
end Reg.D5.S3.Quantum.Matrix.HsfQubitMixedCubic

