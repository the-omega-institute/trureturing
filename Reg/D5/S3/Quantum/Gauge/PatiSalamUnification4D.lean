import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Gauge.PatiSalamUnification4D
import Reg.Support.SingleDependentReadout

/-! Source registrations for the Pati–Salam generators and fermion weights. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.PatiSalamUnification4D
open _root_.OmegaMath.SpinorWeights5
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D

set_option autoImplicit false

noncomputable section

abbrev spinorWeightSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => PSState) (fun _ => ℝ)

def spinorWeightActual : Realization spinorWeightSignature :=
  realize spinorWeightSignature (fun _ _ x => psT3L x) (fun e => nomatch e)

def spinorWeightErased : Realization spinorWeightSignature :=
  realize spinorWeightSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev spinorWeightArena : Arena where
  signature := spinorWeightSignature
  Law R := ∀ x : PSState,
    let w := (ps16ToSpinor x).1
    R.readout () () x = t3L w ∧ psT3R x = t3R w ∧ psBMinusL x = bMinusL w ∧
      psHypercharge x = hypercharge w ∧ psElectricCharge x = electricCharge w

private theorem spinor_weight_erased_fails : ¬ spinorWeightArena.Law spinorWeightErased := by
  intro h
  let up : PSState := .inl (0, 0)
  have hzero : (0 : ℝ) = t3L (ps16ToSpinor up).1 := (h up).1
  rw [← (ps16_matches_so10_spinor16 up).1] at hzero
  change (0 : ℝ) = 1 / 2 at hzero
  norm_num at hzero

def spinorWeightFamily : Registration spinorWeightArena
    (type_of% (@ps16_matches_so10_spinor16)) where
  actual := spinorWeightActual
  bridge := Iff.rfl
  variation := ⟨ps16_matches_so10_spinor16, spinorWeightErased, spinor_weight_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    spinorWeightArena.Law spinorWeightActual spinorWeightErased spinor_weight_erased_fails
  dependence := by
    rintro ⟨⟩
    refine ⟨(), .inl (0, 0), .inl (0, 1), ?_⟩
    change (1 / 2 : ℝ) ≠ -1 / 2
    norm_num

def spinorWeightRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ps16_matches_so10_spinor16) (Realization spinorWeightSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.PatiSalamUnification4D.ps16_matches_so10_spinor16.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D.spinorWeightFamily
  realizationSource := none
  generated := false
  arena := .source ⟨spinorWeightArena⟩
  objectArena := .source ⟨spinorWeightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source spinorWeightArena ⟨spinorWeightFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spinorWeightSignature (fun _ _ x => psT3L x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.PatiSalamUnification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


open scoped Matrix
open Matrix
open _root_.D5.S3.Quantum.Gauge.SU5SO10GrandUnification4D (TraceFree)

local notation "matrixBracket" =>
  _root_.D5.S3.Quantum.Gauge.SU5SO10GrandUnification4D.commutator

abbrev colorBlockSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => M3) (fun _ => M4)

def colorBlockActual : Realization colorBlockSignature :=
  realize colorBlockSignature (fun _ _ A => colorBlock A) (fun e => nomatch e)

def colorBlockErased : Realization colorBlockSignature :=
  realize colorBlockSignature (fun _ _ _ => single 0 3 1) (fun e => nomatch e)

abbrev colorBlockArena : Arena where
  signature := colorBlockSignature
  Law R := ∀ A : M3, Commute (R.readout () () A) bMinusLGen ∧ Commute (colorBlock A) t15Gen

private theorem color_block_erased_fails : ¬ colorBlockArena.Law colorBlockErased := by
  intro h
  have hcomm : Commute (single 0 3 1 : M4) bMinusLGen := (h 0).1
  have hentry := congrArg (fun A : M4 => A 0 3) hcomm.eq
  norm_num [bMinusLGen, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry

def colorBlockFamily : Registration colorBlockArena
    (type_of% (@su4_sm_subalgebra_commute)) where
  actual := colorBlockActual
  bridge := Iff.rfl
  variation := ⟨su4_sm_subalgebra_commute, colorBlockErased, color_block_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    colorBlockArena.Law colorBlockActual colorBlockErased color_block_erased_fails
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hentry := congrArg (fun A : M4 => A 0 0) h
    change ((0 : M3) + ((0 : ℂ) / 3) • (1 : M3)) 0 0 =
      ((1 : M3) + ((0 : ℂ) / 3) • (1 : M3)) 0 0 at hentry
    norm_num at hentry

def colorBlockRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@su4_sm_subalgebra_commute) (Realization colorBlockSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.PatiSalamUnification4D.su4_sm_subalgebra_commute.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D.colorBlockFamily
  realizationSource := none
  generated := false
  arena := .source ⟨colorBlockArena⟩
  objectArena := .source ⟨colorBlockArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source colorBlockArena ⟨colorBlockFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize colorBlockSignature
    (fun _ _ A => colorBlock A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.PatiSalamUnification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev leptoquarkParams := Σ _ : M3, Σ _ : ℂ, ColorColumn

abbrev leptoquarkSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature leptoquarkParams
    (fun _ => ColorRow) (fun _ => M4)

def leptoquarkActual : Realization leptoquarkSignature :=
  realize leptoquarkSignature (fun _ p D => adjointBlocks p.1 p.2.1 p.2.2 D) (fun e => nomatch e)

def leptoquarkErased : Realization leptoquarkSignature :=
  realize leptoquarkSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev leptoquarkArena : Arena where
  signature := leptoquarkSignature
  Law R := ∀ (A : M3) (t : ℂ) (C : ColorColumn) (D : ColorRow),
    matrixBracket bMinusLGen (R.readout () ⟨A, t, C⟩ D) =
      adjointBlocks 0 0 ((4 / 3 : ℂ) • C) ((-4 / 3 : ℂ) • D)

private theorem leptoquark_erased_fails : ¬ leptoquarkArena.Law leptoquarkErased := by
  intro h
  have hentry := congrArg (fun A : M4 => A 3 0) (h 0 0 0 (single 0 0 1))
  change matrixBracket bMinusLGen (0 : M4) 3 0 =
      ((-4 / 3 : ℂ) • (single 0 0 1 : ColorRow)) 0 0 at hentry
  norm_num [_root_.D5.S3.Quantum.Gauge.SU5SO10GrandUnification4D.commutator,
    Matrix.smul_apply, smul_eq_mul] at hentry

def leptoquarkFamily : Registration leptoquarkArena
    (type_of% (@su4_adjoint_leptoquark_bMinusL)) where
  actual := leptoquarkActual
  bridge := Iff.rfl
  variation := ⟨su4_adjoint_leptoquark_bMinusL, leptoquarkErased, leptoquark_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    leptoquarkArena.Law leptoquarkActual leptoquarkErased leptoquark_erased_fails
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨0, 0, 0⟩, 0, single 0 0 1, ?_⟩
    intro h
    have hentry := congrArg (fun A : M4 => A 3 0) h
    change (0 : ℂ) = 1 at hentry
    exact zero_ne_one hentry

def leptoquarkRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@su4_adjoint_leptoquark_bMinusL) (Realization leptoquarkSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.PatiSalamUnification4D.su4_adjoint_leptoquark_bMinusL.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D.leptoquarkFamily
  realizationSource := none
  generated := false
  arena := .source ⟨leptoquarkArena⟩
  objectArena := .source ⟨leptoquarkArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source leptoquarkArena ⟨leptoquarkFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leptoquarkSignature
    (fun _ p D => adjointBlocks p.1 p.2.1 p.2.2 D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.PatiSalamUnification4D
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev adjointCoordinates := M3 × ℂ × ColorColumn × ColorRow

abbrev adjointCoordinateSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => adjointCoordinates)
    (fun _ => M4)

def adjointCoordinateActual : Realization adjointCoordinateSignature :=
  realize adjointCoordinateSignature
    (fun _ _ p => adjointBlocks p.1 p.2.1 p.2.2.1 p.2.2.2) (fun e => nomatch e)

def adjointCoordinateErased : Realization adjointCoordinateSignature :=
  realize adjointCoordinateSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev adjointCoordinateArena : Arena where
  signature := adjointCoordinateSignature
  Law R := ∀ (M : M4), M.trace = 0 →
    (∃! p : adjointCoordinates, p.1.trace = 0 ∧ R.readout () () p = M) ∧
    Module.finrank ℂ (TraceFree 4) = 15 ∧ Module.finrank ℂ (TraceFree 3) = 8 ∧
    Module.finrank ℂ ℂ = 1 ∧ Module.finrank ℂ ColorColumn = 3 ∧
    Module.finrank ℂ ColorRow = 3

private theorem adjoint_coordinate_erased_fails :
    ¬ adjointCoordinateArena.Law adjointCoordinateErased := by
  intro h
  let N : M4 := single 0 1 1
  have hn : N.trace = 0 := by
    norm_num [N, Matrix.trace, Fin.sum_univ_succ, Matrix.single_apply]
  obtain ⟨p, hp, _⟩ := (h N hn).1
  have he := congrArg (fun A : M4 => A 0 1) hp.2
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

def adjointCoordinateFamily : Registration adjointCoordinateArena
    (type_of% (@su4_adjoint_decomposition)) where
  actual := adjointCoordinateActual
  bridge := Iff.rfl
  variation :=
    ⟨su4_adjoint_decomposition, adjointCoordinateErased, adjoint_coordinate_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    adjointCoordinateArena.Law adjointCoordinateActual adjointCoordinateErased
    adjoint_coordinate_erased_fails
  dependence := by
    rintro ⟨⟩
    refine ⟨(), ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, single 0 0 1⟩, ?_⟩
    intro h
    have hentry := congrArg (fun A : M4 => A 3 0) h
    change (0 : ℂ) = 1 at hentry
    exact zero_ne_one hentry

def adjointCoordinateRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@su4_adjoint_decomposition) (Realization adjointCoordinateSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.PatiSalamUnification4D.su4_adjoint_decomposition.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D.adjointCoordinateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨adjointCoordinateArena⟩
  objectArena := .source ⟨adjointCoordinateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source adjointCoordinateArena ⟨adjointCoordinateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjointCoordinateSignature
    (fun _ _ p => adjointBlocks p.1 p.2.1 p.2.2.1 p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.PatiSalamUnification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


open _root_.OmegaMath.SU4SO6Cover (SU4)
open _root_.OmegaMath.SU2xSU2SO4Cover (SU2 su2NegOne)

abbrev vectorMatrix := Matrix (Fin 10) (Fin 10) ℝ
abbrev vectorParams := Σ _ : SU4, SU2

abbrev vectorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature vectorParams
    (fun _ => SU2) (fun _ => vectorMatrix)

def vectorActual : Realization vectorSignature :=
  realize vectorSignature (fun _ p R => patiSalamToSO10 p.1 p.2 R) (fun e => nomatch e)

def vectorErased : Realization vectorSignature :=
  realize vectorSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem vector_one : patiSalamToSO10 1 1 1 = 1 :=
  (patiSalamToSO10_kernel 1 1 1).2 ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩

private theorem vector_dependence : ObservationalDependence vectorSignature vectorActual := by
  rintro ⟨⟩
  refine ⟨⟨1, 1⟩, su2NegOne, 1, ?_⟩
  change patiSalamToSO10 1 1 su2NegOne ≠ patiSalamToSO10 1 1 1
  rw [vector_one]
  have hsign : su2NegOne ≠ (1 : SU2) := by
    intro h
    have he := congrArg (fun S : SU2 => (S : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
    change (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 at he
    norm_num at he
  intro h
  rcases ((patiSalamToSO10_kernel 1 1 su2NegOne).1 h).2 with h₁ | h₂
  · exact hsign h₁.2
  · exact hsign h₂.1.symm

abbrev vectorKernelArena : Arena where
  signature := vectorSignature
  Law Q := ∀ (U : SU4) (L R : SU2),
    Q.readout () ⟨U, L⟩ R = 1 ↔
      ((U : M4) = 1 ∨ (U : M4) = -1) ∧
        ((L = 1 ∧ R = 1) ∨ (L = su2NegOne ∧ R = su2NegOne))

private theorem vector_kernel_erased_fails : ¬ vectorKernelArena.Law vectorErased := by
  intro h
  exact zero_ne_one ((h 1 1 1).2 ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩)

def vectorKernelFamily : Registration vectorKernelArena (type_of% (@patiSalamToSO10_kernel)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨patiSalamToSO10_kernel, vectorErased, vector_kernel_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    vectorKernelArena.Law vectorActual vectorErased vector_kernel_erased_fails
  dependence := vector_dependence

def vectorKernelRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@patiSalamToSO10_kernel) (Realization vectorSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.PatiSalamUnification4D.patiSalamToSO10_kernel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D.vectorKernelFamily
  realizationSource := none
  generated := false
  arena := .source ⟨vectorKernelArena⟩
  objectArena := .source ⟨vectorKernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source vectorKernelArena ⟨vectorKernelFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vectorSignature
    (fun _ p R => patiSalamToSO10 p.1 p.2 R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.PatiSalamUnification4D
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev vectorOrientationArena : Arena where
  signature := vectorSignature
  Law Q := ∀ (U : SU4) (L R : SU2),
    (patiSalamToSO10 U L R)ᵀ * patiSalamToSO10 U L R = 1 ∧
      (Q.readout () ⟨U, L⟩ R).det = 1

private theorem vector_orientation_erased_fails : ¬ vectorOrientationArena.Law vectorErased := by
  intro h
  have he : (0 : vectorMatrix).det = 1 := (h 1 1 1).2
  simp at he

def vectorOrientationFamily : Registration vectorOrientationArena
    (type_of% (@patiSalamToSO10_special_orthogonal)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨patiSalamToSO10_special_orthogonal, vectorErased, vector_orientation_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    vectorOrientationArena.Law vectorActual vectorErased vector_orientation_erased_fails
  dependence := vector_dependence

def vectorOrientationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@patiSalamToSO10_special_orthogonal) (Realization vectorSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.PatiSalamUnification4D.patiSalamToSO10_special_orthogonal.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D.vectorOrientationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨vectorOrientationArena⟩
  objectArena := .source ⟨vectorOrientationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source vectorOrientationArena ⟨vectorOrientationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vectorSignature
    (fun _ p R => patiSalamToSO10 p.1 p.2 R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.PatiSalamUnification4D
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev vectorMultiplicationArena : Arena where
  signature := vectorSignature
  Law Q := ∀ (U V : SU4) (L R L' R' : SU2),
    patiSalamToSO10 (U * V) (L * L') (R * R') =
      Q.readout () ⟨U, L⟩ R * patiSalamToSO10 V L' R'

private theorem vector_multiplication_erased_fails :
    ¬ vectorMultiplicationArena.Law vectorErased := by
  intro h
  have he : patiSalamToSO10 ((1 : SU4) * 1) ((1 : SU2) * 1) ((1 : SU2) * 1) =
      (0 : vectorMatrix) * patiSalamToSO10 1 1 1 := h 1 1 1 1 1 1
  simp [vector_one] at he

def vectorMultiplicationFamily : Registration vectorMultiplicationArena
    (type_of% (@patiSalamToSO10_hom)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨patiSalamToSO10_hom, vectorErased, vector_multiplication_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    vectorMultiplicationArena.Law vectorActual vectorErased vector_multiplication_erased_fails
  dependence := vector_dependence

def vectorMultiplicationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@patiSalamToSO10_hom) (Realization vectorSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.PatiSalamUnification4D.patiSalamToSO10_hom.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D.vectorMultiplicationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨vectorMultiplicationArena⟩
  objectArena := .source ⟨vectorMultiplicationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source vectorMultiplicationArena ⟨vectorMultiplicationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vectorSignature
    (fun _ p R => patiSalamToSO10 p.1 p.2 R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.PatiSalamUnification4D
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Gauge.PatiSalamUnification4D
