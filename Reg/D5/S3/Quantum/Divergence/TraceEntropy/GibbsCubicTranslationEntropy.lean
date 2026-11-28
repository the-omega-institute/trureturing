import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy

/-! The cubic entropy derivatives and correction as source-bound observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
open _root_.D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy (overlap)
open _root_.D5.S3.Quantum.Recovery.BKMRelativeDensity (omega)

namespace Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy

private abbrev readoutSignature (State Output : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => State) (fun _ => Output)

private abbrev ScalarMatrix := Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ

private theorem scalarOne_posDef : (1 : ScalarMatrix.{u}).PosDef := Matrix.PosDef.one

private abbrev equalitySignature := readoutSignature ℝ (ℝ → Prop)

private def rejectedEquality : Realization equalitySignature :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equalityDependence :
    ObservationalDependence equalitySignature
      (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact one_ne_zero (Eq.mp (congrFun h 0) rfl : (1 : ℝ) = 0)

private abbrev nonnegativeSignature := readoutSignature ℝ Prop

private def rejectedNonnegative : Realization nonnegativeSignature :=
  realize nonnegativeSignature (fun _ _ _ => False) (fun e => nomatch e)

private theorem nonnegativeDependence :
    ObservationalDependence nonnegativeSignature
      (realize nonnegativeSignature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, -1, ?_⟩
  intro h
  have hn : (0 : ℝ) ≤ -1 := Eq.mp h le_rfl
  norm_num at hn

private abbrev derivativeSignature := readoutSignature (ℝ → ℝ) (ℝ → ℝ → Prop)

private def rejectedDerivative : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ _ _ _ => False) (fun e => nomatch e)

private theorem derivativeDependence :
    ObservationalDependence derivativeSignature
      (realize derivativeSignature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), (fun _ : ℝ => 0), id, ?_⟩
  intro h
  have hzero : HasDerivAt (id : ℝ → ℝ) 0 0 :=
    Eq.mp (congrFun (congrFun h 0) 0) (hasDerivAt_const 0 (0 : ℝ))
  exact one_ne_zero ((hasDerivAt_id 0).unique hzero)

private abbrev rightDerivativeSignature :=
  readoutSignature (ℝ → ℝ) (ℝ → Set ℝ → ℝ → Prop)

private def rejectedRightDerivative : Realization rightDerivativeSignature :=
  realize rightDerivativeSignature (fun _ _ _ _ _ _ => False) (fun e => nomatch e)

private theorem rightDerivativeDependence :
    ObservationalDependence rightDerivativeSignature
      (realize rightDerivativeSignature
        (fun _ _ f => HasDerivWithinAt f) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), (fun _ : ℝ => 0), id, ?_⟩
  intro h
  have hzero : HasDerivWithinAt (id : ℝ → ℝ) 0 Set.univ 0 :=
    Eq.mp (congrFun (congrFun (congrFun h 0) Set.univ) 0)
      (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt
  exact one_ne_zero ((hasDerivAt_id 0).unique (hasDerivWithinAt_univ.mp hzero))

namespace TraceDerivative

private abbrev signature := derivativeSignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.PosDef),
    R.readout () () (fun s : ℝ => cubicEntropy B (M + s • B))
      (9 * (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re -
        3 * (B * M ^ 2).trace.re * Real.log (M ^ 3).trace.re +
        3 * correction B M) 0

private theorem rejected_law : ¬ arena.{u}.Law rejectedDerivative := by
  intro h
  exact h (n := ULift.{u} Unit) 1 1 scalarOne_posDef scalarOne_posDef

def family : Registration arena.{u} (type_of% @hasDerivAt_cubicEntropy.{u}) where
  actual := realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_cubicEntropy.{u}, rejectedDerivative, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedDerivative rejected_law
  dependence := derivativeDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hasDerivAt_cubicEntropy.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.TraceDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TraceDerivative

namespace RightTraceDerivative

private abbrev signature := rightDerivativeSignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.PosSemidef),
    R.readout () () (fun s : ℝ => cubicEntropy B (M + s • B))
      (9 * (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re -
        3 * (B * M ^ 2).trace.re * Real.log (M ^ 3).trace.re +
        3 * correction B M) (Set.Ici 0) 0

private theorem rejected_law : ¬ arena.{u}.Law rejectedRightDerivative := by
  intro h
  exact h (n := ULift.{u} Unit) 1 0 scalarOne_posDef Matrix.PosSemidef.zero

def family : Registration arena.{u} (type_of% @hasDerivWithinAt_cubicEntropy.{u}) where
  actual := realize signature (fun _ _ f => HasDerivWithinAt f) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@hasDerivWithinAt_cubicEntropy.{u}, rejectedRightDerivative, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedRightDerivative rejected_law
  dependence := rightDerivativeDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hasDerivWithinAt_cubicEntropy.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.RightTraceDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => HasDerivWithinAt f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RightTraceDerivative

namespace SpectralCorrection

private abbrev signature := equalitySignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.IsHermitian) (hM : M.IsHermitian),
    let b := hB.eigenvalues
    let Q := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary).symm
    let U := Q M
    R.readout () () (correction B M) ((1 / 2 : ℝ) *
      ∑ i, ∑ j, (b i - b j) * (Real.log (b i) - Real.log (b j)) *
        Complex.normSq (U i j))

private theorem rejected_law : ¬ arena.{u}.Law rejectedEquality := by
  intro h
  exact h (n := ULift.{u} Unit) 1 1 Matrix.isHermitian_one Matrix.isHermitian_one

def family : Registration arena.{u} (type_of% @correction_spectral.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@correction_spectral.{u}, rejectedEquality, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedEquality rejected_law
  dependence := equalityDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@correction_spectral.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.correction_spectral.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.SpectralCorrection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralCorrection

namespace BKMCorrection

private abbrev signature := equalitySignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.IsHermitian),
    let C := cfc Real.log B * M - M * cfc Real.log B
    R.readout () () (correction B M) ((1 / 2 : ℝ) * (Cᴴ * omega B C).trace.re)

private theorem rejected_law : ¬ arena.{u}.Law rejectedEquality := by
  intro h
  exact h (n := ULift.{u} Unit) 1 1 scalarOne_posDef Matrix.isHermitian_one

def family : Registration arena.{u} (type_of% @correction_eq_bkm.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@correction_eq_bkm.{u}, rejectedEquality, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedEquality rejected_law
  dependence := equalityDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@correction_eq_bkm.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.correction_eq_bkm.audit
  realizationName := `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.BKMCorrection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BKMCorrection

namespace CorrectionNonnegative

private abbrev signature := nonnegativeSignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.IsHermitian),
    R.readout () () (correction B M)

private theorem rejected_law : ¬ arena.{u}.Law rejectedNonnegative := by
  intro h
  exact h (n := ULift.{u} Unit) 1 1 scalarOne_posDef Matrix.isHermitian_one

def family : Registration arena.{u} (type_of% @correction_nonneg.{u}) where
  actual := realize signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@correction_nonneg.{u}, rejectedNonnegative, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedNonnegative rejected_law
  dependence := nonnegativeDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@correction_nonneg.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.correction_nonneg.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.CorrectionNonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CorrectionNonnegative

namespace CorrectionCommutation

private abbrev signature := equalitySignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.IsHermitian),
    R.readout () () (correction B M) 0 ↔ Commute B M

private theorem rejected_law : ¬ arena.{u}.Law rejectedEquality := by
  intro h
  exact (h (n := ULift.{u} Unit) 1 1 scalarOne_posDef Matrix.isHermitian_one).mpr (Commute.refl _)

def family : Registration arena.{u} (type_of% @correction_eq_zero_iff_commute.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@correction_eq_zero_iff_commute.{u}, rejectedEquality, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedEquality rejected_law
  dependence := equalityDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@correction_eq_zero_iff_commute.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.correction_eq_zero_iff_commute.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.CorrectionCommutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CorrectionCommutation

namespace RightSpectralDerivative

private abbrev signature := rightDerivativeSignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.PosSemidef),
    let pi := spectralWeight hB.isHermitian hM.isHermitian
    let x := spectralRatio hB.isHermitian hM.isHermitian
    R.readout () () (fun s : ℝ => cubicEntropy B (M + s • B))
      (9 * (∑ p, pi p * x p ^ 2 * Real.log (x p)) -
        3 * (∑ p, pi p * x p ^ 2) * Real.log (∑ p, pi p * x p ^ 3) +
        3 * correction B M) (Set.Ici 0) 0

private theorem rejected_law : ¬ arena.{u}.Law rejectedRightDerivative := by
  intro h
  exact h (n := ULift.{u} Unit) 1 0 scalarOne_posDef Matrix.PosSemidef.zero

def family :
    Registration arena.{u} (type_of% @hasDerivWithinAt_cubicEntropy_spectral_pair.{u}) where
  actual := realize signature (fun _ _ f => HasDerivWithinAt f) (fun e => nomatch e)
  bridge := Iff.rfl
  variation :=
    ⟨@hasDerivWithinAt_cubicEntropy_spectral_pair.{u}, rejectedRightDerivative, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedRightDerivative rejected_law
  dependence := rightDerivativeDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hasDerivWithinAt_cubicEntropy_spectral_pair.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy_spectral_pair.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.RightSpectralDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => HasDerivWithinAt f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RightSpectralDerivative

namespace SpectralComparison

private abbrev signature := nonnegativeSignature

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.PosDef)
    (hNorm : (B ^ 3).trace.re = 1),
    let pi := spectralWeight hB.isHermitian hM.isHermitian
    let x := spectralRatio hB.isHermitian hM.isHermitian
    let S := (B * M ^ 2).trace.re
    let T := (M ^ 3).trace.re
    let nu := fun p => pi p * x p ^ 2 / S
    let H := (∑ p, pi p * x p ^ 2 * Real.log (x p ^ 2)) - S * Real.log S
    let D := Real.log (∑ p, nu p * x p) - ∑ p, nu p * Real.log (x p)
    (∀ p, 0 ≤ pi p ∧ 0 < x p ∧ 0 ≤ nu p) ∧
      (∀ p, pi p = 0 ↔ overlap hB.isHermitian hM.isHermitian p.1 p.2 = 0) ∧
      (∑ p, pi p) = 1 ∧ (∑ p, nu p) = 1 ∧ 0 < S ∧ 0 < T ∧
      (∑ p, pi p * x p ^ 3 / T) = 1 ∧
      (∑ p, nu p * x p) = T / S ∧
      (∑ p, nu p * Real.log (x p)) =
        (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re / S ∧
      HasDerivAt (fun s : ℝ => cubicEntropy B (M + s • B))
        (3 * (H + correction B M - S * D)) 0 ∧
      R.readout () () D ∧
      (0 < D ↔ ∃ p q : n × n, pi p ≠ 0 ∧ pi q ≠ 0 ∧ x p ≠ x q)

private theorem rejected_law : ¬ arena.{u}.Law rejectedNonnegative := by
  intro h
  have hNorm : ((1 : ScalarMatrix.{u}) ^ 3).trace.re = 1 := by
    simp [Matrix.trace_one, Fintype.card_ulift, Fintype.card_unit]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hfalse, _⟩ :=
    h (n := ULift.{u} Unit) 1 1 scalarOne_posDef scalarOne_posDef hNorm
  exact hfalse

def family : Registration arena.{u} (type_of% @hasDerivAt_cubicEntropy_spectral_pair.{u}) where
  actual := realize signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_cubicEntropy_spectral_pair.{u}, rejectedNonnegative, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _ rejectedNonnegative rejected_law
  dependence := nonnegativeDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hasDerivAt_cubicEntropy_spectral_pair.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy_spectral_pair.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy.SpectralComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralComparison

end Reg.D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
