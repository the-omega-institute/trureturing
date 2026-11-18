import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianExternalSignedCandidate OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalGenerators
open OriginalGaussianExternalAnalyticCandidate (b ell correction)
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
namespace h_ne_zero
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1),
    R.readout () () (h e u r) (0)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false (u := 0) (r := 0) (by norm_num)
def family : Registration arena (type_of% (@h_ne_zero)) where
  actual := complexNotEqual
  bridge := Iff.rfl
  variation := ⟨@h_ne_zero, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexNotEqual complexFalse rejected_fails
  dependence := complexNotEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@h_ne_zero) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.h_ne_zero.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.h_ne_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end h_ne_zero

namespace source_frequency
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e : Bool) {u r : ℂ}
    (hb : b u ≠ 0) (hh : h e u r ≠ 0),
    R.readout () () (u * b u * mLog e u r + beta e u) (modeA e u r)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false (u := 0) (r := 0) (by norm_num [b]) (by norm_num [h])
def family : Registration arena (type_of% (@source_frequency)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@source_frequency, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_frequency) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.source_frequency.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.source_frequency.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end source_frequency

namespace W_square
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1),
    R.readout () () (W e u r ^ 2) (h e u r / b u)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false (u := 0) (r := 0) (by norm_num)
def family : Registration arena (type_of% (@W_square)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@W_square, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@W_square) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.W_square.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.W_square.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end W_square

namespace source_W_normalization
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1),
    R.readout () () (sourceMode e u r * b u * W e u r) (1)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false (u := 0) (r := 0) (by norm_num)
def family : Registration arena (type_of% (@source_W_normalization)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@source_W_normalization, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_W_normalization) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.source_W_normalization.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.source_W_normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end source_W_normalization

namespace W_sum_ne_zero
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1),
    R.readout () () (W e u r + W f v r) (0)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (r := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@W_sum_ne_zero)) where
  actual := complexNotEqual
  bridge := Iff.rfl
  variation := ⟨@W_sum_ne_zero, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexNotEqual complexFalse rejected_fails
  dependence := complexNotEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@W_sum_ne_zero) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.W_sum_ne_zero.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.W_sum_ne_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end W_sum_ne_zero

namespace ell_eq_source
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {r : ℂ} (hr : ‖r‖ < 1),
    R.readout () () (ell r) (OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh (r := 0) (by norm_num)
def family : Registration arena (type_of% (@ell_eq_source)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@ell_eq_source, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ell_eq_source) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.ell_eq_source.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.ell_eq_source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ell_eq_source

namespace E_ne_zero
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + Real.sqrt ‖r‖ < 1) (hv : ‖v‖ + Real.sqrt ‖r‖ < 1),
    R.readout () () (E e f u v r) (0)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (r := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@E_ne_zero)) where
  actual := complexNotEqual
  bridge := Iff.rfl
  variation := ⟨@E_ne_zero, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexNotEqual complexFalse rejected_fails
  dependence := complexNotEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@E_ne_zero) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.E_ne_zero.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.E_ne_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end E_ne_zero

namespace candidateJ_diagonal
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1),
    R.readout () () (candidateJ e e u u r) (      (r / 4 - correction r) / (b u * h e u r) +
        r ^ 2 * u / (8 * (b u * h e u r) ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false (u := 0) (r := 0) (by norm_num)
def family : Registration arena (type_of% (@candidateJ_diagonal)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@candidateJ_diagonal, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateJ_diagonal) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidateJ_diagonal.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidateJ_diagonal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateJ_diagonal

namespace candidateT_original_displacement
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1),
    let x : ℂ := r
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 / period x
    R.readout () () (modeScale f v * L e (fun w => candidateT e f w v x) u -
      modeScale e u * L f (fun w => candidateT e f u w x) v) (      (1 - x) * sourceMode e u x * sourceMode f v x *
        (modeA e u x * modeH f v x lam - modeH e u x lam * modeA f v x) / 2)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@candidateT_original_displacement)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@candidateT_original_displacement, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateT_original_displacement) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidateT_original_displacement.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidateT_original_displacement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateT_original_displacement


abbrev derivativeSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ × ℂ)
    (fun _ => ℂ → ℂ) (fun _ => Prop)
def derivativeActual : Realization derivativeSignature :=
  realize _ (fun _ a f => HasDerivAt f a.2 a.1) (fun e => nomatch e)
def derivativeBad : Realization derivativeSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
private theorem derivativeDependence :
    ObservationalDependence derivativeSignature derivativeActual := by
  intro i
  refine ⟨(0,0), (fun _ => 0), (fun x => x), ?_⟩
  intro hh
  have hd : HasDerivAt (fun x : ℂ => x) 0 0 := Eq.mp hh (hasDerivAt_const _ _)
  exact zero_ne_one (hd.unique (hasDerivAt_id (0 : ℂ)))

namespace source_u
abbrev arena : Arena where
  signature := derivativeSignature
  Law R := ∀ (e : Bool) {u r : ℂ} (_hu : ‖u‖ + ‖r‖ < 1),
    R.readout () (u, mLog e u r * sourceMode e u r) (fun w => sourceMode e w r)
private theorem rejected_fails : ¬ arena.Law derivativeBad := by
  intro hh
  exact hh false (u := 0) (r := 0) (by norm_num)
def family : Registration arena (type_of% (@source_u)) where
  actual := derivativeActual
  bridge := Iff.rfl
  variation := ⟨@source_u, derivativeBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law derivativeActual derivativeBad rejected_fails
  dependence := derivativeDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_u) (Realization derivativeSignature) (ℂ × ℂ) Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.source_u.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.source_u.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature derivativeActual.readout derivativeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end source_u

abbrev realSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)
def realLess : Realization realSignature :=
  realize _ (fun _ _ x y => x < y) (fun e => nomatch e)
def realBad : Realization realSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem realDependence : ObservationalDependence realSignature realLess := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro hh
  have he : (1 : ℝ) < 1 := Eq.mp (congrFun hh 1) (show (0 : ℝ) < 1 by norm_num)
  exact (lt_irrefl 1) he
namespace original_small
abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {w : ℂ} {r : ℝ} (_hr : 0 ≤ r) (_hr1 : r < 1)
      (_hw : ‖w‖ + Real.sqrt r < 1),
    R.readout () () (‖w‖ + ‖(r : ℂ)‖) 1
private theorem rejected_fails : ¬ arena.Law realBad := by
  intro hh
  exact hh (w := 0) (r := 0) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@original_small)) where
  actual := realLess
  bridge := Iff.rfl
  variation := ⟨@original_small, realBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law realLess realBad rejected_fails
  dependence := realDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_small) (Realization realSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.original_small.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.original_small.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature realLess.readout realLess.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_small

abbrev jointSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℂ × ℂ → ℂ) (fun _ => ℂ × ℂ → Prop)
def jointDiff : Realization jointSignature :=
  realize _ (fun _ _ f p => DifferentiableAt ℂ f p) (fun e => nomatch e)
def jointAnalytic : Realization jointSignature :=
  realize _ (fun _ _ f p => AnalyticAt ℂ f p) (fun e => nomatch e)
def jointBad : Realization jointSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem joint_inv_not_diff :
    ¬ DifferentiableAt ℂ (fun p : ℂ × ℂ => p.1⁻¹) (0,0) := by
  intro hd
  have hs := (hd.hasFDerivAt.comp_hasDerivAt (f := fun w : ℂ => (w, (0 : ℂ))) 0
    ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) (0 : ℂ)))).differentiableAt
  exact (differentiableAt_inv_iff.mp hs) rfl
theorem jointDiffDependence : ObservationalDependence jointSignature jointDiff := by
  intro i
  refine ⟨(), (fun _ => 0), (fun p => p.1⁻¹), ?_⟩
  intro hh
  exact joint_inv_not_diff (Eq.mp (congrFun hh (0,0)) (differentiableAt_const (0 : ℂ)))
private theorem jointAnalyticDependence : ObservationalDependence jointSignature jointAnalytic := by
  intro i
  refine ⟨(), (fun _ => 0), (fun p => p.1⁻¹), ?_⟩
  intro hh
  have ha : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1⁻¹) (0,0) :=
    Eq.mp (congrFun hh (0,0)) analyticAt_const
  exact joint_inv_not_diff ha.differentiableAt
namespace candidateJ_joint_analytic
abbrev arena : Arena where
  signature := jointSignature
  Law R := ∀ (e f : Bool) {u v r : ℂ}
      (_hu : ‖u‖ + ‖r‖ < 1) (_hv : ‖v‖ + ‖r‖ < 1),
    R.readout () () (fun p : ℂ × ℂ => candidateJ e f p.1 p.2 r) (u,v)
private theorem rejected_fails : ¬ arena.Law jointBad := by
  intro hh
  exact hh false false (u := 0) (v := 0) (r := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@candidateJ_joint_analytic)) where
  actual := jointAnalytic
  bridge := Iff.rfl
  variation := ⟨@candidateJ_joint_analytic, jointBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law jointAnalytic jointBad rejected_fails
  dependence := jointAnalyticDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateJ_joint_analytic) (Realization jointSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidateJ_joint_analytic.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidateJ_joint_analytic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize jointSignature jointAnalytic.readout jointAnalytic.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateJ_joint_analytic

namespace candidates_original_joint_differentiable
abbrev arena : Arena where
  signature := jointSignature
  Law R := ∀ (e f : Bool) {u v : ℂ} {r : ℝ} (_hr : 0 < r) (_hr1 : r < 1)
      (_hu : ‖u‖ + Real.sqrt r < 1) (_hv : ‖v‖ + Real.sqrt r < 1),
    R.readout () () (fun p : ℂ × ℂ => candidateJ e f p.1 p.2 (r : ℂ)) (u,v) ∧
    R.readout () () (fun p : ℂ × ℂ => candidateT e f p.1 p.2 (r : ℂ)) (u,v)
private theorem rejected_fails : ¬ arena.Law jointBad := by
  intro hh
  exact (hh false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@candidates_original_joint_differentiable)) where
  actual := jointDiff
  bridge := Iff.rfl
  variation := ⟨@candidates_original_joint_differentiable, jointBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law jointDiff jointBad rejected_fails
  dependence := jointDiffDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidates_original_joint_differentiable) (Realization jointSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidates_original_joint_differentiable.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource.candidates_original_joint_differentiable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize jointSignature jointDiff.readout jointDiff.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false },
    {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidates_original_joint_differentiable

end Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
