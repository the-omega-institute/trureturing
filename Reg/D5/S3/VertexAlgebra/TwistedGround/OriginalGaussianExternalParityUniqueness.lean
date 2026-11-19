import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness

noncomputable section
open scoped BigOperators
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianExternalResolvent OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalParityUniqueness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness

abbrev eqSignature : Signature where
  Params := Type
  State T := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def eqActual : Realization eqSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def eqRejected : Realization eqSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨ℂ, 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

namespace externalJ_neg
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ) (z : ℂ),
    R.readout () _ (externalJ out p out' q (-z)) (externalJ out p out' q z)

private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 false 0 0

def family : Registration arena (type_of% (@externalJ_neg)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@externalJ_neg, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalJ_neg) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.externalJ_neg.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.externalJ_neg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
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
end externalJ_neg

namespace externalT_neg
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ) (z : ℂ),
    R.readout () _ (externalT out p out' q (-z)) (externalT out p out' q z)

private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 false 0 0

def family : Registration arena (type_of% (@externalT_neg)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@externalT_neg, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalT_neg) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.externalT_neg.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.externalT_neg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
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
end externalT_neg

namespace kernelMode_neg
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (square out out' : Bool) (u v z : ℂ),
    R.readout () _ (kernelMode square out out' u v (-z)) (kernelMode square out out' u v z)

private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false false false 0 0 0

def family : Registration arena (type_of% (@kernelMode_neg)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@kernelMode_neg, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernelMode_neg) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.kernelMode_neg.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.kernelMode_neg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end kernelMode_neg

namespace positive_even_coefficients_zero
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (c : ℕ → ℕ → ℕ → ℂ)
    (_hodd : ∀ (p q k : ℕ), Odd k → c p q k = 0)
    (_hdiff : ∀ (p q k : ℕ),
      ((p : ℂ) - q) * c p q k -
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0)
    (_hrad : ∀ (p q k : ℕ),
      ((k : ℂ) - p - q - 1) * c p q k +
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0),
    ∀ p q k, R.readout () _ (c p q k) 0

private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  have hh := h (fun _ _ _ => 0) (by intros; rfl)
    (by intros; simp) (by intros; simp) 0 0 0
  exact hh

def family : Registration arena (type_of% (@positive_even_coefficients_zero)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@positive_even_coefficients_zero, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_even_coefficients_zero) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.positive_even_coefficients_zero.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.positive_even_coefficients_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
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
end positive_even_coefficients_zero

namespace externalT_positive_germ_unique
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (candidate : ℕ → ℕ → ℂ → ℂ)
    (_heven : ∀ p q z, candidate p q (-z) = candidate p q z)
    (c : ℕ → ℕ → ℕ → ℂ)
    (_hexp : ∀ p q, HasFPowerSeriesAt
      (fun z => externalT true p true q z - candidate p q z)
      (FormalMultilinearSeries.ofScalars ℂ (c p q)) 0)
    (_hdiff : ∀ (p q k : ℕ),
      ((p : ℂ) - q) * c p q k -
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0)
    (_hrad : ∀ (p q k : ℕ),
      ((k : ℂ) - p - q - 1) * c p q k +
        (p + 1 / 2) * (if p = 0 then 0 else c (p - 1) q k) +
        (q + 1 / 2) * (if q = 0 then 0 else c p (q - 1) k) = 0),
    ∀ p q, ∀ᶠ z in nhds (0 : ℂ), R.readout () _ (externalT true p true q z) (candidate p q z)

private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  have heven : ∀ p q z, externalT true p true q (-z) = externalT true p true q z := by
    intros
    apply externalT_neg
  have hexp : ∀ p q, HasFPowerSeriesAt
      (fun z => externalT true p true q z - externalT true p true q z)
      (FormalMultilinearSeries.ofScalars ℂ (fun _ => (0 : ℂ))) 0 := by
    intro p q
    simpa [show (fun _ : ℕ => (0 : ℂ)) = (0 : ℕ → ℂ) from rfl] using
      (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (c := (0 : ℂ)) (e := 0))
  have hh := h (fun p q z => externalT true p true q z) heven
    (fun _ _ _ => 0) hexp (by intros; simp) (by intros; simp) 0 0
  exact (Filter.Eventually.exists hh).choose_spec

def family : Registration arena (type_of% (@externalT_positive_germ_unique)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@externalT_positive_germ_unique, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalT_positive_germ_unique) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.externalT_positive_germ_unique.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness.externalT_positive_germ_unique.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalT_positive_germ_unique

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
