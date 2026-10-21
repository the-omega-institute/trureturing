import LeanInformationAuditInterface.Contract.Registration
import D5.S1.DifferentialAlgebra.ExponentialDifferentialField
import Reg.Support.DependentFamily

/-! Readouts for the normalized logarithmic series and its rational differential field. -/

noncomputable section

namespace Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField

open _root_.D5.S1.DifferentialAlgebra.ExponentialDifferentialField
open _root_.D5.S1.DifferentialAlgebra.LogarithmicExponentialSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Differential

attribute [local instance 2000] Algebra.toSMul

abbrev normalizedSignature : Signature where
  Params := Unit
  State _ := PowerSeries ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ × PowerSeries ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def normalizedActual : Realization normalizedSignature :=
  realize normalizedSignature
    (fun _ _ f => (PowerSeries.constantCoeff f, PowerSeries.derivative f))
    (fun e => nomatch e)

def normalizedRejected : Realization normalizedSignature :=
  realize normalizedSignature
    (fun _ _ f => (PowerSeries.constantCoeff f + 1, PowerSeries.derivative f))
    (fun e => nomatch e)

def normalizedArena : Arena where
  signature := normalizedSignature
  Law R := (R.readout () () F).1 = 0 ∧
    (R.readout () () F).2 =
      PowerSeries.exp ℚ * (2 - PowerSeries.exp ℚ)⁻¹ ∧
    ∀ f, (R.readout () () f).1 = 0 →
      (R.readout () () f).2 =
        PowerSeries.exp ℚ * (2 - PowerSeries.exp ℚ)⁻¹ → f = F

private theorem normalizedRejected_bad : ¬ normalizedArena.Law normalizedRejected := by
  intro h
  have hc := h.1
  change PowerSeries.constantCoeff F + 1 = 0 at hc
  rw [normalized_characterization.1] at hc
  simpa using hc

def normalizedFamily : Registration normalizedArena (type_of% normalized_characterization) where
  actual := normalizedActual
  bridge := by
    constructor <;> exact fun h => h
  variation := ⟨normalized_characterization, normalizedRejected, normalizedRejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normalizedRejected, ?_, rfl, normalizedRejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : PowerSeries ℚ), (1 : PowerSeries ℚ), ?_⟩
    change (PowerSeries.constantCoeff 0, PowerSeries.derivative 0) ≠
      (PowerSeries.constantCoeff 1, PowerSeries.derivative 1)
    intro heq
    have hc := congrArg Prod.fst heq
    simpa using hc

def normalizedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    normalized_characterization (Realization normalizedSignature) Unit Unit where
  unitName := Lean.Name.str `D5.S1.DifferentialAlgebra.LogarithmicExponentialSeries.normalized_characterization "__information_unit"
  realizationName := `Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField.normalizedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨normalizedArena⟩
  objectArena := .source ⟨normalizedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normalizedArena ⟨normalizedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normalizedSignature normalizedActual.readout normalizedActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem shift_ne (a : L) : a + 1 ≠ a := by
  intro h
  have h1 : (1 : L) = 0 := add_left_cancel (h.trans (add_zero a).symm)
  exact one_ne_zero h1

abbrev kSignature : Signature where
  Params := Unit
  State _ := K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := L
  Anchor := Empty
  finiteAnchor := inferInstance

def kActual : Realization kSignature :=
  realize kSignature (fun _ _ x => algebraMap K L x) (fun e => nomatch e)

def kRejected : Realization kSignature :=
  realize kSignature (fun _ _ x => algebraMap K L x + 1) (fun e => nomatch e)

def kXArena : Arena where
  signature := kSignature
  Law R := R.readout () () RatFunc.X = algebraMap (PowerSeries ℚ) L PowerSeries.X

private theorem kXRejected_bad : ¬ kXArena.Law kRejected := by
  intro h
  exact shift_ne _ (h.trans kX_image.symm)

def kXFamily : Registration kXArena (type_of% kX_image) where
  actual := kActual
  bridge := by
    constructor <;> exact fun h => h
  variation := ⟨kX_image, kRejected, kXRejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨kRejected, ?_, rfl, kXRejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : K), (1 : K), ?_⟩
    change algebraMap K L 0 ≠ algebraMap K L 1
    simp

def kXRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    kX_image (Realization kSignature) Unit Unit where
  unitName := Lean.Name.str `D5.S1.DifferentialAlgebra.ExponentialDifferentialField.kX_image "__information_unit"
  realizationName := `Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField.kXFamily
  realizationSource := none
  generated := false
  arena := .source ⟨kXArena⟩
  objectArena := .source ⟨kXArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kXArena ⟨kXFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kSignature kActual.readout kActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.DifferentialAlgebra.ExponentialDifferentialField
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev hSignature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := L
  Anchor := Empty
  finiteAnchor := inferInstance

def hActual : Realization hSignature :=
  realize hSignature (fun _ _ x => algebraMap H L x) (fun e => nomatch e)

def hRejected : Realization hSignature :=
  realize hSignature (fun _ _ x => algebraMap H L x + 1) (fun e => nomatch e)

def hXArena : Arena where
  signature := hSignature
  Law R := R.readout () () RatFunc.X = expImage

private theorem hXRejected_bad : ¬ hXArena.Law hRejected := by
  intro h
  exact shift_ne _ (h.trans hX_image.symm)

def hXFamily : Registration hXArena (type_of% hX_image) where
  actual := hActual
  bridge := by
    constructor <;> exact fun h => h
  variation := ⟨hX_image, hRejected, hXRejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hRejected, ?_, rfl, hXRejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : H), (1 : H), ?_⟩
    change algebraMap H L 0 ≠ algebraMap H L 1
    simp

def hXRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    hX_image (Realization hSignature) Unit Unit where
  unitName := Lean.Name.str `D5.S1.DifferentialAlgebra.ExponentialDifferentialField.hX_image "__information_unit"
  realizationName := `Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField.hXFamily
  realizationSource := none
  generated := false
  arena := .source ⟨hXArena⟩
  objectArena := .source ⟨hXArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hXArena ⟨hXFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize hSignature hActual.readout hActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.DifferentialAlgebra.ExponentialDifferentialField
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def logDerivativeArena : Arena where
  signature := hSignature
  Law R := logImage′ = R.readout () () (RatFunc.X / (2 - RatFunc.X))

private theorem logDerivativeRejected_bad : ¬ logDerivativeArena.Law hRejected := by
  intro h
  exact shift_ne _ (h.symm.trans logImage_derivative)

def logDerivativeFamily : Registration logDerivativeArena (type_of% logImage_derivative) where
  actual := hActual
  bridge := by
    constructor <;> exact fun h => h
  variation := ⟨logImage_derivative, hRejected, logDerivativeRejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hRejected, ?_, rfl, logDerivativeRejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : H), (1 : H), ?_⟩
    change algebraMap H L 0 ≠ algebraMap H L 1
    simp

def logDerivativeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    logImage_derivative (Realization hSignature) Unit Unit where
  unitName := Lean.Name.str `D5.S1.DifferentialAlgebra.ExponentialDifferentialField.logImage_derivative "__information_unit"
  realizationName := `Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField.logDerivativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logDerivativeArena⟩
  objectArena := .source ⟨logDerivativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logDerivativeArena ⟨logDerivativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize hSignature hActual.readout hActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.DifferentialAlgebra.ExponentialDifferentialField
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def rationalImageArena : Arena where
  signature := hSignature
  Law R := R.readout () () (RatFunc.X / (2 - RatFunc.X)) =
    algebraMap (PowerSeries ℚ) L (PowerSeries.derivative F)

private theorem rationalImageRejected_bad : ¬ rationalImageArena.Law hRejected := by
  intro h
  exact shift_ne _ (h.trans rational_image.symm)

def rationalImageFamily : Registration rationalImageArena (type_of% rational_image) where
  actual := hActual
  bridge := by
    constructor <;> exact fun h => h
  variation := ⟨rational_image, hRejected, rationalImageRejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hRejected, ?_, rfl, rationalImageRejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : H), (1 : H), ?_⟩
    change algebraMap H L 0 ≠ algebraMap H L 1
    simp

def rationalImageRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    rational_image (Realization hSignature) Unit Unit where
  unitName := Lean.Name.str `D5.S1.DifferentialAlgebra.ExponentialDifferentialField.rational_image "__information_unit"
  realizationName := `Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField.rationalImageFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rationalImageArena⟩
  objectArena := .source ⟨rationalImageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rationalImageArena ⟨rationalImageFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize hSignature hActual.readout hActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.DifferentialAlgebra.ExponentialDifferentialField
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev transcendentalSignature : Signature where
  Params := Unit
  State _ := Polynomial H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := L
  Anchor := Empty
  finiteAnchor := inferInstance

def transcendentalActual : Realization transcendentalSignature :=
  realize transcendentalSignature
    (fun _ _ p => Polynomial.aeval logImage p) (fun e => nomatch e)

def transcendentalRejected : Realization transcendentalSignature :=
  realize transcendentalSignature (fun _ _ _ => 0) (fun e => nomatch e)

def transcendentalArena : Arena where
  signature := transcendentalSignature
  Law R := Function.Injective (R.readout () ())

private theorem transcendentalRejected_bad :
    ¬ transcendentalArena.Law transcendentalRejected := by
  intro h
  change Function.Injective (fun _ : Polynomial H => (0 : L)) at h
  have hh : (0 : Polynomial H) = 1 := h rfl
  exact zero_ne_one hh

def transcendentalFamily : Registration transcendentalArena (type_of% logImage_transcendental) where
  actual := transcendentalActual
  bridge := by
    constructor
    · intro h
      exact transcendental_iff_injective.mp h
    · intro h
      exact transcendental_iff_injective.mpr h
  variation := ⟨transcendental_iff_injective.mp logImage_transcendental,
    transcendentalRejected, transcendentalRejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨transcendentalRejected, ?_, rfl, transcendentalRejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : Polynomial H), (1 : Polynomial H), ?_⟩
    change Polynomial.aeval logImage 0 ≠ Polynomial.aeval logImage 1
    simp

def transcendentalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    logImage_transcendental (Realization transcendentalSignature) Unit Unit where
  unitName := Lean.Name.str `D5.S1.DifferentialAlgebra.ExponentialDifferentialField.logImage_transcendental "__information_unit"
  realizationName := `Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField.transcendentalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transcendentalArena⟩
  objectArena := .source ⟨transcendentalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transcendentalArena ⟨transcendentalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transcendentalSignature transcendentalActual.readout transcendentalActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.DifferentialAlgebra.ExponentialDifferentialField
