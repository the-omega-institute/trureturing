import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.SingleEntrySpectralGap
import Reg.Support.DependentFamily

/-! Source-bound registrations for consumed free-mode coordinate helpers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open scoped BigOperators
open Matrix

namespace Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary
open _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.StatisticalMechanics.SingleEntrySpectralGap
open _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure ModeParameters where
  Sites : Type u
  finite : Fintype Sites
  decidable : DecidableEq Sites
  a : Sites → ℝ
  b : Sites → ℝ
  eta : ℝ
  theta : ℝ

abbrev modeSignature : Signature where
  Params := ModeParameters.{u}
  State p := Option (Finset p.Sites) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Finset p.Sites) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def modeReadout : ∀ role p, (modeSignature.{u}).State p → (modeSignature.{u}).Output role p :=
  fun _ p x => letI := p.finite; letI := p.decidable
    modeNegativeGenerator p.a p.b p.eta p.theta *ᵥ x

def modeAnchor : ∀ (_ : (modeSignature.{u}).Anchor) p, (modeSignature.{u}).State p :=
  fun e => nomatch e

def modeActual : Realization modeSignature.{u} := realize modeSignature modeReadout modeAnchor

def modeRejected : Realization modeSignature.{u} :=
  realize modeSignature (fun r p x s => modeReadout r p x s + 1) modeAnchor

private theorem modeDependence : ObservationalDependence modeSignature.{u} modeActual := by
  intro role
  let p : ModeParameters.{u} :=
    ⟨ULift.{u} Unit, inferInstance, inferInstance, fun _ => 1, fun _ => 1, 1, 1⟩
  refine ⟨p, (fun _ => 0), Pi.single none 1, ?_⟩
  intro h
  have hh := congrFun h none
  simp [modeActual, modeReadout, realize, p, action_none, Pi.single_apply] at hh

namespace ActionNone

abbrev arena : Arena where
  signature := modeSignature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) (x : Option (Finset ι) → ℝ),
    R.readout () ⟨ι, fi, de, a, b, η, θ⟩ x none = θ * x none - η * ∑ S, x (some S)

private theorem rejected_law : ¬ arena.{u}.Law modeRejected := by
  intro h
  have hh := h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1) 1 1 0
  norm_num [modeRejected, modeReadout, realize] at hh

def family : Registration arena.{u} (type_of% @action_none.{u}) where
  actual := modeActual
  bridge := Iff.rfl
  variation := ⟨@action_none.{u}, modeRejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨modeRejected,
    fun j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := modeDependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 3, 4, 5, 6]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]

run_cmd do
  for index in [:selection.readouts.size] do
    let mut e := (← Lean.getConstInfo ``action_none).type
    let mut binders := 0
    let some selected := selection.readouts[index]? | throwError "Missing auxiliary readout"
    for step in selected.path do
      e ← match e, step with
        | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
          binders := binders + 1
          pure b
        | .app f _, "fn" => pure f
        | .app _ a, "arg" => pure a
        | _, _ => throwError "The original auxiliary observation path is absent"
    let args := e.getAppArgs
    unless binders == 8 && e.isAppOf ``Matrix.mulVec &&
        args[args.size - 1]? == some (.bvar 0) do
      throwError "The observation is not the original mode action on x"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@action_none.{u}) (Realization modeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.ActionNone.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.ActionNone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize modeSignature modeReadout modeAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end ActionNone

namespace ActionSome

abbrev arena : Arena where
  signature := modeSignature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) (x : Option (Finset ι) → ℝ) (S : Finset ι),
    R.readout () ⟨ι, fi, de, a, b, η, θ⟩ x (some S) =
      subsetRate a b S * x (some S) +
        modeWeight a b S * (η * (∑ T, x (some T)) - θ * x none)

private theorem rejected_law : ¬ arena.{u}.Law modeRejected := by
  intro h
  have hh := h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1) 1 1 0 ∅
  norm_num [modeRejected, modeReadout, realize] at hh

def family : Registration arena.{u} (type_of% @action_some.{u}) where
  actual := modeActual
  bridge := Iff.rfl
  variation := ⟨@action_some.{u}, modeRejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨modeRejected,
    fun j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := modeDependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 3, 4, 5, 6]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]

run_cmd do
  for index in [:selection.readouts.size] do
    let mut e := (← Lean.getConstInfo ``action_some).type
    let mut binders := 0
    let some selected := selection.readouts[index]? | throwError "Missing auxiliary readout"
    for step in selected.path do
      e ← match e, step with
        | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
          binders := binders + 1
          pure b
        | .app f _, "fn" => pure f
        | .app _ a, "arg" => pure a
        | _, _ => throwError "The original auxiliary observation path is absent"
    let args := e.getAppArgs
    unless binders == 9 && e.isAppOf ``Matrix.mulVec &&
        args[args.size - 1]? == some (.bvar 1) do
      throwError "The observation is not the original mode action on x"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@action_some.{u}) (Realization modeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.ActionSome.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.ActionSome.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize modeSignature modeReadout modeAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end ActionSome

structure TransformParameters where
  Sites : Type u
  finite : Fintype Sites
  decidable : DecidableEq Sites
  a : Sites → ℝ
  b : Sites → ℝ

abbrev transformSignature : Signature where
  Params := TransformParameters.{u}
  State p := Option (Finset p.Sites) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Finset p.Sites) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def transformReadout : ∀ role p, (transformSignature.{u}).State p →
    (transformSignature.{u}).Output role p :=
  fun _ p x => letI := p.finite; letI := p.decidable
    coordinateTransform p.a p.b *ᵥ x

def transformAnchor : ∀ (_ : (transformSignature.{u}).Anchor) p,
    (transformSignature.{u}).State p := fun e => nomatch e

def transformActual : Realization transformSignature.{u} :=
  realize transformSignature transformReadout transformAnchor

def transformRejected : Realization transformSignature.{u} :=
  realize transformSignature (fun r p x s => transformReadout r p x s + 1) transformAnchor

private theorem transformDependence :
    ObservationalDependence transformSignature.{u} transformActual := by
  intro role
  let p : TransformParameters.{u} :=
    ⟨ULift.{u} Unit, inferInstance, inferInstance, fun _ => 1, fun _ => 1⟩
  refine ⟨p, (fun _ => 0), Pi.single none 1, ?_⟩
  intro h
  have hh := congrFun h none
  simp [transformActual, transformReadout, realize, p, coordinateTransform,
    mulVec, dotProduct, Fintype.sum_option, Pi.single_apply] at hh

namespace TransformEmpty

abbrev arena : Arena where
  signature := transformSignature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    (a b : ι → ℝ), (∀ i, 0 < a i) → (∀ i, 0 < b i) →
    ∀ (p : Option (Finset ι) → ℝ),
    p (some ∅) = ∑ S, R.readout () ⟨ι, fi, de, a, b⟩ p (some S)

private theorem rejected_law : ¬ arena.{u}.Law transformRejected := by
  intro h
  have hh := h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1)
    (by intro i; norm_num) (by intro i; norm_num) 0
  norm_num [transformRejected, transformReadout, realize, Fintype.card_finset] at hh

def family : Registration arena.{u} (type_of% @transform_empty.{u}) where
  actual := transformActual
  bridge := Iff.rfl
  variation := ⟨@transform_empty.{u}, transformRejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨transformRejected,
    fun j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := transformDependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 3, 4]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]

run_cmd do
  for index in [:selection.readouts.size] do
    let mut e := (← Lean.getConstInfo ``transform_empty).type
    let mut binders := 0
    let some selected := selection.readouts[index]? | throwError "Missing auxiliary readout"
    for step in selected.path do
      e ← match e, step with
        | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
          binders := binders + 1
          pure b
        | .app f _, "fn" => pure f
        | .app _ a, "arg" => pure a
        | _, _ => throwError "The original auxiliary observation path is absent"
    let args := e.getAppArgs
    unless binders == 9 && e.isAppOf ``Matrix.mulVec &&
        args[args.size - 1]? == some (.bvar 1) do
      throwError "The observation is not the original transformed probability vector"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@transform_empty.{u}) (Realization transformSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.TransformEmpty.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.TransformEmpty.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transformSignature transformReadout transformAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end TransformEmpty

namespace TransformInverse

abbrev signature : Signature where
  Params := TransformParameters.{u}
  State p := Option (Finset p.Sites) × Option (Finset p.Sites)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p s => letI := p.finite; letI := p.decidable
    coordinateTransform p.a p.b s.1 s.2

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun r p s => actualReadout r p s + 1) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    (a b : ι → ℝ), (∀ i, 0 < a i) → (∀ i, 0 < b i) →
    inverseTransform a b * (show Matrix (Option (Finset ι)) (Option (Finset ι)) ℝ from
      fun x y => R.readout () ⟨ι, fi, de, a, b⟩ (x, y)) = 1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := congrFun (congrFun (h (ι := ULift.{u} Unit)
    (fun _ => 1) (fun _ => 1) (by intro i; norm_num) (by intro i; norm_num)) none) none
  norm_num [rejected, actualReadout, realize, Matrix.mul_apply,
    Fintype.sum_option, inverseTransform, coordinateTransform] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let p : TransformParameters.{u} :=
    ⟨ULift.{u} Unit, inferInstance, inferInstance, fun _ => 1, fun _ => 1⟩
  refine ⟨p, (none, none), (none, some ∅), ?_⟩
  norm_num [actual, actualReadout, realize, coordinateTransform]

def family : Registration arena.{u} (type_of% @transform_inverse.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@transform_inverse.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 3, 4]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]

run_cmd do
  for index in [:selection.readouts.size] do
    let mut e := (← Lean.getConstInfo ``transform_inverse).type
    let mut binders := 0
    let some selected := selection.readouts[index]? | throwError "Missing auxiliary readout"
    for step in selected.path do
      e ← match e, step with
        | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
          binders := binders + 1
          pure b
        | .app f _, "fn" => pure f
        | .app _ a, "arg" => pure a
        | _, _ => throwError "The original auxiliary observation path is absent"
    let args := e.getAppArgs
    unless binders == 7 && e.isAppOf ``coordinateTransform do
      throwError "The observation is not the original coordinate-transform operand"
    unless args[args.size - 2]? == some (.bvar 3) &&
        args[args.size - 1]? == some (.bvar 2) do
      throwError "The original transform rate binders were not retained"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@transform_inverse.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.TransformInverse.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.TransformInverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end TransformInverse

namespace InverseEmpty

abbrev signature : Signature where
  Params := TransformParameters.{u}
  State p := Finset p.Sites
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p S => letI := p.finite; letI := p.decidable
    productInverse p.a p.b S ∅

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun r p S => actualReadout r p S + 1) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    (a b : ι → ℝ), (∀ i, 0 < a i) → (∀ i, 0 < b i) →
    ∀ S : Finset ι, R.readout () ⟨ι, fi, de, a, b⟩ S = modeWeight a b S

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1)
    (by intro i; norm_num) (by intro i; norm_num) ∅
  have he := inverse_empty (ι := ULift.{u} Unit) (fun _ => (1 : ℝ)) (fun _ => 1)
    (by intro i; norm_num) (by intro i; norm_num) ∅
  change productInverse _ _ ∅ ∅ + 1 = _ at hh
  linarith

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let p : TransformParameters.{u} :=
    ⟨ULift.{u} Unit, inferInstance, inferInstance, fun _ => 1, fun _ => 2⟩
  refine ⟨p, ∅, Finset.univ, ?_⟩
  change productInverse (fun _ : ULift.{u} Unit => (1 : ℝ)) (fun _ => 2) ∅ ∅ ≠
    productInverse (fun _ : ULift.{u} Unit => (1 : ℝ)) (fun _ => 2) Finset.univ ∅
  rw [inverse_empty _ _ (by intro i; norm_num) (by intro i; norm_num),
    inverse_empty _ _ (by intro i; norm_num) (by intro i; norm_num)]
  norm_num [modeWeight,
    _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot.occupancy,
    siteRate, Finset.prod_const]

def family : Registration arena.{u} (type_of% @inverse_empty.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverse_empty.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 3, 4]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]

run_cmd do
  for index in [:selection.readouts.size] do
    let mut e := (← Lean.getConstInfo ``inverse_empty).type
    let mut binders := 0
    let some selected := selection.readouts[index]? | throwError "Missing auxiliary readout"
    for step in selected.path do
      e ← match e, step with
        | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
          binders := binders + 1
          pure b
        | .app f _, "fn" => pure f
        | .app _ a, "arg" => pure a
        | _, _ => throwError "The original auxiliary observation path is absent"
    let args := e.getAppArgs
    unless binders == 8 && e.isAppOf ``productInverse &&
        args[args.size - 2]? == some (.bvar 0) do
      throwError "The observation is not the original empty-column entry at S"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inverse_empty.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.InverseEmpty.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.InverseEmpty.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end InverseEmpty

structure GeneratorParameters where
  Sites : Type u
  finite : Fintype Sites
  decidable : DecidableEq Sites
  rates : Rates Sites

namespace TransformGenerator

abbrev signature : Signature where
  Params := GeneratorParameters.{u}
  State p := Option (Finset p.Sites) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Finset p.Sites) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p x => letI := p.finite; letI := p.decidable
    coordinateTransform p.rates.a p.rates.b *ᵥ (generator p.rates *ᵥ x)

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun r p x s => actualReadout r p x s + 1) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι]
    (k : Rates ι) (p : Option (Finset ι) → ℝ),
    R.readout () ⟨ι, fi, de, k⟩ p =
      -(modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ (coordinateTransform k.a k.b *ᵥ p))

private def unitRates : Rates (ULift.{u} Unit) where
  a := fun _ => 1
  b := fun _ => 1
  eta := 1
  theta := 1
  a_pos := by intro i; norm_num
  b_pos := by intro i; norm_num
  eta_pos := by norm_num
  theta_pos := by norm_num

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := congrFun (h unitRates 0) none
  norm_num [rejected, actualReadout, realize] at hh

private theorem transformed_none {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : Rates ι) (x : Option (Finset ι) → ℝ) :
    (coordinateTransform k.a k.b *ᵥ (generator k *ᵥ x)) none =
      -k.theta * x none + k.eta * x (some ∅) := by
  have h := dual_backward k (Pi.single none 1) x
  simpa [coordinateTransform, mulVec, dotProduct, Fintype.sum_option,
    backward, Pi.single_apply] using h

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let p : GeneratorParameters.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance, unitRates⟩
  refine ⟨p, (fun _ => 0), Pi.single none 1, ?_⟩
  intro h
  have hh := congrFun h none
  change (coordinateTransform unitRates.a unitRates.b *ᵥ (generator unitRates *ᵥ 0)) none =
    (coordinateTransform unitRates.a unitRates.b *ᵥ
      (generator unitRates *ᵥ Pi.single none 1)) none at hh
  rw [transformed_none, transformed_none] at hh
  norm_num [unitRates, Pi.single_apply] at hh

def family : Registration arena.{u} (type_of% @transform_generator.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@transform_generator.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 3]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]

run_cmd do
  for index in [:selection.readouts.size] do
    let mut e := (← Lean.getConstInfo ``transform_generator).type
    let mut binders := 0
    let some selected := selection.readouts[index]? | throwError "Missing auxiliary readout"
    for step in selected.path do
      e ← match e, step with
        | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
          binders := binders + 1
          pure b
        | .app f _, "fn" => pure f
        | .app _ a, "arg" => pure a
        | _, _ => throwError "The original auxiliary observation path is absent"
    let args := e.getAppArgs
    unless binders == 5 && e.isAppOf ``Matrix.mulVec do
      throwError "The observation is not the original transformed generator action"
    let inner := args[args.size - 1]!
    let innerArgs := inner.getAppArgs
    unless inner.isAppOf ``Matrix.mulVec && innerArgs[innerArgs.size - 1]? == some (.bvar 0) do
      throwError "The transformed generator action lost the original vector binder"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@transform_generator.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.TransformGenerator.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.TransformGenerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end TransformGenerator

structure ProductParameters where
  Sites : Type u
  f : Sites → ℝ
  g : Sites → ℝ

namespace SumSubsetProduct

abbrev signature : Signature where
  Params := ProductParameters.{u}
  State p := p.Sites
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun role p i => if role then p.g i else p.f i

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected (selected : Bool) : Realization signature.{u} :=
  realize signature (fun role p i =>
    if role = selected then actualReadout role p i + 1 else actualReadout role p i) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ),
    (∑ S : Finset ι, ∏ i,
      if i ∈ S then R.readout false ⟨ι, f, g⟩ i else R.readout true ⟨ι, f, g⟩ i) =
      ∏ i, (f i + g i)

private theorem rejected_law (selected : Bool) : ¬ arena.{u}.Law (rejected selected) := by
  intro h
  have hh := h (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 0)
  cases selected
  · have hh' : (∑ S : Finset (ULift.{u} Unit), ∏ i, if i ∈ S then (1 : ℝ) else 0) = 0 := by
      simpa [rejected, actualReadout, realize] using hh
    rw [sum_subset_product] at hh'
    norm_num at hh'
  · have hh' : (∑ S : Finset (ULift.{u} Unit), ∏ i, if i ∈ S then (0 : ℝ) else 1) = 0 := by
      simpa [rejected, actualReadout, realize] using hh
    rw [sum_subset_product] at hh'
    norm_num at hh'

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let v : ULift.{u} (Fin 2) → ℝ := fun i => if i.down = 0 then 0 else 1
  refine ⟨⟨ULift.{u} (Fin 2), v, v⟩, ULift.up 0, ULift.up 1, ?_⟩
  cases role <;> norm_num [actual, actualReadout, realize, v]

def family : Registration arena.{u} (type_of% @sum_subset_product.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_subset_product.{u}, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p x
      simp [actual, rejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 3, 4]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
    { path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]

run_cmd do
  for index in [:selection.readouts.size] do
    let mut e := (← Lean.getConstInfo ``sum_subset_product).type
    let mut binders := 0
    let some selected := selection.readouts[index]? | throwError "Missing auxiliary readout"
    for step in selected.path do
      e ← match e, step with
        | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
          binders := binders + 1
          pure b
        | .app f _, "fn" => pure f
        | .app _ a, "arg" => pure a
        | _, _ => throwError "The original auxiliary observation path is absent"
    let args := e.getAppArgs
    unless binders == 7 && args.size == 1 && args[0]? == some (.bvar 0) do
      throwError "The observation is not an original site value"
    unless e.getAppFn == (if index == 0 then .bvar 3 else .bvar 2) do
      throwError "The f and g observations lost their separate original role binders"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_subset_product.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.SumSubsetProduct.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary.SumSubsetProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end SumSubsetProduct

end Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary
