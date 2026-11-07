import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
/-! Full-telescope source realizations and single-readout sensitivity evidence. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Finset LeanInformationAudit AddCircle
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.Analysis
open IntegerNewton SmoothCircleFourier
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality (delta)
universe u
namespace Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
private def zeroTest : Test where
  lift _ := 0
  smooth := contDiff_const
  periodic _ := rfl
private theorem zero_disjoint :
    Disjoint (tsupport zeroTest.periodic.lift) (tsupport zeroTest.periodic.lift) := by
  have hz : zeroTest.periodic.lift = 0 := by
    funext x
    induction x using Quotient.inductionOn with
    | h x => rfl
  simp [hz]
abbrev complexSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def complexActual : Realization complexSignature :=
  realize complexSignature (fun _ _ x y => x=y) (fun e => nomatch e)
def complexRejected : Realization complexSignature :=
  realize complexSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem complex_dependence : ObservationalDependence complexSignature complexActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hh := congrFun h (0 : ℂ)
  have hz : (1 : ℂ)=0 := Eq.mp hh rfl
  norm_num at hz
abbrev seriesSignature (I : Type) : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => I → ℝ) (fun _ => Prop)
def seriesActual (I : Type) : Realization (seriesSignature I) :=
  realize (seriesSignature I) (fun _ _ x => Summable x) (fun e => nomatch e)
def seriesRejected (I : Type) : Realization (seriesSignature I) :=
  realize (seriesSignature I) (fun _ _ _ => False) (fun e => nomatch e)
private theorem series_dependence (I : Type) [Infinite I] :
    ObservationalDependence (seriesSignature I) (seriesActual I) := by
  intro i
  refine ⟨(),0,(fun _ => 1),?_⟩
  intro h
  have hh : Summable (fun _ : I => (1 : ℝ)) := Eq.mp h summable_zero
  norm_num [summable_const_iff] at hh
abbrev sumSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  Unit (fun _ => ℤ → ℂ) (fun _ => ℂ → Prop)
def sumActual : Realization sumSignature :=
  realize sumSignature (fun _ _ x y => HasSum x y) (fun e => nomatch e)
def sumRejected : Realization sumSignature :=
  realize sumSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem sum_dependence : ObservationalDependence sumSignature sumActual := by
  intro i
  refine ⟨(),0,(fun _ => 1),?_⟩
  intro h
  have hh := congrFun h (0 : ℂ)
  have hs : HasSum (fun _ : ℤ => (1 : ℂ)) 0 := Eq.mp hh hasSum_zero
  have hc := hs.summable
  norm_num [summable_const_iff] at hc
abbrev equalitySignature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type u) (fun E => E) (fun E => E → Prop)
def equalityActual : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ _ x y => x=y) (fun e => nomatch e)
def equalityRejected : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem equality_dependence : ObservationalDependence equalitySignature.{u} equalityActual := by
  intro i
  refine ⟨ULift.{u} Bool,⟨false⟩,⟨true⟩,?_⟩
  intro h
  have hh := congrFun h (⟨false⟩ : ULift.{u} Bool)
  have hz : (⟨true⟩ : ULift.{u} Bool)=⟨false⟩ := Eq.mp hh rfl
  cases hz

namespace multiplier
def arena : Arena where
  signature := complexSignature
  Law ρ := ∀ (f : Test) (j : ℕ) (m : ℤ),
    ρ.readout () () ((f.frequencyBinomial j).coefficient m) (((Ring.choose m j : ℤ) : ℂ) * f.coefficient m)
private theorem rejected_bad : ¬ arena.Law (complexRejected) := by
  intro h
  exact h zeroTest 0 0
def evidence : Registration arena (type_of% (@Test.coefficient_frequencyBinomial)) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨@Test.coefficient_frequencyBinomial,complexRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (complexActual) (complexRejected) rejected_bad
  dependence := complex_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Test.coefficient_frequencyBinomial) (Realization (complexSignature)) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.multiplier.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.multiplier.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (complexSignature) (complexActual).readout (complexActual).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end multiplier

namespace differential_zero
def arena : Arena where
  signature := complexSignature
  Law ρ := ∀ (f g : Test)
    (hfg : ∀ x : ℝ, f.lift x * g.lift x = 0) (j : ℕ),
    ∀ x : ℝ, ρ.readout () () (((f.frequencyBinomial j).product g).lift x) (0)
private theorem rejected_bad : ¬ arena.Law (complexRejected) := by
  intro h
  exact h zeroTest zeroTest (by intro x; simp [zeroTest]) 0 0
def evidence : Registration arena (type_of% (@Test.frequencyBinomial_product_zero)) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨@Test.frequencyBinomial_product_zero,complexRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (complexActual) (complexRejected) rejected_bad
  dependence := complex_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Test.frequencyBinomial_product_zero) (Realization (complexSignature)) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.differential_zero.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.differential_zero.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (complexSignature) (complexActual).readout (complexActual).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end differential_zero

namespace support
def arena : Arena where
  signature := complexSignature
  Law ρ := ∀ (f g : Test)
    (h : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)),
    ∀ x : ℝ, ρ.readout () () (f.lift x * g.lift x) (0)
private theorem rejected_bad : ¬ arena.Law (complexRejected) := by
  intro h
  exact h zeroTest zeroTest zero_disjoint 0
def evidence : Registration arena (type_of% (@Test.product_zero_of_disjoint_tsupport)) where
  actual := complexActual
  bridge := Iff.rfl
  variation := ⟨@Test.product_zero_of_disjoint_tsupport,complexRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (complexActual) (complexRejected) rejected_bad
  dependence := complex_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Test.product_zero_of_disjoint_tsupport) (Realization (complexSignature)) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.support.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.support.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (complexSignature) (complexActual).readout (complexActual).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end support

namespace product
def arena : Arena where
  signature := sumSignature
  Law ρ := ∀ (T : ℝ) [Fact (0<T)],
    ∀ (F G : C(AddCircle T, ℂ))
    (hF : Summable (fun m : ℤ => ‖fourierCoeff F m‖)) (t : ℤ),
    ρ.readout () () (fun m : ℤ => fourierCoeff F m * fourierCoeff G (t-m))
      (fourierCoeff (F*G) t) ∧
    Summable (fun m : ℤ => ‖fourierCoeff F m * fourierCoeff G (t-m)‖)
private theorem rejected_bad : ¬ arena.Law (sumRejected) := by
  intro h
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  exact (h 1 0 0 (by simpa [fourierCoeff] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))) 0).1
def evidence : Registration arena (type_of% (@fourierCoeff_mul_hasSum)) where
  actual := sumActual
  bridge := Iff.rfl
  variation := ⟨@fourierCoeff_mul_hasSum,sumRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (sumActual) (sumRejected) rejected_bad
  dependence := sum_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fourierCoeff_mul_hasSum) (Realization (sumSignature)) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.product.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.product.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (sumSignature) (sumActual).readout (sumActual).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end product

namespace double_absolute
def arena : Arena where
  signature := seriesSignature (ℤ × ℤ)
  Law ρ := ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (C : ℤ → ℤ → E) (K : ℝ) (R : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (f g : Test),
    ρ.readout () () (fun mn : ℤ × ℤ =>
      ‖(f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2‖)
private theorem rejected_bad : ¬ arena.{u}.Law (seriesRejected (ℤ × ℤ)) := by
  intro h
  exact h (ULift.{u} ℂ) (fun _ _ => 0) 0 0 (by norm_num) (by intro m n; simp) zeroTest zeroTest
def evidence : Registration arena (type_of% (@FiniteDeltaContact.double_smear_absolute.{u})) where
  actual := seriesActual (ℤ × ℤ)
  bridge := Iff.rfl
  variation := ⟨@FiniteDeltaContact.double_smear_absolute.{u},seriesRejected (ℤ × ℤ),rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (seriesActual (ℤ × ℤ)) (seriesRejected (ℤ × ℤ)) rejected_bad
  dependence := series_dependence (ℤ × ℤ)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@FiniteDeltaContact.double_smear_absolute.{u}) (Realization (seriesSignature (ℤ × ℤ))) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.double_absolute.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.double_absolute.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (seriesSignature (ℤ × ℤ)) (seriesActual (ℤ × ℤ)).readout (seriesActual (ℤ × ℤ)).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end double_absolute

namespace contact_absolute
def arena : Arena where
  signature := seriesSignature ℤ
  Law ρ := ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (C : ℤ → ℤ → E) (K : ℝ) (R : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (f g : Test) (j : ℕ),
    ρ.readout () () (fun t : ℤ =>
      ‖(((f.frequencyBinomial j).product g).coefficient t) • contactCoefficient C j t‖)
private theorem rejected_bad : ¬ arena.{u}.Law (seriesRejected ℤ) := by
  intro h
  exact h (ULift.{u} ℂ) (fun _ _ => 0) 0 0 (by norm_num) (by intro m n; simp) zeroTest zeroTest 0
def evidence : Registration arena (type_of% (@FiniteDeltaContact.contact_series_absolute.{u})) where
  actual := seriesActual ℤ
  bridge := Iff.rfl
  variation := ⟨@FiniteDeltaContact.contact_series_absolute.{u},seriesRejected ℤ,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (seriesActual ℤ) (seriesRejected ℤ) rejected_bad
  dependence := series_dependence ℤ
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@FiniteDeltaContact.contact_series_absolute.{u}) (Realization (seriesSignature ℤ)) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.contact_absolute.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.contact_absolute.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (seriesSignature ℤ) (seriesActual ℤ).readout (seriesActual ℤ).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end contact_absolute

namespace contact_formula
def arena : Arena where
  signature := seriesSignature (ℤ × ℤ)
  Law ρ := ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (C : ℤ → ℤ → E) (K : ℝ) (R N : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (hdelta : delta^[N] C = 0) (f g : Test),
    ρ.readout () () (fun mn : ℤ × ℤ =>
      ‖(f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2‖) ∧
    (∀ j : ℕ, Summable (fun t : ℤ =>
      ‖(((f.frequencyBinomial j).product g).coefficient t) • contactCoefficient C j t‖)) ∧
    (∑' mn : ℤ × ℤ, (f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2) =
      ∑ j ∈ range N, ∑' t : ℤ,
        (((f.frequencyBinomial j).product g).coefficient t) • contactCoefficient C j t
private theorem rejected_bad : ¬ arena.{u}.Law (seriesRejected (ℤ × ℤ)) := by
  intro h
  exact (h (ULift.{u} ℂ) (fun _ _ => 0) 0 0 0 (by norm_num) (by intro m n; simp) rfl zeroTest zeroTest).1
def evidence : Registration arena (type_of% (@FiniteDeltaContact.delta_smooth_contact_formula.{u})) where
  actual := seriesActual (ℤ × ℤ)
  bridge := Iff.rfl
  variation := ⟨@FiniteDeltaContact.delta_smooth_contact_formula.{u},seriesRejected (ℤ × ℤ),rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (seriesActual (ℤ × ℤ)) (seriesRejected (ℤ × ℤ)) rejected_bad
  dependence := series_dependence (ℤ × ℤ)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@FiniteDeltaContact.delta_smooth_contact_formula.{u}) (Realization (seriesSignature (ℤ × ℤ))) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.contact_formula.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.contact_formula.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (seriesSignature (ℤ × ℤ)) (seriesActual (ℤ × ℤ)).readout (seriesActual (ℤ × ℤ)).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end contact_formula

namespace zero_product
def arena : Arena where
  signature := equalitySignature.{u}
  Law ρ := ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (C : ℤ → ℤ → E) (K : ℝ) (R N : ℕ)
    (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (hdelta : delta^[N] C = 0) (f g : Test)
    (hfg : ∀ x : ℝ, f.lift x * g.lift x = 0),
    ρ.readout () E ((∑' mn : ℤ × ℤ, (f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2)) (0)
private theorem rejected_bad : ¬ arena.{u}.Law (equalityRejected) := by
  intro h
  exact h (ULift.{u} ℂ) (fun _ _ => 0) 0 0 0 (by norm_num) (by intro m n; simp) rfl zeroTest zeroTest (by intro x; simp [zeroTest])
def evidence : Registration arena (type_of% (@FiniteDeltaContact.double_smear_eq_zero_of_product_zero.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@FiniteDeltaContact.double_smear_eq_zero_of_product_zero.{u},equalityRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (equalityActual) (equalityRejected) rejected_bad
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@FiniteDeltaContact.double_smear_eq_zero_of_product_zero.{u}) (Realization (equalitySignature.{u})) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.zero_product.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.zero_product.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (equalitySignature.{u}) (equalityActual).readout (equalityActual).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end zero_product

namespace separated
def arena : Arena where
  signature := equalitySignature.{u}
  Law ρ := ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (C : ℤ → ℤ → E) (K : ℝ) (R N : ℕ) (hK : 0 ≤ K)
    (hC : ∀ m n : ℤ,
      ‖C m n‖ ≤ K*(1+|(m : ℝ)|)^R*(1+|(n : ℝ)|)^R)
    (hdelta : delta^[N] C = 0) (f g : Test)
    (hfg : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)),
    ρ.readout () E ((∑' mn : ℤ × ℤ, (f.coefficient mn.1 * g.coefficient mn.2) • C mn.1 mn.2)) (0)
private theorem rejected_bad : ¬ arena.{u}.Law (equalityRejected) := by
  intro h
  exact h (ULift.{u} ℂ) (fun _ _ => 0) 0 0 0 (by norm_num) (by intro m n; simp) rfl zeroTest zeroTest zero_disjoint
def evidence : Registration arena (type_of% (@FiniteDeltaContact.double_smear_eq_zero_of_disjoint_tsupport.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@FiniteDeltaContact.double_smear_eq_zero_of_disjoint_tsupport.{u},equalityRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law (equalityActual) (equalityRejected) rejected_bad
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@FiniteDeltaContact.double_smear_eq_zero_of_disjoint_tsupport.{u}) (Realization (equalitySignature.{u})) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.separated.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact.separated.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (equalitySignature.{u}) (equalityActual).readout (equalityActual).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end separated
end Reg.D5.S3.VertexAlgebra.Analysis.SmoothCircleContact
