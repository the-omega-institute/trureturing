import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization

/-! Source bindings for the Wu endpoint quartic comparisons. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp (congrFun h 0) (le_refl 0))

namespace PrefixAverage

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (κ : ℝ) {v y : Spectrum4}, Antitone v → 0 ≤ v 3 → Antitone y →
    (∀ k, endpointPrefixSum y k ≤ endpointPrefixSum v k) →
    ((∑ i, y i) = ∑ i, v i) →
    ∃ k : Fin 4, R.readout () () (wuQuarticSum κ y)
      (wuQuarticSum κ (endpointPrefixAverage k v))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsort : Antitone (0 : Spectrum4) := fun _ _ _ => le_rfl
  have hzero : ∀ i : Fin 4, 0 ≤ (0 : Spectrum4) i := fun _ => le_rfl
  obtain ⟨_, hfalse⟩ := h 0 hsort (hzero 3) hsort (fun _ => le_rfl) rfl
  exact hfalse

def family : Registration arena (type_of% @wuQuartic_le_some_prefixAverage) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@wuQuartic_le_some_prefixAverage, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wuQuartic_le_some_prefixAverage) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.wuQuartic_le_some_prefixAverage.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.PrefixAverage.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrefixAverage

namespace PrefixMaximum

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (κ : ℝ) {v y : Spectrum4}, Antitone v → 0 ≤ v 3 → Antitone y →
    (∀ k, endpointPrefixSum y k ≤ endpointPrefixSum v k) →
    ((∑ i, y i) = ∑ i, v i) →
    R.readout () () (wuQuarticSum κ y) (wuQuarticPrefixMax κ v)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsort : Antitone (0 : Spectrum4) := fun _ _ _ => le_rfl
  have hzero : ∀ i : Fin 4, 0 ≤ (0 : Spectrum4) i := fun _ => le_rfl
  exact h 0 hsort (hzero 3) hsort (fun _ => le_rfl) rfl

def family : Registration arena (type_of% @wuQuartic_le_prefixMax) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@wuQuartic_le_prefixMax, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wuQuartic_le_prefixMax) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.wuQuartic_le_prefixMax.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.PrefixMaximum.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrefixMaximum

namespace MajorizedFloor

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x y : Spectrum4}, Antitone x → (∀ i, 0 ≤ x i) → Antitone y →
    (∀ k, endpointPrefixSum y k ≤ endpointPrefixSum (endpointClassical x) k) →
    ((∑ i, y i) = ∑ i, endpointClassical x i) →
    R.readout () () (spectralMoment 1 x ^ 2 * (spectralMoment 2 x - spectralMoment 1 x ^ 2) ^ 2 / 5)
      (spectralMoment 3 x * spectralMoment 3 y - spectralMoment 2 x * spectralMoment 4 y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : endpointClassical (0 : Spectrum4) = 0 := by
    funext i
    fin_cases i <;> norm_num [endpointClassical, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hsort : Antitone (0 : Spectrum4) := fun _ _ _ => le_rfl
  refine h (x := 0) (y := 0) hsort (fun _ => le_rfl) hsort ?_ ?_
  · rw [hzero]
    exact fun _ => le_rfl
  · rw [hzero]

def family : Registration arena (type_of% @endpoint_quartic_floor_of_majorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpoint_quartic_floor_of_majorization, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_quartic_floor_of_majorization) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.endpoint_quartic_floor_of_majorization.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.MajorizedFloor.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization
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

end MajorizedFloor

namespace SpectralFloor

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode) (hX : X.PosSemidef),
    let x := hX.isHermitian.eigenvalues₀
    let y := (A₁_isHermitian X hX.isHermitian).eigenvalues₀
    R.readout () () (spectralMoment 1 x ^ 2 * (spectralMoment 2 x - spectralMoment 1 x ^ 2) ^ 2 / 5)
      (spectralMoment 3 x * spectralMoment 3 y - spectralMoment 2 x * spectralMoment 4 y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (Matrix.PosSemidef.zero : (0 : TwoMode).PosSemidef)

def family : Registration arena (type_of% @A1_spectral_quartic_floor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A1_spectral_quartic_floor, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_spectral_quartic_floor) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.A1_spectral_quartic_floor.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.SpectralFloor.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization
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

end SpectralFloor

namespace TraceFloor

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : TwoMode), X.PosSemidef →
    R.readout () ()
      (endpointTraceMoment 1 X ^ 2 * (endpointTraceMoment 2 X - endpointTraceMoment 1 X ^ 2) ^ 2 / 5)
      (endpointTraceMoment 3 X * endpointTraceMoment 3 (A₁ X) -
        endpointTraceMoment 2 X * endpointTraceMoment 4 (A₁ X))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (Matrix.PosSemidef.zero : (0 : TwoMode).PosSemidef)

def family : Registration arena (type_of% @A1_quartic_floor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A1_quartic_floor, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_quartic_floor) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.A1_quartic_floor.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization.TraceFloor.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization
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

end TraceFloor

end Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization
