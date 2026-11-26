import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction

/-! Source-bound registrations for the scalar and physical occupation entropy bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => ¬ x ≤ y) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (not_le_of_gt zero_lt_one) (Eq.mp (congrFun h 0) (le_rfl : (0 : ℝ) ≤ 0))

namespace EntropySlope

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b z : ℝ}
      (hab : a < b) (htrace : a + b = 1) (hz : 0 ≤ z) (hzab : z < a * b),
    R.readout () () (entropySlope a b * z) (fixedOccupationEntropy a b z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hab : (1 / 3 : ℝ) < 2 / 3 := by norm_num
  have htrace : (1 / 3 : ℝ) + 2 / 3 = 1 := by norm_num
  have hz : (0 : ℝ) < (1 / 3) * (2 / 3) := by norm_num
  exact law hab htrace le_rfl hz (entropySlope_mul_le_fixedOccupationEntropy hab htrace le_rfl hz)

def family : Registration arena (type_of% @entropySlope_mul_le_fixedOccupationEntropy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropySlope_mul_le_fixedOccupationEntropy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entropySlope_mul_le_fixedOccupationEntropy) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.entropySlope_mul_le_fixedOccupationEntropy.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.EntropySlope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EntropySlope

namespace FiniteAmplitude

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b z α η : ℝ}
      (ha : 0 < a) (hab : a < b) (htrace : a + b = 1)
      (hη : 0 < η) (hz : 0 < z)
      (hamp : z ≤ a * b * η / (2 + η))
      (hα : α * entropySlope a b = 2 * (1 + η) / (1 + 2 * Real.sqrt (a * b))),
    0 < η * z / (1 + 2 * Real.sqrt (a * b)) ∧
      R.readout () () (η * z / (1 + 2 * Real.sqrt (a * b)))
        (α * fixedOccupationEntropy a b z - 4 * occupationDefect a b z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let a : ℝ := 1 / 3
  let b : ℝ := 2 / 3
  let z : ℝ := 1 / 9
  let η : ℝ := 2
  let α := 2 * (1 + η) / (1 + 2 * Real.sqrt (a * b)) / entropySlope a b
  have ha : 0 < a := by norm_num [a]
  have hab : a < b := by norm_num [a, b]
  have htrace : a + b = 1 := by norm_num [a, b]
  have hη : 0 < η := by norm_num [η]
  have hz : 0 < z := by norm_num [z]
  have hamp : z ≤ a * b * η / (2 + η) := by norm_num [a, b, z, η]
  have hslope : 0 < entropySlope a b :=
    div_pos (sub_pos.mpr (Real.log_lt_log ha hab)) (sub_pos.mpr hab)
  have hα : α * entropySlope a b = 2 * (1 + η) / (1 + 2 * Real.sqrt (a * b)) :=
    div_mul_cancel₀ _ hslope.ne'
  exact (law ha hab htrace hη hz hamp hα).2
    (finite_amplitude_obstruction ha hab htrace hη hz hamp hα).2

def family : Registration arena (type_of% @finite_amplitude_obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_amplitude_obstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_amplitude_obstruction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.finite_amplitude_obstruction.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.FiniteAmplitude.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteAmplitude

namespace Product

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℝ} (hh : 0 < h) (w : ℂ)
      (hw : 0 < Complex.normSq w) (hcap : Complex.normSq w ≤ amplitudeCap h),
    let a := gibbsLow h
    let b := gibbsHigh h
    let z := Complex.normSq w
    let ρ := witness a b w
    let D := localGibbs a b ⊗ₖ localGibbs a b
    let margin := cubicExcess h * z / (1 + 2 * Real.sqrt (a * b))
    (localGibbs a b).PosDef ∧ (localGibbs a b).trace = 1 ∧
      (coherentDensity a b w).PosDef ∧ (coherentDensity a b w).trace = 1 ∧
      ρ.PosDef ∧ ρ.trace = 1 ∧
      (∀ k, hole ρ k = a ∧ particle ρ k = b) ∧
      0 < margin ∧
      R.readout () () margin (cubicCoefficient h * traceRelativeEntropy ρ D - 4 * qStar ρ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hh : (0 : ℝ) < 1 := zero_lt_one
  obtain ⟨hcap, _, hwitness⟩ := amplitude_interval hh
  obtain ⟨w, hw, _⟩ := hwitness (amplitudeCap 1) ⟨hcap, le_rfl⟩
  have hz : 0 < Complex.normSq w := hw.symm ▸ hcap
  have hzcap : Complex.normSq w ≤ amplitudeCap 1 := hw.le
  obtain ⟨_, _, _, _, _, _, _, _, hbad⟩ := law hh w hz hzcap
  obtain ⟨_, _, _, _, _, _, _, _, hgood⟩ := matched_product_obstruction hh w hz hzcap
  exact hbad hgood

def family : Registration arena (type_of% @matched_product_obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matched_product_obstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@matched_product_obstruction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.matched_product_obstruction.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.Product.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Select the quantitative gap at the end of the product-state conjunction.
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Product

namespace Interval

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => ¬ x < y) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (lt_irrefl (1 : ℝ)) (Eq.mp (congrFun h 1) (zero_lt_one : (0 : ℝ) < 1))

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℝ} (hh : 0 < h),
    0 < amplitudeCap h ∧
      Set.InjOn (fun z : ℝ => witness (gibbsLow h) (gibbsHigh h) (Real.sqrt z : ℂ))
        (Ioc 0 (amplitudeCap h)) ∧
      ∀ z ∈ Ioc 0 (amplitudeCap h), ∃ w : ℂ,
        Complex.normSq w = z ∧
        let ρ := witness (gibbsLow h) (gibbsHigh h) w
        let D := localGibbs (gibbsLow h) (gibbsHigh h) ⊗ₖ localGibbs (gibbsLow h) (gibbsHigh h)
        ρ.PosDef ∧ ρ.trace = 1 ∧
          R.readout () () (4 * qStar ρ) (cubicCoefficient h * traceRelativeEntropy ρ D)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hh : (0 : ℝ) < 1 := zero_lt_one
  obtain ⟨hcap, _, hwitness⟩ := law hh
  obtain ⟨w, hw, _, _, hbad⟩ := hwitness (amplitudeCap 1) ⟨hcap, le_rfl⟩
  have hz : 0 < Complex.normSq w := hw.symm ▸ hcap
  have hzcap : Complex.normSq w ≤ amplitudeCap 1 := hw.le
  obtain ⟨_, _, _, _, _, _, _, hmargin, hgap⟩ := matched_product_obstruction hh w hz hzcap
  exact hbad (sub_pos.mp (hmargin.trans_le hgap))

def family : Registration arena (type_of% @amplitude_interval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@amplitude_interval, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@amplitude_interval) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.amplitude_interval.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction.Interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Select the strict gap inside the existential realization of the amplitude.
      path := #["body", "body", "arg", "arg", "body", "body", "arg", "body",
        "arg", "body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interval

end Reg.D5.S3.Quantum.Semigroups.WuCubicOccupationEntropyObstruction
