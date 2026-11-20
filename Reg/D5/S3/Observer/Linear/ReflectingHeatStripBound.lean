import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.ReflectingHeatStripBound
import Reg.Support.SingleDependentReadout

/-! Cellwise values and the physical-time Gramian of the reflecting path. -/

namespace Reg.D5.S3.Observer.Linear.ReflectingHeatStripBound

open _root_.D5.S3.Observer.Linear.ReflectingHeatStripBound
open _root_.D5.S3.Analytic.Hardy.FiniteStripMomentBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit Matrix Set

noncomputable section
open scoped BigOperators

private abbrev twoCellMode : Mode 2 := 0

private theorem twoCellRate : rate 2 twoCellMode = 2 := by
  unfold rate
  change 2 - 2 * Real.cos (((1 : ℕ) : ℝ) * Real.pi / ((2 : ℕ) : ℝ)) = 2
  push_cast
  rw [one_mul, Real.cos_pi_div_two]
  ring

private theorem twoCellWeight : weight 2 twoCellMode = 1 := by
  norm_num [weight, twoCellRate]

private theorem twoCellValuesDistinct :
    cellMode 2 twoCellMode 0 ≠ cellMode 2 twoCellMode 1 := by
  intro he
  have hs := cellMode_sum_zero 2 twoCellMode
  rw [Fin.sum_univ_two, ← he] at hs
  have hz : cellMode 2 twoCellMode 0 = 0 := by linarith
  have hm := cellMode_mass_inner 2 twoCellMode twoCellMode
  rw [Fin.sum_univ_two, ← he, hz] at hm
  norm_num at hm

namespace Generator

abbrev signature :=
  SingleDependentReadout.signature ((n : ℕ) × Mode n) (fun p => Fin p.1) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p i => reflectingGenerator p.1 (cellMode p.1 p.2) i)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n) (i : Fin n),
    R.readout () ⟨n, j⟩ i = -physicalRate n j * cellMode n j i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 2 twoCellMode 0
  have h1 := h 2 twoCellMode 1
  have hp : physicalRate 2 twoCellMode ≠ 0 := by norm_num [physicalRate, twoCellRate]
  have he : -physicalRate 2 twoCellMode * cellMode 2 twoCellMode 0 =
      -physicalRate 2 twoCellMode * cellMode 2 twoCellMode 1 := h0.symm.trans h1
  exact twoCellValuesDistinct (mul_left_cancel₀ (neg_ne_zero.mpr hp) he)

def family : Registration arena (type_of% @reflectingGenerator_cellMode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reflectingGenerator_cellMode, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨2, twoCellMode⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
    change reflectingGenerator 2 (cellMode 2 twoCellMode) 0 ≠
      reflectingGenerator 2 (cellMode 2 twoCellMode) 1
    rw [reflectingGenerator_cellMode, reflectingGenerator_cellMode]
    have hp : physicalRate 2 twoCellMode ≠ 0 := by norm_num [physicalRate, twoCellRate]
    exact fun he => twoCellValuesDistinct (mul_left_cancel₀ (neg_ne_zero.mpr hp) he)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reflectingGenerator_cellMode)
    (type_of% (realize signature (fun _ p i => reflectingGenerator p.1 (cellMode p.1 p.2) i)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ReflectingHeatStripBound.reflectingGenerator_cellMode.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatStripBound.Generator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p i => reflectingGenerator p.1 (cellMode p.1 p.2) i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatStripBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Generator

namespace CellMode

abbrev signature :=
  SingleDependentReadout.signature ((n : ℕ) × Mode n) (fun p => Fin p.1) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p i => cellMode p.1 p.2 i) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨⟨2, twoCellMode⟩, (0 : Fin 2), (1 : Fin 2), twoCellValuesDistinct⟩

namespace Mean

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j : Mode n), (∑ i : Fin n, R.readout () ⟨n, j⟩ i) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 twoCellMode
  norm_num [rejected, realize, Fin.sum_univ_two] at hbad

def family : Registration arena (type_of% @cellMode_sum_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cellMode_sum_zero, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cellMode_sum_zero)
    (type_of% (realize signature (fun _ p i => cellMode p.1 p.2 i) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ReflectingHeatStripBound.cellMode_sum_zero.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatStripBound.CellMode.Mean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => cellMode p.1 p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatStripBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Mean

namespace MassInner

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (j k : Mode n),
    (∑ i : Fin n, R.readout () ⟨n, j⟩ i * cellMode n k i) / (n : ℝ) =
      if j = k then 1 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 twoCellMode twoCellMode
  simp [rejected, realize] at hbad

def family : Registration arena (type_of% @cellMode_mass_inner) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cellMode_mass_inner, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cellMode_mass_inner)
    (type_of% (realize signature (fun _ p i => cellMode p.1 p.2 i) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ReflectingHeatStripBound.cellMode_mass_inner.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatStripBound.CellMode.MassInner.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => cellMode p.1 p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatStripBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "body",
        "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end MassInner
end CellMode

namespace Evolution

abbrev signature := SingleDependentReadout.signature
  ((n : ℕ) × (Mode n → ℝ)) (fun _ => ℝ) (fun p => Fin p.1 → ℝ)

def actual : Realization signature :=
  realize signature (fun _ p t => reflectingHeatFlow p.1 p.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (c : Mode n → ℝ) (t : ℝ),
    (∀ i, HasDerivAt (fun s => reflectingHeatFlow n c s i)
      (reflectingGenerator n (reflectingHeatFlow n c t) i) t) ∧
    (∑ i : Fin n, R.readout () ⟨n, c⟩ t i) = 0 ∧
    ∀ j, (∑ i, reflectingHeatFlow n c t i * cellMode n j i) / (n : ℝ) =
      c j * Real.exp (-physicalRate n j * t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 2 (fun _ => 0) 0).2.1
  norm_num [rejected, realize, Fin.sum_univ_two] at hbad

def family : Registration arena (type_of% @reflectingHeatFlow_spec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reflectingHeatFlow_spec, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    let c : Mode 2 → ℝ := fun _ => 1
    refine ⟨⟨2, c⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change reflectingHeatFlow 2 c 0 ≠ reflectingHeatFlow 2 c 1
    intro he
    have h0 := (reflectingHeatFlow_spec 2 c 0).2.2 twoCellMode
    have h1 := (reflectingHeatFlow_spec 2 c 1).2.2 twoCellMode
    rw [he, h1] at h0
    have h := (Real.exp_lt_one_iff.mpr
      (show -physicalRate 2 twoCellMode < 0 by norm_num [physicalRate, twoCellRate]))
    exact h.ne (by simpa [c] using h0)
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reflectingHeatFlow_spec)
    (type_of% (realize signature (fun _ p t => reflectingHeatFlow p.1 p.2 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ReflectingHeatStripBound.reflectingHeatFlow_spec.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatStripBound.Evolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => reflectingHeatFlow p.1 p.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatStripBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg",
        "body", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Evolution

namespace InverseDiagonal

abbrev signature := SingleDependentReadout.signature ℕ
  (fun _ => ℝ) (fun n => Matrix (Mode n) (Mode n) ℝ)

def actual : Realization signature :=
  realize signature (fun _ n T => physicalGramian n T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 2 ≤ n) {a β : ℝ} (_ha : 0 < a) (_hβ : 0 < β) (j : Mode n),
    (n : ℝ) / weight n j *
        ((∏ k ∈ Finset.univ.erase j, (radius β (rate n j) + radius β (rate n k)) /
          |rate n j - rate n k|) * Real.exp (-(n : ℝ) * a * (radius β (rate n j) - rate n j) / 2) /
          Real.sqrt ((n : ℝ) * a)) ≤
      Real.sqrt ((R.readout () n (a / (n : ℝ)))⁻¹ j j)

private theorem twoCellBoundPositive :
    0 < (2 : ℝ) / weight 2 twoCellMode *
        ((∏ k ∈ Finset.univ.erase twoCellMode, (radius 1 (rate 2 twoCellMode) +
          radius 1 (rate 2 k)) / |rate 2 twoCellMode - rate 2 k|) *
          Real.exp (-(2 : ℝ) * 1 * (radius 1 (rate 2 twoCellMode) - rate 2 twoCellMode) / 2) /
          Real.sqrt ((2 : ℝ) * 1)) := by
  have hempty : Finset.univ.erase twoCellMode = ∅ := by
    ext k
    have hk : k = twoCellMode := Fin.ext (by have := k.isLt; change k.val = 0; omega)
    simp [hk]
  rw [twoCellWeight, hempty, Finset.prod_empty]
  positivity

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by decide) (a := 1) (β := 1) zero_lt_one zero_lt_one twoCellMode
  have hz : Real.sqrt (((0 : Matrix (Mode 2) (Mode 2) ℝ)⁻¹) twoCellMode twoCellMode) = 0 := by simp
  change _ ≤ Real.sqrt (((0 : Matrix (Mode 2) (Mode 2) ℝ)⁻¹) twoCellMode twoCellMode) at hbad
  rw [hz] at hbad
  exact twoCellBoundPositive.not_ge hbad

def family : Registration arena (type_of% @inverse_diagonal_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inverse_diagonal_lower_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(2 : ℕ), (0 : ℝ), 1 / (2 : ℝ), ?_⟩
    change physicalGramian 2 0 ≠ physicalGramian 2 (1 / 2)
    intro he
    have hzero : physicalGramian 2 0 = 0 := by ext j k; simp [physicalGramian]
    have h := inverse_diagonal_lower_bound 2 (by decide) (a := 1) (β := 1)
      zero_lt_one zero_lt_one twoCellMode
    change _ ≤ Real.sqrt ((physicalGramian 2 (1 / 2))⁻¹ twoCellMode twoCellMode) at h
    rw [← he, hzero, Matrix.inv_zero] at h
    exact twoCellBoundPositive.not_ge (by simpa using h)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@inverse_diagonal_lower_bound)
    (type_of% (realize signature (fun _ n T => physicalGramian n T) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ReflectingHeatStripBound.inverse_diagonal_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ReflectingHeatStripBound.InverseDiagonal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n T => physicalGramian n T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ReflectingHeatStripBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg",
        "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end InverseDiagonal
end

end Reg.D5.S3.Observer.Linear.ReflectingHeatStripBound
