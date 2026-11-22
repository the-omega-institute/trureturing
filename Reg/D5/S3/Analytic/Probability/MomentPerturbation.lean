import LeanInformationAuditInterface.Contract.Registration
import Mathlib.MeasureTheory.Measure.DiracProba
import D5.S3.Analytic.Probability.MomentPerturbation
import Reg.Support.DependentFamily

/-! Source-bound observations of the moment tilt, Gram form, and weak limit. -/

namespace Reg.D5.S3.Analytic.Probability.MomentPerturbation

open _root_.D5.S3.Analytic.Probability.MomentPerturbation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ observed expected => observed = expected) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ observed expected => observed ≠ expected) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℝ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hfalse

namespace Cancellation

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (R : ℕ) (μ : ProbabilityMeasure ℝ) (p : Polynomial ℝ), p.natDegree ≤ R →
    r.readout () () (∫ x, p.eval x * (density R μ x - 1) ∂(μ : Measure ℝ)) 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 standardGaussian 1 (by simp)
    (integral_eval_mul_density_sub_one 0 standardGaussian 1 (by simp))

def source_registration : Registration arena (type_of% @integral_eval_mul_density_sub_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_eval_mul_density_sub_one, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@integral_eval_mul_density_sub_one) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Cancellation.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Cancellation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ observed expected => observed = expected) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.MomentPerturbation
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
  options := #[] }

end Cancellation

namespace Mass

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (R : ℕ) (μ : ProbabilityMeasure ℝ),
    r.readout () () (∫ x, density R μ x ∂(μ : Measure ℝ)) 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 standardGaussian (integral_density 0 standardGaussian)

def source_registration : Registration arena (type_of% @integral_density) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_density, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@integral_density) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Mass.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Mass.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ observed expected => observed = expected) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.MomentPerturbation
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
  options := #[] }

end Mass

private theorem unitSensitivity {A : Arena} [Subsingleton A.signature.Role]
    [IsEmpty A.signature.Anchor] {actual rejected : Realization A.signature}
    (h : ¬ A.Law rejected) : Sensitivity A actual :=
  ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    funext fun e => isEmptyElim e, h⟩, fun e => isEmptyElim e⟩

private theorem comparisonDependence {cmp : ℝ → ℝ → Prop} {x y z : ℝ}
    (hx : cmp x z) (hy : ¬ cmp y z) :
    ObservationalDependence signature
      (realize signature (fun _ _ l r => cmp l r) (fun e => nomatch e)) := by
  intro i
  exact ⟨(), x, y, fun h => hy ((congrFun h z).mp hx)⟩

private def pointIndicator (x : ℝ) : ℝ :=
  if x = 0 then 1 else 0

private theorem pointIndicator_not_continuous : ¬ Continuous pointIndicator := by
  intro h
  have he : pointIndicator ⁻¹' Set.Ioi (1 / 2 : ℝ) = {0} := by
    ext x
    by_cases hx : x = 0 <;> norm_num [Set.mem_Ioi, pointIndicator, hx]
  have hopen : IsOpen (pointIndicator ⁻¹' Set.Ioi (1 / 2 : ℝ)) := isOpen_Ioi.preimage h
  rw [he] at hopen
  exact not_isOpen_singleton 0 hopen

namespace Bounds

def actual : Realization signature :=
  realize signature (fun _ _ l r => l ≤ r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ l r => ¬ l ≤ r) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (R : ℕ) (μ : ProbabilityMeasure ℝ) (x : ℝ),
    r.readout () () (1 / 2) (density R μ x) ∧ density R μ x ≤ 3 / 2

theorem rejected_law : ¬ arena.Law rejected :=
  fun h => (h 0 standardGaussian 0).1 (density_bounds 0 standardGaussian 0).1

def source_registration : Registration arena (type_of% @density_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨density_bounds, rejected, rejected_law⟩
  sensitivity := unitSensitivity (rejected := rejected) rejected_law
  dependence := comparisonDependence (show (0 : ℝ) ≤ 0 from le_rfl)
    (show ¬ (1 : ℝ) ≤ 0 from not_le_of_gt zero_lt_one)


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@density_bounds) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Bounds.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Bounds.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l r => l ≤ r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.MomentPerturbation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Bounds

namespace Separation

def actual : Realization signature :=
  realize signature (fun _ _ l r => l < r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ l r => ¬ l < r) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ R : ℕ,
    r.readout () () (∫ x, perturbation R standardGaussian x ∂(standardGaussian : Measure ℝ))
      (∫ x, perturbation R standardGaussian x ∂(tilted R standardGaussian : Measure ℝ)) ∧
    tilted R standardGaussian ≠ standardGaussian

theorem rejected_law : ¬ arena.Law rejected :=
  fun h => (h 0).1 (tilted_gaussian_separation 0).1

def source_registration : Registration arena (type_of% @tilted_gaussian_separation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tilted_gaussian_separation, rejected, rejected_law⟩
  sensitivity := unitSensitivity (rejected := rejected) rejected_law
  dependence := comparisonDependence (show (0 : ℝ) < 1 from zero_lt_one)
    (show ¬ (1 : ℝ) < 1 from lt_irrefl 1)


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tilted_gaussian_separation) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Separation.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Separation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l r => l < r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.MomentPerturbation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Separation

namespace DensityContinuity

abbrev signature : Signature where
  Params := Σ _ : ℕ, ProbabilityMeasure ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => density p.1 p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => pointIndicator x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (R : ℕ) (μ : ProbabilityMeasure ℝ), Continuous (r.readout () ⟨R, μ⟩)

theorem rejected_law : ¬ arena.Law rejected :=
  fun h => pointIndicator_not_continuous (h 0 standardGaussian)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let μ := standardGaussian
  refine ⟨⟨0, μ⟩, ?_⟩
  change ∃ x y : ℝ, density 0 μ x ≠ density 0 μ y
  by_contra! h
  have hc : density 0 μ = fun _ => density 0 μ 0 := funext fun x => h x 0
  have hm := integral_density 0 μ
  rw [hc] at hm
  have hone : density 0 μ 0 = 1 := by simpa using hm
  have he : tilted 0 μ = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    change (μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (density 0 μ x)) = _
    simp [hc, hone]
  exact (tilted_gaussian_separation 0).2 he

def source_registration : Registration arena (type_of% @continuous_density) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_density, rejected, rejected_law⟩
  sensitivity := unitSensitivity (rejected := rejected) rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@continuous_density) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.DensityContinuity.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.MomentPerturbation.DensityContinuity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => density p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.MomentPerturbation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end DensityContinuity

namespace WeakContinuity

abbrev signature : Signature where
  Params := ℕ
  State _ := ProbabilityMeasure ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ProbabilityMeasure ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ R μ => tilted R μ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ R : ℕ, Continuous (r.readout () R)

private def jump (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ := by
  classical
  exact if μ = diracProba (0 : ℝ) then diracProba 1 else diracProba 0

private theorem jump_not_continuous : ¬ Continuous jump := by
  intro h
  apply pointIndicator_not_continuous
  have hcomp : jump ∘ diracProba = diracProba ∘ pointIndicator := by
    funext x
    by_cases hx : x = 0 <;> simp [jump, pointIndicator, hx, injective_diracProba.eq_iff]
  apply (isEmbedding_diracProba (X := ℝ)).continuous_iff.mpr
  rw [← hcomp]
  exact h.comp continuous_diracProba

def rejected : Realization signature :=
  realize signature (fun _ _ μ => jump μ) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected :=
  fun h => jump_not_continuous (h 0)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, diracProba 0, diracProba 1, ?_⟩
  change tilted 0 (diracProba 0) ≠ tilted 0 (diracProba 1)
  have hdirac (x : ℝ) : tilted 0 (diracProba x) = diracProba x := by
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.dirac x).withDensity (fun y => ENNReal.ofReal (density 0 (diracProba x) y)) =
      Measure.dirac x
    rw [dirac_withDensity]
    have hn := integral_density 0 (diracProba x)
    change (∫ y, density 0 (diracProba x) y ∂Measure.dirac x) = 1 at hn
    rw [integral_dirac] at hn
    simp [hn]
  rw [hdirac, hdirac]
  exact fun h => zero_ne_one (injective_diracProba h)

def source_registration : Registration arena (type_of% @continuous_tilted) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_tilted, rejected, rejected_law⟩
  sensitivity := unitSensitivity (rejected := rejected) rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@continuous_tilted) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.WeakContinuity.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.MomentPerturbation.WeakContinuity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ R μ => tilted R μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.MomentPerturbation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end WeakContinuity

namespace Gram

open Matrix

abbrev signature : Signature where
  Params := ℕ
  State _ := ProbabilityMeasure ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ R := Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ R μ => gram R μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ R : ℕ, (r.readout () R standardGaussian).PosDef

private theorem zero_not_posDef : ¬ (0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  intro h
  have hu : (fun _ : Fin 1 => (1 : ℝ)) ≠ 0 := by
    intro he
    exact one_ne_zero (congrFun he 0)
  simpa using h.dotProduct_mulVec_pos hu

theorem rejected_law : ¬ arena.Law rejected :=
  fun h => zero_not_posDef (h 0)

private theorem gram_dirac_outside : gram 0 (diracProba (2 : ℝ)) = 0 := by
  ext i j
  change (∫ x, window x * x ^ (i.val + j.val) ∂Measure.dirac 2) = 0
  rw [integral_dirac]
  have hw : window 2 = 0 := by norm_num [window]
  simp [hw]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, standardGaussian, diracProba 2, ?_⟩
  change gram 0 standardGaussian ≠ gram 0 (diracProba 2)
  rw [gram_dirac_outside]
  intro h
  exact zero_not_posDef (h ▸ gaussian_gram_posDef 0)

def source_registration : Registration arena (type_of% @gaussian_gram_posDef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gaussian_gram_posDef, rejected, rejected_law⟩
  sensitivity := unitSensitivity (rejected := rejected) rejected_law
  dependence := dependence


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@gaussian_gram_posDef) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Gram.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.MomentPerturbation.Gram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ R μ => gram R μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.MomentPerturbation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Gram

end

end Reg.D5.S3.Analytic.Probability.MomentPerturbation
