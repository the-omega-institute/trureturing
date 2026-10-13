import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.HyperbolicHausdorffComparison
import Reg.Support.DependentFamily

open _root_.D5.S3.Geometry.HyperbolicHausdorffComparison
open _root_.D5.S3.Geometry.HyperbolicUpperHalfSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace Reg.D5.S3.Geometry.HyperbolicHausdorffComparison

private local instance : MeasurableSpace (UpperHalfSpace ℂ) := borel _
private local instance : BorelSpace (UpperHalfSpace ℂ) := ⟨rfl⟩
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p : UpperHalfSpace ℂ) (r : ℝ)
    (_hr : 0 < r) (_hrh : r < height p) (s : Set (UpperHalfSpace ℂ))
    (_hs : s ⊆ Metric.ball p r),
    R.readout false () (Measure.hausdorffMeasure 3 s)
      ((ENNReal.ofReal (height p + 2*r)) ^ (3 : ℝ) *
        Measure.hausdorffMeasure 3 (HyperbolicSpace.mk '' s)) ∧
    R.readout true () (Measure.hausdorffMeasure 3 (HyperbolicSpace.mk '' s))
      ((ENNReal.ofReal ((height p-r)⁻¹)) ^ (3 : ℝ) *
        Measure.hausdorffMeasure 3 s)

theorem positive : arena.Law actual := local_hausdorff_comparison

theorem negative : ¬ arena.Law rejected := by
  intro h
  let p : UpperHalfSpace ℂ := ⟨WithLp.toLp 2 (0, (1 : ℝ)), by norm_num⟩
  exact (h p (1/2) (by norm_num) (by norm_num [p, height]) ∅ (by simp)).1

/-- Change one comparison while preserving the other comparison on every state. -/
def rejectedAt (i : Bool) : Realization signature :=
  realize signature (fun j _ a b => if j = i then False else a ≤ b)
    (fun e => nomatch e)

theorem negativeAt (i : Bool) : ¬ arena.Law (rejectedAt i) := by
  intro h
  let p : UpperHalfSpace ℂ := ⟨WithLp.toLp 2 (0, (1 : ℝ)), by norm_num⟩
  have hh := h p (1/2) (by norm_num) (by norm_num [p, height]) ∅ (by simp)
  cases i with
  | false => simpa [rejectedAt, realize] using hh.1
  | true => simpa [rejectedAt, realize] using hh.2

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℝ≥0∞) ≤ 0) = ((1 : ℝ≥0∞) ≤ 0) at he
  have hz : (0 : ℝ≥0∞) ≤ 0 := le_rfl
  have hn : (1 : ℝ≥0∞) ≤ 0 := he ▸ hz
  norm_num at hn

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.HyperbolicHausdorffComparison.local_hausdorff_comparison)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, rfl, negativeAt i⟩
      intro j hji
      funext p a b
      simp [actual, rejectedAt, realize, hji]
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.HyperbolicHausdorffComparison.local_hausdorff_comparison)
    (type_of% (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Geometry.HyperbolicHausdorffComparison.local_hausdorff_comparison
    "Reg.D5.S3.Geometry.HyperbolicHausdorffComparison/Reg.D5.S3.Geometry.HyperbolicHausdorffComparison.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Geometry.HyperbolicHausdorffComparison.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.HyperbolicHausdorffComparison, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end Reg.D5.S3.Geometry.HyperbolicHausdorffComparison
