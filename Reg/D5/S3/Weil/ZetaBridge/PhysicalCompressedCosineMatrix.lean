import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.PhysicalCompressedCosineMatrix
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.ZetaBridge.PhysicalCompressedCosineMatrix

open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Four unrestricted real parameters and the original integration variable. -/
abbrev signature : Signature where
  Params := (a : ℝ) × (s : ℝ) × (u : ℝ) × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p x => Real.cos (p.2.2.1 * x) * Real.cos (p.2.2.2 * (x + p.2.1)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original oriented-integral law, including reversed endpoints
and both zero-frequency resonances. -/
def arena : Arena where
  signature := signature
  Law R := ∀ a s u v : ℝ,
    (∫ x in (-a)..(a - s), R.readout () ⟨a, s, u, v⟩ x) =
      Real.cos ((u + v) * s / 2) *
        _root_.PhysicalCompressedCosineMatrix.S ((2 * a - s) / 2) (u - v) +
      Real.cos ((u - v) * s / 2) *
        _root_.PhysicalCompressedCosineMatrix.S ((2 * a - s) / 2) (u + v)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 0 0 0
  norm_num [rejected, realize, _root_.PhysicalCompressedCosineMatrix.S] at hz

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0, 1, 0⟩, 0, Real.pi, ?_⟩
  norm_num [actual, realize]

def family : Registration arena
    (type_of% (@_root_.PhysicalCompressedCosineMatrix.integral_cos_product_overlap)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.PhysicalCompressedCosineMatrix.integral_cos_product_overlap,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      have hrole : j = i := by
        change Unit at j i
        exact Subsingleton.elim j i
      exact (hji hrole).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.PhysicalCompressedCosineMatrix.integral_cos_product_overlap)
    (type_of% (realize signature
      (fun _ p x => Real.cos (p.2.2.1 * x) * Real.cos (p.2.2.2 * (x + p.2.1)))
      (fun e => nomatch e))) Type Unit where
  unitName := `PhysicalCompressedCosineMatrix.integral_cos_product_overlap.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PhysicalCompressedCosineMatrix.family
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
    (fun _ p x => Real.cos (p.2.2.1 * x) * Real.cos (p.2.2.2 * (x + p.2.1)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PhysicalCompressedCosineMatrix
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg",
        "fn", "fn", "fn", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Weil.ZetaBridge.PhysicalCompressedCosineMatrix
