import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation
import Reg.Support.SingleDependentReadout

/-! Exact compact-profile source family with its mass equality readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real MeasureTheory Set LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s epsilon : ℝ}, 1 < s → 0 < epsilon →
    ∃ (A B : ℝ) (g : ℝ → ℝ),
      0 < A ∧ A < B ∧ ContinuousOn g (Icc A B) ∧
      (∀ u ∈ Icc A B, g u ∈ Ioo 0 1) ∧
      R.readout () () (∫ u in Ioc A B, g u) 1 ∧
      |(∫ u in Ioc A B, g u * log u) -
        (log (a s) - (π / s) * cos (π / s) / sin (π / s))| < epsilon ∧
      s - π * cos (π / s) / sin (π / s) - epsilon <
        ∫ u in Ioc A B, binEntropy (g u)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, B, g, hA, hAB, hg, hgr, hmass, hlog, hent⟩ :=
    h (s := 2) (epsilon := 1) (by norm_num) (by norm_num)
  exact hmass

def family : Registration arena (type_of% @compact_profile) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compact_profile, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compact_profile) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation.compact_profile.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Truncation
