import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence

/-! Source-bound observations of the original four public statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence

namespace Norm

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℝ → ℂ} (hf : MemLp f 2 halfLineMeasure)
    {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re),
    R.readout () () (halfLineMellin f s) ≤
      ‖hf.toLp f‖ / Real.sqrt (2 * s.re + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : ℝ → ℂ := fun _ => 0
  have hf : MemLp f 2 halfLineMeasure := by
    simp [f]
  have hh := h hf (s := 0) (by norm_num)
  simp [rejected, realize, f, halfLineMellin] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@halfLineMellin_norm_le)) where
  actual := actual
  bridge := by
    constructor
    · intro h
      intro f hf s hs
      simpa [actual, realize] using h hf hs
    · intro h
      intro f hf s hs
      simpa [actual, realize] using h hf hs
  variation := ⟨halfLineMellin_norm_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@halfLineMellin_norm_le) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.halfLineMellin_norm_le.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.Norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Norm

namespace Differentiable

abbrev signature : Signature where
  Params := ℂ
  State _ := ℂ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s g => DifferentiableAt ℂ g s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℝ → ℂ} (hf : MemLp f 2 halfLineMeasure)
    {s : ℂ} (_hs : -(1 / 2 : ℝ) < s.re), R.readout () s (halfLineMellin f)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf : MemLp (fun _ : ℝ => (0 : ℂ)) 2 halfLineMeasure := MemLp.zero'
  have hh := h hf (s := 0) (by norm_num)
  simpa [rejected, realize] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z⁻¹), ?_⟩
  intro hb
  have he : DifferentiableAt ℂ (fun _ : ℂ => (0 : ℂ)) 0 =
      DifferentiableAt ℂ (fun z : ℂ => z⁻¹) 0 := by
    simpa [actual, realize] using hb
  have hzero : DifferentiableAt ℂ (fun _ : ℂ => (0 : ℂ)) 0 := differentiableAt_const 0
  have hinv := Eq.mp he hzero
  exact (differentiableAt_inv_iff.mp hinv) rfl

def family : Registration arena (type_of% (@halfLineMellin_differentiableAt)) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize]
  variation := ⟨by
    simpa only [arena, actual, realize] using @halfLineMellin_differentiableAt,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@halfLineMellin_differentiableAt) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.halfLineMellin_differentiableAt.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.Differentiable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := by
    exact some (realize signature (fun _ s g => DifferentiableAt ℂ g s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Differentiable

namespace Analytic

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ g => AnalyticOnNhd ℂ g
    {s : ℂ | -(1 / 2 : ℝ) < s.re}) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℝ → ℂ} (_hf : MemLp f 2 halfLineMeasure),
    R.readout () () (halfLineMellin f)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf : MemLp (fun _ : ℝ => (0 : ℂ)) 2 halfLineMeasure := MemLp.zero'
  have hh := h hf
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z⁻¹), ?_⟩
  intro hb
  have he : (AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ))
      {s : ℂ | -(1 / 2 : ℝ) < s.re} ↔
      AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) {s : ℂ | -(1 / 2 : ℝ) < s.re}) := by
    simpa [actual, realize] using hb
  have hinv : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) {s : ℂ | -(1 / 2 : ℝ) < s.re} :=
    he.mp analyticOnNhd_const
  have hd := (hinv 0 (by norm_num)).differentiableAt
  exact (differentiableAt_inv_iff.mp hd) rfl

def family : Registration arena (type_of% (@halfLineMellin_analyticOnNhd)) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize]
  variation := ⟨by
    simpa only [arena, actual, realize] using @halfLineMellin_analyticOnNhd,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@halfLineMellin_analyticOnNhd) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.halfLineMellin_analyticOnNhd.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.Analytic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := by
    exact some (realize signature (fun _ _ g => AnalyticOnNhd ℂ g
      {s : ℂ | -(1 / 2 : ℝ) < s.re}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Analytic

namespace Mobius

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => MemLp f 2 (volume.restrict (Ioi (1 : ℝ))))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ R.readout () () mobiusPartialSum

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h trivial

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℝ)), mobiusPartialSum, ?_⟩
  intro hb
  have he : MemLp (fun _ : ℝ => (0 : ℝ)) 2 (volume.restrict (Ioi (1 : ℝ))) =
      MemLp mobiusPartialSum 2 (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [actual, realize] using hb
  have hm := Eq.mp he MemLp.zero'
  exact mobiusPartialSum_not_memLp hm

def family : Registration arena (type_of% (@mobiusPartialSum_not_memLp)) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize]
  variation := ⟨by
    simpa only [arena, actual, realize] using @mobiusPartialSum_not_memLp,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mobiusPartialSum_not_memLp) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.mobiusPartialSum_not_memLp.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.Mobius.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := by
    exact some (realize signature (fun _ _ f => MemLp f 2
      (volume.restrict (Ioi (1 : ℝ)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Mobius

end Reg.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
