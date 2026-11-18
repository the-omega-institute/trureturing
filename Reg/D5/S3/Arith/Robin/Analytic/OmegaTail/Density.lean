import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Density
import Reg.Support.SingleDependentReadout

/-! Exact source families for normalized selection density integrals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real MeasureTheory Set LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Density

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Density

namespace Range

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => Set ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Ioo (0 : ℝ) x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (∅ : Set ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s u : ℝ}, 1 < s → 0 < u → q s u ∈ R.readout () () 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (u := 1) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @q_range) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@q_range, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 / 2 : ℝ), ?_⟩
    intro he
    have hhalf : (1 / 4 : ℝ) ∈ actual.readout i () (1 / 2) := by
      change (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2)
      norm_num
    have hbad : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 0 :=
      Eq.mpr (congrArg (fun U : Set ℝ => (1 / 4 : ℝ) ∈ U) he) hhalf
    norm_num at hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_range) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density.q_range.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Density.Range.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Range

namespace Continuity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f U => ContinuousOn f U) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → R.readout () () (q s) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (by norm_num)

def family : Registration arena (type_of% @q_continuous) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@q_continuous, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), Real.log, (fun _ : ℝ => 0), ?_⟩
    intro he
    have hlog : ContinuousOn Real.log univ := Eq.mpr (congrFun he univ) continuousOn_const
    have hc : ContinuousAt Real.log 0 := (continuousOn_univ.mp hlog).continuousAt
    exact (continuousAt_log_iff.mp hc) rfl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_continuous) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density.q_continuous.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Density.Continuity.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density
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

end Continuity

namespace Mass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → IntegrableOn (q s) (Ioi 0) ∧
    R.readout () () (∫ u in Ioi (0 : ℝ), q s u) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (s := 2) (by norm_num)).2

def family : Registration arena (type_of% @q_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@q_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_mass) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density.q_mass.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Density.Mass.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Mass

namespace LogMoment

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → IntegrableOn (fun u : ℝ => q s u * log u) (Ioi 0) ∧
    R.readout () () (∫ u in Ioi (0 : ℝ), q s u * log u)
      (log (a s) - (π / s) * cos (π / s) / sin (π / s))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (s := 2) (by norm_num)).2

def family : Registration arena (type_of% @q_log_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@q_log_moment, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_log_moment) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density.q_log_moment.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Density.LogMoment.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LogMoment

namespace Entropy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → IntegrableOn (fun u : ℝ => binEntropy (q s u)) (Ioi 0) ∧
    R.readout () () (∫ u in Ioi (0 : ℝ), binEntropy (q s u))
      (s - π * cos (π / s) / sin (π / s))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (s := 2) (by norm_num)).2

def family : Registration arena (type_of% @q_entropy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@q_entropy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_entropy) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density.q_entropy.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Density.Entropy.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Density
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Entropy

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Density
