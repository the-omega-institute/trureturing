import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
import Reg.Support.SingleDependentReadout

/-! Source families for Norton endpoint localization and adjacent cancellation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open _root_.D5.S3.Arith.OmegaGreedyPermutation (prime)
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
  (aAlpha a KS result norton_endpoint_bounds norton_adjacent_cancellation)

namespace Reg.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh := congrFun he (0 : ℝ)
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
  norm_num at hbad

namespace Endpoint

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected (i : Bool) : Realization signature :=
  realize signature (fun j _ x y => if j = i then False else x ≤ y)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α : ℝ), 1 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      R.readout false () (c * (prime (n - 1) : ℝ) ^ α)
          (prime (n - 1 + aAlpha α n - 1) : ℝ) ∧
        R.readout true () (prime (n - 1 + aAlpha α n - 1) : ℝ)
          (C * (prime (n - 1) : ℝ) ^ α)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  obtain ⟨c, C, hc, hC, hfalse⟩ := h 2 (by norm_num)
  obtain ⟨n, hn⟩ := hfalse.exists
  cases i
  · exact hn.1
  · exact hn.2

def family : Registration arena (type_of% @norton_endpoint_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@norton_endpoint_bounds, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p x y
      simp [rejected, actual, realize, hj]
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℝ)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norton_endpoint_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.BeriZelinskyQuestion6.norton_endpoint_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6.Endpoint.family
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
    owner := `D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg",
        "fn", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg",
        "fn", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

namespace Adjacent

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α : ℝ), 1 < α → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    R.readout () () (c * (prime (n - 1) : ℝ) ^ (α - 1))
      ((aAlpha α (n + 1) : ℝ) - aAlpha α n + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc, hfalse⟩ := h 2 (by norm_num)
  obtain ⟨n, hn⟩ := hfalse.exists
  exact hn

def family : Registration arena (type_of% @norton_adjacent_cancellation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@norton_adjacent_cancellation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norton_adjacent_cancellation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.BeriZelinskyQuestion6.norton_adjacent_cancellation.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6.Adjacent.family
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
    owner := `D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Adjacent
namespace Limit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℤ)
    (fun _ => Filter ℕ → Filter ℤ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (fun n : ℕ => (a n : ℤ) - KS n) atTop atTop

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (fun n : ℕ => (n : ℤ)), (fun _ : ℕ => (0 : ℤ)), ?_⟩
    intro he
    have hh := congrFun (congrFun he (atTop : Filter ℕ)) (atTop : Filter ℤ)
    have hcast : Tendsto (fun n : ℕ => (n : ℤ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hconst : Tendsto (fun _ : ℕ => (0 : ℤ)) atTop atTop := Eq.mp hh hcast
    exact not_tendsto_const_atTop (0 : ℤ) (atTop : Filter ℕ) hconst

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.BeriZelinskyQuestion6.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6.Limit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit
end Reg.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
