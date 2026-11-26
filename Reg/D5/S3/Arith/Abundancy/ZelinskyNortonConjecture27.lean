import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27
import Reg.Support.SingleDependentReadout

/-! A source family retaining the full eventual first-difference assertion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6 (aAlpha)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α : ℝ), 1 < α → ∀ (C : ℝ), 0 < C → ∀ᶠ n : ℕ in atTop,
    R.readout () () ((aAlpha α n : ℝ) + C) (aAlpha α (n + 1) : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn⟩ := (h 2 (by norm_num) 1 (by norm_num)).exists
  exact hn

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh := congrFun he (1 : ℝ)
  change ((0 : ℝ) < 1) = ((1 : ℝ) < 1) at hh
  have hbad : (1 : ℝ) < 1 := Eq.mp hh (by norm_num)
  exact (lt_irrefl 1) hbad

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27
