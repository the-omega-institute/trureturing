import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference
import Reg.Support.SingleDependentReadout

/-! A source family for the equality inside the refuted first-difference claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.BeriZelinskyQuestion6 (a)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ m : ℕ, 0 < m → ∃ n ≥ 1,
    R.readout () () (a (n + 1) - a n) m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro m hm
  exact ⟨1, le_rfl, trivial⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hh := congrFun he (0 : ℕ)
  change ((0 : ℕ) = 0) = ((1 : ℕ) = 0) at hh
  have hbad : (1 : ℕ) = 0 := Eq.mp hh rfl
  omega

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference
    definition := some {
      owner := `D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference
      name := `D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Abundancy.ZelinskyNortonFirstDifference
