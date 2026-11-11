import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Rounding
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope source-family audit attempts for the mathematical target. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Rounding
open _root_.D5.S3.Combinatorics.Circle.SparseNecklaceRounding

abbrev signature : Signature where
  Params := Type u
  State α := List (RoundBlock α)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := List α × List α
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ bs => (plusWord bs,minusWord bs)) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ bs => (plusWord bs ++ plusWord bs,minusWord bs)) (fun e => nomatch e)

/-- All type, function, rational, list and hypothesis binders are retained.
Only the two rounded word outputs are observed. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [DecidableEq α]
    (f g : α → ℚ) (H N x y : ℚ) (bs : List (RoundBlock α)),
    FractionalFits f g H N x y bs → (plusWord bs).Nodup →
    RoundingConclusion f g H N x y bs
      (R.readout () α bs).1 (R.readout () α bs).2

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let i : ULift.{u} Unit := ⟨()⟩
  have hh := h (fun _ : ULift.{u} Unit => (0 : ℚ)) (fun _ => (0 : ℚ))
    0 0 0 0 [RoundBlock.one i]
    (by norm_num [FractionalFits,Rectangle]) (by simp [plusWord])
  have hl := hh.1.length_eq
  norm_num [rejected,realize,plusWord,minusWord] at hl

private theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨ULift.{u} Unit,[],[RoundBlock.one ⟨()⟩],?_⟩
  intro he
  have hl := congrArg (fun w => w.1.length) he
  norm_num [actual,realize,plusWord,minusWord] at hl

/-- Typed dependent-family evidence attempt. This is not a four-slot Contract
registration: native sourceSelection paths, enrolled readout checking and
current compiler binding evidence remain to be supplied at integration. -/
def source_registration : Registration arena.{u} (type_of% (@simultaneous_rounding.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨simultaneous_rounding,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := actual_dependence

/-- The full dependent source law is proved above. Exact compiler source
occurrence selection is still absent, so this typed attempt does not claim a
validated four-slot binding. -/
noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@simultaneous_rounding.{u}) (type_of% (realize signature.{u} (fun _ _ bs => (plusWord bs, minusWord bs)) (fun e => nomatch e))) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Rounding.simultaneous_rounding.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Rounding.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ bs => (plusWord bs, minusWord bs)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Rounding
