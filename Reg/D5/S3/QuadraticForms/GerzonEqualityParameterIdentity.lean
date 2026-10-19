import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.GerzonEqualityParameterIdentity
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
namespace Reg.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity
open _root_.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false
noncomputable section
universe u_2 u_3

namespace Gram

abbrev signature : Signature where
  Params := Σ F : Type u_2, F
  State p := p.1 → ℕ → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_2} :=
  realize signature.{u_2} (fun _ p power => power p.2 2) (fun e => nomatch e)

def rejected : Realization signature.{u_2} :=
  realize signature.{u_2} (fun _ p power => power p.2 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_2}
  Law R := ∀ {F : Type u_2} {S : Type u_3} [Field F] [AddCommGroup S] [Module F S]
    {n : ℕ} (K : LinearMap.BilinForm F S) (P : Fin n → S) (a b : F)
    (_hgram : ∀ i j, K (P i) (P j) = if i = j then a ^ 2 else b)
    (t : Fin n → F) (j : Fin n),
    K (∑ i, t i • P i) (P j) =
      (R.readout () ⟨F, a⟩ (@HPow.hPow F ℕ F inferInstance) - b) * t j + b * ∑ i, t i

theorem rejected_law : ¬ arena.{u_2,u_3}.Law rejected := by
  intro h
  let F := ULift.{u_2} ℚ
  let S := ULift.{u_3} PUnit
  have he := h (F := F) (S := S) (n := 1) 0 (fun _ => 0) 0 0
    (by intro i j; change (0 : F) = if i = j then 0 ^ 2 else 0; split_ifs <;> norm_num) (fun _ => 1) 0
  change (0 : F) = (0 ^ 0 - 0) * 1 + 0 * ∑ _ : Fin 1, (1 : F) at he
  norm_num at he

def source_registration : Registration arena.{u_2,u_3} (type_of% @_root_.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity.gram_pair_sum.{u_2,u_3}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.{u_2,u_3}.Law actual from (@_root_.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity.gram_pair_sum.{u_2,u_3}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u_2} ℚ, ⟨0⟩⟩, (fun _ _ => ⟨0⟩), (fun _ _ => ⟨1⟩), ?_⟩
    intro h
    have he := congrArg ULift.down h
    change (0 : ℚ) = 1 at he
    norm_num at he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity.gram_pair_sum.{u_2,u_3}) (Realization signature.{u_2}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity.Gram.unit
  realizationName := `Reg.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity.Gram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_2,u_3}⟩
  objectArena := .source ⟨arena.{u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_2,u_3} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_2} (fun _ p power => power p.2 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.GerzonEqualityParameterIdentity
    definition := none
    coordinates := #[0, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Gram

end
end Reg.D5.S3.QuadraticForms.GerzonEqualityParameterIdentity
