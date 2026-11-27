import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.SignedContactJacobian
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.ULift

/-! Source-bound observation of interior motion in the homogeneous contact kernel. -/

namespace Reg.D5.S3.QuadraticForms.SignedContactJacobian

open Matrix LeanInformationAudit
open _root_.D5.S3.QuadraticForms.SignedContactJacobian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix

noncomputable section
universe u um un uk

abbrev signature : Signature where
  Params := Σ _ : Type u, Type uk
  State p := p.2 → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2 → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, uk} :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

def rejected : Realization signature.{u, uk} :=
  realize signature (fun _ _ v => Classical.choice ⟨v⟩) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, uk}
  Law r := ∀ {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {m : Type um} {n : Type un} {k : Type uk}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]
    (contact : Matrix m n R) (tangent : Matrix m k R)
    (weight curvature factor : k → R),
    (∀ i, curvature i ≠ 0) → (∀ i, 0 < factor i) →
    (∀ i, weight i = -(factor i * curvature i)) →
    ∀ (a : n → R) (y : m → R) (v : k → R),
    (contact *ᵥ a + tangent *ᵥ (diagonal weight *ᵥ v) = 0 ∧
      contactᵀ *ᵥ y = 0 ∧ tangentᵀ *ᵥ y + diagonal curvature *ᵥ v = 0) ↔
      contact *ᵥ a = 0 ∧ contactᵀ *ᵥ y = 0 ∧ tangentᵀ *ᵥ y = 0 ∧
        r.readout () ⟨R, k⟩ v = 0

private theorem rejected_law : ¬ arena.{u, um, un, uk}.Law rejected.{u, uk} := by
  intro h
  let R := ULift.{u} ℤ
  let : LinearOrder R := LinearOrder.lift' ULift.down ULift.down_injective
  let : IsStrictOrderedRing R :=
    Function.Injective.isStrictOrderedRing ULift.down rfl rfl (fun _ _ => rfl)
      (fun _ _ => rfl) Iff.rfl Iff.rfl
  let m := ULift.{um} Unit
  let n := ULift.{un} Unit
  let k := ULift.{uk} Unit
  have hAt := h (R := R) (m := m) (n := n) (k := k) 0 0
    (fun _ => -1) (fun _ => 1) (fun _ => 1)
    (fun _ => one_ne_zero) (fun _ => zero_lt_one) (fun _ => by rw [one_mul]) 0 0
  have hzero := (hAt 0).mp ⟨by simp, by simp, by simp⟩
  have hread : rejected.readout () ⟨R, k⟩ 1 = 0 := hzero.2.2.2
  have hbad := (hAt 1).mpr ⟨by simp, by simp, by simp, hread⟩
  have hrow := congrFun hbad.2.2 (ULift.up () : k)
  exact one_ne_zero (by simpa only [transpose_zero, zero_mulVec, Pi.add_apply,
    Pi.zero_apply, zero_add, mulVec_diagonal, Pi.one_apply, mul_one] using hrow)

private theorem dependence : ObservationalDependence signature.{u, uk} actual := by
  intro i
  let R := ULift.{u} ℤ
  let k := ULift.{uk} Unit
  refine ⟨⟨R, k⟩, 0, 1, ?_⟩
  intro h
  exact zero_ne_one (congrFun h (ULift.up () : k))

def sourceRegistration : Registration arena.{u, um, un, uk} (type_of% @kernel_iff.{u, um, un, uk}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_iff.{u, um, un, uk}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kernel_iff.{u, um, un, uk}) (Realization signature.{u, uk}) Unit Unit := {
  unitName := .str `D5.S3.QuadraticForms.SignedContactJacobian.kernel_iff "__information_unit"
  realizationName := `Reg.D5.S3.QuadraticForms.SignedContactJacobian.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, um, un, uk}⟩
  objectArena := .source ⟨arena.{u, um, un, uk}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, um, un, uk} ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u, uk} (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SignedContactJacobian
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #[ "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg",
        "fn", "arg"]
      stateBinder := 21
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.QuadraticForms.SignedContactJacobian
