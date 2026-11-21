import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees
import Reg.Support.DependentFamily

/-! The quotient degree order constrains the right-hand side read by the integer fibers. -/

namespace Reg.D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees

open _root_.D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

noncomputable section

abbrev signature : Signature where
  Params := Type u
  State I := I → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := I → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R :=
    ∀ {I : Type u} {J : Type v} [Finite J] (A : (J → ℤ) →+ (I → ℤ)) (w : I → ℤ)
      (p : J → ℤ) (B : ℕ) (_hB : 0 < B) (_hp : ∀ j, 0 < p j) (_hpA : A p = B • w),
      let q : (I → ℤ) ⧸ A.range := QuotientAddGroup.mk w
      let h := addOrderOf q
      0 < h ∧ (∀ N ∈ countedDegrees A (R.readout () I w), h ∣ N) ∧
        ∃ b r : ℕ, B = h * b ∧ b ≤ r ∧ 0 < r ∧
          h * r ∈ countedDegrees A w ∧ h * (r + 1) ∈ countedDegrees A w ∧
          ∀ t ≥ (b - 1) * r, h * t ∈ countedDegrees A w

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro altered
  let I := PUnit.{u+1}
  let J := PUnit.{v+1}
  let A : (J → ℤ) →+ (I → ℤ) := {
    toFun := fun v _ => 2 * v PUnit.unit
    map_zero' := by funext i; simp
    map_add' := by intro a b; funext i; exact mul_add _ _ _ }
  let w (_ : I) : ℤ := 1
  let p (_ : J) : ℤ := 1
  have hA : A p = (2 : ℕ) • w := by funext i; rfl
  have alt := altered A w p 2 (by decide) (fun _ => Int.zero_lt_one) hA
  have zeroMem : (1 : ℕ) ∈ countedDegrees A (rejected.readout () I w) :=
    ⟨0, fun _ => le_rfl, by change A 0 = (1 : ℕ) • (0 : I → ℤ); simp⟩
  have dvd := alt.2.1 1 zeroMem
  have annihilated := (addOrderOf_dvd_iff_nsmul_eq_zero).mp dvd
  rw [one_nsmul, QuotientAddGroup.eq_zero_iff] at annihilated
  obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp annihilated
  have bad := congrFun hv PUnit.unit
  change (2 : ℤ) * v PUnit.unit = 1 at bad
  omega

def family : Registration arena.{u,v} (type_of% (@eventual_counts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventual_counts, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{u+1}, fun _ => 0, fun _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun equal PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_counts) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees.fiberDegreeOrder
  realizationName := `Reg.D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg", "body", "domain", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees
