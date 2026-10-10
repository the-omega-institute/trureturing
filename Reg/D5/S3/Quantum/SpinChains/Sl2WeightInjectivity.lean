import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.Sl2WeightInjectivity
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.Sl2WeightInjectivity

attribute [local instance] LieRing.ofAssociativeRing

namespace Reg.D5.S3.Quantum.SpinChains.Sl2WeightInjectivity

universe u_1 u_2

abbrev signature : Signature where
  Params := Type u_2
  State p := p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_2} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{u_2} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_2}
  Law R := ∀ {K : Type u_1} [Field K] [CharZero K]
    {V : Type u_2} [AddCommGroup V] [Module K V]
    {h e f : Module.End K V} (_t : IsSl2Triple h e f) (n : ℕ),
    ∀ (v : V) (q k : ℕ), h v = (q : K) • v → k ≤ q →
      (e ^ n) v = 0 → (f ^ k) v = 0 → R.readout () V v 0

theorem rejected_law : ¬ arena.{u_1, u_2}.Law rejected := by
  intro law
  let K := ULift.{u_1} ℚ
  let V := ULift.{u_2} (ℚ × ℚ)
  let : CharZero K := ⟨fun m n eq =>
    (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))
      (congrArg ULift.down eq)⟩
  let h : Module.End K V := {
    toFun v := ⟨(v.down.1, -v.down.2)⟩
    map_add' x y := by
      apply ULift.ext
      change (x.down.1 + y.down.1, -(x.down.2 + y.down.2)) =
        (x.down.1 + y.down.1, -x.down.2 + -y.down.2)
      simp [add_comm]
    map_smul' c x := by
      apply ULift.ext
      change (c.down * x.down.1, -(c.down * x.down.2)) =
        (c.down * x.down.1, c.down * -x.down.2)
      simp }
  let e : Module.End K V := {
    toFun v := ⟨(v.down.2, 0)⟩
    map_add' x y := by
      apply ULift.ext
      change (x.down.2 + y.down.2, (0 : ℚ)) = (x.down.2 + y.down.2, 0 + 0)
      simp
    map_smul' c x := by
      apply ULift.ext
      change (c.down * x.down.2, (0 : ℚ)) = (c.down * x.down.2, c.down * 0)
      simp }
  let f : Module.End K V := {
    toFun v := ⟨(0, v.down.1)⟩
    map_add' x y := by
      apply ULift.ext
      change ((0 : ℚ), x.down.1 + y.down.1) = (0 + 0, x.down.1 + y.down.1)
      simp
    map_smul' c x := by
      apply ULift.ext
      change ((0 : ℚ), c.down * x.down.1) = (c.down * 0, c.down * x.down.1)
      simp }
  have triple : IsSl2Triple h e f := by
    constructor
    · intro hz
      have he := congrArg (fun a : Module.End K V => (a ⟨(1, 0)⟩).down.1) hz
      norm_num [h] at he
    · apply LinearMap.ext
      intro v
      apply ULift.ext
      change (v.down.1 - 0, 0 - v.down.2) = (v.down.1, -v.down.2)
      simp
    · apply LinearMap.ext
      intro v
      apply ULift.ext
      rw [two_smul]
      change (v.down.2 - -v.down.2, (0 : ℚ) - 0) = (v.down.2 + v.down.2, 0 + 0)
      simp
    · apply LinearMap.ext
      intro v
      apply ULift.ext
      rw [two_smul]
      change ((0 : ℚ) - 0, -v.down.1 - v.down.1) = (-(0 + 0), -(v.down.1 + v.down.1))
      simp [sub_eq_add_neg]
  exact law triple 0 0 0 0 (by simp) (by omega) (by simp) (by simp)

def family : Registration arena.{u_1, u_2} (type_of% @lowering_kernel_zero.{u_1, u_2}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lowering_kernel_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u_2} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro he
    have hp := congrFun he (ULift.up false)
    change (ULift.up false = ULift.up false) = (ULift.up true = ULift.up false) at hp
    have impossible : (ULift.up true : ULift.{u_2} Bool) = ULift.up false := hp ▸ rfl
    cases impossible

def registration : Contract.Registration.{_, _, _, 0, 0, 0, u_2 + 1, u_2, 0, u_2, 0, 0}
    (@lowering_kernel_zero.{u_1, u_2}) (Realization signature.{u_2}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightInjectivity.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightInjectivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1, u_2}⟩
  objectArena := .source ⟨arena.{u_1, u_2}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u_1, u_2} ⟨family.{u_1, u_2}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature.{u_2} actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightInjectivity
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.SpinChains.Sl2WeightInjectivity
