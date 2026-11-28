import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.WisemanA261041
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Partitions.WisemanA261041

open _root_.D5.S3.Combinatorics.Partitions.WisemanA261041
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => Nat.card (Left n)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, r.readout () () n = Nat.card (Right n)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem right_zero : Nat.card (Right 0) = 1 := by
  let : Nonempty (Right 0) := ⟨⟨Setoid.ker (fun _ : Fin 1 => ()), fun i hi => by omega⟩⟩
  let : Subsingleton (Right 0) := ⟨fun s t => by
    apply Subtype.ext
    apply Setoid.ext
    intro i j
    have h : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    subst j
    exact iff_of_true (s.val.iseqv.refl i) (t.val.iseqv.refl i)⟩
  exact Nat.card_unique

private theorem right_one : 1 < Nat.card (Right 1) := by
  classical
  let view (s : Right 1) (i j : Fin 2) := decide (s.val i j)
  have faithful : Function.Injective view := by
    intro s t h
    apply Subtype.ext
    apply Setoid.ext
    intro i j
    simpa only [view, decide_eq_decide] using congrFun (congrFun h i) j
  let : Finite (Right 1) := Finite.of_injective view faithful
  refine Finite.one_lt_card_iff_nontrivial.mpr ⟨
    ⟨Setoid.ker (fun i : Fin 2 => i), fun i hi => by omega⟩,
    ⟨Setoid.ker (fun _ : Fin 2 => ()), fun i hi => by omega⟩, ?_⟩
  intro h
  have hSetoid : Setoid.ker (fun i : Fin 2 => i) = Setoid.ker (fun _ : Fin 2 => ()) :=
    congrArg Subtype.val h
  have h' : (0 : Fin 2) = 1 := by
    change (Setoid.ker (fun i : Fin 2 => i)) 0 1
    rw [hSetoid]
    rfl
  exact (by decide : (0 : Fin 2) ≠ 1) h'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : 0 = Nat.card (Right 0) := h 0
  rw [right_zero] at h0
  exact Nat.zero_ne_one h0

def sourceRegistration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Nat.card (Left 0) ≠ Nat.card (Left 1)
    rw [result 0, result 1, right_zero]
    exact ne_of_lt right_one

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Partitions.WisemanA261041.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.WisemanA261041.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => Nat.card (Left n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.WisemanA261041
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.Partitions.WisemanA261041
