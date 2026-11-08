import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.Symbolic.SurjectiveWordBalance

/-! The local-rule readout over the complete finite-word balance family. -/

set_option autoImplicit false
noncomputable section
universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.SurjectiveWordBalance
open _root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift
open Function

namespace Reg.D5.S1.Dynamics.Symbolic.SurjectiveWordBalance

abbrev Inputs := Σ A : Type u, Σ k : ℕ, Σ _h : (Fin (k + 2) → A) → A,
  Σ n : ℕ, Fin n → A

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := Fin (P.2.1 + 2) → P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P => P.2.2.1) (fun e => Empty.elim e)

def constantTarget : Realization signature.{u} :=
  realize signature (fun _ P x =>
    if hn : 0 < P.2.2.2.1 then P.2.2.2.2 ⟨0, hn⟩ else P.2.2.1 x)
    (fun e => Empty.elim e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [Finite A] (k : ℕ)
    (h : (Fin (k + 2) → A) → A) (_hsurj : Surjective (code h))
    (n : ℕ) (w : Fin n → A),
    Nat.card {p : Fin (n + k + 1) → A //
      ∀ i : Fin n, R.readout () ⟨A, k, h, n, w⟩
        (fun j : Fin (k + 2) => p ⟨i.val + j.val, by omega⟩) = w i} =
          (Nat.card A) ^ (k + 1)

private theorem projection_surjective {A : Type u} :
    Surjective (code (k := 0) (fun b : Fin 2 → A => b 0)) := by
  intro y
  refine ⟨y, ?_⟩
  funext i
  change y (i + (0 : ℕ)) = y i
  simp

private theorem constant_rejected : ¬ arena.{u}.Law constantTarget := by
  intro hlaw
  have hc := @hlaw (ULift.{u} Bool) inferInstance 0 (fun b => b 0)
    projection_surjective 1 (fun _ => ⟨false⟩)
  norm_num [constantTarget, realize, Nat.card_eq_fintype_card,
    Fintype.card_fun] at hc

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let P : Inputs.{u} := ⟨ULift.{u} Bool, 0, (fun b => b 0), 1, fun _ => ⟨false⟩⟩
  refine ⟨P, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  intro he
  change (ULift.up false : ULift.{u} Bool) = ULift.up true at he
  cases he

def family : Registration arena.{u}
    (type_of% (@surjective_word_balance.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@surjective_word_balance.{u}, constantTarget, constant_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨constantTarget, ?_, rfl, constant_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@surjective_word_balance.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.SurjectiveWordBalance.balance
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.SurjectiveWordBalance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ P => P.2.2.1) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.SurjectiveWordBalance
    definition := none
    coordinates := #[0, 2, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Symbolic.SurjectiveWordBalance
