import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section
universe u v
namespace Reg.D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel

structure Parameters where
  C : Type u
  ringC : CommRing C
  B : Type v
  groupB : AddCommGroup B
  x : C
  lam : letI := ringC; letI := groupB; C →+ B
  k : ℕ
  hk : 2 ≤ k
  h : ℕ
  other : List Bool

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State _ := List Bool
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actualPred (role : Bool) (p : Parameters.{u,v}) (w : List Bool) : Prop :=
  letI := p.ringC
  letI := p.groupB
  if role then
    match (scanner p.k (by have := p.hk; omega)).eval w,
      (scanner p.k (by have := p.hk; omega)).eval p.other with
    | none, none => True
    | some s, some t => SignatureEq (fun n => p.lam (p.x ^ n)) p.k p.h
        (p.lam (polynomialValue p.x w)) w.length s
        (p.lam (polynomialValue p.x p.other)) p.other.length t
    | _, _ => False
  else NativeKernel p.x p.lam p.k p.h w p.other

def actual : Realization signature.{u,v} :=
  realize signature actualPred (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ p w, R.readout false p w ↔ R.readout true p w

private theorem actual_law : arena.{u,v}.Law actual := by
  intro p w
  letI := p.ringC
  letI := p.groupB
  exact actual_history_kernel_signature p.x p.lam p.k p.hk p.h w p.other

def intervention (i : Bool) : Realization signature.{u,v} :=
  realize signature (fun j p w => if j = i then ¬ actualPred j p w else actualPred j p w)
    (fun e => nomatch e)

def zeroParameters : Parameters.{u,v} where
  C := ULift.{u} ℤ
  ringC := inferInstance
  B := ULift.{v} ℤ
  groupB := inferInstance
  x := 0
  lam := 0
  k := 2
  hk := by decide
  h := 0
  other := []

private theorem accepted_empty : actual.readout false zeroParameters ([] : List Bool) := by
  intro a ha
  have he : a = [] := List.length_eq_zero_iff.mp (by simpa using ha)
  subst a
  rfl

private theorem rejected_history :
    ¬ actual.readout false zeroParameters [true, true] := by
  intro he
  have hh := he [] (by simp)
  norm_num [nativeReadout, polynomialValue, D5.S0.Tower.DBonacci.Names.DBonacciAdmissible,
    D5.S0.Tower.DBonacci.Names.runAdmissible] at hh

private theorem intervention_breaks (i : Bool) : ¬ arena.{u,v}.Law (intervention i) := by
  intro h
  have he := h zeroParameters []
  have ha := accepted_empty (u := u) (v := v)
  have hb := (actual_law zeroParameters []).mp ha
  cases i with
  | false =>
    change (¬actualPred false zeroParameters []) ↔ actualPred true zeroParameters [] at he
    exact he.mpr hb ha
  | true =>
    change actualPred false zeroParameters [] ↔ ¬actualPred true zeroParameters [] at he
    exact he.mp ha hb

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨zeroParameters, [], [true, true], ?_⟩
  intro he
  cases i with
  | false => exact rejected_history (Eq.mp he accepted_empty)
  | true =>
    have ha := (actual_law zeroParameters []).mp accepted_empty
    have hb := Eq.mp he ha
    exact rejected_history ((actual_law zeroParameters [true, true]).mpr hb)

def source_registration :
    Registration arena.{u,v} (type_of% @actual_history_kernel_signature.{u,v}) where
  actual := actual
  bridge := by
    constructor
    · intro H p w
      letI := p.ringC
      letI := p.groupB
      exact @H p.C p.B p.ringC p.groupB p.x p.lam p.k p.hk p.h w p.other
    · intro H C B instC instB x lam k hk h w other
      exact H ⟨C, instC, B, instB, x, lam, k, hk, h, other⟩ w
  variation := ⟨actual_law, intervention false, intervention_breaks false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_breaks i⟩
      intro j hji
      funext p w
      simp [actual, intervention, realize, hji, actualPred]
    · intro i
      exact nomatch i
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@actual_history_kernel_signature.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel.unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actualPred (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,10]
    readouts := #[
      { path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
        stateBinder := 9
        functionOperand := false
        stateOperand := none
        booleanPredicate := true },
      { path := #["body","body","body","body","body","body","body","body","body","body","body","arg"]
        stateBinder := 9
        functionOperand := false
        stateOperand := none
        booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel
