import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.PresburgerFormulaGrowth
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open PresburgerArithmetic PresburgerPatternGrowth PresburgerFormulaGrowth

namespace Reg.D5.S0.Computability.PresburgerFormulaGrowth
noncomputable section
set_option autoImplicit false

abbrev signature : Signature where
  Params := QF
  State _ := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p env => p.eval env) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ env => decide (env = [0])) (fun e => nomatch e)

abbrev arena.{u,v} : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {Y : Type v} (p : QF) (m : Nat)
    (sourceEnv : X → List Int) (suffixEnv : Y → List Int)
    (_length_source : ∀ x, (sourceEnv x).length = m),
    Growth (fun x y => R.readout () p (sourceEnv x ++ suffixEnv y))
      (budget p).1 (budget p).2

theorem rejected_law.{u,v} : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  have hh := h (X := ULift.{u} Bool) (Y := ULift.{v} Unit) .truth 1
    (fun x => [if x.down then 0 else 1]) (fun _ => []) (by intro x; simp)
  let f : ULift.{u} Bool → Unit → Bool :=
    fun x _ => decide (([if x.down then 0 else 1] : List Int) = [0])
  have bound := (polynomial_trace_bound hh).2 (fun _ : Unit => (⟨()⟩ : ULift.{v} Unit))
  change (traces f).card ≤ 1 * (Fintype.card Unit + 1) ^ 0 at bound
  have all : traces f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro b
    apply (mem_traces _ _).mpr
    refine ⟨⟨b ()⟩, ?_⟩
    funext i
    cases i
    cases hb : b () <;> simp [f, hb]
  rw [all, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_unit] at bound
  norm_num at bound

def evidence.{u,v} : Registration arena.{u,v}
    (type_of% (@PresburgerFormulaGrowth.qf_growth.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨PresburgerFormulaGrowth.qf_growth, rejected, rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law.{u,v}⟩
      · intro j h; exact (h (Subsingleton.elim j i)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨QF.atom (.le ⟨0, [1]⟩), [-1], [1], ?_⟩
    change QF.eval (.atom (.le ⟨0, [1]⟩)) [-1] ≠
      QF.eval (.atom (.le ⟨0, [1]⟩)) [1]
    decide

noncomputable def registration.{u,v} :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@PresburgerFormulaGrowth.qf_growth.{u,v})
      (type_of% (realize signature (fun _ p env => p.eval env) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `D5.S0.Computability.PresburgerFormulaGrowth.qf_growth.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerFormulaGrowth.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v}⟩,
  objectArena := .source ⟨arena.{u,v}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v} ⟨evidence.{u,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p env => p.eval env) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerFormulaGrowth
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S0.Computability.PresburgerFormulaGrowth
