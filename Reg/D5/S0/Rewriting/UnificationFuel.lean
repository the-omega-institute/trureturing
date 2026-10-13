import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Rewriting.UnificationFuel
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Rewriting.UnificationFuel

open Lambda Lambda.UnificationFuel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Constraints × SubstInfo
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Nat → Option Result) × Result
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s => (fun fuel => core fuel s.1 s.2.subst, run s.1 s.2))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (fun _ => none, .ok [])) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (cs : Constraints) (S : SubstInfo),
    (∃ bound, ∀ fuel, bound ≤ fuel →
      (R.readout () () (cs,S)).1 fuel = some ((cs.unify S).map SubstInfo.subst)) ∧
    (∀ fuel r, (R.readout () () (cs,S)).1 fuel = some r →
      r = (cs.unify S).map SubstInfo.subst) ∧
    (R.readout () () (cs,S)).2 = (cs.unify S).map SubstInfo.subst

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨b,hb⟩ := (h [] SubstInfo.empty).1
  have bad := hb b (Nat.le_refl b)
  cases bad

private theorem empty_result : run [] SubstInfo.empty = .ok [] := by
  rw [(exact_fuel_simulation [] SubstInfo.empty).2.2]
  unfold Constraints.unify
  rw [Constraints.unifyCore.eq_def]
  rfl

private theorem clash_result :
    run [(NativeTermUnification.leaf false, NativeTermUnification.leaf true)] SubstInfo.empty =
      .error (.ImpossibleToUnify (NativeTermUnification.leaf false,
        NativeTermUnification.leaf true) (some (NativeTermUnification.leaf false,
          NativeTermUnification.leaf true))) := by
  rw [(exact_fuel_simulation _ _).2.2]
  unfold Constraints.unify
  rw [Constraints.unifyCore.eq_def]
  dsimp only
  rw [Constraint.unifyOne.eq_def]
  rfl

def evidence : Registration arena (type_of% (@Lambda.UnificationFuel.exact_fuel_simulation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_fuel_simulation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), ([],SubstInfo.empty),
      ([(NativeTermUnification.leaf false, NativeTermUnification.leaf true)],SubstInfo.empty), ?_⟩
    intro h
    have hresult := congrArg Prod.snd h
    change run [] SubstInfo.empty = run _ SubstInfo.empty at hresult
    rw [empty_result, clash_result] at hresult
    cases hresult

noncomputable def registration_exact_fuel_simulation :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@Lambda.UnificationFuel.exact_fuel_simulation)
      (type_of% (realize signature
        (fun _ _ s => (fun fuel => core fuel s.1 s.2.subst, run s.1 s.2))
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S0.Rewriting.UnificationFuel.unit,
  realizationName := `Reg.D5.S0.Rewriting.UnificationFuel.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ _ s => (fun fuel => core fuel s.1 s.2.subst, run s.1 s.2))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S0.Rewriting.UnificationFuel
