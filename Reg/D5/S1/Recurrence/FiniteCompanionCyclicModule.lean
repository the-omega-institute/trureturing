import D5.S1.Recurrence.FiniteCompanionCyclicModule
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S1.Recurrence.FiniteCompanionCyclicModule
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.FiniteCompanionCyclicModule
noncomputable section
universe u

abbrev signature : Signature where
  Params := (Type u) × ℕ
  State p := Fin p.2 → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.2 → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

abbrev bad : Realization signature.{u} :=
  realize signature (fun _ p v => if h : 0 < p.2 then fun _ => v ⟨0,h⟩ else v)
    (fun e => nomatch e)

abbrev presentationArena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [CommRing A] (u : A) (q : ℕ) (hq : 0 < q),
    (∀ f : Polynomial A, cyclicEquiv u q hq (projection u q f) =
      Module.AEval'.of (time u q hq) ((Polynomial.aeval (time u q hq) f) (e0 q hq))) ∧
    (∀ v : Fin q → A, (cyclicEquiv u q hq).symm (Module.AEval'.of (time u q hq) v) =
      projection u q (coordinatePolynomial u q (r.readout () ⟨A,q⟩ v))) ∧
    cyclicEquiv u q hq 1 = Module.AEval'.of (time u q hq) (e0 q hq)

private theorem bad_presentation : ¬ presentationArena.{u}.Law bad := by
  intro h
  let v : Fin 2 → ULift.{u} ℤ := fun i => if i.val = 0 then 0 else 1
  let w := bad.readout () ⟨ULift.{u} ℤ,2⟩ v
  have hv := (@h (ULift.{u} ℤ) inferInstance 0 2 (by decide)).2.1 v
  have hw := (cyclic_presentation (0 : ULift.{u} ℤ) 2 (by decide)).2.1 w
  have he := (cyclicEquiv (0 : ULift.{u} ℤ) 2 (by decide)).symm.injective (hv.trans hw.symm)
  have hh := (Module.AEval'.of (time (0 : ULift.{u} ℤ) 2 (by decide))).injective he
  have hc := congrArg (fun z => (z (1 : Fin 2)).down) hh
  norm_num [w, bad, realize, v] at hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℤ,1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrArg (fun z => (z (0 : Fin 1)).down) h
  norm_num [actual, realize] at he

def presentationEvidence : Registration presentationArena.{u}
    (∀ {A : Type u} [CommRing A] (u : A) (q : ℕ) (hq : 0 < q),
      (∀ f : Polynomial A, cyclicEquiv u q hq (projection u q f) =
        Module.AEval'.of (time u q hq) ((Polynomial.aeval (time u q hq) f) (e0 q hq))) ∧
      (∀ v : Fin q → A, (cyclicEquiv u q hq).symm (Module.AEval'.of (time u q hq) v) =
        projection u q (coordinatePolynomial u q v)) ∧
      cyclicEquiv u q hq 1 = Module.AEval'.of (time u q hq) (e0 q hq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cyclic_presentation, bad, bad_presentation⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_presentation⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def cyclic_presentation_registration :
    Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
      (@_root_.D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclic_presentation.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.FiniteCompanionCyclicModule.presentation_unit
  realizationName := `Reg.D5.S1.Recurrence.FiniteCompanionCyclicModule.presentationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨presentationArena.{u}⟩
  objectArena := .source ⟨presentationArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source presentationArena.{u} ⟨presentationEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.FiniteCompanionCyclicModule
    definition := none
    coordinates := #[0,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg",
        "body", "arg", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev kernelSignature : Signature where
  Params := Σ A : Type u, CommRing A × ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev kernelActual : Realization kernelSignature.{u} :=
  realize kernelSignature (fun _ _ a => a) (fun e => nomatch e)

abbrev kernelBad : Realization kernelSignature.{u} :=
  realize kernelSignature (fun _ p _ => @Zero.zero p.1 p.2.1.toZero)
    (fun e => nomatch e)

abbrev kernelArena : Arena where
  signature := kernelSignature.{u}
  Law r := ∀ {A : Type u} [inst : CommRing A] (u : A) (q : ℕ) (hq : 0 < q),
    LinearMap.ker (evaluate (r.readout () ⟨A,inst,q⟩ u) q hq) =
      (Ideal.span {P u q} : Ideal (Polynomial A))

private theorem bad_kernel : ¬ kernelArena.{u}.Law kernelBad := by
  intro h
  have hh := @h (ULift.{u} ℤ) inferInstance 1 1 (by decide)
  have hp : P (1 : ULift.{u} ℤ) 1 ∈
      (Ideal.span {P (1 : ULift.{u} ℤ) 1} : Ideal (Polynomial (ULift.{u} ℤ))) :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [← hh] at hp
  change P (1 : ULift.{u} ℤ) 1 ∈ LinearMap.ker (evaluate (0 : ULift.{u} ℤ) 1 (by decide)) at hp
  rw [evaluate_ker] at hp
  rcases Ideal.mem_span_singleton.mp hp with ⟨g, hg⟩
  have he := congrArg (Polynomial.eval (0 : ULift.{u} ℤ)) hg
  have hz : (0 : ULift.{u} ℤ) = -1 := by simpa [P,H] using he
  have hd := congrArg ULift.down hz
  norm_num at hd

private theorem kernel_dependence : ObservationalDependence kernelSignature.{u} kernelActual := by
  intro i
  refine ⟨⟨ULift.{u} ℤ,inferInstance,1⟩, 0, 1, ?_⟩
  intro h
  have hd := congrArg ULift.down h
  norm_num [kernelActual, realize] at hd

def kernelEvidence : Registration kernelArena.{u}
    (∀ {A : Type u} [CommRing A] (u : A) (q : ℕ) (hq : 0 < q),
      LinearMap.ker (evaluate u q hq) = (Ideal.span {P u q} : Ideal (Polynomial A))) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨evaluate_ker, kernelBad, bad_kernel⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨kernelBad, ?_, rfl, bad_kernel⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := kernel_dependence

noncomputable def evaluate_ker_registration :
    Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
      (@_root_.D5.S1.Recurrence.FiniteCompanionCyclicModule.evaluate_ker.{u})
      (Realization kernelSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.FiniteCompanionCyclicModule.kernel_unit
  realizationName := `Reg.D5.S1.Recurrence.FiniteCompanionCyclicModule.kernelEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena.{u}⟩
  objectArena := .source ⟨kernelArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena.{u} ⟨kernelEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature.{u} (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.FiniteCompanionCyclicModule
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.FiniteCompanionCyclicModule
