import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic

/-! Source-bound dependent-family audits of accepted-word propagation. -/

open _root_.D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation
open _root_.D5.S0.Automata.TypedPartialDFAO
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation

universe u v w z

structure Parameters where
  K : Type u
  E : Type v
  Alphabet : Type w
  Q : Type z
  division : DivisionRing K
  additive : AddCommGroup E
  module : @Module K E division.toSemiring additive.toAddCommMonoid
  decidable : DecidableEq Q
  machine : BaseAutomaton Alphabet Q
  final : Finset Q
  effects : Alphabet → @Module.End K E division.toSemiring additive.toAddCommMonoid module

attribute [instance] Parameters.division Parameters.additive Parameters.module Parameters.decidable

private abbrev toy : Parameters.{u,v,w,z} where
  K := ULift.{u} (ZMod 2)
  E := ULift.{v} (ZMod 2)
  Alphabet := ULift.{w} Empty
  Q := ULift.{z} Unit
  division := inferInstance
  additive := inferInstance
  module := inferInstance
  decidable := inferInstance
  machine := ⟨⟨()⟩, fun _ _ => none⟩
  final := {⟨()⟩}
  effects a := nomatch a.down

private theorem accepted_bot (p : Parameters.{u,v,w,z}) (n : ℕ) (q : p.Q) :
    acceptedSpan p.machine p.final p.effects ⊥ n q = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro x ⟨word, _, _, t, ht, rfl⟩
  have : t = 0 := ht
  simp [this]

private theorem future_bot (p : Parameters.{u,v,w,z}) (q : p.Q) :
    fullFuture p.machine p.final p.effects ⊥ q = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro x ⟨word, _, t, ht, rfl⟩
  have : t = 0 := ht
  simp [this]

namespace Words

abbrev signature : Signature where
  Params := Parameters.{u,v,w,z} × ℕ
  State p := Submodule p.1.K p.1.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.Q → Submodule p.1.K p.1.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w,z} :=
  realize signature (fun _ p U => acceptedSpan p.1.machine p.1.final p.1.effects U p.2)
    (fun e => nomatch e)

def rejected : Realization signature.{u,v,w,z} :=
  realize signature (fun _ _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v,w,z}
  Law r := ∀ {K : Type u} {E : Type v} {Alphabet : Type w} {Q : Type z}
    [d : DivisionRing K] [a : AddCommGroup E] [m : Module K E] [de : DecidableEq Q]
    (M : BaseAutomaton Alphabet Q) (F : Finset Q) (A : Alphabet → Module.End K E)
    (U : Submodule K E) (n : ℕ),
    propagation M F A U n = r.readout () (⟨K, E, Alphabet, Q, d, a, m, de, M, F, A⟩, n) U

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let p := toy.{u,v,w,z}
  have he := congrFun (h p.machine p.final p.effects ⊤ 0) (ULift.up ())
  have hm : (1 : ULift.{v} (ZMod 2)) ∈
      propagation p.machine p.final p.effects ⊤ 0 (ULift.up ()) := by
    have hf : (ULift.up () : p.Q) ∈ p.final := Finset.mem_singleton_self _
    have hv : propagation p.machine p.final p.effects ⊤ 0 (ULift.up ()) = ⊤ := if_pos hf
    rw [hv]
    exact Submodule.mem_top
  change _ = (⊥ : Submodule p.K p.E) at he
  rw [he] at hm
  exact (one_ne_zero : (1 : ULift.{v} (ZMod 2)) ≠ 0) hm

def family : Registration arena.{u,v,w,z} (type_of% (@propagation_eq_accepted.{u,v,w,z})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@propagation_eq_accepted, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    change ObservationalDependence signature actual
    intro i
    let p := toy.{u,v,w,z}
    refine ⟨(p, 0), ⊥, ⊤, ?_⟩
    intro he
    have hq := congrFun he (ULift.up ())
    change acceptedSpan p.machine p.final p.effects ⊥ 0 _ =
      acceptedSpan p.machine p.final p.effects ⊤ 0 _ at hq
    have hm : (1 : ULift.{v} (ZMod 2)) ∈
        acceptedSpan p.machine p.final p.effects ⊤ 0 (ULift.up ()) :=
      Submodule.subset_span ⟨[], by simp, ⟨ULift.up (), Finset.mem_singleton_self _, rfl⟩,
        1, Submodule.mem_top, by simp⟩
    rw [← hq, accepted_bot] at hm
    exact (one_ne_zero : (1 : ULift.{v} (ZMod 2)) ≠ 0) hm

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@propagation_eq_accepted.{u,v,w,z})
    (type_of% (realize signature.{u,v,w,z}
      (fun _ p U => acceptedSpan p.1.machine p.1.final p.1.effects U p.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation.propagation_eq_accepted.information_unit
  realizationName := `Reg.D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation.Words.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨family.{u,v,w,z}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w,z}
    (fun _ p U => acceptedSpan p.1.machine p.1.final p.1.effects U p.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9,10,12]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Words

structure FiniteParameters extends Parameters.{u,v,w,z} where
  finiteQ : Fintype Q
  finiteE : @FiniteDimensional K E division additive module

attribute [instance] FiniteParameters.finiteQ FiniteParameters.finiteE

namespace Stability

abbrev signature : Signature where
  Params := FiniteParameters.{u,v,w,z}
  State p := Submodule p.K p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Q → Submodule p.K p.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w,z} :=
  realize signature (fun _ p U => fullFuture p.machine p.final p.effects U) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w,z} :=
  realize signature (fun _ _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v,w,z}
  Law r := ∀ {K : Type u} {E : Type v} {Alphabet : Type w} {Q : Type z}
    [d : DivisionRing K] [a : AddCommGroup E] [m : Module K E] [de : DecidableEq Q]
    [ft : Fintype Q] [fd : FiniteDimensional K E]
    (M : BaseAutomaton Alphabet Q) (F : Finset Q) (A : Alphabet → Module.End K E)
    (U : Submodule K E),
    (∀ n, (∀ q, propagation M F A U (n + 1) q = propagation M F A U n q) →
      ∀ m q, propagation M F A U (n + m) q = propagation M F A U n q) ∧
    (let B := Fintype.card Q * Module.finrank K E - F.card * Module.finrank K U
     (∀ n, B ≤ n → propagation M F A U n = propagation M F A U B) ∧
       ∀ q, r.readout () ⟨⟨K,E,Alphabet,Q,d,a,m,de,M,F,A⟩,ft,fd⟩ U q =
         propagation M F A U B q)

private abbrev finiteToy : FiniteParameters.{u,v,w,z} where
  toParameters := toy
  finiteQ := by change Fintype (ULift.{z} Unit); infer_instance
  finiteE := by
    change FiniteDimensional (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2))
    infer_instance

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let p := finiteToy.{u,v,w,z}
  have he := (h p.machine p.final p.effects ⊤).2.2 (ULift.up ())
  let B := Fintype.card p.Q * Module.finrank p.K p.E -
    p.final.card * Module.finrank p.K (⊤ : Submodule p.K p.E)
  have hm : (1 : ULift.{v} (ZMod 2)) ∈ propagation p.machine p.final p.effects ⊤ B
      (ULift.up ()) := by
    rw [propagation_eq_accepted]
    exact Submodule.subset_span ⟨[], Nat.zero_le _,
      ⟨ULift.up (), Finset.mem_singleton_self _, rfl⟩, 1, Submodule.mem_top, by simp⟩
  change (⊥ : Submodule p.K p.E) = propagation p.machine p.final p.effects ⊤ B _ at he
  rw [← he] at hm
  exact (one_ne_zero : (1 : ULift.{v} (ZMod 2)) ≠ 0) hm

def family : Registration arena.{u,v,w,z} (type_of% (@simultaneous_stabilization.{u,v,w,z})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneous_stabilization, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    change ObservationalDependence signature actual
    intro i
    let p := finiteToy.{u,v,w,z}
    refine ⟨p, ⊥, ⊤, ?_⟩
    intro he
    have hq := congrFun he (ULift.up ())
    change fullFuture p.machine p.final p.effects ⊥ _ =
      fullFuture p.machine p.final p.effects ⊤ _ at hq
    have hm : (1 : ULift.{v} (ZMod 2)) ∈
        fullFuture p.machine p.final p.effects ⊤ (ULift.up ()) :=
      Submodule.subset_span ⟨[], ⟨ULift.up (), Finset.mem_singleton_self _, rfl⟩,
        1, Submodule.mem_top, by simp⟩
    rw [← hq, future_bot] at hm
    exact (one_ne_zero : (1 : ULift.{v} (ZMod 2)) ≠ 0) hm

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@simultaneous_stabilization.{u,v,w,z})
    (type_of% (realize signature.{u,v,w,z}
      (fun _ p U => fullFuture p.machine p.final p.effects U) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation.simultaneous_stabilization.information_unit
  realizationName := `Reg.D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation.Stability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨family.{u,v,w,z}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w,z}
    (fun _ p U => fullFuture p.machine p.final p.effects U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9,10,11,12]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","body","fn","arg","fn"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Stability

namespace Delay

structure Parameters where
  K : Type u
  E : Type v
  division : DivisionRing K
  additive : AddCommGroup E
  module : @Module K E division.toSemiring additive.toAddCommMonoid
  length : ℕ

attribute [instance] Parameters.division Parameters.additive Parameters.module

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Submodule p.K p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → Fin (p.length + 1) → Submodule p.K p.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p U => propagation (chain p.length) (chainFinal p.length)
    (fun _ => (1 : Module.End p.K p.E)) U) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {K : Type u} {E : Type v}
    [d : DivisionRing K] [a : AddCommGroup E] [m : Module K E]
    (L : ℕ) (U : Submodule K E),
    (∀ n q, r.readout () ⟨K,E,d,a,m,L⟩ U n q = if L ≤ q.val + n then U else ⊥) ∧
    (∀ n, n < L → propagation (chain L) (chainFinal L)
      (fun _ => (1 : Module.End K E)) U n (chain L).start = ⊥) ∧
    propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U L
      (chain L).start = U ∧
    (2 ≤ L → U ≠ ⊥ →
      propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U 1 (chain L).start =
        propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U 0 (chain L).start ∧
      propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U L (chain L).start ≠
        propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U 0 (chain L).start)

private abbrev toy : Parameters.{u,v} where
  K := ULift.{u} (ZMod 2)
  E := ULift.{v} (ZMod 2)
  division := inferInstance
  additive := inferInstance
  module := inferInstance
  length := 0

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let p := toy.{u,v}
  have he := (@h p.K p.E p.division p.additive p.module 0 ⊤).1 0 ⟨0, by omega⟩
  change (⊥ : Submodule p.K p.E) = (if 0 ≤ 0 + 0 then ⊤ else ⊥) at he
  have hm : (1 : ULift.{v} (ZMod 2)) ∈ (⊥ : Submodule p.K p.E) := by
    rw [he]
    change (1 : ULift.{v} (ZMod 2)) ∈ (⊤ : Submodule p.K p.E)
    exact Submodule.mem_top
  exact (one_ne_zero : (1 : ULift.{v} (ZMod 2)) ≠ 0) hm

def family : Registration arena.{u,v} (type_of% (@arbitrary_chain_delay.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@arbitrary_chain_delay, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    change ObservationalDependence signature actual
    intro i
    let p := toy.{u,v}
    refine ⟨p, ⊥, ⊤, ?_⟩
    intro he
    have hq := congrFun (congrFun he 0) ⟨0, by omega⟩
    dsimp only [actual, realize, p, toy, propagation, chainFinal] at hq
    have he' : (⊥ : Submodule p.K p.E) = ⊤ := by
      simpa only [Finset.mem_singleton_self, ite_true] using hq
    exact bot_ne_top he'

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@arbitrary_chain_delay.{u,v})
    (type_of% (realize signature.{u,v}
      (fun _ p U => propagation (chain p.length) (chainFinal p.length)
        (fun _ => (1 : Module.End p.K p.E)) U) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation.arbitrary_chain_delay.information_unit
  realizationName := `Reg.D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation.Delay.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v}
    (fun _ p U => propagation (chain p.length) (chainFinal p.length)
      (fun _ => (1 : Module.End p.K p.E)) U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","body","body","fn","arg","fn","fn"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Delay

#print axioms Words.family
#print axioms Stability.family
#print axioms Delay.family

end Reg.D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation
