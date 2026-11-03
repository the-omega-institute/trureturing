import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript
open scoped Classical

namespace Reg.D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript

universe u

abbrev Parameters := Σ T : Interface.{u}, Σ _S : Source T, Σ C : Type u,
  Σ _n : ℕ, Σ _i : T.Ty, Σ _d : ℕ, Σ _P : Policy T C, Σ _c : C, List (Token T)

namespace Parameters
abbrev interface (p : Parameters.{u}) := p.1
abbrev source (p : Parameters.{u}) := p.2.1
abbrev Archive (p : Parameters.{u}) := p.2.2.1
abbrev n (p : Parameters.{u}) := p.2.2.2.1
abbrev i (p : Parameters.{u}) := p.2.2.2.2.1
abbrev d (p : Parameters.{u}) := p.2.2.2.2.2.1
abbrev policy (p : Parameters.{u}) := p.2.2.2.2.2.2.1
abbrev archive (p : Parameters.{u}) := p.2.2.2.2.2.2.2.1
abbrev history (p : Parameters.{u}) := p.2.2.2.2.2.2.2.2
end Parameters

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := p.interface.State p.i
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PMF (Transcript p.interface p.Archive)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p z => run p.source p.policy p.d p.i z p.archive p.history) Empty.elim

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {T : Interface.{u}} (S : Source T) (Archive : Type u) (n : ℕ)
    {i : T.Ty} {z w : T.State i}, residual S n i z w →
    ∀ d (_hd : d ≤ n) (P : Policy T Archive) (c : Archive) (h : List (Token T)),
      R.readout () ⟨T, S, Archive, n, i, d, P, c, h⟩ z =
        R.readout () ⟨T, S, Archive, n, i, d, P, c, h⟩ w

/-- The intervention changes the whole execution-law family, holding the source
relation, action contracts and every other operand fixed. -/
def rejected : Realization signature.{u} :=
  realize signature (fun _ p z =>
    if ht : Nonempty (p.interface.State p.i) then
      if z = Classical.choice ht then PMF.pure ([Token.horizon p.i], [p.archive])
      else PMF.pure ([Token.stopped p.i], [p.archive])
    else PMF.pure ([Token.horizon p.i], [p.archive])) Empty.elim

def toyInterface (_visible : Bool) : Interface.{u} where
  Ty := ULift Unit
  State _ := ULift Bool
  Observation _ := ULift Bool
  Action _ _ := ULift Empty
  Event _ := ULift Unit
  Record _ := ULift Unit
  Terminal _ := ULift Unit

def toySource (visible : Bool) : Source (toyInterface.{u} visible) where
  observe z := ⟨if visible then z.down else false⟩
  legal _ _ := False
  kernel _ _ h := h.elim
  refusal _ _ _ := (⟨()⟩, ⟨()⟩, ⟨()⟩)

def toyPolicy (visible : Bool) : Policy (toyInterface.{u} visible) (ULift.{u} Unit) where
  write c _ _ := c
  permitted _ _ _ _ _ := True
  select _ _ _ _ _ := PMF.pure none
  selects_permitted _ _ _ _ _ _ _ := trivial

def toyParameter (visible : Bool) : Parameters.{u} :=
  ⟨toyInterface visible, toySource visible, ULift Unit, 0, ⟨()⟩, 0,
    toyPolicy visible, ⟨()⟩, []⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let p := toyParameter.{u} false
  let ht : Nonempty (p.interface.State p.i) := ⟨⟨false⟩⟩
  let z : p.interface.State p.i := Classical.choice ht
  let w : p.interface.State p.i := ⟨!z.down⟩
  have hw : w ≠ z := by
    intro eq
    have hh := congrArg ULift.down eq
    cases z.down <;> simp_all [w]
  have related : residual p.source 0 p.i z w := by rfl
  have hh := law (T := p.interface) p.source p.Archive 0 related 0 le_rfl p.policy p.archive []
  change rejected.readout () p z = rejected.readout () p w at hh
  simp only [rejected, realize, dite_eq_left ht] at hh
  change (if z = z then PMF.pure ([Token.horizon p.i], [p.archive])
      else PMF.pure ([Token.stopped p.i], [p.archive])) =
    (if w = z then PMF.pure ([Token.horizon p.i], [p.archive])
      else PMF.pure ([Token.stopped p.i], [p.archive])) at hh
  rw [ite_eq_left rfl, ite_eq_right hw] at hh
  have bad := congrArg PMF.support hh
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff] at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨toyParameter.{u} true, ⟨false⟩, ⟨true⟩, ?_⟩
  intro eq
  change PMF.pure ([Token.observed (T := toyInterface.{u} true) ⟨()⟩ ⟨false⟩,
      Token.horizon (T := toyInterface.{u} true) ⟨()⟩], [(ULift.up () : ULift.{u} Unit), ULift.up (), ULift.up ()]) =
    PMF.pure ([Token.observed (T := toyInterface.{u} true) ⟨()⟩ ⟨true⟩,
      Token.horizon (T := toyInterface.{u} true) ⟨()⟩], [(ULift.up () : ULift.{u} Unit), ULift.up (), ULift.up ()]) at eq
  have bad := congrArg PMF.support eq
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff] at bad
  cases bad

def family : Registration arena.{u}
    (type_of% (@recursive_residual_preserves_adaptive_law.{u})) where
  actual := realize signature.{u}
    (fun _ p z => run p.source p.policy p.d p.i z p.archive p.history) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@recursive_residual_preserves_adaptive_law.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@recursive_residual_preserves_adaptive_law.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p z => run p.source p.policy p.d p.i z p.archive p.history) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 8, 10, 11, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Observer.ProbabilisticClosure.RecursiveJointTranscript
