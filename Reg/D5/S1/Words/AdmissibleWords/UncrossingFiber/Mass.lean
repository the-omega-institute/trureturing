import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.UncrossingFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S1.Words.AdmissibleWords.UncrossingFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass

open _root_.D5.S1.Words.AdmissibleWords.UncrossingFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- `Type` is a higher-universe parameter domain. Dictionaries remain in each Law. -/
abbrev signature : Signature where
  Params := Type
  State V := Multiset (Finset V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev oneEmpty : Multiset (Finset (Fin 1)) := (∅ : Finset (Fin 1)) ::ₘ 0
abbrev emptyFamily : Finset (Finset (Fin 1)) := {∅}

theorem oneEmpty_comparable : Comparable oneEmpty := by
  intro A hA B hB
  have hA' : A = ∅ := by simpa [oneEmpty] using hA
  have hB' : B = ∅ := by simpa [oneEmpty] using hB
  subst A
  subst B
  exact Or.inl Finset.Subset.rfl

theorem zero_comparable : Comparable (0 : Multiset (Finset (Fin 1))) := by
  intro A hA
  simp at hA

theorem emptyFamily_closed : ClosedFamily emptyFamily := by
  intro A hA B hB
  have hA' : A = ∅ := by simpa [emptyFamily] using hA
  have hB' : B = ∅ := by simpa [emptyFamily] using hB
  subst A
  subst B
  simp [emptyFamily]

theorem oneEmpty_family : FamilyRows emptyFamily oneEmpty := by
  intro A hA
  have hA' : A = ∅ := by simpa [oneEmpty] using hA
  subst A
  simp [emptyFamily]

theorem zero_family : FamilyRows emptyFamily (0 : Multiset (Finset (Fin 1))) := by
  intro A hA
  simp at hA

theorem empty_margins : ∀ v, margin oneEmpty v = margin (0 : Multiset (Finset (Fin 1))) v := by
  intro v
  simp [oneEmpty, margin]

/-- The singleton-role proof also works when Params lives in Type 1. -/
theorem sensitivity (law : Realization signature → Prop) (hbad : ¬ law rejected) :
    Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨Fin 1, (0 : Multiset (Finset (Fin 1))), oneEmpty, ?_⟩
  change (0 : Multiset (Finset (Fin 1))).card ≠ oneEmpty.card
  simp [oneEmpty]

namespace MarginLeCard

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    (M : Multiset (Finset V)) (v : V), margin M v ≤ F.readout () V M

theorem positive : arena.Law actual := @margin_le_card

theorem bridge : (type_of% (@margin_le_card)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law (V := Fin 1) ((Finset.univ : Finset (Fin 1)) ::ₘ 0) 0
  change margin ((Finset.univ : Finset (Fin 1)) ::ₘ 0) 0 ≤ 0 at h
  simpa [margin] using h

def evidence : Registration arena (type_of% (@margin_le_card)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end MarginLeCard

namespace MarginEqCardIff

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M : Multiset (Finset V)} (v : V),
    margin M v = F.readout () V M ↔ ∀ A, A ∈ M → v ∈ A

theorem positive : arena.Law actual := @margin_eq_card_iff

theorem bridge : (type_of% (@margin_eq_card_iff)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := (law (V := Fin 1)
    (M := (Finset.univ : Finset (Fin 1)) ::ₘ 0) 0).mpr (by
      intro A hA
      have hA' : A = Finset.univ := by simpa using hA
      subst A
      simp)
  change margin ((Finset.univ : Finset (Fin 1)) ::ₘ 0) 0 = 0 at h
  simpa [margin] using h

def evidence : Registration arena (type_of% (@margin_eq_card_iff)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end MarginEqCardIff

namespace ComparableMarginUnique

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M N : Multiset (Finset V)}
    (hM : Comparable M) (hN : Comparable N)
    (hcard : F.readout () V M = N.card)
    (hmarg : ∀ v, margin M v = margin N v), M = N

theorem positive : arena.Law actual := @comparable_margin_unique

theorem bridge : (type_of% (@comparable_margin_unique)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  have h : oneEmpty = (0 : Multiset (Finset (Fin 1))) :=
    law oneEmpty_comparable zero_comparable rfl empty_margins
  have hc := congrArg Multiset.card h
  simpa [oneEmpty] using hc

def evidence : Registration arena (type_of% (@comparable_margin_unique)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end ComparableMarginUnique

namespace ForwardStepCard

abbrev crossA : Finset (Fin 2) := {0}
abbrev crossB : Finset (Fin 2) := {1}
abbrev crossInput : Multiset (Finset (Fin 2)) := crossA ::ₘ crossB ::ₘ 0
abbrev crossOutput : Multiset (Finset (Fin 2)) :=
  (crossA ∩ crossB) ::ₘ (crossA ∪ crossB) ::ₘ 0

theorem crossing : ForwardStep crossInput crossOutput := by
  refine ⟨0, crossA, crossB, ?_, ?_, rfl, rfl⟩
  · intro h
    have hf := h (show (0 : Fin 2) ∈ crossA by simp [crossA])
    simpa [crossB] using hf
  · intro h
    have hf := h (show (1 : Fin 2) ∈ crossB by simp [crossB])
    simpa [crossA] using hf

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M N : Multiset (Finset V)} (h : ForwardStep M N),
    F.readout () V M = N.card

theorem positive : arena.Law actual := @forwardStep_card

theorem bridge : (type_of% (@forwardStep_card)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law crossing
  change 0 = crossOutput.card at h
  simpa [crossOutput] using h

def evidence : Registration arena (type_of% (@forwardStep_card)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end ForwardStepCard

namespace ForwardRouteCard

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M N : Multiset (Finset V)} {k : Nat} (h : ForwardRoute M N k),
    F.readout () V M = N.card

theorem positive : arena.Law actual := @forwardRoute_card

theorem bridge : (type_of% (@forwardRoute_card)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law (ForwardRoute.zero oneEmpty)
  change 0 = oneEmpty.card at h
  simpa [oneEmpty] using h

def evidence : Registration arena (type_of% (@forwardRoute_card)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end ForwardRouteCard

namespace SameMarginCommonComparable

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M N : Multiset (Finset V)}
    (hcard : F.readout () V M = N.card)
    (hmarg : ∀ v, margin M v = margin N v),
    ∃ k l P,
      k ≤ M.card * (Fintype.card V) ^ 2 / 2 ∧
        l ≤ N.card * (Fintype.card V) ^ 2 / 2 ∧
          ForwardRoute M P k ∧ ForwardRoute N P l ∧ Comparable P

theorem positive : arena.Law actual := @same_margin_common_comparable

theorem bridge :
    (type_of% (@same_margin_common_comparable)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  obtain ⟨k, l, P, hk, hl, hr, hs, hP⟩ :=
    law (M := oneEmpty) (N := (0 : Multiset (Finset (Fin 1)))) rfl empty_margins
  have hc : oneEmpty.card = (0 : Multiset (Finset (Fin 1))).card :=
    (forwardRoute_card hr).trans (forwardRoute_card hs).symm
  simpa [oneEmpty] using hc

def evidence : Registration arena (type_of% (@same_margin_common_comparable)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end SameMarginCommonComparable

namespace ExchangePathInvariants

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {L : Finset (Finset V)} {M N : Multiset (Finset V)}
    (hM : FamilyRows L M) (h : ExchangePath L M N),
    FamilyRows L N ∧ F.readout () V N = M.card ∧
      ∀ v, margin N v = margin M v

theorem positive : arena.Law actual := @exchangePath_invariants

theorem bridge : (type_of% (@exchangePath_invariants)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  have h := law (L := emptyFamily) (M := oneEmpty) (N := oneEmpty)
    oneEmpty_family (show ExchangePath emptyFamily oneEmpty oneEmpty from .refl)
  have hc := h.2.1
  change 0 = oneEmpty.card at hc
  simpa [oneEmpty] using hc

def evidence : Registration arena (type_of% (@exchangePath_invariants)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end ExchangePathInvariants

namespace SameMarginConnected

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {L : Finset (Finset V)} (hL : ClosedFamily L)
    {M N : Multiset (Finset V)} (hM : FamilyRows L M) (hN : FamilyRows L N)
    (hc : F.readout () V M = N.card) (hm : ∀ v, margin M v = margin N v),
    ExchangePath L M N

theorem positive : arena.Law actual := @same_margin_connected

theorem bridge : (type_of% (@same_margin_connected)) ↔ arena.Law actual := Iff.rfl

theorem negative : ¬ arena.Law rejected := by
  intro law
  have hp : ExchangePath emptyFamily oneEmpty (0 : Multiset (Finset (Fin 1))) :=
    law emptyFamily_closed oneEmpty_family zero_family rfl empty_margins
  have hc := (exchangePath_invariants oneEmpty_family hp).2.1
  simpa [oneEmpty] using hc

def evidence : Registration arena (type_of% (@same_margin_connected)) where
  actual := actual
  bridge := bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := sensitivity _ negative
  dependence := dependence

end SameMarginConnected

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.MarginLeCard

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@margin_le_card) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.margin_le_card.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.MarginLeCard.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.MarginLeCard

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ForwardStepCard

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@forwardStep_card) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardStep_card.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ForwardStepCard.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ForwardStepCard

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ForwardRouteCard

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@forwardRoute_card) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardRoute_card.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ForwardRouteCard.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ForwardRouteCard

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.MarginEqCardIff

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@margin_eq_card_iff) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.margin_eq_card_iff.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.MarginEqCardIff.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.MarginEqCardIff

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.SameMarginConnected

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@same_margin_connected) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.same_margin_connected.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.SameMarginConnected.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.SameMarginConnected

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ExchangePathInvariants

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exchangePath_invariants) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.exchangePath_invariants.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ExchangePathInvariants.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ExchangePathInvariants

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ComparableMarginUnique

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@comparable_margin_unique) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.comparable_margin_unique.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ComparableMarginUnique.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.ComparableMarginUnique

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.SameMarginCommonComparable

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@same_margin_common_comparable) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.same_margin_common_comparable.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.SameMarginCommonComparable.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Mass.SameMarginCommonComparable
