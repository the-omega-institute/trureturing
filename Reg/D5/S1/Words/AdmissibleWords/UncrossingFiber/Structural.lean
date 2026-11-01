import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.UncrossingFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S1.Words.AdmissibleWords.UncrossingFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural

universe t s o
noncomputable section

/-- Parameters may contain an arbitrary small type; only the one role is finite. -/
abbrev singletonSignature (P : Type t) (S : P → Type s) (O : P → Type o) :
    Signature.{t,s,0,o,0} where
  Params := P
  State := S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := O
  Anchor := Empty
  finiteAnchor := inferInstance

/-- One intervention changes a whole readout family and fixes all anchors. -/
theorem singletonSensitivity {P : Type t} {S : P → Type s} {O : P → Type o}
    (actual bad : Realization (singletonSignature P S O))
    (law : Realization (singletonSignature P S O) → Prop) (hbad : ¬ law bad) :
    Sensitivity ⟨singletonSignature P S O, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

abbrev oneEmpty : Multiset (Finset (Fin 1)) := (∅ : Finset (Fin 1)) ::ₘ 0
abbrev emptyFamily : Finset (Finset (Fin 1)) := {∅}
abbrev crossA : Finset (Fin 2) := {0}
abbrev crossB : Finset (Fin 2) := {1}
abbrev crossInput : Multiset (Finset (Fin 2)) := crossA ::ₘ crossB ::ₘ 0
abbrev crossOutput : Multiset (Finset (Fin 2)) :=
  (crossA ∩ crossB) ::ₘ (crossA ∪ crossB) ::ₘ 0
abbrev fullFamily : Finset (Finset (Fin 2)) := Finset.univ

theorem zero_comparable {V : Type} : Comparable (0 : Multiset (Finset V)) := by
  intro A hA
  simp at hA

theorem oneEmpty_comparable : Comparable oneEmpty := by
  intro A hA B hB
  have hA' : A = ∅ := by simpa [oneEmpty] using hA
  have hB' : B = ∅ := by simpa [oneEmpty] using hB
  subst A
  subst B
  exact Or.inl Finset.Subset.rfl

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

theorem fullFamily_closed : ClosedFamily fullFamily := by
  intro A hA B hB
  simp [fullFamily]

theorem crossInput_family : FamilyRows fullFamily crossInput := by
  intro A hA
  simp [fullFamily]

theorem crossA_not_subset : ¬ crossA ⊆ crossB := by
  intro h
  have hf := h (show (0 : Fin 2) ∈ crossA by simp [crossA])
  simpa [crossB] using hf

theorem crossB_not_subset : ¬ crossB ⊆ crossA := by
  intro h
  have hf := h (show (1 : Fin 2) ∈ crossB by simp [crossB])
  simpa [crossA] using hf

theorem crossing : ForwardStep crossInput crossOutput :=
  ⟨0, crossA, crossB, crossA_not_subset, crossB_not_subset, rfl, rfl⟩

theorem cross_not_comparable : ¬ Comparable crossInput := by
  intro h
  rcases h (A := crossA) (B := crossB)
    (by simp [crossInput]) (by simp [crossInput]) with hAB | hBA
  · exact crossA_not_subset hAB
  · exact crossB_not_subset hBA

theorem zero_no_forward : ¬ ∃ N, ForwardStep (0 : Multiset (Finset (Fin 2))) N := by
  rintro ⟨N, hs⟩
  rcases hs with ⟨R, A, B, hAB, hBA, hm, hn⟩
  have hc := congrArg Multiset.card hm
  simp only [Multiset.card_zero, Multiset.card_cons] at hc
  omega

namespace Addition

abbrev signature : Signature.{0,0,0,0,0} :=
  singletonSignature Unit (fun _ => Nat) (fun _ => Nat → Nat)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x + y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hf := congrFun h 0
  change (0 : Nat) + 0 = 1 + 0 at hf
  omega

end Addition

namespace NatEquality

abbrev signature : Signature.{0,0,0,0,0} :=
  singletonSignature Unit (fun _ => Nat) (fun _ => Nat → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => Eq x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (fun y : Nat => 0 = y) ≠ (fun y : Nat => 1 = y)
  intro h
  have hf : (1 : Nat) = 0 := Eq.mp (congrFun h 0) rfl
  omega

end NatEquality

namespace Subset

abbrev signature : Signature.{1,0,0,0,0} :=
  singletonSignature (Σ V : Type, Finset V) (fun p => Finset p.1) (fun _ => Bool)

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p B => decide (p.2 ⊆ B)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨⟨Fin 1, Finset.univ⟩, ∅, Finset.univ, ?_⟩
  have hyes : actual.readout i ⟨Fin 1, Finset.univ⟩ Finset.univ = true := by
    simp [actual, realize]
  have hno : actual.readout i ⟨Fin 1, Finset.univ⟩ ∅ = false := by
    simp [actual, realize]
  rw [hno, hyes]
  exact Bool.false_ne_true

end Subset

namespace RowsInFamily

abbrev signature : Signature.{1,0,0,0,0} :=
  singletonSignature (Σ V : Type, Finset (Finset V))
    (fun p => Multiset (Finset p.1)) (fun _ => Bool)

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p M => decide (FamilyRows p.2 M)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

theorem empty_rows : FamilyRows emptyFamily (0 : Multiset (Finset (Fin 1))) := by
  intro A hA
  simp at hA

theorem full_row_not_in_family :
    ¬ FamilyRows emptyFamily ((Finset.univ : Finset (Fin 1)) ::ₘ 0) := by
  intro h
  have hf := h (A := Finset.univ) (by simp)
  simpa [emptyFamily] using hf

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨⟨Fin 1, emptyFamily⟩, 0, (Finset.univ : Finset (Fin 1)) ::ₘ 0, ?_⟩
  change decide (FamilyRows emptyFamily (0 : Multiset (Finset (Fin 1)))) ≠
    decide (FamilyRows emptyFamily ((Finset.univ : Finset (Fin 1)) ::ₘ 0))
  intro h
  have hz : decide (FamilyRows emptyFamily (0 : Multiset (Finset (Fin 1)))) = true := by
    simpa only [decide_eq_true_eq] using empty_rows
  apply full_row_not_in_family
  exact of_decide_eq_true (h.symm.trans hz)

end RowsInFamily

namespace Comparability

abbrev signature : Signature.{1,0,0,0,0} :=
  singletonSignature Type (fun V => Multiset (Finset V)) (fun _ => Bool)

def actual : Realization signature := by
  classical
  exact realize signature (fun _ _ M => decide (Comparable M)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨Fin 2, (0 : Multiset (Finset (Fin 2))), crossInput, ?_⟩
  change decide (Comparable (0 : Multiset (Finset (Fin 2)))) ≠ decide (Comparable crossInput)
  intro h
  have hz : decide (Comparable (0 : Multiset (Finset (Fin 2)))) = true := by
    simpa only [decide_eq_true_eq] using (zero_comparable (V := Fin 2))
  exact cross_not_comparable (of_decide_eq_true (h.symm.trans hz))

end Comparability

namespace RowMembership

abbrev signature : Signature.{1,0,0,0,0} :=
  singletonSignature (Σ V : Type, Finset (Finset V)) (fun p => Finset p.1) (fun _ => Bool)

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p A => decide (A ∈ p.2)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨⟨Fin 1, emptyFamily⟩, ∅, Finset.univ, ?_⟩
  change decide ((∅ : Finset (Fin 1)) ∈ emptyFamily) ≠
    decide ((Finset.univ : Finset (Fin 1)) ∈ emptyFamily)
  simp [emptyFamily]

end RowMembership

namespace MarginEraseAdd

abbrev arena : Arena where
  signature := Addition.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M : Multiset (Finset V)} {A : Finset V} (hA : A ∈ M) (v : V),
    F.readout () () (margin (M.erase A) v) (if v ∈ A then 1 else 0) = margin M v

theorem bridge : (type_of% (@margin_erase_add)) ↔ arena.Law Addition.actual := Iff.rfl
theorem positive : arena.Law Addition.actual := @margin_erase_add

theorem negative : ¬ arena.Law Addition.rejected := by
  intro law
  have hf := law (V := Fin 1) (M := (Finset.univ : Finset (Fin 1)) ::ₘ 0)
    (A := Finset.univ) (by simp) 0
  change 0 = margin ((Finset.univ : Finset (Fin 1)) ::ₘ 0) 0 at hf
  simpa [margin] using hf

theorem sensitivity : Sensitivity arena Addition.actual :=
  singletonSensitivity Addition.actual Addition.rejected arena.Law negative
theorem dependence : ObservationalDependence Addition.signature Addition.actual := Addition.dependence

def evidence : Registration arena (type_of% (@margin_erase_add)) where
  actual := Addition.actual
  bridge := bridge
  variation := ⟨positive, Addition.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end MarginEraseAdd

namespace ExistsMinRow

abbrev arena : Arena where
  signature := Subset.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M : Multiset (Finset V)} (hM : Comparable M) (hne : M ≠ 0),
    ∃ A, A ∈ M ∧ ∀ ⦃B⦄, B ∈ M → F.readout () ⟨V,A⟩ B = true

theorem bridge : (type_of% (@exists_min_row)) ↔ arena.Law Subset.actual := by
  classical
  simp only [arena, Subset.actual, realize, decide_eq_true_eq]

theorem positive : arena.Law Subset.actual := bridge.mp (@exists_min_row)

theorem negative : ¬ arena.Law Subset.rejected := by
  intro law
  obtain ⟨A, hA, hmin⟩ := law (M := oneEmpty) oneEmpty_comparable (by simp [oneEmpty])
  have hf := hmin hA
  change false = true at hf
  cases hf

theorem sensitivity : Sensitivity arena Subset.actual :=
  singletonSensitivity Subset.actual Subset.rejected arena.Law negative
theorem dependence : ObservationalDependence Subset.signature Subset.actual := Subset.dependence

def evidence : Registration arena (type_of% (@exists_min_row)) where
  actual := Subset.actual
  bridge := bridge
  variation := ⟨positive, Subset.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end ExistsMinRow

namespace ForwardStepMargin

abbrev arena : Arena where
  signature := NatEquality.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M N : Multiset (Finset V)} (h : ForwardStep M N),
    ∀ v, F.readout () () (margin M v) (margin N v)

theorem bridge : (type_of% (@forwardStep_margin)) ↔ arena.Law NatEquality.actual := Iff.rfl
theorem positive : arena.Law NatEquality.actual := @forwardStep_margin

theorem negative : ¬ arena.Law NatEquality.rejected := by
  intro law
  exact law crossing (0 : Fin 2)

theorem sensitivity : Sensitivity arena NatEquality.actual :=
  singletonSensitivity NatEquality.actual NatEquality.rejected arena.Law negative
theorem dependence : ObservationalDependence NatEquality.signature NatEquality.actual := NatEquality.dependence

def evidence : Registration arena (type_of% (@forwardStep_margin)) where
  actual := NatEquality.actual
  bridge := bridge
  variation := ⟨positive, NatEquality.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end ForwardStepMargin

namespace ForwardStepFamily

abbrev arena : Arena where
  signature := RowsInFamily.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {L : Finset (Finset V)} (hL : ClosedFamily L) {M N : Multiset (Finset V)}
    (hM : FamilyRows L M) (h : ForwardStep M N), F.readout () ⟨V,L⟩ N = true

theorem bridge : (type_of% (@forwardStep_family)) ↔ arena.Law RowsInFamily.actual := by
  classical
  simp only [arena, RowsInFamily.actual, realize, decide_eq_true_eq]

theorem positive : arena.Law RowsInFamily.actual := bridge.mp (@forwardStep_family)

theorem negative : ¬ arena.Law RowsInFamily.rejected := by
  intro law
  have hf := law fullFamily_closed crossInput_family crossing
  change false = true at hf
  cases hf

theorem sensitivity : Sensitivity arena RowsInFamily.actual :=
  singletonSensitivity RowsInFamily.actual RowsInFamily.rejected arena.Law negative
theorem dependence : ObservationalDependence RowsInFamily.signature RowsInFamily.actual := RowsInFamily.dependence

def evidence : Registration arena (type_of% (@forwardStep_family)) where
  actual := RowsInFamily.actual
  bridge := bridge
  variation := ⟨positive, RowsInFamily.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end ForwardStepFamily

namespace ForwardRouteMargin

abbrev arena : Arena where
  signature := NatEquality.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {M N : Multiset (Finset V)} {k : Nat} (h : ForwardRoute M N k),
    ∀ v, F.readout () () (margin M v) (margin N v)

theorem bridge : (type_of% (@forwardRoute_margin)) ↔ arena.Law NatEquality.actual := Iff.rfl
theorem positive : arena.Law NatEquality.actual := @forwardRoute_margin

theorem negative : ¬ arena.Law NatEquality.rejected := by
  intro law
  exact law (ForwardRoute.zero oneEmpty) (0 : Fin 1)

theorem sensitivity : Sensitivity arena NatEquality.actual :=
  singletonSensitivity NatEquality.actual NatEquality.rejected arena.Law negative
theorem dependence : ObservationalDependence NatEquality.signature NatEquality.actual := NatEquality.dependence

def evidence : Registration arena (type_of% (@forwardRoute_margin)) where
  actual := NatEquality.actual
  bridge := bridge
  variation := ⟨positive, NatEquality.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end ForwardRouteMargin

namespace ForwardRouteFamily

abbrev arena : Arena where
  signature := RowsInFamily.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {L : Finset (Finset V)} (hL : ClosedFamily L) {M N : Multiset (Finset V)} {k : Nat}
    (hM : FamilyRows L M) (h : ForwardRoute M N k), F.readout () ⟨V,L⟩ N = true

theorem bridge : (type_of% (@forwardRoute_family)) ↔ arena.Law RowsInFamily.actual := by
  classical
  simp only [arena, RowsInFamily.actual, realize, decide_eq_true_eq]

theorem positive : arena.Law RowsInFamily.actual := bridge.mp (@forwardRoute_family)

theorem negative : ¬ arena.Law RowsInFamily.rejected := by
  intro law
  have hf := law emptyFamily_closed oneEmpty_family (ForwardRoute.zero oneEmpty)
  change false = true at hf
  cases hf

theorem sensitivity : Sensitivity arena RowsInFamily.actual :=
  singletonSensitivity RowsInFamily.actual RowsInFamily.rejected arena.Law negative
theorem dependence : ObservationalDependence RowsInFamily.signature RowsInFamily.actual := RowsInFamily.dependence

def evidence : Registration arena (type_of% (@forwardRoute_family)) where
  actual := RowsInFamily.actual
  bridge := bridge
  variation := ⟨positive, RowsInFamily.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end ForwardRouteFamily

namespace ComparableOfNoForwardStep

abbrev arena : Arena where
  signature := Comparability.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    (M : Multiset (Finset V)) (h : ¬ ∃ N, ForwardStep M N), F.readout () V M = true

theorem bridge : (type_of% (@comparable_of_no_forward_step)) ↔ arena.Law Comparability.actual := by
  classical
  simp only [arena, Comparability.actual, realize, decide_eq_true_eq]

theorem positive : arena.Law Comparability.actual := bridge.mp (@comparable_of_no_forward_step)

theorem negative : ¬ arena.Law Comparability.rejected := by
  intro law
  have hf := law (0 : Multiset (Finset (Fin 2))) zero_no_forward
  change false = true at hf
  cases hf

theorem sensitivity : Sensitivity arena Comparability.actual :=
  singletonSensitivity Comparability.actual Comparability.rejected arena.Law negative
theorem dependence : ObservationalDependence Comparability.signature Comparability.actual := Comparability.dependence

def evidence : Registration arena (type_of% (@comparable_of_no_forward_step)) where
  actual := Comparability.actual
  bridge := bridge
  variation := ⟨positive, Comparability.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end ComparableOfNoForwardStep

namespace ThresholdRowsFamily

abbrev arena : Arena where
  signature := RowMembership.signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V]
    {L : Finset (Finset V)} (hL : ClosedFamily L) {M : Multiset (Finset V)}
    (hM : FamilyRows L M),
    FamilyRows L (thresholdRows M) ∧
      ∀ j : Fin M.card, F.readout () ⟨V,L⟩ (thresholdRow M j) = true

theorem bridge : (type_of% (@thresholdRows_family)) ↔ arena.Law RowMembership.actual := by
  classical
  simp only [arena, RowMembership.actual, realize, decide_eq_true_eq]

theorem positive : arena.Law RowMembership.actual := bridge.mp (@thresholdRows_family)

theorem negative : ¬ arena.Law RowMembership.rejected := by
  intro law
  have hf := (law emptyFamily_closed oneEmpty_family).2 ⟨0, by simp [oneEmpty]⟩
  change false = true at hf
  cases hf

theorem sensitivity : Sensitivity arena RowMembership.actual :=
  singletonSensitivity RowMembership.actual RowMembership.rejected arena.Law negative
theorem dependence : ObservationalDependence RowMembership.signature RowMembership.actual := RowMembership.dependence

def evidence : Registration arena (type_of% (@thresholdRows_family)) where
  actual := RowMembership.actual
  bridge := bridge
  variation := ⟨positive, RowMembership.rejected, negative⟩
  sensitivity := sensitivity
  dependence := dependence

end ThresholdRowsFamily

namespace MarginEraseAdd

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@margin_erase_add) (Realization Addition.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.margin_erase_add.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.MarginEraseAdd.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Addition.signature Addition.actual.readout Addition.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MarginEraseAdd


namespace ExistsMinRow

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_min_row) (Realization Subset.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.exists_min_row.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.ExistsMinRow.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Subset.signature Subset.actual.readout Subset.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExistsMinRow


namespace ForwardStepMargin

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@forwardStep_margin) (Realization NatEquality.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardStep_margin.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.ForwardStepMargin.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize NatEquality.signature NatEquality.actual.readout NatEquality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ForwardStepMargin


namespace ForwardStepFamily

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@forwardStep_family) (Realization RowsInFamily.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardStep_family.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.ForwardStepFamily.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RowsInFamily.signature RowsInFamily.actual.readout RowsInFamily.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ForwardStepFamily


namespace ForwardRouteMargin

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@forwardRoute_margin) (Realization NatEquality.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardRoute_margin.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.ForwardRouteMargin.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize NatEquality.signature NatEquality.actual.readout NatEquality.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ForwardRouteMargin


namespace ForwardRouteFamily

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@forwardRoute_family) (Realization RowsInFamily.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardRoute_family.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.ForwardRouteFamily.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RowsInFamily.signature RowsInFamily.actual.readout RowsInFamily.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ForwardRouteFamily


namespace ComparableOfNoForwardStep

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@comparable_of_no_forward_step) (Realization Comparability.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.comparable_of_no_forward_step.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.ComparableOfNoForwardStep.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Comparability.signature Comparability.actual.readout Comparability.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ComparableOfNoForwardStep


namespace ThresholdRowsFamily

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thresholdRows_family) (Realization RowMembership.signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.thresholdRows_family.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural.ThresholdRowsFamily.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RowMembership.signature RowMembership.actual.readout RowMembership.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ThresholdRowsFamily

end
end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Structural
