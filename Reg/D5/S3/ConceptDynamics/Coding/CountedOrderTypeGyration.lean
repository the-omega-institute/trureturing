import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
import Reg.Support.DependentFamily

noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

abbrev timeSignature : Signature where
  Params := Σ' d : ℕ, NeZero d
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def timeActual : Realization timeSignature :=
  realize timeSignature (fun _ p t =>
    letI : NeZero p.1 := p.2
    timeIndex (t.val : ℤ)) (fun e => nomatch e)

def timeRejected : Realization timeSignature :=
  realize timeSignature (fun _ p _ => ⟨0, by
      letI : NeZero p.1 := p.2
      exact Nat.pos_of_ne_zero (NeZero.ne p.1)⟩)
    (fun e => nomatch e)

def timeArena : Arena where
  signature := timeSignature
  Law r := ∀ {d : ℕ} [h : NeZero d] (t : Fin d),
    r.readout () ⟨d, h⟩ t = t

theorem time_actual_law : timeArena.Law timeActual := by
  intro d h t
  exact timeIndex_nat t

theorem time_rejected_law : ¬ timeArena.Law timeRejected := by
  intro h
  have he := congrArg Fin.val (h (1 : Fin 2))
  change 0 = 1 at he
  exact Nat.zero_ne_one he

def timeRegistration : Registration timeArena (timeArena.Law timeActual) where
  actual := timeActual
  bridge := Iff.rfl
  variation := ⟨time_actual_law, timeRejected, time_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨timeRejected, ?_, rfl, time_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨2, inferInstance⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
    change timeIndex ((0 : Fin 2).val : ℤ) ≠ timeIndex ((1 : Fin 2).val : ℤ)
    rw [timeIndex_nat, timeIndex_nat]
    decide

noncomputable def registration_time : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.timeIndex_nat)
    (type_of% (realize timeSignature (fun _ p t =>
      letI : NeZero p.1 := p.2
      timeIndex (t.val : ℤ)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.time
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.timeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨timeArena⟩
  objectArena := .source ⟨timeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source timeArena ⟨timeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize timeSignature (fun _ p t =>
    letI : NeZero p.1 := p.2
    timeIndex (t.val : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev cardinalSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def cardinalActual : Realization cardinalSignature :=
  realize cardinalSignature (fun _ z k => Fintype.card (Increasing z k))
    (fun e => nomatch e)

def cardinalRejected : Realization cardinalSignature :=
  realize cardinalSignature (fun _ z k => cardinalActual.readout () z k + 1)
    (fun e => nomatch e)

def cardinalArena : Arena where
  signature := cardinalSignature
  Law r := ∀ z k : ℕ, r.readout () z k = Nat.choose z k

theorem cardinal_actual_law : cardinalArena.Law cardinalActual := by
  intro z k
  exact increasing_card z k

theorem cardinal_rejected_law : ¬ cardinalArena.Law cardinalRejected := by
  intro h
  have he := h 0 0
  change cardinalActual.readout () 0 0 + 1 = _ at he
  rw [cardinal_actual_law] at he
  norm_num at he

def cardinalRegistration : Registration cardinalArena (cardinalArena.Law cardinalActual) where
  actual := cardinalActual
  bridge := Iff.rfl
  variation := ⟨cardinal_actual_law, cardinalRejected, cardinal_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cardinalRejected, ?_, rfl, cardinal_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), ?_⟩
    change Fintype.card (Increasing 0 0) ≠ Fintype.card (Increasing 0 1)
    rw [increasing_card, increasing_card]
    decide

noncomputable def registration_cardinal : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.increasing_card)
    (type_of% (realize cardinalSignature (fun _ z k => Fintype.card (Increasing z k))
      (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.cardinal
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.cardinalRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨cardinalArena⟩
  objectArena := .source ⟨cardinalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cardinalArena ⟨cardinalRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardinalSignature (fun _ z k => Fintype.card (Increasing z k))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
