import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial
import Reg.Support.DependentFamily

noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial

abbrev binomialSignature : Signature where
  Params := Σ n : ℕ, Σ m : ℕ, Σ _ : Entry n m, ℕ
  State p := Entry p.1 p.2.1 → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def binomialActual : Realization binomialSignature :=
  realize binomialSignature (fun _ p z =>
    MvPolynomial.eval z (binomialEntry p.2.2.1 p.2.2.2))
    (fun e => nomatch e)

def binomialRejected : Realization binomialSignature :=
  realize binomialSignature (fun _ p z => binomialActual.readout () p z + 1)
    (fun e => nomatch e)

def binomialArena : Arena where
  signature := binomialSignature
  Law r := ∀ {n m : ℕ} (z : Entry n m → ℤ) (e : Entry n m) (k : ℕ),
    r.readout () ⟨n, m, e, k⟩ (fun e => (z e : ℚ)) = ((Ring.choose (z e) k : ℤ) : ℚ)

theorem binomial_actual_law : binomialArena.Law binomialActual := by
  intro n m z e k
  exact binomialEntry_eval_signed z e k

theorem binomial_rejected_law : ¬ binomialArena.Law binomialRejected := by
  intro h
  have he := h (fun _ : Entry 1 1 => (0 : ℤ)) (Sum.inl (0, 0)) 0
  change binomialActual.readout () ⟨1, 1, Sum.inl (0, 0), 0⟩ (fun _ => 0) + 1 = _ at he
  have hp := binomial_actual_law (fun _ : Entry 1 1 => (0 : ℤ)) (Sum.inl (0, 0)) 0
  change binomialActual.readout () ⟨1, 1, Sum.inl (0, 0), 0⟩ (fun _ => 0) = _ at hp
  rw [hp] at he
  linarith

def binomialRegistration : Registration binomialArena (binomialArena.Law binomialActual) where
  actual := binomialActual
  bridge := Iff.rfl
  variation := ⟨binomial_actual_law, binomialRejected, binomial_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨binomialRejected, ?_, rfl, binomial_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, 1, Sum.inl (0, 0), 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change MvPolynomial.eval (fun _ : Entry 1 1 => (0 : ℚ))
      (binomialEntry (Sum.inl (0, 0)) 1) ≠
        MvPolynomial.eval (fun _ : Entry 1 1 => (1 : ℚ))
          (binomialEntry (Sum.inl (0, 0)) 1)
    have h0 := binomialEntry_eval_signed (fun _ : Entry 1 1 => (0 : ℤ))
      (Sum.inl (0, 0)) 1
    have h1 := binomialEntry_eval_signed (fun _ : Entry 1 1 => (1 : ℤ))
      (Sum.inl (0, 0)) 1
    simp only [Ring.choose_one_right, Int.cast_zero, Int.cast_one] at h0 h1
    rw [h0, h1]
    exact zero_ne_one

noncomputable def registration_binomial : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.binomialEntry_eval_signed)
    (type_of% (realize binomialSignature (fun _ p z =>
      MvPolynomial.eval z (binomialEntry p.2.2.1 p.2.2.2))
      (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial.binomial
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial.binomialRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨binomialArena⟩
  objectArena := .source ⟨binomialArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source binomialArena ⟨binomialRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize binomialSignature (fun _ p z =>
    MvPolynomial.eval z (binomialEntry p.2.2.1 p.2.2.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial
    definition := none
    coordinates := #[0, 1, 3, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial
