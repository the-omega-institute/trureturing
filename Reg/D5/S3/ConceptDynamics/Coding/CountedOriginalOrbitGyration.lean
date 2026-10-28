import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
noncomputable section

abbrev cardinalSignature : Signature where
  Params := Σ' _n : ℕ, Σ' d : ℕ, NeZero d
  State p := CountMat p.1 p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def cardinalActual : Realization cardinalSignature :=
  realize cardinalSignature (fun _ p A =>
    letI : NeZero p.2.1 := p.2.2
    Fintype.card (PrimitivePath A p.2.1)) (fun e => nomatch e)

def cardinalRejected : Realization cardinalSignature :=
  realize cardinalSignature (fun _ p A => cardinalActual.readout () p A + 1)
    (fun e => nomatch e)

def cardinalArena : Arena where
  signature := cardinalSignature
  Law r := ∀ {n : ℕ} (A : CountMat n n) (d : ℕ) [h : NeZero d],
    r.readout () ⟨n, d, h⟩ A = d * Fintype.card (ActualPathOrbit A d)

private theorem cardinal_actual_law : cardinalArena.Law cardinalActual := by
  intro n A d h
  exact primitivePath_card_eq_period_mul_orbit_card A d

private theorem cardinal_rejected_law : ¬ cardinalArena.Law cardinalRejected := by
  intro h
  let A : CountMat 0 0 := fun _ _ => 0
  have he := h A 1
  have ha := primitivePath_card_eq_period_mul_orbit_card A 1
  change Fintype.card (PrimitivePath A 1) + 1 = _ at he
  omega

private theorem cardinal_dependence : ObservationalDependence cardinalSignature cardinalActual := by
  intro i
  cases i
  let A₀ : CountMat 1 1 := fun _ _ => 0
  let A₁ : CountMat 1 1 := fun _ _ => 1
  haveI : IsEmpty (PrimitivePath A₀ 1) :=
    ⟨fun x => Fin.elim0 (x.val.val 0).number⟩
  let a : LegalWord A₁ 1 := ⟨fun _ => ⟨0, 0, 0⟩, fun _ => rfl⟩
  have ha : Primitive a.val := by
    intro k hk
    exact (hk (Subsingleton.elim _ _)).elim
  have hp : 0 < Fintype.card (PrimitivePath A₁ 1) :=
    Fintype.card_pos_iff.mpr ⟨primitiveWordEquiv A₁ ⟨a, ha⟩⟩
  refine ⟨⟨1, 1, inferInstance⟩, A₀, A₁, ?_⟩
  change Fintype.card (PrimitivePath A₀ 1) ≠ Fintype.card (PrimitivePath A₁ 1)
  rw [Fintype.card_eq_zero]
  exact (Nat.ne_of_gt hp).symm

def cardinalRegistration : Registration cardinalArena
    (∀ {n : ℕ} (A : CountMat n n) (d : ℕ) [NeZero d],
      Fintype.card (PrimitivePath A d) = d * Fintype.card (ActualPathOrbit A d)) where
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
  dependence := cardinal_dependence

def registration_cardinal : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.primitivePath_card_eq_period_mul_orbit_card)
    (type_of% (realize cardinalSignature (fun _ p A =>
      letI : NeZero p.2.1 := p.2.2
      Fintype.card (PrimitivePath A p.2.1)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration.cardinal
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration.cardinalRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨cardinalArena⟩
  objectArena := .source ⟨cardinalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cardinalArena ⟨cardinalRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardinalSignature (fun _ p A =>
    letI : NeZero p.2.1 := p.2.2
    Fintype.card (PrimitivePath A p.2.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
