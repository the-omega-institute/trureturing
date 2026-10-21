import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.EtaOddOccupation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Partitions.EtaOddOccupation
open LeanInformationAudit Complex

noncomputable section

namespace Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

namespace Normalization

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (r : ℕ) (c τ : ℂ) (_ : 0 < τ.im),
    a.readout () ()
      (c * exp (2 * Real.pi * I * τ * r / 48) *
        oddCoefficientSeries r (exp (Real.pi * I * τ)))
      (c * (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ r)

theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_eq_eta)) ↔ arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := @D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_eq_eta

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 I (by norm_num)

def family : Registration arena (type_of% (@D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_eq_eta)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_eq_eta) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.Normalization.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.Normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.EtaOddOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalization

namespace S

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (m : ℕ) (c τ : ℂ) (_ : 0 < τ.im),
    a.readout () ()
      (c * exp (2 * Real.pi * I * (-1 / τ) * (2 * m) / 48) *
        oddCoefficientSeries (2 * m) (exp (Real.pi * I * (-1 / τ))))
      (c * ((2 : ℂ) ^ m)⁻¹ *
        (ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ (2 * m))

theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_S)) ↔ arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := @D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_S

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 I (by norm_num)

def family : Registration arena (type_of% (@D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_S)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.EtaOddOccupation.normalized_odd_character_S) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.S.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.S.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.EtaOddOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end S

end Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation

#print axioms Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.Normalization.family
#print axioms Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.Normalization.audit
#print axioms Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.S.family
#print axioms Reg.D5.S3.Combinatorics.Partitions.EtaOddOccupation.S.audit
