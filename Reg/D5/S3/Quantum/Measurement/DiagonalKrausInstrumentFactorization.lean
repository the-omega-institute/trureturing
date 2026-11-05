import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
import Reg.Support.DependentFamily

/-! Source-bound registrations for diagonal Kraus instrument coordinates. -/

set_option linter.style.longLine false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
universe u_1 u_2 u_3 u_4 u_5

abbrev FamilyParams := Σ I : Type u_1, Σ O : Type u_2, Σ A : Type u_3,
  Σ B : Type u_4, Σ R : Type u_5, A → B → R → Matrix O I ℂ

abbrev signature : Signature where
  Params := FamilyParams.{u_1,u_2,u_3,u_4,u_5}
  State z := z.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ z := z.2.2.2.1 → z.2.2.2.2.1 → Matrix z.2.1 z.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1,u_2,u_3,u_4,u_5} :=
  realize signature (fun _ z => z.2.2.2.2.2) (fun e _ => Empty.elim e)

def rejected : Realization signature.{u_1,u_2,u_3,u_4,u_5} :=
  realize signature (fun _ _ _ _ _ _ _ => 0) (fun e _ => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u_1,u_2,u_3,u_4,u_5}
  Law L :=
    ∀ {I : Type u_1} {O : Type u_2} {A : Type u_3} {B : Type u_4} {R : Type u_5}
      [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      [Fintype B] [Fintype R]
      (K : A → B → R → Matrix O I ℂ)
    (_hcomplete : ∀ a, ∑ b, ∑ r, (K a b r).conjTranspose * K a b r = 1),
    (∀ a b o i, 0 ≤ weight K a b o i) ∧
    (∀ a i, ∑ b, ∑ o, weight (L.readout () ⟨I, O, A, B, R, K⟩) a b o i = 1) ∧
    ((∀ a b i o o', o ≠ o' →
        ∑ r, K a b r o i * (starRingEnd ℂ) (K a b r o' i) = 0) ↔
      ∀ (p : I → ℂ) a b,
        MatrixMap.of_kraus (K a b) (K a b) (Matrix.diagonal p) =
          Matrix.diagonal fun o => (∑ i, (weight K a b o i : ℂ) * p i)) ∧
    (∀ a, ∃ channel : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel I O,
      ∀ rho : Matrix I I ℂ,
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
          ∑ b, MatrixMap.of_kraus (K a b) (K a b) rho)

-- The scalar normal form is used by the subsequent `change`.
set_option linter.flexible false in
private theorem rejected_law : ¬ arena.{u_1,u_2,u_3,u_4,u_5}.Law rejected := by
  intro h
  let K : ULift.{u_3} Unit → ULift.{u_4} Unit → ULift.{u_5} Unit →
      Matrix (ULift.{u_2} Unit) (ULift.{u_1} Unit) ℂ := fun _ _ _ _ _ => 1
  have hc : ∀ a, ∑ b, ∑ r, (K a b r).conjTranspose * K a b r = 1 := by
    intro a
    simp only [Fintype.sum_unique]
    ext i j
    rw [Matrix.mul_apply]
    simp [K, Matrix.one_apply, Subsingleton.elim i j]
    change star (1 : ℂ) = 1
    simp
  have hh := (h K hc).2.1 ⟨()⟩ ⟨()⟩
  norm_num [rejected, realize, weight] at hh

private theorem dependence : ObservationalDependence signature.{u_1,u_2,u_3,u_4,u_5} actual := by
  intro role
  let z : FamilyParams.{u_1,u_2,u_3,u_4,u_5} :=
    ⟨ULift.{u_1} Unit, ULift.{u_2} Unit, ULift.{u_3} Bool, ULift.{u_4} Unit, ULift.{u_5} Unit,
      (fun a _ _ _ _ => if a.down then 1 else 0)⟩
  refine ⟨z, ⟨false⟩, ⟨true⟩, ?_⟩
  intro he
  have hh := congrFun (congrFun (congrFun (congrFun he ⟨()⟩) ⟨()⟩) ⟨()⟩) ⟨()⟩
  norm_num [actual, realize, z] at hh

def family : Registration arena.{u_1,u_2,u_3,u_4,u_5}
    (type_of% (@diagonal_instrument_factorization.{u_1,u_2,u_3,u_4,u_5})) where
  actual := realize signature.{u_1,u_2,u_3,u_4,u_5} (fun _ z => z.2.2.2.2.2) (fun e _ => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@diagonal_instrument_factorization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hother
      exact (hother (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence


def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonal_instrument_factorization.{u_1,u_2,u_3,u_4,u_5})
    (Realization signature.{u_1,u_2,u_3,u_4,u_5}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1,u_2,u_3,u_4,u_5}⟩
  objectArena := .source ⟨arena.{u_1,u_2,u_3,u_4,u_5}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1,u_2,u_3,u_4,u_5} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1,u_2,u_3,u_4,u_5} (fun _ z => z.2.2.2.2.2) (fun e _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 11]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "fn", "fn", "fn", "fn", "arg"], stateBinder := 0, functionOperand := true,
        stateOperand := none, booleanPredicate := false } ] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization

set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.diagonal_entry_expansion

namespace Reg.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
noncomputable section
namespace DiagonalEntryExpansion

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => (starRingEnd ℂ) x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena.{u, v, w} : Arena where
  signature := signature
  Law L := ∀ {I : Type u} {O : Type v} {R : Type w}
    [Fintype I] [DecidableEq I] [Fintype R]
    (K : R → Matrix O I ℂ) (p : I → ℂ) (o o' : O),
    MatrixMap.of_kraus K K (Matrix.diagonal p) o o' =
      ∑ i, (∑ r, K r o i * L.readout () () (K r o' i)) * p i

set_option backward.isDefEq.respectTransparency false in
private theorem rejected_law.{u, v, w} : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit)
    inferInstance inferInstance inferInstance (fun _ _ _ => 1) (fun _ => 1) ⟨()⟩ ⟨()⟩
  rw [diagonal_entry_expansion] at hb
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (starRingEnd ℂ) 0 ≠ (starRingEnd ℂ) 1
  simp

def source_registration.{u, v, w} : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.diagonal_entry_expansion.{u, v, w})) where
  actual := realize signature (fun _ _ x => (starRingEnd ℂ) x) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.diagonal_entry_expansion.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u, v, w} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.diagonal_entry_expansion.{u, v, w}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.diagonal_entry_expansion.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization.DiagonalEntryExpansion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (starRingEnd ℂ) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end DiagonalEntryExpansion

end
end Reg.D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
