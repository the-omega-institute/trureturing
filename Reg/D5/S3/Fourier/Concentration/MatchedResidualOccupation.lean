import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.MatchedResidualOccupation

/-! Dependence of the permutation bound on the residual degree and edge mass. -/

namespace Reg.D5.S3.Fourier.Concentration.MatchedResidualOccupation

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open _root_.D5.S3.Fourier.Concentration.MatchedResidualOccupation
open _root_.D5.S3.Quantum.Entanglement.OccupancyWordSectors
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ × ℝ) (fun _ => ℝ)

private def permutationBudget (x : ℕ × ℝ) : ℝ :=
  (x.1.factorial : ℝ) * x.2 ^ x.1

def actual : Realization signature :=
  realize signature (fun _ _ x => permutationBudget x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J] {d : ℕ}
      (w : J → ℝ), (∀ j, 0 ≤ w j) → ∀ (E : J → J → Prop) [DecidableRel E]
      (S : Finset ((J → ℕ) × (J → ℕ))),
    (∀ x ∈ S, ∃ u v : Word J d, (occupation u).count = x.1 ∧
      (occupation v).count = x.2 ∧ ∀ i, E (u i) (v i)) →
    let budget := V.readout () ()
    (∑ x ∈ S, monomialWeight w x.1 * monomialWeight w x.2) ≤
      budget (d, ∑ e : J × J, if E e.1 e.2 then w e.1 * w e.2 else 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law (J := ULift.{u} Unit) (d := 1) (fun _ => 0) (fun _ => le_rfl)
    (fun _ _ => False) ∅ (by simp)
  norm_num [rejected, realize] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (1, 0), (1, 1), ?_⟩
  change permutationBudget (1, 0) ≠ permutationBudget (1, 1)
  norm_num [permutationBudget]

def evidence : Registration arena.{u} (type_of% @matched_occupation_mass_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matched_occupation_mass_le.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@matched_occupation_mass_le.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.MatchedResidualOccupation.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.MatchedResidualOccupation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => permutationBudget x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.MatchedResidualOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.MatchedResidualOccupation
