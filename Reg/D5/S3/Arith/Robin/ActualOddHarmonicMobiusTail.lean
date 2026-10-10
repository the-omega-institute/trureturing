import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail
open Finset
open _root_.D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail
open _root_.D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel (harmonicPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ N : ℕ, |harmonicPrefix N| ≤ 1 ∧ |R.readout () () N| ≤ 2) ∧
    R.readout () () 1 = 1 ∧
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      weightedOddTail D M b = b M*(R.readout () () M-R.readout () () D) +
        ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*(R.readout () () n-R.readout () () D)) ∧
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      (∀ n ∈ Icc (D+1) M, 0 ≤ b n) →
      AntitoneOn b (Set.Icc (D+1) M) →
      (-2-R.readout () () D)*b (D+1) ≤ weightedOddTail D M b ∧
      weightedOddTail D M b ≤ (2-R.readout () () D)*b (D+1) ∧
      |weightedOddTail D M b| ≤ 4*b (D+1))

def actual : Realization signature :=
  realize signature (fun _ _ n => oddHarmonicPrefix n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hunit := h.2.1
  change (0 : ℝ) = 1 at hunit
  norm_num at hunit

def registration : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change oddHarmonicPrefix 0 ≠ oddHarmonicPrefix 1
    rw [result.2.1]
    simp [oddHarmonicPrefix]

noncomputable def registration_1 :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      result (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail.resultUnit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail
