import D5.S3.Arith.Additive.BenfieldLippard.PositiveFixedLength
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Additive.BenfieldLippard.PositiveFixedLength

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false

private abbrev signature := Reg.Support.SingleDependentReadout.signature
  (ℕ × ℕ) (fun _ => ℕ) (fun _ => Prop)

private def actual : Realization signature :=
  realize signature (fun _ p n => BenfieldLippard.PosRep p.1 p.2 n) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 2 ≤ k → ∃ j : ℕ, 1 ≤ j ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    R.readout () (k, j) n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨j, _, N, hn⟩ := h 2 le_rfl
  exact hn N le_rfl

def family : Registration arena (type_of% BenfieldLippard.eventual_fixed_length) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨BenfieldLippard.eventual_fixed_length, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨(2, 1), 0, 1, ?_⟩
    change BenfieldLippard.PosRep 2 1 0 ≠ BenfieldLippard.PosRep 2 1 1
    intro h
    have hOne : BenfieldLippard.PosRep 2 1 1 := ⟨fun _ => 1, by simp, by simp⟩
    obtain ⟨f, hPos, hSum⟩ := Eq.mpr h hOne
    rw [Fin.sum_univ_one] at hSum
    exact (pow_pos (hPos 0) _).ne' hSum.symm

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    BenfieldLippard.eventual_fixed_length (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Additive.BenfieldLippard.PositiveFixedLength.eventual_fixed_length.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.BenfieldLippard.PositiveFixedLength.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => BenfieldLippard.PosRep p.1 p.2 n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.BenfieldLippard.PositiveFixedLength
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "body", "body", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Additive.BenfieldLippard.PositiveFixedLength
