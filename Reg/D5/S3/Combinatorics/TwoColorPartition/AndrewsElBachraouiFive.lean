import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive
import Reg.Support.SingleDependentReadout
import Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
open Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts

namespace Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℤ)

noncomputable def actual : Realization signature :=
  realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ k m : ℕ, 1 ≤ m → m < k →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ r.readout () ⟨k,m⟩ n

noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℤ)) (fun e => nomatch e)

theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨N, hN⟩ := h 2 1 (by decide) (by decide)
  have hn := hN N le_rfl
  norm_num [bad, realize] at hn

noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive.result,
    bad, bad_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_not_law
  dependence := by
    intro i
    refine ⟨⟨2,1⟩, 0, 2, ?_⟩
    change dCoeff 2 1 0 ≠ dCoeff 2 1 2
    rw [dCoeff_zero, dCoeff_two]
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive.result)
    (type_of% (realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => dCoeff p.1 p.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFive
