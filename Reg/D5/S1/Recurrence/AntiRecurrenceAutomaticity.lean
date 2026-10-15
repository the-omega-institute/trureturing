import D5.S1.Recurrence.AntiRecurrenceAutomaticity
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S1.Recurrence.AntiRecurrenceAutomaticity

open _root_.D5.S1.Recurrence.AntiRecurrenceAutomaticity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

noncomputable section

abbrev signature : Signature where
  Params := Σ k : ℕ, Σ _ : Fin k → ℕ, ℕ → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => discrepancy p.1 p.2.1 p.2.2 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p n => (p.2.2 n : ℤ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j),
    ∃ A B : ℕ → ℕ, Source k a A B ∧
      (∀ A' B', Source k a A' B' → A' = A ∧ B' = B) ∧
      Automatic (trace k a) (by
        have h : k ≤ trace k a := by
          calc
            k = ∑ _j : Fin k, 1 := by simp
            _ ≤ ∑ j : Fin k, a j := sum_le_sum (fun j _ => ha j)
            _ = trace k a := rfl
        omega) (R.readout () ⟨k, a, A⟩)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  obtain ⟨A, B, hS, _, hAuto⟩ := h 2 (fun _ => 1) (by omega) (by intro j; omega)
  change Automatic (trace 2 (fun _ => 1)) _ (fun n => (A n : ℤ)) at hAuto
  obtain ⟨Q, inst, M, hM⟩ := hAuto
  letI : Fintype Q := inst
  let C : ℤ := ∑ q : Q, |M.output q|
  have hC : 0 ≤ C := sum_nonneg (fun q _ => abs_nonneg (M.output q))
  let n := C.toNat + 1
  have hn : C < (n : ℤ) := by
    dsimp [n]
    rw [Int.toNat_of_nonneg hC]
    omega
  have hb : |(A n : ℤ)| ≤ C := by
    have hm := hM n
    change M.evalOutput _ = (A n : ℤ) at hm
    rw [← hm]
    exact single_le_sum (fun q _ => abs_nonneg (M.output q)) (mem_univ _)
  have hA : (n : ℤ) ≤ A n := by exact_mod_cast hS.monoA.id_le n
  have hv : (A n : ℤ) ≤ C := (le_abs_self _).trans hb
  omega

def registration : Registration arena
    (type_of% (@_root_.D5.S1.Recurrence.AntiRecurrenceAutomaticity.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Recurrence.AntiRecurrenceAutomaticity.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2, (fun _ => 1), (fun _ => 0)⟩, 0, 1, ?_⟩
    norm_num [actual, realize, discrepancy, slope, trace]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.AntiRecurrenceAutomaticity.result)
    (Realization signature) Unit Unit := {
  unitName := `D5.S1.Recurrence.AntiRecurrenceAutomaticity.result.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.AntiRecurrenceAutomaticity.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => discrepancy p.1 p.2.1 p.2.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.AntiRecurrenceAutomaticity
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
#print axioms audit

end
end Reg.D5.S1.Recurrence.AntiRecurrenceAutomaticity
