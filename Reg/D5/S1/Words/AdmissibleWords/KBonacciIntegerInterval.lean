import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
import Reg.Support.DependentFamily

open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.ClosedRunStarts
open D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ∀ {n : ℕ}, (Fin n → Bool) → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => @integerValue k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun {_} _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k n : ℕ), 2 ≤ k →
    Set.BijOn (R.readout () () k (n := n))
      {w : Fin n → Bool | ∀ s : ℕ, ¬ TrueBlock w s k}
      (Set.Ico (0 : ℤ) (dbonacci k (n + 2) : ℤ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (1 : ℤ) ∈ Set.Ico (0 : ℤ) (dbonacci 2 (1 + 2) : ℤ) := by
    norm_num [dbonacci_add_two_of_lt]
  obtain ⟨w, _, he⟩ := (h 2 1 (by decide)).surjOn hz
  change (0 : ℤ) = 1 at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  intro he
  have h := congrArg (fun f : ∀ {n : ℕ}, (Fin n → Bool) → ℤ =>
    @f 3 (fun j => decide (j.val = 2))) he
  change integerValue 2 (fun j : Fin 3 => decide (j.val = 2)) =
    integerValue 3 (fun j : Fin 3 => decide (j.val = 2)) at h
  have hwTwo : dbonacci 2 4 = 3 := by
    rw [show 4 = 2 + 2 by rfl, dbonacci_add_two_of_le 2 2 (by decide)]
    norm_num [Fin.sum_univ_succ, dbonacci_add_two_of_lt]
  have hwThree : dbonacci 3 4 = 4 := by
    simpa using dbonacci_add_two_of_lt 3 2 (by decide)
  have htwo : integerValue 2 (fun j : Fin 3 => decide (j.val = 2)) = 3 := by
    norm_num [integerValue, Fin.sum_univ_succ, hwTwo, hwThree]
  have hthree : integerValue 3 (fun j : Fin 3 => decide (j.val = 2)) = 4 := by
    norm_num [integerValue, Fin.sum_univ_succ, hwTwo, hwThree]
  rw [htwo, hthree] at h
  norm_num at h

def registration : Registration arena (type_of% integer_value_interval_bijection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integer_value_interval_bijection, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval.integer_value_interval_bijection)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ _ k => @integerValue k) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval.integer_value_interval_bijection.__information_unit,
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ k => @integerValue k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
