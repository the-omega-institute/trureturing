import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.OeisA398589EventualPeriodicity
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.OeisA398589EventualPeriodicity

namespace Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ k t => row k t) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ t => t) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ k : ℕ, ∃ N p : ℕ, 0 < p ∧
    ∀ t : ℕ, N ≤ t → r.readout () k (t + p) = r.readout () k t

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, p, hp, ht⟩ := h 0
  have heq := ht N le_rfl
  change N + p = N at heq
  omega

noncomputable def registration : Registration arena
    (∀ k : ℕ, ∃ N p : ℕ, 0 < p ∧
      ∀ t : ℕ, N ≤ t → row k (t + p) = row k t) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventual_periodicity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    classical
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change row 1 0 ≠ row 1 1
    have hz : row 1 0 = 1 := by
      unfold row
      rw [Nat.strongRec_eq]
      simp [rowStep]
    intro heq
    have he : row 1 1 = 1 := heq.symm.trans hz
    have hstep : row 1 1 = rowStep 1 1 (fun m _ => row 1 m) := by
      unfold row
      rw [Nat.strongRec_eq]
    rw [hstep] at he
    unfold rowStep at he
    rw [dif_neg (by decide : ¬ (1 : ℕ) = 0)] at he
    generalize_proofs h at he
    have hbad := (Nat.find_spec h).2 0 (by decide) (by
      simpa [hz] using he.symm)
    rw [he] at hbad
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ k t => row k t) (fun a => nomatch a))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "OeisA398589EventualPeriodicity") "eventual_periodicity") "Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity/Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ k t => row k t) (fun a => nomatch a)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "arg", "body", "arg", "body", "arg", "body", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms _root_.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity
#print axioms registration
end Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity
