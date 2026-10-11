import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CountedExchangeChain
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.Coding.CountedExchangeChain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain

abbrev signature : Signature where
  Params := ℕ
  State m := CountMat m m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := CountMat m m
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ B => B) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n m : ℕ} {A : CountMat n n} {B : CountMat m m} {L : ℕ}
    (c : ExchangeChain ℕ A B L), Nonempty (WindowConjugacy A (R.readout () m B) L)

theorem actual_law : arena.Law actual := by
  intro n m A B L c
  exact chain_has_window_conjugacy c

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A : CountMat 1 1 := fun _ _ => 1
  let x : Path A := ⟨fun _ => ⟨0, 0, 0⟩, fun _ => rfl⟩
  obtain ⟨f⟩ := h (ExchangeChain.nil A)
  exact Fin.elim0 ((f.homeomorph x).val 0).number

def registration : Registration arena
    (∀ {n m : ℕ} {A : CountMat n n} {B : CountMat m m} {L : ℕ}
      (c : ExchangeChain ℕ A B L), Nonempty (WindowConjugacy A B L)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (m : ℕ) (x y : CountMat m m), x ≠ y
    refine ⟨1, (fun _ _ => 1), (fun _ _ => 2), ?_⟩
    intro h
    have hentry := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
    exact (by decide : (1 : ℕ) ≠ 2) hentry

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.chain_has_window_conjugacy) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ B => B) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CountedExchangeChain") "chain_has_window_conjugacy") "Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain/Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ B => B) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain, definition := none, coordinates := #[1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain
