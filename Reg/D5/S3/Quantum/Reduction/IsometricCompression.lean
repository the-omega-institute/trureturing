import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Reduction.IsometricCompression
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Reduction.IsometricCompression
open LeanInformationAudit
open scoped Matrix BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Reduction.IsometricCompression
universe u v w

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := Matrix p.1 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p.1 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {n : Type u} {d : Type v}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    {ι : Type w} (U : Matrix n d ℂ)
    (K : ι → Matrix n n ℂ) (k : ι → Matrix d d ℂ)
    (h : ∀ a, K a * U = U * k a) (w : List ι),
    (w.map K).prod * U = r.readout () ⟨n,d⟩ U * (w.map k).prod

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n d _ _ _ _ ι U K k h w
  exact word_intertwines U K k h w

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let U : Matrix (ULift.{u} (Fin 1)) (ULift.{v} (Fin 1)) ℂ := fun _ _ => 1
  have heq := h U (fun _ : ULift.{w} (Fin 1) => 0) (fun _ => 0)
    (by intro a; simp) []
  have hz : U = 0 := by simpa [rejected, realize] using heq
  have hentry := congrFun (congrFun hz (ULift.up 0)) (ULift.up 0)
  exact one_ne_zero (show (1 : ℂ) = 0 from hentry)

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩, (fun _ _ => (0 : ℂ)), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

noncomputable def registration_1.{u_1, u_2, u_5} : LeanInformationAudit.Contract.Registration.{max ((max u_1 u_2) + 2) ((max (u_1 + 1) (u_2 + 1)) + 2), max ((max u_1 u_2) + 2) ((max (u_1 + 1) (u_2 + 1)) + 2), max (u_1 + 1) (u_2 + 1), 1, 1, 0, 1, 1, 0, 0, 0, max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0, 0} (@_root_.D5.S3.Quantum.Reduction.IsometricCompression.word_intertwines.{u_1, u_2, u_5}) (type_of% (arena.{u_1, u_2, u_5})) (type_of% (arena.{u_1, u_2, u_5})) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Reduction") "IsometricCompression") "word_intertwines") "Reg.D5.S3.Quantum.Reduction.IsometricCompression/Reg.D5.S3.Quantum.Reduction.IsometricCompression.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u_1, u_2, u_5})⟩,
  objectArena := ⟨(arena.{u_1, u_2, u_5})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_5}) ⟨(registration.{u_1, u_2, u_5})⟩,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Reduction.IsometricCompression, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.Quantum.Reduction.IsometricCompression
