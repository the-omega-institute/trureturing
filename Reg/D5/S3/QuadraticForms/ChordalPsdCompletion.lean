import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.ChordalPsdCompletion
import D5.S3.Combinatorics.Graph.Chordal.Characterization
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ChordalPsdCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.ChordalPsdCompletion

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ V : Type u, Matrix V V ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

/-- The complete original telescope, varying only the requested entry readout. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law Z := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (_hG : G.IsChordal)
    (A : Matrix V V ℝ)
    (_hA : ∀ C : Set V, G.IsClique C →
      (A.submatrix (Subtype.val : C → V) Subtype.val).PosSemidef),
    ∃ B : Matrix V V ℝ, B.PosSemidef ∧
      ∀ i j, i = j ∨ G.Adj i j → B i j = Z.readout () ⟨V, A⟩ i j

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin 1)
  let G : SimpleGraph V := ⊥
  have hp : G.IsPEO (fun i => i.down.val) := by
    refine ⟨fun i j _ => Subsingleton.elim _ _, ?_⟩
    intro v i hi
    exact hi.2.elim
  have hz (C : Set V) (_hC : G.IsClique C) :
      ((0 : Matrix V V ℝ).submatrix (Subtype.val : C → V) Subtype.val).PosSemidef := by
    have he : (0 : Matrix V V ℝ).submatrix (Subtype.val : C → V) Subtype.val =
        (0 : Matrix C C ℝ) := by ext i j; rfl
    rw [he]
    exact Matrix.PosSemidef.zero
  obtain ⟨B, hB, hb⟩ := h G hp.isChordal (0 : Matrix V V ℝ) hz
  let i : V := ⟨0⟩
  have hi := hb i i (Or.inl rfl)
  have hn := hB.diag_nonneg (i := i)
  change B i i = -1 at hi
  linarith

def evidence : Registration arena.{u}
    (type_of% @exists_posSemidef_completion.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_posSemidef_completion.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let V := ULift.{u} (Fin 2)
    let A : Matrix V V ℝ := fun x _ => x.down.val
    refine ⟨⟨V, A⟩, ⟨0⟩, ⟨1⟩, ?_⟩
    intro he
    have hh := congrFun he (⟨0⟩ : V)
    norm_num [actual, realize, A] at hh

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_posSemidef_completion.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.QuadraticForms.ChordalPsdCompletion.exists_posSemidef_completion.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.ChordalPsdCompletion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.ChordalPsdCompletion
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.ChordalPsdCompletion
