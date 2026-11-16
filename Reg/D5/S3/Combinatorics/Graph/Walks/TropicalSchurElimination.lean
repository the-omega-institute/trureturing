import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination

/-! Source-bound audits of the whole min-plus edge-weight family. -/
open _root_.D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal
set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination
universe u
noncomputable section
local instance (X : Type u) : Quiver.{0} X := completeQuiver X

private theorem endpoints_eq_of_top_bound {X : Type u} {a z : X} (q : Walk a z)
    (h : weight (fun _ _ => (⊤ : ℝ≥0∞)) q ≤ 0) : a = z := by
  cases q with
  | nil => rfl
  | cons q e => simp [weight] at h

abbrev signature : Signature where
  Params := Type u
  State V := V → V → ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := ∀ b : V, {x : V // x ≠ b} → {x : V // x ≠ b} → ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ W => schur W) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} (W : V → V → ℝ≥0∞) (b : V)
    (a z : {x : V // x ≠ b}),
    (∀ p : Walk a.val z.val, ∃ q : Walk a z,
      weight (R.readout () V W b) q ≤ weight W p) ∧
    (∀ q : Walk a z, ∃ p : Walk a.val z.val,
      weight W p = weight (R.readout () V W b) q) ∧
    distance (R.readout () V W b) a z = distance W a.val z.val

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let b : ULift.{u} (Fin 3) := ⟨0⟩
  let a : {x : ULift.{u} (Fin 3) // x ≠ b} := ⟨⟨1⟩, by decide⟩
  let z : {x : ULift.{u} (Fin 3) // x ≠ b} := ⟨⟨2⟩, by decide⟩
  let p : Walk a.val z.val := Quiver.Path.nil.cons PUnit.unit
  obtain ⟨q, hq⟩ := (h (fun _ _ => 0) b a z).1 p
  have he : a = z := endpoints_eq_of_top_bound q
    (by simpa [weight, p, rejected, realize] using hq)
  have he' := congrArg (fun x => x.val.down.val) he
  norm_num [a, z] at he'

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let b : ULift.{u} (Fin 2) := ⟨0⟩
  let a : {x : ULift.{u} (Fin 2) // x ≠ b} := ⟨⟨1⟩, by decide⟩
  refine ⟨ULift.{u} (Fin 2), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun (congrFun h b) a) a
  norm_num [actual, realize, schur] at he

def evidence : Registration arena.{u} (type_of% (@pivot_walks_and_distance.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pivot_walks_and_distance, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pivot_walks_and_distance.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination.pivot
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ W => schur W) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "body", "fn", "arg", "fn", "fn", "fn", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Walks.TropicalSchurElimination
