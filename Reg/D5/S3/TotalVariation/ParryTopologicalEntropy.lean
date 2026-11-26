import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.TotalVariation.ParryTopologicalEntropy

/-! Admissibility is the observation in the topological entropy law. -/

open Dynamics SymbolicDynamics
open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.TotalVariation.ParryTopologicalEntropy
open _root_.D5.S3.TotalVariation.ParryBilateralLaw (Admissible)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.TotalVariation.ParryTopologicalEntropy

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℤ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k x => allowedPath k x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (k : ℕ) (_hk : 2 ≤ k),
    coverEntropy (FullShift.shift (1 : ℤ)) {x | F.readout () k x = true} =
      (Real.log (dbonacciPerronRoot k) : EReal)

private theorem positive : arena.Law actual := bilateral_entropy

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 (by decide)
  have empty : {x : ℤ → Bool | rejected.readout () 2 x = true} = ∅ := by
    ext x
    simp [rejected, realize]
  rw [empty, coverEntropy_empty] at hh
  exact (EReal.coe_ne_bot _).symm hh

def evidence : Registration arena (type_of% bilateral_entropy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro _
    refine ⟨2, fun _ => false, fun _ => true, ?_⟩
    change allowedPath 2 (fun _ => false) ≠ allowedPath 2 (fun _ => true)
    classical
    have yes : Admissible 2 (fun _ => false) := fun _ => ⟨0, rfl⟩
    have no : ¬ Admissible 2 (fun _ => true) := by
      intro h
      obtain ⟨_, hfalse⟩ := h 0
      cases hfalse
    simp [allowedPath, yes, no]

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    bilateral_entropy (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.TotalVariation.ParryTopologicalEntropy.bilateral_entropy
  realizationName := `Reg.D5.S3.TotalVariation.ParryTopologicalEntropy.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k x => allowedPath k x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.ParryTopologicalEntropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.TotalVariation.ParryTopologicalEntropy
