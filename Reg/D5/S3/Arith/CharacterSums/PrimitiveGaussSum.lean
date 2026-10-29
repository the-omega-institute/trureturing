import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.CharacterSums.PrimitiveGaussSum
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.CharacterSums
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.CharacterSums.PrimitiveGaussSum

def claim : Prop := ∀ {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}, χ.IsPrimitive →
      gaussSum χ (ZMod.stdAddChar (N := N)) ≠ 0

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
    χ.IsPrimitive → R.readout () () (gaussSum χ (ZMod.stdAddChar (N := N))) ≠ 0

private theorem actual_law : arena.Law actual := by
  intro N _ χ hχ
  exact primitive_gaussSum_ne_zero hχ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  exact h hp rfl

def family : Registration arena (type_of% @primitive_gaussSum_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    exact zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@primitive_gaussSum_ne_zero)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CharacterSums.PrimitiveGaussSum.unit
  realizationName := `Reg.D5.S3.Arith.CharacterSums.PrimitiveGaussSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.CharacterSums.PrimitiveGaussSum
