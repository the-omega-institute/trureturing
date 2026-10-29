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
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => if b then claim else True) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () true

private theorem actual_law : arena.Law actual := by
  simpa [arena, actual, claim] using @primitive_gaussSum_ne_zero

private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected]

def family : Registration arena (type_of% @primitive_gaussSum_ne_zero) where
  actual := actual
  bridge := by
    simp [arena, actual, claim]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · rfl
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
  dependence := by
    intro i
    refine ⟨(), false, true, ?_⟩
    simp [actual]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@primitive_gaussSum_ne_zero)
    (Realization signature) Unit where
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
  readout := some (realize signature (fun _ _ b => if b then claim else True)
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
