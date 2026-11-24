import D5.S3.CharacterSums.DirichletTriangleExplicit
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData

/-! The last addition in the complete explicit formula is observed literally. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex
open _root_.D5.S3.CharacterSums.DirichletTrianglePerron
open _root_.D5.S3.CharacterSums.DirichletTriangleExplicit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DirichletTriangleExplicit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => fun w => z + w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z => fun w => z + w + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x),
    (∀ {t : ℝ}, 0 < t → Summable
      (fun ρ : {z : ℂ // completion χ z = 0} =>
        (analyticOrderNatAt (completion χ) ρ.1 : ℂ) * zeroKernel ρ.1 t)) ∧
    characterTriangle χ x = R.readout () ()
      (-zeroTriangle χ x - (1 - (x : ℂ)⁻¹) * logDeriv χ.LFunction 2)
      (parityCorrection χ x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, χ, hχ, hne⟩ :=
    _root_.Reg.D5.S3.CharacterSums.DirichletCompletion.ZeroData.primitive_example
  letI : NeZero q := ⟨hq⟩
  have he := (h hχ hne (x := 1) (by norm_num)).2
  have hf := (characterTriangle_explicit hχ hne (x := 1) (by norm_num)).2
  change _ = _ + _ + 1 at he
  have hz : (0 : ℂ) = 1 := by linear_combination he - hf
  exact zero_ne_one hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : ℂ)
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @characterTriangle_explicit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@characterTriangle_explicit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@characterTriangle_explicit) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletTriangleExplicit.characterTriangle_explicit
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleExplicit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => fun w => z + w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.DirichletTriangleExplicit
