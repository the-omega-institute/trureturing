import LeanInformationAuditInterface.Contract.Registration
import D5.S3.PrimeGaps.ChiFourWeightedMangoldt
import Reg.Support.SingleDependentReadout

/-! Source observations for character prefixes and weighted Mangoldt sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.PrimeGaps.ChiFourWeightedMangoldt

namespace Reg.D5.S3.PrimeGaps.ChiFourWeightedMangoldt

namespace Prefix

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ X => ∑ n ∈ Ioc 0 X, ZMod.χ₄ (n : ZMod 4))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : ℕ, R.readout () () X = (((X + 1) / 2 % 2 : ℕ) : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := h 0
  norm_num [rejected, realize] at h'

def family : Registration arena
    (type_of% @_root_.D5.S3.PrimeGaps.ChiFourWeightedMangoldt.sum_chi_four_prefix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_chi_four_prefix, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (∑ n ∈ Ioc (0 : ℕ) 0, ZMod.χ₄ (n : ZMod 4)) ≠
      ∑ n ∈ Ioc (0 : ℕ) 1, ZMod.χ₄ (n : ZMod 4)
    rw [sum_chi_four_prefix, sum_chi_four_prefix]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.PrimeGaps.ChiFourWeightedMangoldt.sum_chi_four_prefix)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.PrimeGaps.ChiFourWeightedMangoldt.sum_chi_four_prefix.audit
  realizationName := `Reg.D5.S3.PrimeGaps.ChiFourWeightedMangoldt.Prefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.PrimeGaps.ChiFourWeightedMangoldt
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Prefix

namespace AbsoluteValue

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => |t|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 13) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, 1 ≤ x →
    R.readout () () (∑ n ∈ Ioc 0 ⌊x⌋₊,
      (ZMod.χ₄ (n : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt n / n) ≤ 12

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := h (x := 1) (by norm_num)
  norm_num [rejected, realize] at h'

def family : Registration arena
    (type_of% @_root_.D5.S3.PrimeGaps.ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve)
    where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨abs_weighted_mangoldt_sum_le_twelve, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.PrimeGaps.ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.PrimeGaps.ChiFourWeightedMangoldt.abs_weighted_mangoldt_sum_le_twelve.audit
  realizationName := `Reg.D5.S3.PrimeGaps.ChiFourWeightedMangoldt.AbsoluteValue.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.PrimeGaps.ChiFourWeightedMangoldt
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AbsoluteValue

end Reg.D5.S3.PrimeGaps.ChiFourWeightedMangoldt
