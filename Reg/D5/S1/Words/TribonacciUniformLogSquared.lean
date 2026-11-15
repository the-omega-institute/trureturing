import D5.S1.Words.TribonacciUniformLogSquared
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.TribonacciPrefixRefutation (signedWordSum)
open _root_.D5.S1.Words.TribonacciAlignedWindows (W)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.TribonacciUniformLogSquared.uniform_log_squared

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ m s => signedWordSum (factor W s m)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ s => (s : ℤ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ C : ℝ, 0 < C ∧ ∀ s m : ℕ,
    |(R.readout () m s : ℝ)| ≤ C * (Real.log (m+2))^2

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨C, _, h⟩
  obtain ⟨s, hs⟩ := exists_nat_gt (C * (Real.log 2)^2)
  have hh := h s 0
  change |((s : ℤ) : ℝ)| ≤ C * (Real.log ((0 : ℕ)+2))^2 at hh
  norm_num only [Nat.cast_zero, zero_add, Int.cast_natCast] at hh
  rw [abs_of_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ (s : ℝ))] at hh
  linarith

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.TribonacciUniformLogSquared.uniform_log_squared)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.TribonacciUniformLogSquared.uniform_log_squared,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨1, 0, 1, ?_⟩
    change (2 : ℤ) ≠ 1
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.TribonacciUniformLogSquared.uniform_log_squared)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.TribonacciUniformLogSquared.uniform_log_squared.__information_unit,
  realizationName := `Reg.D5.S1.Words.TribonacciUniformLogSquared.uniform_log_squared.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.TribonacciUniformLogSquared,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := some #["arg", "fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S1.Words.TribonacciUniformLogSquared.uniform_log_squared
