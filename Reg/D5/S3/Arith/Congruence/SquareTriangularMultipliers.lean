import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.SquareTriangularMultipliers
import Reg.Support.DependentFamily

/-! # Source-bound observation audit for the A400520 conclusion -/

open _root_.D5.S3.Arith.Congruence.SquareTriangularMultipliers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.SquareTriangularMultipliers

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- The entire source conclusion; only the observation in universal positivity varies. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 0 < R.readout () () n ∧
      ∃ k : ℕ, 1 ≤ k ∧ P n k ∧ a n = (k : ℤ) ∧
        ∀ j : ℕ, 1 ≤ j → P n j → k ≤ j) ∧ a 0 = 1 ∧ a 1 = 1

theorem actual_law : arena.Law actual := result

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible := (h.1 0).1
  change (0 : ℤ) < -1 at impossible
  omega

private theorem distinct_values : a 2 ≠ a 0 := by
  intro heq
  obtain ⟨k, _, hp, ha, _⟩ := (result.1 2).2
  have hcast : (k : ℤ) = 1 := ha.symm.trans (heq.trans result.2.1)
  have hk : k = 1 := by exact_mod_cast hcast
  subst k
  rcases hp.1 with ⟨s, hs⟩ | ⟨s, hs⟩
  · norm_num at hs
    by_cases hsmall : s ≤ 1
    · have hs01 : s = 0 ∨ s = 1 := by omega
      rcases hs01 with rfl | rfl <;> norm_num at hs
    · have hlarge : 2 * 2 ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
  · norm_num at hs
    by_cases hsmall : s ≤ 1
    · have hs01 : s = 0 ∨ s = 1 := by omega
      rcases hs01 with rfl | rfl <;> norm_num at hs
    · have hlarge : 2 * 2 ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
      nlinarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 2, 0, distinct_values⟩

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.Congruence.SquareTriangularMultipliers.result)
      (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => a n) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Arith.Congruence.SquareTriangularMultipliers.result.informationUnit,
  realizationName := `Reg.D5.S3.Arith.Congruence.SquareTriangularMultipliers.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => a n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.SquareTriangularMultipliers,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Arith.Congruence.SquareTriangularMultipliers
