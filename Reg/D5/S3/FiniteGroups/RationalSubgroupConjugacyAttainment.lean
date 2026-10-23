import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment
import Reg.Support.DependentFamily
import Mathlib.Data.Fintype.Powerset

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment

open _root_.D5.S3.FiniteGroups.SubgroupConjugacyRatio
open _root_.D5.S3.FiniteGroups.CyclicPrimePowerAction

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℤ, ℤ
  State _ := FiniteGroup
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun role _ W => if role then latticeCount W.Carrier else classCount W.Carrier)
    (fun e => nomatch e)

def rejectClasses : Realization signature :=
  realize signature (fun role _ W => if role then latticeCount W.Carrier else 0)
    (fun e => nomatch e)

def rejectLattice : Realization signature :=
  realize signature (fun role _ W => if role then 0 else classCount W.Carrier)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ a b : ℤ, 1 ≤ a → a < b → ∃ W : FiniteGroup,
    b * (r.readout false ⟨a, b⟩ W : ℤ) = a * (r.readout true ⟨a, b⟩ W : ℤ)

private theorem lattice_positive (W : FiniteGroup) : 0 < latticeCount W.Carrier := by
  have : Finite (Subgroup W.Carrier) :=
    Finite.of_injective (fun H : Subgroup W.Carrier => (H : Set W.Carrier))
      SetLike.coe_injective
  exact Nat.card_pos

private theorem classes_positive (W : FiniteGroup) : 0 < classCount W.Carrier := by
  have : Finite (Subgroup W.Carrier) :=
    Finite.of_injective (fun H : Subgroup W.Carrier => (H : Set W.Carrier))
      SetLike.coe_injective
  exact Nat.card_pos

private theorem rejectClasses_law : ¬ arena.Law rejectClasses := by
  intro h
  obtain ⟨W, he⟩ := h 1 2 (by decide) (by decide)
  change (2 : ℤ) * 0 = 1 * (latticeCount W.Carrier : ℤ) at he
  have hp : (0 : ℤ) < latticeCount W.Carrier := by exact_mod_cast lattice_positive W
  omega

private theorem rejectLattice_law : ¬ arena.Law rejectLattice := by
  intro h
  obtain ⟨W, he⟩ := h 1 2 (by decide) (by decide)
  change (2 : ℤ) * (classCount W.Carrier : ℤ) = 1 * 0 at he
  have hp : (0 : ℤ) < classCount W.Carrier := by exact_mod_cast classes_positive W
  omega

private def small : FiniteGroup := finiteSplitGroup 7 3 1 (by decide) (by decide)
  (by decide) (by decide)

private def large : FiniteGroup := finiteSplitGroup 13 3 2 (by decide) (by decide)
  (by decide) (by decide)

private theorem small_counts : latticeCount small.Carrier = 10 ∧
    classCount small.Carrier = 4 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact split_counts (actionData 7 3 1 (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide)

private theorem large_counts : latticeCount large.Carrier = 18 ∧
    classCount large.Carrier = 6 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact split_counts (actionData 13 3 2 (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 2⟩, small, large, ?_⟩
  cases role
  · change classCount small.Carrier ≠ classCount large.Carrier
    rw [small_counts.2, large_counts.2]
    decide
  · change latticeCount small.Carrier ≠ latticeCount large.Carrier
    rw [small_counts.1, large_counts.1]
    decide

def sourceRegistration : Registration arena
    (∀ a b : ℤ, 1 ≤ a → a < b → ∃ W : FiniteGroup,
      b * (classCount W.Carrier : ℤ) = a * (latticeCount W.Carrier : ℤ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment.rational_attainment,
    rejectClasses, rejectClasses_law⟩
  sensitivity := by
    constructor
    · intro role
      cases role
      · refine ⟨rejectClasses, ?_, rfl, rejectClasses_law⟩
        intro j hj
        cases j
        · exact False.elim (hj rfl)
        · rfl
      · refine ⟨rejectLattice, ?_, rfl, rejectLattice_law⟩
        intro j hj
        cases j
        · rfl
        · exact False.elim (hj rfl)
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment.rational_attainment)
      (type_of% (realize signature
        (fun role (_ : Σ _ : ℤ, ℤ) W =>
          if role then latticeCount W.Carrier else classCount W.Carrier)
        (fun e => nomatch e)))
      FiniteGroup Unit := {
  unitName :=
    `D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment.rational_attainment.reg.__information_unit,
  realizationName :=
    `Reg.D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun role (_ : Σ _ : ℤ, ℤ) W =>
      if role then latticeCount W.Carrier else classCount W.Carrier)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[
      { path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"],
        stateBinder := 4, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "arg", "arg"],
        stateBinder := 4, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment
