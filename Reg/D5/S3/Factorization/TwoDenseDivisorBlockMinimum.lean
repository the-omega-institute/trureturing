import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Factorization.TwoDenseDivisorBlockMinimum

/-! Source-bound length observations for the three divisor-block inequalities. -/

namespace Reg.D5.S3.Factorization.TwoDenseDivisorBlockMinimum

open _root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ B => B.length) (fun e => nomatch e)

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem actual_dependence :
    DependentFamily.ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(), [], [1], by decide⟩

namespace DenseCopy

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (u v : ℕ), 0 < u → 0 < v → u.Coprime v →
    (u.divisorsAntidiagonalList.map Prod.fst).IsChain
      (fun a b => b ≤ 2 * a) →
    ∀ B ∈ divisorBlocks (u * v), u.divisors.card ≤ R.readout () () B

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.block_card_ge_of_dense_factor)

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := h 1 1 (by decide) (by decide) (by decide) (by decide) [1] (by decide)
  change 1 ≤ 0 at hh
  omega

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.block_card_ge_of_dense_factor, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.block_card_ge_of_dense_factor)
    (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum.block_card_ge_of_dense_factor.__information_unit
  realizationName := `Reg.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.DenseCopy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ (B : List ℕ) => B.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DenseCopy

namespace FirstFactor

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (u v : ℕ), 0 < u → 0 < v → u.Coprime v →
    (u.divisorsAntidiagonalList.map Prod.fst).IsChain
      (fun a b => b ≤ 2 * a) →
    (∀ p, p.Prime → p ∣ v → 2 * u < p) →
    ∀ B ∈ divisorBlocks (u * v),
      (_root_.D5.S3.Factorization.TwoDenseDivisorBlocksPalindrome.row (u * v)).headD 0 ≤
        R.readout () () B

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.first_block_min_of_dense_factor)

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have rough : ∀ p : ℕ, p.Prime → p ∣ 1 → 2 * 1 < p := by
    intro p hp hd
    have he := Nat.dvd_one.mp hd
    exact (hp.ne_one he).elim
  have hh := h 1 1 (by decide) (by decide) (by decide) (by decide) rough [1] (by decide)
  change 1 ≤ 0 at hh
  omega

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.first_block_min_of_dense_factor, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.first_block_min_of_dense_factor)
    (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum.first_block_min_of_dense_factor.__information_unit
  realizationName := `Reg.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.FirstFactor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ (B : List ℕ) => B.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FirstFactor

namespace WholeEvent

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ n : ℕ, 0 < n → ∀ B ∈ divisorBlocks n,
    (_root_.D5.S3.Factorization.TwoDenseDivisorBlocksPalindrome.row n).headD 0 ≤
      R.readout () () B

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.result)

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := h 1 (by decide) [1] (by decide)
  change 1 ≤ 0 at hh
  omega

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.result, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.result)
    (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum.result.__information_unit
  realizationName := `Reg.D5.S3.Factorization.TwoDenseDivisorBlockMinimum.WholeEvent.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ (B : List ℕ) => B.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum
    definition := some {
      owner := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum
      name := `D5.S3.Factorization.TwoDenseDivisorBlockMinimum.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WholeEvent

end Reg.D5.S3.Factorization.TwoDenseDivisorBlockMinimum
