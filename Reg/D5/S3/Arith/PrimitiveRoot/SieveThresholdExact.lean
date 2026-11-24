import D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The feasibility readout is sensitive to the actual integer. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
open _root_.D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
open _root_.D5.S3.Arith.PrimitiveRoot.SieveThreshold (Feasible)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℕ) (_hx : 3483481 ≤ x),
    (Feasible (R.readout () () x) ↔ x ≠ 3483481 ∧ x ≠ 3573571)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : ¬ Feasible 0 := by
    rintro ⟨e, T, he, hcover, hδ, hpos⟩
    norm_num at hpos
  have hh := h 4100000 (by decide)
  exact h0 (hh.mpr ⟨by decide, by decide⟩)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% feasible_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨feasible_iff,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    feasible_iff (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThresholdExact.feasible_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdExact.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace PrimeRoot
open _root_.D5.S3.Arith.PrimitiveRoot.CharacterSieve
open scoped BigOperators

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3483482) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (_hp : 3483482 ≤ R.readout () () p)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (p - 1).primeFactors, q →
      |(smoothedCharacterSum p χ).re| ≤ (3 / 2 : ℝ) * Real.sqrt p * Real.log p)
    (_hmain : (p : ℝ) / 2 - Real.sqrt p ≤ (smoothedCharacterSum p 1).re),
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hM : ∀ χ : DirichletCharacter ℂ 2, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (2 - 1).primeFactors, q →
      |(smoothedCharacterSum 2 χ).re| ≤ (3 / 2 : ℝ) * Real.sqrt 2 * Real.log 2 := by
    intro χ hχ hord
    have ho : orderOf χ = 1 := Nat.dvd_one.mp (by simpa using hord)
    exact (hχ (orderOf_eq_one_iff.mp ho)).elim
  have hmain : (2 : ℝ) / 2 - Real.sqrt 2 ≤ (smoothedCharacterSum 2 1).re := by
    simp [smoothedCharacterSum, Finset.sum_range_succ]
  obtain ⟨q, hq, hlt, _⟩ := h 2 (by norm_num [rejected, realize]) hM hmain
  have := hq.two_le
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @exists_prime_primitiveRoot) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_prime_primitiveRoot, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_prime_primitiveRoot) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThresholdExact.exists_prime_primitiveRoot.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdExact.PrimeRoot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeRoot



namespace Necessary
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3483481) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℕ, Feasible x → R.readout () () x ≠ 3483481 ∧ x ≠ 3573571
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 4100000
    (_root_.D5.S3.Arith.PrimitiveRoot.SieveThreshold.feasible_of_ge_4100000 _ le_rfl)).1
  exact hh rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @feasible_ne_exceptions) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@feasible_ne_exceptions, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@feasible_ne_exceptions) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThresholdExact.feasible_ne_exceptions.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdExact.Necessary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Necessary

end Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
