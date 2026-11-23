import D5.S3.Arith.PrimitiveRoot.CharacterExpansion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! Character-expansion weighted sieve readout. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion

open _root_.D5.S3.Arith.PrimitiveRoot.CharacterExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Factorization.Galois.GeneralPowerCharacterLayer (powerSubgroup)
open scoped BigOperators Classical

namespace Weight

abbrev signature : Signature where
  Params := Σ p : ℕ, (ZMod p)ˣ
  State p := ZMod p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p W => W p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ) (e : ℕ)
    (_he : ∀ q ∈ e.primeFactors, q ∣ p - 1) (T : Finset ℕ)
    (_hT : ∀ t ∈ T, t.Prime ∧ t ∣ p - 1 ∧ t ∉ e.primeFactors) (M : ℝ)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ T, orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M) (_hδ : 0 ≤ delta T ∨ e.primeFactors = ∅),
    |(∑ a : (ZMod p)ˣ, R.readout () ⟨p, a⟩ W *
        (if ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q then 1 else 0) *
        (1 - ((T.filter (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card : ℝ))) -
      theta e * delta T * ∑ a : (ZMod p)ˣ, W a| ≤ theta e * errorCoefficient e T * M

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hm : ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ (1 : ℕ).primeFactors, q ∨
        ∃ t ∈ ({2} : Finset ℕ),
          orderOf χ ∣ t * (∏ q ∈ (1 : ℕ).primeFactors, q)) →
      |(∑ a : ZMod 3, ((1 : ℝ) : ℂ) * χ a).re| ≤ (0 : ℝ) := by
    intro χ hχ _
    simp only [Complex.ofReal_one, one_mul, MulChar.sum_eq_zero_of_ne_one hχ,
      Complex.zero_re, abs_zero, le_refl]
  have hh := h 3 (fun _ => 1) 1 (by simp) {2} (by
    intro t ht
    have ht2 := Finset.mem_singleton.mp ht
    subst t
    exact ⟨Nat.prime_two, by decide, by simp⟩) 0 hm (Or.inl (by norm_num [delta]))
  norm_num [theta, delta, errorCoefficient, rejected, realize,
    Nat.totient_prime Nat.prime_three] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @weighted_sieve_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_sieve_lower_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_sieve_lower_bound) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterExpansion.weighted_sieve_lower_bound).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion.Weight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p W => W p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterExpansion
    definition := none
    coordinates := #[0, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Weight

namespace Nonnegative

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (W : ZMod p → ℂ) (M : ℝ) (t : ℕ)
    (_hM : ∀ χ : DirichletCharacter ℂ p, orderOf χ = Nat.gcd t (p - 1) →
      |(∑ a, W a * χ a).re| ≤ M), 0 ≤ R.readout () () M

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hm : ∀ χ : DirichletCharacter ℂ 3, orderOf χ = Nat.gcd 2 (3 - 1) →
      |(∑ a : ZMod 3, (1 : ℂ) * χ a).re| ≤ (0 : ℝ) := by
    intro χ ho
    have hχ : χ ≠ 1 := by
      intro hz
      rw [hz, orderOf_one] at ho
      norm_num at ho
    simp only [one_mul, MulChar.sum_eq_zero_of_ne_one hχ,
      Complex.zero_re, abs_zero, le_refl]
  have hh := h 3 (fun _ => 1) 0 2 hm
  change (0 : ℝ) ≤ -1 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @bound_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bound_nonneg, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bound_nonneg) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterExpansion.bound_nonneg).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion.Nonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nonnegative

namespace UnitSum

abbrev signature : Signature where
  Params := Σ p : ℕ, (ZMod p)ˣ
  State p := ZMod p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p W => W p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [NeZero p] (W : ZMod p → ℂ)
    (χ : DirichletCharacter ℂ p),
    (∑ a : ZMod p, W a * χ a) =
      ∑ a : (ZMod p)ˣ, R.readout () ⟨p, a⟩ W * χ a

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hh := h 3 (fun _ => 1) 1
  rw [sum_units_character] at hh
  norm_num [rejected, realize, MulChar.one_apply_coe, ZMod.card_units] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @sum_units_character) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_units_character, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sum_units_character) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterExpansion.sum_units_character).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion.UnitSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p W => W p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterExpansion
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UnitSum

namespace Density

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => theta e) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ e : ℕ, 0 < R.readout () () e

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := h 1
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize, theta, Nat.prime_two.primeFactors]

def family : Registration arena (type_of% @theta_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@theta_pos, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@theta_pos) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterExpansion.theta_pos).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion.Density.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => theta e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterExpansion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Density

namespace AbsoluteWeight

abbrev signature := Weight.signature

abbrev actual : Realization signature := Weight.actual

abbrev rejected : Realization signature := Weight.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ) (e : ℕ)
    (_he : ∀ q ∈ e.primeFactors, q ∣ p - 1) (T : Finset ℕ)
    (_hT : ∀ t ∈ T, t.Prime ∧ t ∣ p - 1 ∧ t ∉ e.primeFactors) (M : ℝ)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ T, orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M),
    |(∑ a : (ZMod p)ˣ, R.readout () ⟨p, a⟩ W *
        (if ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q then 1 else 0) *
        (1 - ((T.filter (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card : ℝ))) -
      theta e * delta T * ∑ a : (ZMod p)ˣ, W a| ≤ theta e * errorCoefficientAbs e T * M

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hm : ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ (1 : ℕ).primeFactors, q ∨
        ∃ t ∈ ({2} : Finset ℕ),
          orderOf χ ∣ t * (∏ q ∈ (1 : ℕ).primeFactors, q)) →
      |(∑ a : ZMod 3, ((1 : ℝ) : ℂ) * χ a).re| ≤ (0 : ℝ) := by
    intro χ hχ _
    simp only [Complex.ofReal_one, one_mul, MulChar.sum_eq_zero_of_ne_one hχ,
      Complex.zero_re, abs_zero, le_refl]
  have hh := h 3 (fun _ => 1) 1 (by simp) {2} (by
    intro t ht
    have ht2 := Finset.mem_singleton.mp ht
    subst t
    exact ⟨Nat.prime_two, by decide, by simp⟩) 0 hm
  norm_num [theta, delta, errorCoefficientAbs, rejected, Weight.rejected, realize,
    Nat.totient_prime Nat.prime_three] at hh

private theorem dependence : ObservationalDependence signature actual :=
  Weight.dependence

def family : Registration arena (type_of% @weighted_sieve_error_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_sieve_error_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_sieve_error_bound) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterExpansion.weighted_sieve_error_bound).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion.AbsoluteWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p W => W p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterExpansion
    definition := none
    coordinates := #[0, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "arg", "fn", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AbsoluteWeight

namespace Coefficient

abbrev signature : Signature where
  Params := Finset ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ T e => errorCoefficientAbs e T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : ℕ) (T : Finset ℕ),
    R.readout () T e = errorCoefficient e T ↔
      0 ≤ delta T ∨ e.primeFactors = ∅

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := (h 2 ∅).mpr (Or.inl (by norm_num [delta]))
  norm_num [rejected, realize, errorCoefficient, delta,
    Nat.prime_two.primeFactors] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨∅, 1, 2, ?_⟩
  change errorCoefficientAbs 1 (∅ : Finset ℕ) ≠ errorCoefficientAbs 2 ∅
  norm_num [errorCoefficientAbs, delta, Nat.prime_two.primeFactors]

def family : Registration arena (type_of% @errorCoefficientAbs_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@errorCoefficientAbs_eq, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@errorCoefficientAbs_eq) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterExpansion.errorCoefficientAbs_eq).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion.Coefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ T e => errorCoefficientAbs e T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterExpansion
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Coefficient

namespace CoefficientNonnegative

abbrev signature := Coefficient.signature

def actual : Realization signature :=
  realize signature (fun _ T e => errorCoefficient e T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : ℕ) (T : Finset ℕ),
    (∑ t ∈ T, (t : ℝ)⁻¹ ≤ (T.card : ℝ) / 2) ↔
      (2 ^ e.primeFactors.card - delta T ≤ errorCoefficient e T ∧
        0 ≤ R.readout () T e)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := (h 1 ∅).mp (by simp)
  norm_num [rejected, realize, delta] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(∅ : Finset ℕ), 1, 2, ?_⟩
  change errorCoefficient 1 (∅ : Finset ℕ) ≠ errorCoefficient 2 ∅
  norm_num [errorCoefficient, delta, Nat.prime_two.primeFactors]

def family : Registration arena (type_of% @errorCoefficient_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@errorCoefficient_nonneg, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@errorCoefficient_nonneg) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterExpansion.errorCoefficient_nonneg).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion.CoefficientNonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ T e => errorCoefficient e T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterExpansion
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoefficientNonnegative

end Reg.D5.S3.Arith.PrimitiveRoot.CharacterExpansion
