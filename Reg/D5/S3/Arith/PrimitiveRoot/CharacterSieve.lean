import D5.S3.Arith.PrimitiveRoot.CharacterSieve
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! Primitive-root weight and smoothed principal-sum readouts. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.PrimitiveRoot.CharacterSieve

open _root_.D5.S3.Arith.PrimitiveRoot.CharacterSieve
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Factorization.Galois.GeneralPowerCharacterLayer (powerSubgroup)
open scoped BigOperators Classical

namespace Weight

abbrev signature : Signature where
  Params := Σ p : ℕ, ZMod p
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
    (T : Finset ℕ)
    (_he : e ≠ 0)
    (_hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T) (M : ℝ)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M),
    0 ≤ delta (sievePrimes p e T) ∨ (Nat.gcd e (p - 1)).primeFactors = ∅ →
      |(∑ a ∈ Finset.univ.filter (fun a : ZMod p => orderOf a = p - 1),
          R.readout () ⟨p, a⟩ W) -
        (∑ a : (ZMod p)ˣ, W a * defect p (Nat.gcd e (p - 1)) T a) -
        theta (Nat.gcd e (p - 1)) * delta (sievePrimes p e T) * ∑ a : (ZMod p)ˣ, W a| ≤
          theta (Nat.gcd e (p - 1)) *
          errorCoefficient (Nat.gcd e (p - 1)) (sievePrimes p e T) * M

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcover : ∀ q : ℕ, q.Prime → q ∣ 3 - 1 → q ∣ 1 ∨ q ∈ ({2} : Finset ℕ) := by
    intro q hq hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (hq.ne_one h1).elim
    · right; simp [h2]
  have hm : ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ (1 : ℕ).primeFactors, q ∨
        ∃ t ∈ sievePrimes 3 1 {2},
          orderOf χ ∣ t * (∏ q ∈ (1 : ℕ).primeFactors, q)) →
      |(∑ a : ZMod 3, ((1 : ℝ) : ℂ) * χ a).re| ≤ (0 : ℝ) := by
    intro χ hχ _
    simp only [Complex.ofReal_one, one_mul, MulChar.sum_eq_zero_of_ne_one hχ,
      Complex.zero_re, abs_zero, le_refl]
  have hf : sievePrimes 3 1 {2} = {2} := by decide
  have hd (a : (ZMod 3)ˣ) : defect 3 1 {2} a = 0 := by
    have hc : ((sievePrimes 3 1 {2}).filter
        (fun t => a ∈ powerSubgroup ((ZMod 3)ˣ) t)).card ≤ 1 := by
      calc
        _ ≤ (sievePrimes 3 1 {2}).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := by rw [hf]; simp
    unfold defect
    dsimp only
    split_ifs with ha
    · omega
    · rfl
  have hh := h 3 (fun _ => 1) 1 {2} (by simp) hcover 0 hm
    (Or.inl (by rw [hf]; norm_num [delta]))
  simp only [show Nat.gcd 1 (3 - 1) = 1 from by decide] at hh
  simp_rw [hd] at hh
  rw [hf] at hh
  norm_num [theta, delta, errorCoefficient, rejected, realize,
    Nat.totient_prime Nat.prime_three] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @primitive_weight_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primitive_weight_lower_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@primitive_weight_lower_bound) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.CharacterSieve.primitive_weight_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterSieve.Weight.family
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
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterSieve
    definition := none
    coordinates := #[0, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Weight

namespace Smoothed

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
  realize signature (fun _ _ p => (smoothedCharacterSum p 1).re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (e : ℕ)
    (T : Finset ℕ) (M : ℝ)
    (_he : e ≠ 0)
    (_hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(smoothedCharacterSum p χ).re| ≤ M)
    (_hpos : 0 < theta (Nat.gcd e (p - 1)) *
      (delta (sievePrimes p e T) * R.readout () () p -
        errorCoefficientAbs (Nat.gcd e (p - 1)) (sievePrimes p e T) * M) +
      smoothedDefect p (Nat.gcd e (p - 1)) T),
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hm : ∀ χ : DirichletCharacter ℂ 2, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ (1 : ℕ).primeFactors, q ∨
        ∃ t ∈ sievePrimes 2 1 ∅,
          orderOf χ ∣ t * (∏ q ∈ (1 : ℕ).primeFactors, q)) →
      |(smoothedCharacterSum 2 χ).re| ≤ (0 : ℝ) := by
    intro χ hχ _
    norm_num [smoothedCharacterSum, Finset.sum_range_succ]
  have hh := h 2 1 ∅ 0 (by simp) (by intro q hq hd; exact Or.inl hd) hm
    (by norm_num [sievePrimes, errorCoefficientAbs, delta, theta,
      smoothedDefect, defect, rejected, realize])
  obtain ⟨q, hq, hlt, ho⟩ := hh
  exact (not_lt_of_ge hq.two_le) hlt

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have h2 : (smoothedCharacterSum 2 1).re = 0 := by
    norm_num [smoothedCharacterSum, Finset.sum_range_succ]
  have h3 : (smoothedCharacterSum 3 1).re = Real.log 2 / 3 := by
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hc : (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) = 1 :=
      MulChar.one_apply (isUnit_iff_ne_zero.mpr (by decide))
    norm_num [smoothedCharacterSum, Finset.sum_range_succ,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, hc, Complex.log_re]
    ring
  refine ⟨(), 2, 3, ?_⟩
  change (smoothedCharacterSum 2 1).re ≠ (smoothedCharacterSum 3 1).re
  rw [h2, h3]
  exact ne_of_lt (div_pos (Real.log_pos (by norm_num)) (by norm_num))

def family : Registration arena (type_of% @exists_prime_primitiveRoot_of_smoothed) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_prime_primitiveRoot_of_smoothed, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_prime_primitiveRoot_of_smoothed) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterSieve.exists_prime_primitiveRoot_of_smoothed).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterSieve.Smoothed.family
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
    (fun _ _ p => (smoothedCharacterSum p 1).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterSieve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg",
        "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Smoothed

namespace AbsoluteWeight

abbrev signature := Weight.signature

abbrev actual : Realization signature := Weight.actual

abbrev rejected : Realization signature := Weight.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ) (e : ℕ)
    (T : Finset ℕ)
    (_he : e ≠ 0)
    (_hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T) (M : ℝ)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M),
      |(∑ a ∈ Finset.univ.filter (fun a : ZMod p => orderOf a = p - 1),
          R.readout () ⟨p, a⟩ W) -
        (∑ a : (ZMod p)ˣ, W a * defect p (Nat.gcd e (p - 1)) T a) -
        theta (Nat.gcd e (p - 1)) * delta (sievePrimes p e T) * ∑ a : (ZMod p)ˣ, W a| ≤
          theta (Nat.gcd e (p - 1)) *
          errorCoefficientAbs (Nat.gcd e (p - 1)) (sievePrimes p e T) * M

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcover : ∀ q : ℕ, q.Prime → q ∣ 3 - 1 → q ∣ 1 ∨ q ∈ ({2} : Finset ℕ) := by
    intro q hq hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (hq.ne_one h1).elim
    · right; simp [h2]
  have hm : ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ (1 : ℕ).primeFactors, q ∨
        ∃ t ∈ sievePrimes 3 1 {2},
          orderOf χ ∣ t * (∏ q ∈ (1 : ℕ).primeFactors, q)) →
      |(∑ a : ZMod 3, ((1 : ℝ) : ℂ) * χ a).re| ≤ (0 : ℝ) := by
    intro χ hχ _
    simp only [Complex.ofReal_one, one_mul, MulChar.sum_eq_zero_of_ne_one hχ,
      Complex.zero_re, abs_zero, le_refl]
  have hf : sievePrimes 3 1 {2} = {2} := by decide
  have hd (a : (ZMod 3)ˣ) : defect 3 1 {2} a = 0 := by
    have hc : ((sievePrimes 3 1 {2}).filter
        (fun t => a ∈ powerSubgroup ((ZMod 3)ˣ) t)).card ≤ 1 := by
      calc
        _ ≤ (sievePrimes 3 1 {2}).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := by rw [hf]; simp
    unfold defect
    dsimp only
    split_ifs with ha
    · omega
    · rfl
  have hh := h 3 (fun _ => 1) 1 {2} (by simp) hcover 0 hm
  simp only [show Nat.gcd 1 (3 - 1) = 1 from by decide] at hh
  simp_rw [hd] at hh
  rw [hf] at hh
  norm_num [theta, delta, errorCoefficientAbs, rejected, Weight.rejected, realize,
    Nat.totient_prime Nat.prime_three] at hh

private theorem dependence : ObservationalDependence signature actual :=
  Weight.dependence

def family : Registration arena (type_of% @primitive_weight_error_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primitive_weight_error_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@primitive_weight_error_bound) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.CharacterSieve.primitive_weight_error_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterSieve.AbsoluteWeight.family
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
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterSieve
    definition := none
    coordinates := #[0, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "arg", "fn", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AbsoluteWeight

namespace SmoothError

abbrev signature := Smoothed.signature

abbrev actual : Realization signature := Smoothed.actual

abbrev rejected : Realization signature := Smoothed.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (e : ℕ)
    (T : Finset ℕ) (M : ℝ)
    (_he : e ≠ 0)
    (_hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(smoothedCharacterSum p χ).re| ≤ M),
    0 ≤ (smoothedCharacterSum p 1).re ∧ 0 ≤ smoothedPrimitiveWeight p ∧
      0 ≤ smoothedDefect p (Nat.gcd e (p - 1)) T ∧
      |smoothedPrimitiveWeight p - smoothedDefect p (Nat.gcd e (p - 1)) T -
        theta (Nat.gcd e (p - 1)) * delta (sievePrimes p e T) * R.readout () () p| ≤
        theta (Nat.gcd e (p - 1)) *
          errorCoefficientAbs (Nat.gcd e (p - 1)) (sievePrimes p e T) * M

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hm : ∀ χ : DirichletCharacter ℂ 2, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ (1 : ℕ).primeFactors, q ∨
        ∃ t ∈ sievePrimes 2 1 ∅,
          orderOf χ ∣ t * (∏ q ∈ (1 : ℕ).primeFactors, q)) →
      |(smoothedCharacterSum 2 χ).re| ≤ (0 : ℝ) := by
    intro χ hχ _
    norm_num [smoothedCharacterSum, Finset.sum_range_succ]
  have hb := smoothed_primitive_weight_error_bound 2 1 ∅ 0 (by simp)
    (by intro q hq hd; exact Or.inl hd) hm
  have hh := h 2 1 ∅ 0 (by simp) (by intro q hq hd; exact Or.inl hd) hm
  have hbound := hb.2.2.2
  norm_num [sievePrimes, errorCoefficientAbs, delta, theta, smoothedDefect, defect,
    smoothedCharacterSum, Finset.sum_range_succ, rejected, Smoothed.rejected, realize] at hbound hh
  have hp : smoothedPrimitiveWeight 2 = 0 := hbound
  norm_num [hp] at hh

private theorem dependence : ObservationalDependence signature actual :=
  Smoothed.dependence

def family : Registration arena (type_of% @smoothed_primitive_weight_error_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@smoothed_primitive_weight_error_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@smoothed_primitive_weight_error_bound) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothed_primitive_weight_error_bound).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterSieve.SmoothError.family
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
    (fun _ _ p => (smoothedCharacterSum p 1).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterSieve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg",
        "arg", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SmoothError

namespace SignedSmoothed

abbrev signature := Smoothed.signature

abbrev actual : Realization signature := Smoothed.actual

abbrev rejected : Realization signature := Smoothed.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (e : ℕ)
    (T : Finset ℕ) (M : ℝ)
    (_he : e ≠ 0)
    (_hcover : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ sievePrimes p e T,
          orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(smoothedCharacterSum p χ).re| ≤ M)
    (_hpos : errorCoefficient (Nat.gcd e (p - 1)) (sievePrimes p e T) * M <
      delta (sievePrimes p e T) * R.readout () () p),
    0 < delta (sievePrimes p e T) ∧
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hm : ∀ χ : DirichletCharacter ℂ 2, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ (1 : ℕ).primeFactors, q ∨
        ∃ t ∈ sievePrimes 2 1 ∅,
          orderOf χ ∣ t * (∏ q ∈ (1 : ℕ).primeFactors, q)) →
      |(smoothedCharacterSum 2 χ).re| ≤ (0 : ℝ) := by
    intro χ hχ _
    norm_num [smoothedCharacterSum, Finset.sum_range_succ]
  have hh := h 2 1 ∅ 0 (by simp) (by intro q hq hd; exact Or.inl hd) hm
    (by norm_num [sievePrimes, errorCoefficient, delta, rejected, Smoothed.rejected, realize])
  obtain ⟨q, hq, hlt, ho⟩ := hh.2
  exact (not_lt_of_ge hq.two_le) hlt

private theorem dependence : ObservationalDependence signature actual :=
  Smoothed.dependence

def family : Registration arena (type_of% @exists_prime_primitiveRoot_of_smoothed_signed) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_prime_primitiveRoot_of_smoothed_signed, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_prime_primitiveRoot_of_smoothed_signed) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.PrimitiveRoot.CharacterSieve.exists_prime_primitiveRoot_of_smoothed_signed).str
      "__information_unit"
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.CharacterSieve.SignedSmoothed.family
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
    (fun _ _ p => (smoothedCharacterSum p 1).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.CharacterSieve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedSmoothed

end Reg.D5.S3.Arith.PrimitiveRoot.CharacterSieve
