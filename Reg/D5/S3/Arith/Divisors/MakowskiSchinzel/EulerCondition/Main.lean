import D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source bridge for the Euler capacity criterion. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main

open Finset
open _root_.D5.S3.Arith.MakowskiSchinzel
open _root_.D5.S3.Arith.MakowskiSchinzel.EulerCondition
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
  realize signature (fun _ _ n => ArithmeticFunction.sigma 1 n.totient) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (∀ r : ℕ, r.Prime → Odd r → (topGroup n r).Nonempty →
      (r : ℚ) * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ) ≤
        ((topGroup n r).gcd (· - 1) : ℕ)) →
    n ≤ 2 * R.readout () () n ∧
      (Odd n → n ≤ R.readout () () n) ∧
      ((nonFermatFactors n).Nonempty →
        n < 2 * R.readout () () n ∧
          (Odd n → n < R.readout () () n))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : ∀ r : ℕ, r.Prime → Odd r → (topGroup 1 r).Nonempty →
      (r : ℚ) * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ) ≤
        ((topGroup 1 r).gcd (· - 1) : ℕ) := by
    intro r _ _ he
    simp [topGroup, primeSources] at he
  have hh := (h 1 hn).1
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@makowski_schinzel_of_euler_condition)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@makowski_schinzel_of_euler_condition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@makowski_schinzel_of_euler_condition) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.EulerCondition.makowski_schinzel_of_euler_condition).str
      "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main.family
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
    (fun _ _ n => ArithmeticFunction.sigma 1 n.totient) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace CommonDivisor

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ a Q => ∑ q ∈ Q, (a.1 : ℚ) / (q - 1 : ℕ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Q : Finset ℕ) (r D : ℕ),
    (∀ q ∈ Q, D ∣ q - 1) →
    (∀ q ∈ Q, (q - 1) / D ∈ Nat.smoothNumbers (r + 1)) →
    R.readout () (r, D) Q ≤
      (r : ℚ) / D * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ) ∧
      (2 ≤ r → 0 < D →
        (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ)) <
          (r : ℚ) / D * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h ∅ 0 0 (by simp) (by simp)).1
  norm_num [rejected, realize] at hh

def sourceFamily : Registration arena (type_of% @mass_le_euler_of_common_dvd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mass_le_euler_of_common_dvd, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1, 1), ∅, {2}, ?_⟩
    simp [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mass_le_euler_of_common_dvd) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.EulerCondition.mass_le_euler_of_common_dvd).str
      "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main.CommonDivisor.sourceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨sourceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ a Q => ∑ q ∈ Q, (a.1 : ℚ) / (q - 1 : ℕ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end CommonDivisor

namespace LabelledGroups

abbrev signature : Signature where
  Params := ℕ → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => psi n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (label : ℕ → ℕ),
    (∀ q₀ ∈ nonFermatFactors n,
      ∏ q ∈ (nonFermatFactors n).filter (fun q => label q = label q₀),
        (q : ℚ) / (q - 1 : ℕ) ≤
          geom (label q₀) ((oddPredecessorPart n).factorization (label q₀))) →
    1 ≤ R.readout () label n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (fun _ => 3) (by simp [nonFermatFactors])
  norm_num [rejected, realize] at hh

def sourceFamily : Registration arena (type_of% @one_le_psi_of_labelled_groups) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_le_psi_of_labelled_groups, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    have hpow : ¬ ∃ k : ℕ, 6 = 2 ^ k := by
      rintro ⟨k, hk⟩
      have hd : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 6)
      have hh := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hd
      norm_num at hh
    have hQ : nonFermatFactors 7 = {7} := by
      simp only [nonFermatFactors, (by norm_num : Nat.Prime 7).primeFactors,
        filter_singleton]
      exact if_pos ⟨by decide, hpow⟩
    have hU : oddPredecessorPart 7 = 3 := by
      rw [oddPredecessorPart, hQ]
      simp only [prod_singleton]
      exact Nat.ordCompl_pow_mul_of_not_dvd 1 Nat.prime_two (by norm_num : ¬ 2 ∣ 3)
    have hpsi7 : psi 7 = 8 / 7 := by
      have hab : (3 : ℕ).abundancyIndex = geom 3 1 := by
        simpa using abundancy_prime_pow (by norm_num : Nat.Prime 3) 1
      rw [psi, hU, hQ, prod_singleton, hab]
      norm_num [geom, sum_range_succ]
    have hpsi1 : psi 1 = 1 := by
      norm_num [psi, oddPredecessorPart, nonFermatFactors, Nat.abundancyIndex]
    refine ⟨(fun _ => 3), 1, 7, ?_⟩
    change psi 1 ≠ psi 7
    rw [hpsi1, hpsi7]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@one_le_psi_of_labelled_groups) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.EulerCondition.one_le_psi_of_labelled_groups).str
      "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main.LabelledGroups.sourceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨sourceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => psi n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LabelledGroups

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Main
