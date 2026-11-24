import D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Ordered prime supports retain their actual rank and reciprocal readouts. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
open _root_.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Rank
abbrev signature : Signature where
  Params := ℕ
  State k := Fin k → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (q : Fin k → ℕ) (i : Fin k)
    (_hm : StrictMonoOn q (Set.Iic i)) (_hp : ∀ j, j ≤ i → (q j).Prime)
    (hi : i.val < 8),
    firstEight ⟨i.val, hi⟩ ≤ R.readout () k q i
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h firstEight 0 (by decide) (by decide) (by decide)
  norm_num [firstEight, rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @prime_rank_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_rank_lower, rejected, rejected_law⟩
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
    (@prime_rank_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.prime_rank_lower.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.Rank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rank

namespace FirstEight
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 8 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 8 → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : Fin 8 → ℕ) (_hm : StrictMono q) (_hp : ∀ i, (q i).Prime),
    ∀ i, firstEight i ≤ R.readout () () q i
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h firstEight (by decide) (by decide) 0
  norm_num [firstEight, rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @first_eight_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@first_eight_le, rejected, rejected_law⟩
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
    (@first_eight_le) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.first_eight_le.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.FirstEight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[ ]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FirstEight

namespace Radical
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
  realize signature (fun _ _ n => ∏ p ∈ n.primeFactors, p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n m : ℕ) (_hc : 8 + m ≤ n.primeFactors.card),
    9699690 * 19 ^ m ≤ R.readout () () n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 9699690 0 (by decide +kernel)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(), 0, 2, by decide +kernel⟩

def family : Registration arena (type_of% @radical_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@radical_lower, rejected, rejected_law⟩
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
    (@radical_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.radical_lower.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.Radical.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => ∏ p ∈ n.primeFactors, p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[ ]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Radical

namespace Reciprocal
abbrev signature : Signature where
  Params := Σ _r : ℕ, ℕ
  State rs := Fin (rs.1 + rs.2) → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ rs q => ∑ i : Fin rs.2, (q (Fin.natAdd rs.1 i) : ℝ)⁻¹)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r s : ℕ} (q : Fin (r + s) → ℕ) (hr : 2 ≤ r) (hs : s ≤ 6)
    (_hm : StrictMonoOn q {j | j.val < s + 2})
    (_hp : ∀ j, j.val < s + 2 → (q j).Prime)
    (_hle : ∀ i : Fin s,
      q ⟨i.val + 2, by omega⟩ ≤ q (Fin.natAdd r i)),
    R.readout () ⟨r, s⟩ q ≤
      ∑ i : Fin s, (firstEight ⟨i.val + 2, by omega⟩ : ℝ)⁻¹
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) (s := 1) ![2, 3, 5] (by decide) (by decide)
    (by decide) (by decide) (by decide)
  norm_num [rejected, realize, firstEight, Fin.sum_univ_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1⟩, (fun _ => 1), (fun _ => 2), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]

def family : Registration arena (type_of% @reciprocal_tail_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reciprocal_tail_bound, rejected, rejected_law⟩
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
    (@reciprocal_tail_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.reciprocal_tail_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.Reciprocal.family
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
    (fun _ rs q => ∑ i : Fin rs.2, (q (Fin.natAdd rs.1 i) : ℝ)⁻¹)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reciprocal

namespace MarginFive
abbrev signature : Signature where
  Params := Σ _r : ℕ, ℕ
  State rs := Fin (rs.1 + rs.2) → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ rs q => 1 - ∑ i : Fin rs.2, (q (Fin.natAdd rs.1 i) : ℝ)⁻¹)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r s : ℕ} (q : Fin (r + s) → ℕ) (hr : 2 ≤ r) (hs : s ≤ 5)
    (_hm : StrictMonoOn q {j | j.val < s + 2})
    (_hp : ∀ j, j.val < s + 2 → (q j).Prime)
    (_hle : ∀ i : Fin s,
      q ⟨i.val + 2, by omega⟩ ≤ q (Fin.natAdd r i)),
    (36628 / 85085 : ℝ) ≤ R.readout () ⟨r, s⟩ q
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) (s := 1) ![2, 3, 5] (by decide) (by decide)
    (by decide) (by decide) (by decide)
  norm_num [rejected, realize, firstEight, Fin.sum_univ_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1⟩, (fun _ => 1), (fun _ => 2), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]

def family : Registration arena (type_of% @reciprocal_tail_margin_five) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reciprocal_tail_margin_five, rejected, rejected_law⟩
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
    (@reciprocal_tail_margin_five) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.reciprocal_tail_margin_five.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.MarginFive.family
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
    (fun _ rs q => 1 - ∑ i : Fin rs.2, (q (Fin.natAdd rs.1 i) : ℝ)⁻¹)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MarginFive

namespace MarginSix
abbrev signature : Signature where
  Params := ℕ
  State r := Fin (r + 6) → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r q => 1 - ∑ i : Fin 6, (q (Fin.natAdd r i) : ℝ)⁻¹)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ} (q : Fin (r + 6) → ℕ) (hr : 2 ≤ r)
    (_hm : StrictMonoOn q {j | j.val < 8})
    (_hp : ∀ j, j.val < 8 → (q j).Prime)
    (_hle : ∀ i : Fin 6,
      q ⟨i.val + 2, by omega⟩ ≤ q (Fin.natAdd r i)),
    (610847 / 1616615 : ℝ) ≤ R.readout () r q
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (r := 2) firstEight (by decide) (by decide) (by decide) (by decide)
  norm_num [rejected, realize, firstEight, Fin.sum_univ_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, (fun _ => 1), (fun _ => 2), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_succ]

def family : Registration arena (type_of% @reciprocal_tail_margin_six) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reciprocal_tail_margin_six, rejected, rejected_law⟩
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
    (@reciprocal_tail_margin_six) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.reciprocal_tail_margin_six.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.MarginSix.family
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
    (fun _ r q => 1 - ∑ i : Fin 6, (q (Fin.natAdd r i) : ℝ)⁻¹)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MarginSix


namespace NthPrime
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ i => Nat.nth Nat.Prime i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Nat.nth Nat.Prime 0 ≠ Nat.nth Nat.Prime 1
  norm_num
namespace Successor
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k p : ℕ} (_hp : p.Prime)
      (_h : Nat.nth Nat.Prime k < p), R.readout () () (k + 1) ≤ p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (k := 0) (p := 3) (by decide) (by norm_num)
  norm_num [rejected, realize] at hh
def family : Registration arena (type_of% @nth_prime_succ_le_of_prime) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nth_prime_succ_le_of_prime, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nth_prime_succ_le_of_prime) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.nth_prime_succ_le_of_prime.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.NthPrime.Successor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => Nat.nth Nat.Prime i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Successor
namespace Sorted
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {qs : List ℕ} (_hsorted : qs.SortedLT)
      (_hprime : ∀ q, q ∈ qs → q.Prime) (i : ℕ) (hi : i < qs.length),
    R.readout () () i ≤ qs[i]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (qs := [2]) (by decide) (by norm_num) 0 (by decide)
  norm_num [rejected, realize] at hh
def family : Registration arena (type_of% @nth_prime_le_get) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nth_prime_le_get, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nth_prime_le_get) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.nth_prime_le_get.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.NthPrime.Sorted.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => Nat.nth Nat.Prime i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Sorted
namespace Five
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 5 = 13
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  norm_num [rejected, realize] at h
def family : Registration arena (type_of% @nth_prime_five) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nth_prime_five, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nth_prime_five) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.nth_prime_five.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.NthPrime.Five.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => Nat.nth Nat.Prime i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Five
namespace Six
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 6 = 17
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  norm_num [rejected, realize] at h
def family : Registration arena (type_of% @nth_prime_six) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nth_prime_six, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nth_prime_six) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.nth_prime_six.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.NthPrime.Six.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => Nat.nth Nat.Prime i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Six
namespace Seven
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 7 = 19
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  norm_num [rejected, realize] at h
def family : Registration arena (type_of% @nth_prime_seven) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nth_prime_seven, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nth_prime_seven) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.nth_prime_seven.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors.NthPrime.Seven.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => Nat.nth Nat.Prime i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Seven
end NthPrime

end Reg.D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
