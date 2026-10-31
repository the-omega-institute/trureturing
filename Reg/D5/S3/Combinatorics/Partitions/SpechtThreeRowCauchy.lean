/- Whole-family evidence for the two HSW evaluated ordinary endpoints.
   Current report binding and the remaining public-helper audit are tracked in issue #24542. -/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchy

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Partitions.SpechtPolytabloid.TauCeti.ThreeRowGram
open _root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2
open _root_.D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
open scoped BigOperators

open private right_coefficient ev_right triProd
  from D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State n := Nat.Partition n
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual (f : ∀ n, Nat.Partition n → ℚ) : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun role n p => if role = true then f n p else (zPartition p : ℚ)⁻¹)
    (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    (∑ p : Nat.Partition n, R.readout false n p * R.readout true n p) =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0

def rejected (f : ∀ n, Nat.Partition n → ℚ) (i : Bool) :
    DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun role n p => if role = i ∧ n = 2 then 0 else (actual f).readout role n p)
    (fun e => nomatch e)

theorem rejected_law (f : ∀ n, Nat.Partition n → ℚ) (i : Bool) :
    ¬ arena.Law (rejected f i) := by
  intro h
  have h2 := h 2 (by decide)
  cases i <;> norm_num [rejected, DependentFamily.realize] at h2

def three : Nat.Partition 3 where
  parts := {3}
  parts_pos := by simp
  parts_sum := by norm_num

def twoOne : Nat.Partition 3 where
  parts := {2, 1}
  parts_pos := by simp
  parts_sum := by norm_num

theorem weight_dependence :
    (zPartition three : ℚ)⁻¹ ≠ (zPartition twoOne : ℚ)⁻¹ := by
  norm_num [zPartition, partitionExponent, zExponent, three, twoOne, Finsupp.prod]

theorem rectangle_formula (p : Nat.Partition 3) :
    rectangleEvSpechtSum p = (2 : ℤ)^p.parts.card *
      (((p.parts.map fun a => (Polynomial.X : Polynomial ℤ)^(2*a) +
          Polynomial.X^a + 1).prod).coeff 3 -
        ((p.parts.map fun a => (Polynomial.X : Polynomial ℤ)^(2*a) +
          Polynomial.X^a + 1).prod).coeff 4) := by
  rw [(evSpechtSums_eq_coefficients p).2]
  have hs : p.parts.toList.sum = 3 := by simpa using p.parts_sum
  have h := right_coefficient p.parts.toList (by omega)
    (fun a ha => p.parts_pos (by simpa using ha))
  rw [← ev_right, hs, Multiset.length_toList] at h
  simpa only [triProd, Multiset.prod_map_toList] using h

theorem rectangle_three : rectangleEvSpechtSum three = 2 := by
  rw [rectangle_formula]
  norm_num [three, Polynomial.coeff_one, Polynomial.coeff_X]

theorem rectangle_twoOne : rectangleEvSpechtSum twoOne = -4 := by
  rw [rectangle_formula]
  norm_num [twoOne, mul_add, add_mul, ← pow_add, Polynomial.coeff_one, Polynomial.coeff_X]

def familyEvidence (f : ∀ n, Nat.Partition n → ℚ)
    (hf : ∀ n : ℕ, 1 ≤ n →
      (∑ p : Nat.Partition n, (zPartition p : ℚ)⁻¹ * f n p) =
        if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0)
    (hdep : f 3 three ≠ f 3 twoOne) :
    DependentFamily.Registration arena (∀ n : ℕ, 1 ≤ n →
      (∑ p : Nat.Partition n, (zPartition p : ℚ)⁻¹ * f n p) =
        if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0) where
  actual := actual f
  bridge := Iff.rfl
  variation := ⟨hf, rejected f false, rejected_law f false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected f i, ?_, rfl, rejected_law f i⟩
      intro j hji
      funext n p
      simp [rejected, DependentFamily.realize, hji]
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨3, three, twoOne, ?_⟩
    cases i
    · exact weight_dependence
    · exact hdep

namespace Rectangle

abbrev sourceScope := type_of% (@ordinaryWeightedRectangleEv_evaluated)

def family : DependentFamily.Registration arena sourceScope :=
  familyEvidence (fun _ p => (rectangleEvSpechtSum p : ℚ))
    ordinaryWeightedRectangleEv_evaluated (by
      rw [rectangle_three, rectangle_twoOne]
      norm_num)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@ordinaryWeightedRectangleEv_evaluated)
      (DependentFamily.Realization signature) (ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.SpechtPolytabloid.TauCeti.ThreeRowGram.ordinaryWeightedRectangleEv_evaluated.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchy.Rectangle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun role n p => if role = true then (rectangleEvSpechtSum p : ℚ) else (zPartition p : ℚ)⁻¹)
    (fun e => nomatch e))
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := some Nat.Partition
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rectangle

namespace Signed

abbrev sourceScope := type_of% (@ordinaryWeightedSignedEv_evaluated)

def family : DependentFamily.Registration arena sourceScope :=
  familyEvidence (fun _ p => (signedEvSpechtSum p : ℚ))
    ordinaryWeightedSignedEv_evaluated (by
      rw [ordinaryEv_identity (by decide : 1 ≤ 3) three,
        ordinaryEv_identity (by decide : 1 ≤ 3) twoOne,
        rectangle_three, rectangle_twoOne]
      norm_num)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@ordinaryWeightedSignedEv_evaluated)
      (DependentFamily.Realization signature) (ℕ → Type) Unit where
  unitName := `D5.S3.Combinatorics.Partitions.SpechtPolytabloid.TauCeti.ThreeRowGram.ordinaryWeightedSignedEv_evaluated.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchy.Signed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun role n p => if role = true then (signedEvSpechtSum p : ℚ) else (zPartition p : ℚ)⁻¹)
    (fun e => nomatch e))
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := some Nat.Partition
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Signed


end
end Reg.D5.S3.Combinatorics.Partitions.SpechtThreeRowCauchy
