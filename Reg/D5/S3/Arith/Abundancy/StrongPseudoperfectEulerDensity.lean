import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
import Reg.Support.SingleDependentReadout

/-! A source family for the limit of the Euler-form relative counting ratio. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit Finset
open scoped BigOperators
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity

namespace Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity

namespace Limit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => Filter ℕ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (fun n => (eulerSPCount n : ℝ) / eulerCount n) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℕ => 0), (fun _ : ℕ => 1), ?_⟩
    intro he
    have he' := congrFun (congrFun he atTop) (𝓝 (0 : ℝ))
    have hh : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp he' tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.result.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.Limit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

namespace ReciprocalSquareSum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ T => ∑ a ∈ Finset.Icc 1 T, 1 / (a : ℝ) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ T : ℕ, R.readout () () T ≤ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change (3 : ℝ) ≤ 2 at hh
  norm_num at hh

def family : Registration arena
    (type_of%
      @_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.reciprocal_square_sum_le_two)
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.reciprocal_square_sum_le_two,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.reciprocal_square_sum_le_two)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.reciprocal_square_sum_le_two.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.ReciprocalSquareSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ReciprocalSquareSum


namespace LargeSquareBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X T : ℕ,
    R.readout () () ((largeSquares X T).card : ℝ) (2 * (X : ℝ) / (T + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.largeSquares_card)
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.largeSquares_card,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℝ)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.largeSquares_card)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.largeSquares_card.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.LargeSquareBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LargeSquareBound


namespace EulerCountPositive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ X => eulerCount X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : ℕ, 5 ≤ X → 0 < R.readout () () X

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 5 le_rfl
  exact (Nat.lt_irrefl 0) hh

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.eulerCount_pos) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.eulerCount_pos,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 5, ?_⟩
    change eulerCount 0 ≠ eulerCount 5
    have hzero : eulerCount 0 = 0 := by simp [eulerCount]
    rw [hzero]
    exact (Nat.ne_of_gt (eulerCount_pos 5 le_rfl)).symm

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.eulerCount_pos)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.eulerCount_pos.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.EulerCountPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EulerCountPositive


namespace PrimeCountComparison

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ X => eulerCount X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : ℕ, _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount X ≤ R.readout () () X

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 5
  have hfive : _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount 5 = 1 := by
    unfold _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount
    rw [Nat.floor_ofNat]
    have he : ((Finset.Ioc 0 5).filter
        (fun p : ℕ => p.Prime ∧ p % 4 = 1)) = {5} := by decide
    rw [he, Finset.card_singleton]
  change _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount 5 ≤ 0 at hh
  rw [hfive] at hh
  omega

def family : Registration arena
    (type_of%
      @_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.primeCount_le_eulerCount)
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.primeCount_le_eulerCount,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 5, ?_⟩
    change eulerCount 0 ≠ eulerCount 5
    have hzero : eulerCount 0 = 0 := by simp [eulerCount]
    rw [hzero]
    exact (Nat.ne_of_gt (eulerCount_pos 5 le_rfl)).symm

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.primeCount_le_eulerCount)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.primeCount_le_eulerCount.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.PrimeCountComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
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

end PrimeCountComparison

namespace SmallSquares

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ T => ((smallSquares T).card : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ T => 3 * (T : ℝ) ^ 3 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ T : ℕ, R.readout () () T ≤ 3 * (T : ℝ) ^ 3

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0
  change 3 * ((0 : ℕ) : ℝ) ^ 3 + 1 ≤ 3 * ((0 : ℕ) : ℝ) ^ 3 at hzero
  norm_num at hzero

def family : Registration arena (type_of% @smallSquares_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@smallSquares_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change ((smallSquares 0).card : ℝ) ≠ ((smallSquares 1).card : ℝ)
    norm_num [smallSquares, ArithmeticFunction.sigma_one_apply]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@smallSquares_card) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.smallSquares_card.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.SmallSquares.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SmallSquares

namespace LargeSquares

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ X T => ((largeSquares X T).card : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ X T => 2 * (X : ℝ) / (T + 1) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X T : ℕ, R.readout () X T ≤ 2 * (X : ℝ) / (T + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0 0
  norm_num [rejected, realize] at hzero

def family : Registration arena (type_of% @largeSquares_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@largeSquares_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change ((largeSquares 1 0).card : ℝ) ≠ ((largeSquares 1 1).card : ℝ)
    norm_num [largeSquares]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@largeSquares_card) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.largeSquares_card.LargeSquares.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.LargeSquares.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LargeSquares

namespace HighPowers

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ X => ((highPowers X).card : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ X => (Nat.sqrt X : ℝ) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : ℕ, R.readout () () X ≤ (Nat.sqrt X : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0
  change (Nat.sqrt 0 : ℝ) + 1 ≤ (Nat.sqrt 0 : ℝ) at hzero
  norm_num at hzero

def family : Registration arena (type_of% @highPowers_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@highPowers_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 32, ?_⟩
    change ((highPowers 0).card : ℝ) ≠ ((highPowers 32).card : ℝ)
    have hz : (highPowers 0).card = 0 := by simp [highPowers]
    have hp : 0 < (highPowers 32).card := by
      apply Finset.card_pos.mpr
      refine ⟨32, Finset.mem_biUnion.mpr ⟨2, by norm_num, ?_⟩⟩
      apply Finset.mem_image.mpr
      exact ⟨1, by norm_num, by norm_num⟩
    rw [hz]
    exact ne_of_lt (by exact_mod_cast hp)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@highPowers_card) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.highPowers_card.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.HighPowers.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HighPowers

namespace PrimeEuler

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ X => eulerCount X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : ℕ, _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount X ≤ R.readout () () X

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfive := h 5
  have hp : _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount 5 = 1 := by
    unfold _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount
    rw [Nat.floor_ofNat]
    have hf : ((Finset.Ioc 0 5).filter
        (fun p : ℕ => p.Prime ∧ p % 4 = 1)) = {5} := by decide
    rw [hf, Finset.card_singleton]
  change _root_.D5.S3.PrimeGaps.ModFourChebyshev.primeCount 5 ≤ 0 at hfive
  omega

def family : Registration arena (type_of% @primeCount_le_eulerCount) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primeCount_le_eulerCount, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 5, ?_⟩
    change eulerCount 0 ≠ eulerCount 5
    have hz : eulerCount 0 = 0 := by simp [eulerCount]
    rw [hz]
    exact ne_of_lt (eulerCount_pos 5 le_rfl)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@primeCount_le_eulerCount) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.primeCount_le_eulerCount.PrimeEuler.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.PrimeEuler.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
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

end PrimeEuler

namespace Q45Positive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ X => eulerCount X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : ℕ, 5 ≤ X → 0 < R.readout () () X

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfive := h 5 le_rfl
  exact (Nat.lt_irrefl 0) hfive

def family : Registration arena (type_of% @eulerCount_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eulerCount_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 5, ?_⟩
    change eulerCount 0 ≠ eulerCount 5
    have hz : eulerCount 0 = 0 := by simp [eulerCount]
    rw [hz]
    exact ne_of_lt (eulerCount_pos 5 le_rfl)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eulerCount_pos) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.eulerCount_pos.Q45Positive.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity.Q45Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Q45Positive

end Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
