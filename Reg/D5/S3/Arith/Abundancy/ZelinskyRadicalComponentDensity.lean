import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
import Reg.Support.SingleDependentReadout

/-! The positive-parameter family of radical-component counting limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit Finset
open scoped BigOperators
open _root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity (largeSquares)
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S1.Deficit.AlmostAdditivity (primeRadical)
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity

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
  Law R := ∀ lam : ℝ, 0 < lam →
    R.readout () () (fun X : ℕ => (radicalComponentCount lam X : ℝ) / X)
      atTop (𝓝 (1 - log 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by norm_num)

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result,
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
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.Limit.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

namespace SquareSmall

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n X T : ℕ}, 0 < n → n ≤ X → n ∉ largeSquares X T →
    ∃ a b : ℕ, Squarefree a ∧ 0 < b ∧ R.readout () () b T ∧ b ^ 2 * a = n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, b, ha, hb, hfalse, he⟩ := h (n := 1) (X := 1) (T := 1)
    (by decide) (by decide) (by norm_num [largeSquares])
  exact hfalse

def family : Registration arena
    (type_of% @square_decomposition_small) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@square_decomposition_small, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℕ)
    change ((0 : ℕ) ≤ 0) = ((1 : ℕ) ≤ 0) at hh
    have hbad : (1 : ℕ) ≤ 0 := Eq.mp hh le_rfl
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@square_decomposition_small)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.squareSmallAudit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.SquareSmall.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SquareSmall

namespace RadicalSandwich

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lam : ℝ} {n X T : ℕ},
    0 < lam → 2 ≤ n → n ≤ X → n ∉ largeSquares X T →
    (T : ℝ) ^ 6 < lam * n →
    (largestPrime n : ℝ) ^ 2 < (lam / (T : ℝ) ^ 2) * n →
    ∀ p ∈ n.primeFactors,
      R.readout () () ((p : ℝ) ^ (n.factorization p + 1)) (lam * primeRadical n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (lam := 100) (n := 2) (X := 2) (T := 1)
    (by norm_num) (by decide) (by decide) (by norm_num [largeSquares])
    (by norm_num) (by norm_num [largestPrime]) 2 (by norm_num)

def family : Registration arena
    (type_of% @radical_sandwich) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@radical_sandwich, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (1 : ℝ)
    change ((0 : ℝ) < 1) = ((1 : ℝ) < 1) at hh
    have hbad : (1 : ℝ) < 1 := Eq.mp hh (by norm_num)
    exact (lt_irrefl 1) hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@radical_sandwich)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.radicalSandwichAudit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.RadicalSandwich.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RadicalSandwich

end Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
