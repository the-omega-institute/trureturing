import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
import Reg.Support.SingleDependentReadout

/-! A source family for the limit of the primitive non-deficient counting ratio. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open _root_.D5.S3.Arith.Robin.PrimeFiberPropagation (divisorRatio)
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
  (count radicalComponentSet radicalComponentCount)
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures

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
  Law R := R.readout () () (fun n => (primitiveCount n : ℝ) / n) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena
    (type_of% @primitive_density_zero) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@primitive_density_zero,
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
    (@primitive_density_zero)
    (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.primitive_density_zero.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.Limit.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
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

namespace Conjectures

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → ℝ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℕ → Filter ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected (i : Fin 3) : Realization signature :=
  realize signature (fun j _ f F G => if j = i then False else Tendsto f F G)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout (⟨0, by decide⟩ : Fin 3) () (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n}) X : ℝ) /
        radicalComponentCount 2 X) atTop (𝓝 0) ∧
    R.readout (⟨1, by decide⟩ : Fin 3) () (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n ∧ Odd n}) X : ℝ) /
        radicalComponentCount 2 X) atTop (𝓝 0) ∧
    ∀ M : Finset ℕ, M.Nonempty → (∀ p ∈ M, p.Prime) →
      R.readout (⟨2, by decide⟩ : Fin 3) () (fun X : ℕ =>
        (count (radicalComponentSet 2 ∩
          {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n}) X : ℝ) /
            radicalComponentCount 2 X) atTop (𝓝 0)

private theorem rejected_law (i : Fin 3) : ¬ arena.Law (rejected i) := by
  intro h
  fin_cases i
  · have hf := h.1
    change False at hf
    exact hf
  · have hf := h.2.1
    change False at hf
    exact hf
  · have hf := h.2.2 {2} (by simp)
      (by intro p hp; simp only [Finset.mem_singleton] at hp; subst p; norm_num)
    change False at hf
    exact hf

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨result, rejected ⟨0, by decide⟩, rejected_law ⟨0, by decide⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p f F G
      simp [rejected, actual, realize, hj]
    · intro e
      exact nomatch e
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
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.result.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.Conjectures.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "arg", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Conjectures

namespace PrimitiveLower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 0 < n → PrimitiveNonDeficient n →
    R.readout () () 2 (divisorRatio n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, _, hn, hC, _⟩ :=
    _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.result 0
  exact h hn hC

def family : Registration arena
    (type_of% @primitive_ratio_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primitive_ratio_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℝ)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@primitive_ratio_lower)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.primitiveLowerAudit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.PrimitiveLower.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimitiveLower

namespace RatioLower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 0 < n → R.readout () () 1 (divisorRatio n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (by decide)

def family : Registration arena
    (type_of% @ratio_one_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ratio_one_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℝ)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ratio_one_le)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.ratioLowerAudit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.RatioLower.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
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

end RatioLower

namespace PrimeStep

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m p : ℕ}, 0 < m → p.Prime → PrimitiveNonDeficient (m * p) →
    R.readout () () (divisorRatio (m * p))
      (2 + 2 / (p : ℝ) ^ (m * p).factorization p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn, hn0, hC, _⟩ :=
    _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive.result 1
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp.pos
  have he : n / p * p = n := Nat.div_mul_cancel hpn
  exact h hm hp (he.symm ▸ hC)

def family : Registration arena
    (type_of% @primitive_prime_step) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primitive_prime_step, rejected, rejected_law⟩
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
    (@primitive_prime_step)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.primeStepAudit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.PrimeStep.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeStep

end Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
