import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real MeasureTheory Set LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight



namespace QuadratureUpper

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b C E : ℝ} {f d : ℝ → ℝ},
    0 ≤ a → a ≤ b → 0 ≤ E → ContinuousOn d (Set.Icc a b) →
    (∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t) →
    (∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E) →
    R.readout () () (∑ p ∈ primeInterval a b, f p)
      (C * (∫ t in a..b, f t) + E * (|f a| + |f b| + ∫ t in a..b, |d t|))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (a := 0) (b := 0) (C := 0) (E := 0)
    (f := fun _ => 0) (d := fun _ => 0) le_rfl le_rfl le_rfl continuousOn_const
    (fun t _ => by simpa using hasDerivAt_const t (0 : ℝ))
    (by
      intro t ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simp [primeCount])

def family : Registration arena (type_of% @prime_quadrature_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_quadrature_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_quadrature_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight.prime_quadrature_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight.QuadratureUpper.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end QuadratureUpper

namespace CentralPrimeWeight

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, 0 ≤ s →
    R.readout () ()
      (∑ p ∈ primeInterval (P / 2) (2 * P), _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.weight P s p)
      ((∫ t in (P / 2)..(2 * P), _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.weight P s t) / log P +
        112 * log 2 * (P / log P ^ 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, hP⟩ := h.exists
  exact hP 0 le_rfl

def family : Registration arena (type_of% @central_prime_weight_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@central_prime_weight_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@central_prime_weight_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight.central_prime_weight_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight.CentralPrimeWeight.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CentralPrimeWeight

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.CentralWeight
