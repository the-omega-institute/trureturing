import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
import Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
import Reg.Support.DependentFamily

/-! Source-bound audits of the Schur orthogonality relations for matrix coefficients of
continuous irreducible representations of a compact group. -/

namespace Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality

open MeasureTheory
open _root_.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
  (Two twoTop twoDiscrete twoTopGroup twoCompact)

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v w

/-! ## A two-element model -/

/-- The sign of an element of the two-element group, as an integer. -/
def signInt : Two.{u} →* ℤ where
  toFun g := if g = 1 then 1 else -1
  map_one' := by decide
  map_mul' := by decide

/-- The non-identity element of the two-element group. -/
def flip : Two.{u} := ⟨Multiplicative.ofAdd 1⟩

theorem flip_ne_one : flip.{u} ≠ 1 := by decide

/-- The complex line in universe `v`. -/
abbrev Line := ULift.{v} ℂ

theorem finrank_line : Module.finrank ℂ Line.{v} = 1 :=
  ULift.moduleEquiv.finrank_eq.trans (Module.finrank_self ℂ)

theorem line_finiteDimensional : FiniteDimensional ℂ Line.{v} :=
  Module.Finite.equiv ULift.moduleEquiv.symm

/-- The sign representation of the two-element group on the complex line. -/
def sign : Representation ℂ Two.{u} Line.{v} :=
  (algebraMap ℂ (Module.End ℂ Line.{v})).toMonoidHom.comp
    ((Int.castRingHom ℂ).toMonoidHom.comp signInt.{u})

theorem sign_flip (x : Line.{v}) : sign.{u, v} flip x = -x := by
  simp [sign, signInt, flip_ne_one]

/-- The sign representation and the trivial representation of the two-element group on the
complex line are not equivalent. -/
theorem sign_not_equiv_trivial :
    IsEmpty (sign.{u, v}.Equiv (Representation.trivial ℂ Two.{u} Line.{w})) := by
  refine ⟨fun e => ?_⟩
  have h := LinearMap.congr_fun (e.isIntertwining' flip.{u}) 1
  simp only [LinearMap.comp_apply, Representation.trivial_apply] at h
  rw [sign_flip, map_neg] at h
  have h2 : (2 : ℂ) • e.toLinearMap 1 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  have h1 : e.toLinearEquiv 1 = 0 := (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have : (1 : Line.{v}) = 0 := e.toLinearEquiv.injective (h1.trans (map_zero _).symm)
  exact one_ne_zero (congrArg ULift.down this)

theorem sign_irreducible : sign.{u, v}.IsIrreducible :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one
    _ finrank_line

theorem trivial_irreducible : (Representation.trivial ℂ Two.{u} Line.{v}).IsIrreducible :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one
    _ finrank_line

/-- The coordinate functional of the complex line. -/
def coord : Module.Dual ℂ Line.{v} := ULift.moduleEquiv.toLinearMap

/-- On a compact discrete group, every Haar measure gives the identity a positive finite mass. -/
theorem integral_indicator_one_ne_zero {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    ∫ g, Set.indicator {(1 : G)} (1 : G → ℂ) g ∂μ ≠ 0 := by
  rw [integral_indicator (measurableSet_singleton 1), Pi.one_def, setIntegral_const]
  have h0 : μ {(1 : G)} ≠ 0 := (isOpen_discrete _).measure_ne_zero μ (Set.singleton_nonempty 1)
  have ht : μ {(1 : G)} ≠ ⊤ := measure_ne_top μ _
  have : μ.real {(1 : G)} ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos h0 ht).ne'
  exact smul_ne_zero this one_ne_zero

/-! ## The matrix coefficient `g ↦ φ (ρ g v)` -/
namespace Coefficient

/-- The matrix coefficient `g ↦ φ (ρ g v)` of a representation on a complex normed space. -/
abbrev signature : Signature where
  Params := Σ G : Type u, Σ _ : Group G, Σ V : Type v, Σ _ : NormedAddCommGroup V,
    Σ _ : NormedSpace ℂ V, Σ _ : Representation ℂ G V, Σ _ : Module.Dual ℂ V, V
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p g => letI := p.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2.1;
    p.2.2.2.2.2.2.1 (p.2.2.2.2.2.1 g p.2.2.2.2.2.2.2)) (fun e => nomatch e)

/-- The indicator of the identity element, read in place of every coefficient. -/
def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p g => letI := p.2.1; Set.indicator {(1 : p.1)} 1 g)
    (fun e => nomatch e)

/-- The coefficient of the sign representation takes the value `1` at the identity and `-1` at
the other element. -/
theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  cases i
  refine ⟨⟨Two.{u}, inferInstance, Line.{v}, inferInstance, inferInstance, sign.{u, v}, coord,
    1⟩, 1, flip, ?_⟩
  change coord (sign.{u, v} 1 1) ≠ coord (sign.{u, v} flip 1)
  rw [sign_flip, map_one sign.{u, v}, Module.End.one_apply]
  change (1 : ℂ) ≠ -1
  norm_num

/-! ### Inequivalent representations -/

/-- Retain the complete telescope of `integral_dual_mul_dual_inv_eq_zero`. -/
abbrev arenaZero : Arena where
  signature := signature.{u, v}
  Law r := ∀ {G : Type u} {V : Type v} {W : Type w} [iG : Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [iV : NormedAddCommGroup V] [iS : NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible],
    IsEmpty (ρ.Equiv σ) → (∀ v, Continuous fun g => ρ g v) →
      ∀ (φ : Module.Dual ℂ V) (ψ : Module.Dual ℂ W), (∀ w, Continuous fun g => ψ (σ g w)) →
        ∀ (v : V) (w : W), ∫ g, r.readout () ⟨G, iG, V, iV, iS, ρ, φ, v⟩ g * ψ (σ g⁻¹ w) ∂μ = 0

/-- With the indicator of the identity in place of the coefficient of the sign representation,
paired with the trivial representation, the integral is the positive mass of the identity. -/
theorem rejected_zero : ¬ arenaZero.{u, v, w}.Law rejected := by
  intro h
  let _ := twoTop.{u}
  have := twoDiscrete.{u}
  have := twoTopGroup.{u}
  have := twoCompact.{u}
  let _ : MeasurableSpace Two.{u} := borel Two.{u}
  have : BorelSpace Two.{u} := ⟨rfl⟩
  have := line_finiteDimensional.{v}
  have := sign_irreducible.{u, v}
  have := trivial_irreducible.{u, w}
  have hz := h (G := Two.{u}) (V := Line.{v}) (W := Line.{w}) (Measure.haar) sign.{u, v}
    (Representation.trivial ℂ Two.{u} Line.{w}) sign_not_equiv_trivial
    (fun _ => continuous_of_discreteTopology) coord coord
    (fun _ => continuous_of_discreteTopology) 1 1
  apply integral_indicator_one_ne_zero (Measure.haar : Measure Two.{u})
  rw [← hz]
  congr 1
  funext g
  change _ = _ * coord (1 : Line.{w})
  change _ = _ * (1 : ℂ)
  rw [mul_one]
  rfl

/-- The exact statement of `integral_dual_mul_dual_inv_eq_zero`. -/
abbrev sourceZero : Prop := type_of% @integral_dual_mul_dual_inv_eq_zero.{u, v, w}

def registrationZero : Registration arenaZero.{u, v, w} sourceZero.{u, v, w} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_dual_mul_dual_inv_eq_zero.{u, v, w}, rejected, rejected_zero⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_zero⟩
    · intro e
      exact nomatch e
  dependence := dependence

/-! ### One representation -/

/-- Retain the complete telescope of `integral_dual_mul_dual_inv_self`. -/
abbrev arenaSelf : Arena where
  signature := signature.{u, v}
  Law r := ∀ {G : Type u} {V : Type v} [iG : Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [iV : NormedAddCommGroup V] [iS : NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [IsProbabilityMeasure μ] (ρ : Representation ℂ G V)
    [ρ.IsIrreducible], (∀ v, Continuous fun g => ρ g v) →
      ∀ (φ ψ : Module.Dual ℂ V) (v w : V),
        ∫ g, r.readout () ⟨G, iG, V, iV, iS, ρ, φ, v⟩ g * ψ (ρ g⁻¹ w) ∂μ =
          φ w * ψ v / Module.finrank ℂ V

/-- With the indicator of the identity in place of the coefficient of the trivial representation
and the zero functional for `φ`, the left side is the positive mass of the identity while the
right side is `0`. -/
theorem rejected_self : ¬ arenaSelf.{u, v}.Law rejected := by
  intro h
  let _ := twoTop.{u}
  have := twoDiscrete.{u}
  have := twoTopGroup.{u}
  have := twoCompact.{u}
  let _ : MeasurableSpace Two.{u} := borel Two.{u}
  have : BorelSpace Two.{u} := ⟨rfl⟩
  have := line_finiteDimensional.{v}
  have := trivial_irreducible.{u, v}
  have hp : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Two.{u})) :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Two.{u}))⟩
  have hz := h (G := Two.{u}) (V := Line.{v})
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Two.{u}))
    (Representation.trivial ℂ Two.{u} Line.{v}) (fun _ => continuous_of_discreteTopology)
    0 coord 1 1
  apply integral_indicator_one_ne_zero
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Two.{u}))
  rw [LinearMap.zero_apply, zero_mul, zero_div] at hz
  rw [← hz]
  congr 1
  funext g
  change _ = _ * coord (1 : Line.{v})
  change _ = _ * (1 : ℂ)
  rw [mul_one]
  rfl

/-- The exact statement of `integral_dual_mul_dual_inv_self`. -/
abbrev sourceSelf : Prop := type_of% @integral_dual_mul_dual_inv_self.{u, v}

def registrationSelf : Registration arenaSelf.{u, v} sourceSelf.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_dual_mul_dual_inv_self.{u, v}, rejected, rejected_self⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_self⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Coefficient

def integral_dual_mul_dual_inv_eq_zero_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@integral_dual_mul_dual_inv_eq_zero.{u, v, w}) (Realization Coefficient.signature.{u, v})
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.integral_dual_mul_dual_inv_eq_zero_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.Coefficient.registrationZero
  realizationSource := none
  generated := false
  arena := .source ⟨Coefficient.arenaZero.{u, v, w}⟩
  objectArena := .source ⟨Coefficient.arenaZero.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Coefficient.arenaZero.{u, v, w} ⟨Coefficient.registrationZero.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Coefficient.signature.{u, v}
    (fun _ p g => letI := p.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2.1;
      p.2.2.2.2.2.2.1 (p.2.2.2.2.2.1 g p.2.2.2.2.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
    definition := none
    coordinates := #[0, 1, 16, 22, 25]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 27
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def integral_dual_mul_dual_inv_self_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@integral_dual_mul_dual_inv_self.{u, v}) (Realization Coefficient.signature.{u, v})
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.integral_dual_mul_dual_inv_self_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.Coefficient.registrationSelf
  realizationSource := none
  generated := false
  arena := .source ⟨Coefficient.arenaSelf.{u, v}⟩
  objectArena := .source ⟨Coefficient.arenaSelf.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Coefficient.arenaSelf.{u, v} ⟨Coefficient.registrationSelf.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Coefficient.signature.{u, v}
    (fun _ p g => letI := p.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2.1;
      p.2.2.2.2.2.2.1 (p.2.2.2.2.2.1 g p.2.2.2.2.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
    definition := none
    coordinates := #[0, 1, 14, 17, 19]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 21
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
