import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace Reg.D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
open _root_.D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- Exact dependent source reconstructions below are typed audit attempts.
They are not Contract.Registration or declared_validated. Whole-family
variation, sensitivity, observational dependence and enrolled source readout
remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24524
and https://github.com/the-omega-institute/trureturing/issues/24498. -/

namespace Support
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  word : List (Index D)
  e : ℤ
  input : Index D →₀ ℕ
  output : Index D →₀ ℕ
  g : ActualGround D hu
abbrev signature : Signature where
  Params := Params
  State p := ModeTuple p.D p.word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p m => allModes p.D
    (fun n => n ∈ nativeNeutralModeProjection p.D p.output p.input) p.word m)
  (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (word : List (Index D)) (e : ℤ)
    (input output : Index D →₀ ℕ) (g : ActualGround D hu) (m : ModeTuple D word),
    nativeOutputProjection D hu output
      (flatTerm D hu (chargedField D hu 0) word e
        (MvPolynomial.monomial input 1 ⊗ₜ[ℂ] g) m) ≠ 0 →
      R.readout () ⟨D, hu, word, e, input, output, g⟩ m

theorem source_bridge : (type_of% (@nativeNeutralCoefficient_projected_support)) ↔
    law actual := Iff.rfl
end Support

namespace FiniteModes
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  word : List (Index D)
  e : ℤ
  input : Index D →₀ ℕ
  output : Index D →₀ ℕ
abbrev signature : Signature where
  Params := Params
  State p := ActualGround p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualGround p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p g =>
    ∑ m ∈ nativeModeBox p.D (nativeNeutralModeProjection p.D p.output p.input) p.word,
      nativeOutputProjection p.D p.hu p.output
        (flatTerm p.D p.hu (chargedField p.D p.hu 0) p.word p.e
          (MvPolynomial.monomial p.input 1 ⊗ₜ[ℂ] g) m))
  (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (word : List (Index D)) (e : ℤ)
    (input output : Index D →₀ ℕ) (g : ActualGround D hu),
    nativeOutputProjection D hu output
      ((wordField D hu (chargedField D hu 0) word).coeff e
        (MvPolynomial.monomial input 1 ⊗ₜ[ℂ] g)) =
      R.readout () ⟨D, hu, word, e, input, output⟩ g

theorem source_bridge : (type_of% (@nativeNeutralCoefficient_frequency_projected_mode_sum)) ↔
    law actual := Iff.rfl
end FiniteModes

namespace Laurent
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  d : Index D →₀ ℕ
  input : Index D →₀ ℕ
  output : Index D →₀ ℕ
  e : ℤ
abbrev signature : Signature where
  Params := Params
  State p := ActualGround p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualGround p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p g => nativeNeutralLaurentCoefficients p.D p.d p.input p.output p.e • g)
  (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (d input output : Index D →₀ ℕ)
    (e : ℤ) (g : ActualGround D hu),
    nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu d e (MvPolynomial.monomial input 1 ⊗ₜ[ℂ] g)) =
        R.readout () ⟨D, hu, d, input, output, e⟩ g

theorem source_bridge : (type_of% (@nativeNeutralCoefficient_eq_laurent_coefficients)) ↔
    law actual := Iff.rfl
end Laurent

namespace Energy
abbrev signature := Laurent.signature

def actual : Realization signature := realize _ (fun _ p g =>
  nativeOutputProjection p.D p.hu p.output
    (nativeNeutralCoefficient p.D p.hu p.d p.e
      (MvPolynomial.monomial p.input 1 ⊗ₜ[ℂ] g))) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (d input output : Index D →₀ ℕ)
    (g : ActualGround D hu) (e : ℤ),
    e ≠ (LatticeHalfFockGradedTrace.oddWeight D output : ℤ) -
      (LatticeHalfFockGradedTrace.oddWeight D input : ℤ) - 2 * nativeSourceEnergy D d →
      R.readout () ⟨D, hu, d, input, output, e⟩ g = 0

theorem source_bridge : (type_of% (@nativeNeutralCoefficient_output_energy_selection)) ↔
    law actual := Iff.rfl
end Energy
end Reg.D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
