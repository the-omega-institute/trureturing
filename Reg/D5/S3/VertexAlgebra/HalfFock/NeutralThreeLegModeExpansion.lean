import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegModeExpansion

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open private creationPolynomial rightPolynomial from D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegModeExpansion
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

namespace ProjectedExpansion
abbrev signature := Laurent.signature

def actual : Realization signature := realize _ (fun _ p g =>
  ∑ shift ∈ (LatticeHalfFockFiniteCorrection.Corr p.D 0 (MvPolynomial.monomial p.d 1)).support,
    ∑ mon ∈ ((LatticeHalfFockFiniteCorrection.Corr p.D 0 (MvPolynomial.monomial p.d 1)) shift).support,
      ((LatticeHalfFockFiniteCorrection.Corr p.D 0 (MvPolynomial.monomial p.d 1)) shift).coeff mon •
        ∑ m ∈ nativeModeBox p.D (nativeNeutralModeProjection p.D p.output p.input) (occurrences p.D mon),
          if p.e + 2 * (shift : ℤ) + 2 * modeSum p.D (occurrences p.D mon) m +
              jetShift p.D (occurrences p.D mon) = 0 then
            ((creationPolynomial p.D (occurrences p.D mon) m *
              rightPolynomial p.D (occurrences p.D mon) m (MvPolynomial.monomial p.input 1)).coeff p.output) • g
          else 0) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (d input output : Index D →₀ ℕ)
    (e : ℤ) (g : ActualGround D hu),
    nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu d e (MvPolynomial.monomial input 1 ⊗ₜ[ℂ] g)) =
        R.readout () ⟨D, hu, d, input, output, e⟩ g

theorem source_bridge : (type_of% (@nativeNeutralCoefficient_finite_projected_expansion)) ↔
    law actual := Iff.rfl
end ProjectedExpansion

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
namespace Evaluation
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  T : ℂˣ
  d : Index D →₀ ℕ
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

def actual : Realization signature := realize _ (fun _ p g =>
  ∑ e ∈ (nativeNeutralLaurentCoefficients p.D p.d p.input p.output).support,
    (p.T : ℂ) ^ e • nativeOutputProjection p.D p.hu p.output
      (nativeNeutralCoefficient p.D p.hu p.d e
        (MvPolynomial.monomial p.input 1 ⊗ₜ[ℂ] g))) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (g : ActualGround D hu),
    nativeNeutralLaurentEntry D T d input output • g =
      R.readout () ⟨D, hu, T, d, input, output⟩ g

theorem source_bridge : (type_of% (@nativeNeutralLaurentEntry_ground_identity)) ↔
    law actual := Iff.rfl
end Evaluation

namespace AtEnergy
abbrev signature := Evaluation.signature

def actual : Realization signature := realize _ (fun _ p g =>
  let E : ℤ := (LatticeHalfFockGradedTrace.oddWeight p.D p.output : ℤ) -
    (LatticeHalfFockGradedTrace.oddWeight p.D p.input : ℤ) - 2 * nativeSourceEnergy p.D p.d
  (p.T : ℂ) ^ E • nativeOutputProjection p.D p.hu p.output
    (nativeNeutralCoefficient p.D p.hu p.d E
      (MvPolynomial.monomial p.input 1 ⊗ₜ[ℂ] g))) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (g : ActualGround D hu),
    nativeNeutralLaurentEntry D T d input output • g =
      R.readout () ⟨D, hu, T, d, input, output⟩ g

theorem source_bridge : (type_of% (@nativeNeutralLaurentEntry_at_energy)) ↔
    law actual := Iff.rfl
end AtEnergy

namespace RawNormal
structure Params where
  D : LatticeData
  T : ℂˣ
abbrev signature : Signature where
  Params := Params
  State p := (Index p.D →₀ ℕ) × (Index p.D →₀ ℕ) × (Index p.D →₀ ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ p s =>
  ∑ shift ∈ (LatticeHalfFockFiniteCorrection.Corr p.D 0 (MvPolynomial.monomial s.1 1)).support,
    ∑ mon ∈ ((LatticeHalfFockFiniteCorrection.Corr p.D 0 (MvPolynomial.monomial s.1 1)) shift).support,
      ((LatticeHalfFockFiniteCorrection.Corr p.D 0 (MvPolynomial.monomial s.1 1)) shift).coeff mon *
        (p.T : ℂ) ^ (-2 * (shift : ℤ)) *
        ∑ m ∈ nativeModeBox p.D (nativeNeutralModeProjection p.D s.2.2 s.2.1) (occurrences p.D mon),
          (nativeRawNormalTerm p.D p.T (occurrences p.D mon) m
            (MvPolynomial.monomial s.2.1 1)).coeff s.2.2) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (T : ℂˣ) (d input output : Index D →₀ ℕ),
    nativeNeutralLaurentEntry D T d input output =
      R.readout () ⟨D, T⟩ (d, input, output)

theorem source_bridge : (type_of% (@nativeNeutralLaurentEntry_raw_normal_expansion)) ↔
    law actual := Iff.rfl
end RawNormal

end Reg.D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
