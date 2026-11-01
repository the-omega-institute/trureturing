import Reg.D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegModeExpansion
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

namespace SourceInsertion
structure Params extends Evaluation.Params where
  a : Index D
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
    nativeNormalReadout p.D p.T p.input p.output
      (MvPolynomial.X p.a * correctionAt p.D p.T (MvPolynomial.monomial p.d 1)) • g +
    ∑ b ∈ p.d.support, ((p.d b : ℂ) * nativeSourceSourceKernel p.D p.T p.a b) •
      (nativeNeutralLaurentEntry p.D p.T (p.d - Finsupp.single b 1) p.input p.output • g))
  (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (a : Index D) (g : ActualGround D hu),
    let E : ℤ := (LatticeHalfFockGradedTrace.oddWeight D output : ℤ) -
      (LatticeHalfFockGradedTrace.oddWeight D input : ℤ) -
      2 * nativeSourceEnergy D (d + Finsupp.single a 1)
    (T : ℂ) ^ E • nativeOutputProjection D hu output
      (nativeNeutralCoefficient D hu (d + Finsupp.single a 1) E
        (MvPolynomial.monomial input 1 ⊗ₜ[ℂ] g)) =
      R.readout () ⟨⟨D, hu, T, d, input, output⟩, a⟩ g

theorem source_bridge : (type_of% (@nativeNeutralCoefficient_source_insertion)) ↔
    law actual := Iff.rfl
end SourceInsertion

namespace IOPropagation
structure Params where
  D : LatticeData
  T : ℂˣ
  input : Index D →₀ ℕ
  output : Index D →₀ ℕ
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p _ => if p.input = p.output then 1 else 0) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (T : ℂˣ) (input output : Index D →₀ ℕ),
    nativeNeutralLaurentEntry D T 0 input output = R.readout () ⟨D,T,input,output⟩ ()

theorem source_bridge : (type_of% (@nativeNeutralLaurentEntry_zero)) ↔ law actual := Iff.rfl
end IOPropagation

namespace UnpairedReadout
structure Params where
  D : LatticeData
  T : ℂˣ
  d : Index D →₀ ℕ
  input : Index D →₀ ℕ
  output : Index D →₀ ℕ
  a : Index D
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ p _ =>
  (∑ j ∈ p.output.support, nativeSourceOutputKernel p.D p.T p.a j *
    nativeNeutralLaurentEntry p.D p.T p.d p.input (p.output - Finsupp.single j 1)) +
  ∑ j ∈ p.input.support, (p.input j : ℂ) * nativeSourceInputKernel p.D p.T p.a j *
    nativeNeutralLaurentEntry p.D p.T p.d (p.input - Finsupp.single j 1) p.output)
  (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (T : ℂˣ) (d input output : Index D →₀ ℕ) (a : Index D),
    nativeNormalReadout D T input output
      (MvPolynomial.X a * correctionAt D T (MvPolynomial.monomial d 1)) =
        R.readout () ⟨D,T,d,input,output,a⟩ ()

theorem source_bridge : (type_of% (@nativeNeutralLaurentEntry_unpaired)) ↔ law actual := Iff.rfl
end UnpairedReadout

namespace FullRecurrence
abbrev signature := UnpairedReadout.signature

def actual : Realization signature := realize _ (fun _ p _ =>
  ((∑ j ∈ p.output.support, nativeSourceOutputKernel p.D p.T p.a j *
    nativeNeutralLaurentEntry p.D p.T p.d p.input (p.output - Finsupp.single j 1)) +
  ∑ j ∈ p.input.support, (p.input j : ℂ) * nativeSourceInputKernel p.D p.T p.a j *
    nativeNeutralLaurentEntry p.D p.T p.d (p.input - Finsupp.single j 1) p.output) +
  ∑ b ∈ p.d.support, (p.d b : ℂ) * nativeSourceSourceKernel p.D p.T p.a b *
    nativeNeutralLaurentEntry p.D p.T (p.d - Finsupp.single b 1) p.input p.output)
  (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (T : ℂˣ) (d input output : Index D →₀ ℕ) (a : Index D),
    nativeNeutralLaurentEntry D T (d + Finsupp.single a 1) input output =
      R.readout () ⟨D,T,d,input,output,a⟩ ()

theorem source_bridge : (type_of% (@nativeNeutralLaurentEntry_recurrence)) ↔ law actual := Iff.rfl
end FullRecurrence

namespace FullGaussian
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  T : ℂˣ
  d : Index D →₀ ℕ
  h : Index D →₀ ℕ
  l : Index D →₀ ℕ
  K : Finset (Index D)
  hd : d.support ⊆ K
  hh : h.support ⊆ K
  hl : l.support ⊆ K
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
  nativeFiniteRawGaussianCoefficient p.D p.T p.K p.d p.h p.l • g) (fun e => nomatch e)

def law (R : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d h l : Index D →₀ ℕ) (K : Finset (Index D))
    (hd : d.support ⊆ K) (hh : h.support ⊆ K) (hl : l.support ⊆ K)
    (g : ActualGround D hu),
    let E : ℤ := (LatticeHalfFockGradedTrace.oddWeight D l : ℤ) -
      (LatticeHalfFockGradedTrace.oddWeight D h : ℤ) - 2 * nativeSourceEnergy D d
    (((FactorialFockMetric.weight d : ℂ) * (FactorialFockMetric.weight h : ℂ))⁻¹) •
      ((T : ℂ) ^ E • nativeOutputProjection D hu l
        (nativeNeutralCoefficient D hu d E (MvPolynomial.monomial h 1 ⊗ₜ[ℂ] g))) =
      R.readout () ⟨D,hu,T,d,h,l,K,hd,hh,hl⟩ g

theorem source_bridge : (type_of% (@nativeNeutralCoefficient_full_raw_gaussian)) ↔
    law actual := Iff.rfl
end FullGaussian

end Reg.D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
