import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace LatticeSugawaraConformal MvPolynomial
open HalfFock.NormFourLowestGrades
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped TensorProduct

/- These dependent realizations preserve the original telescopes and actual outputs.
Whole-family variation, role sensitivity, observational dependence and typed source
selection remain unproved; these bridges are not Contract.Registration values.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22171 -/

namespace Ground
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ
abbrev signature : Signature where
  Params := Params
  State p := ActualGround p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p u => zeroMode p.D p.hu p.a p.s (1 ⊗ₜ[ℂ] u)) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (u : ActualGround D hu),
    r.readout () ⟨D, hu, a, ha, s⟩ u =
      (1 / 32 : ℂ) • (1 ⊗ₜ[ℂ] u) +
        (s / 32) • (1 ⊗ₜ[ℂ] groundAction D hu a u)

theorem source_bridge : (type_of% (@zeroMode_ground)) ↔ law actual := Iff.rfl
end Ground

namespace Oscillator
structure Params extends Ground.Params where
  i : Fin D.rank
abbrev signature : Signature where
  Params := Params
  State p := ActualGround p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p u => zeroMode p.D p.hu p.a p.s (X (p.i, 0) ⊗ₜ[ℂ] u)) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (i : Fin D.rank) (u : ActualGround D hu),
    r.readout () ⟨⟨D, hu, a, ha, s⟩, i⟩ u =
      ((1 / 32 : ℂ) • X (i, 0) +
        ((bilinear D a (unitCharge D i) : ℂ) / 16) • chargePolynomial D a) ⊗ₜ[ℂ] u +
      (s / 32) • ((X (i, 0) -
        (2 * (bilinear D a (unitCharge D i) : ℂ)) • chargePolynomial D a) ⊗ₜ[ℂ]
          groundAction D hu a u)

theorem source_bridge : (type_of% (@zeroMode_X)) ↔ law actual := Iff.rfl
end Oscillator

namespace CompleteGrade
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule ℂ (ActualTensor p.D p.hu)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => actualGrade p.D p.hu 1) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    r.readout () ⟨D, hu⟩ () = Submodule.span ℂ
      (Set.range (fun x : Fin D.rank × ActualGround D hu =>
        (X (x.1, 0) : Oscillator D) ⊗ₜ[ℂ] x.2))

theorem source_bridge : (type_of% (@actualGrade_one_eq_span)) ↔ law actual := Iff.rfl
end CompleteGrade

namespace Cubic
structure Params extends Ground.Params where
  hs : s ^ 2 = 1
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℂ (actualGrade p.D p.hu 1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => actualGradeOneZeroMode p.D p.hu p.a p.ha p.s *
    (actualGradeOneZeroMode p.D p.hu p.a p.ha p.s - (1 / 16 : ℂ) • 1) *
    (actualGradeOneZeroMode p.D p.hu p.a p.ha p.s - (1 / 2 : ℂ) • 1))
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ () = 0

theorem source_bridge : (type_of% (@actualGradeOneZeroMode_polynomial)) ↔ law actual := Iff.rfl
end Cubic

end Reg.D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades
