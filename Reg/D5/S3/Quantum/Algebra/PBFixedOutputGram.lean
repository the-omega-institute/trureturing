import D5.S3.Quantum.Algebra.PBFixedOutputGram
import Reg.Support.SingleDependentReadout

/-! Source-bound audit attempts for fixed-output PB identities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

namespace Reg.D5.S3.Quantum.Algebra.PBFixedOutputGram

open _root_.D5.S3.Quantum.Algebra.PBFixedOutputGram
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace RealAxis

structure Inputs where
  E : Type u
  H : Type v
  [groupE : AddCommGroup E]
  [moduleE : Module ℝ E]
  [groupH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℝ H]
  J : E →ₗ[ℝ] E →ₗ[ℝ] E
  κ : E →ₗ[ℝ] E
  ρ : E →ₗ[ℝ] E
  F : SpectralPair J κ ρ
  R : VectorModel (H := H) J
  t : E
  k : E

attribute [instance] Inputs.groupE Inputs.moduleE Inputs.groupH Inputs.innerH

abbrev signature : Signature where
  Params := Inputs.{u,v}
  State P := P.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ g => g) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@fixed_output_anchor_identity.{u,v})

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ (P : Inputs.{u,v}),
    (∀ a b, P.J a b = P.J b a) → ∀ g : P.E,
    let output := r.readout () P g
    (∀ (w : P.H), ‖w‖ = 1 → ∀ T α : ℝ,
      scalarPB P.J P.κ P.ρ P.t P.k output (T • P.F.e+α • P.F.n)
        (vectorReading P.R w)) →
    ∀ (ξ η ν : P.H) (d : ℝ), d ≠ 0 → P.F.lam ≠ 0 →
    ‖ξ‖ = 1 → ‖η‖ = 1 → ‖ν‖ = 1 →
    P.R.op P.F.n ξ = 0 → P.R.op P.F.n η = (2 : ℝ) • η →
    P.R.op P.F.j ξ = d • η → P.R.op P.F.e ξ = d • ν → inner ℝ η ν = 0 →
    P.J P.F.n ((P.F.μ+P.F.lam) • P.J P.F.n P.t-P.J P.F.n P.k) =
      (P.F.μ+P.F.lam) • P.J P.F.n P.t-P.J P.F.n P.k →
    inner ℝ ν (P.R.op output ξ) =
      -inner ℝ η (P.R.op ((P.F.μ+P.F.lam) • P.J P.F.n P.t-P.J P.F.n P.k) ξ)

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual.{u,v} := by
  constructor
  · intro h P hs g
    exact h P.J hs P.κ P.ρ P.F P.R P.t P.k g
  · intro h E groupE moduleE H groupH innerH J hs κ ρ F R t k g
    exact h (@Inputs.mk E H groupE moduleE groupH innerH J κ ρ F R t k) hs g

private theorem every_readout (r : Realization signature.{u, v}) : arena.Law r := by
  intro P hs g
  exact fixed_output_anchor_identity P.J hs P.κ P.ρ P.F P.R P.t P.k
    (r.readout () P g)

/-- Arbitrarily replacing the fixed output also replaces its PB premise, so the
exact source law has no rejected whole-family readout. -/
theorem registration_obstruction :
    ¬ Nonempty (Registration arena.{u,v} sourceScope.{u,v}) := by
  rintro ⟨r⟩
  obtain ⟨bad, hbad⟩ := r.variation.2
  exact hbad (every_readout bad)

end RealAxis

namespace ComplexAxes

local instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerProductSpace ℝ H := InnerProductSpace.complexToReal

structure Inputs where
  E : Type u
  H : Type v
  [groupE : AddCommGroup E]
  [moduleE : Module ℝ E]
  [groupH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℂ H]
  J : E →ₗ[ℝ] E →ₗ[ℝ] E
  κ : E →ₗ[ℝ] E
  ρ : E →ₗ[ℝ] E
  F : SpectralPair J κ ρ
  R : VectorModel (H := H) J
  t : E
  k : E

attribute [instance] Inputs.groupE Inputs.moduleE Inputs.groupH Inputs.innerH

abbrev signature : Signature where
  Params := Inputs.{u,v}
  State P := P.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ g => g) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@fixed_output_two_axis_identity.{u,v})

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ (P : Inputs.{u,v}),
    (∀ a b, P.J a b = P.J b a) → ∀ g : P.E,
    let output := r.readout () P g
    P.κ P.F.j = (-P.F.lam) • P.F.e → P.ρ P.F.j = P.F.μ • P.F.j →
    P.J P.F.n P.F.e = P.F.e →
    (∀ (w : P.H), ‖w‖ = 1 → ∀ T α : ℝ,
      scalarPB P.J P.κ P.ρ P.t P.k output (T • P.F.e+α • P.F.n) (vectorReading P.R w) ∧
      scalarPB P.J P.κ P.ρ P.t P.k output (T • P.F.j+α • P.F.n) (vectorReading P.R w)) →
    ∀ (ι : ℂ), ι = Complex.I ∨ ι = -Complex.I →
    ∀ (ξ η : P.H) (d : ℝ), d ≠ 0 → P.F.lam ≠ 0 → ‖ξ‖ = 1 → ‖η‖ = 1 →
    P.R.op P.F.n ξ = 0 → P.R.op P.F.n η = (2 : ℝ) • η →
    P.R.op P.F.n ((-ι) • η) = (2 : ℝ) • ((-ι) • η) →
    P.R.op P.F.j ξ = d • η → P.R.op P.F.e ξ = d • ((-ι) • η) →
    P.J P.F.n ((P.F.μ+P.F.lam) • P.J P.F.n P.t-P.J P.F.n P.k) =
      (P.F.μ+P.F.lam) • P.J P.F.n P.t-P.J P.F.n P.k →
    inner ℂ η (P.R.op output ξ) =
      ι * inner ℂ η (P.R.op ((P.F.μ+P.F.lam) • P.J P.F.n P.t-P.J P.F.n P.k) ξ)

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual.{u,v} := by
  constructor
  · intro h P hs g
    exact h P.J hs P.κ P.ρ P.F P.R P.t P.k g
  · intro h E groupE moduleE H groupH innerH J hs κ ρ F R t k g
    exact h (@Inputs.mk E H groupE moduleE groupH innerH J κ ρ F R t k) hs g

private theorem every_readout (r : Realization signature.{u, v}) : arena.Law r := by
  intro P hs g
  exact fixed_output_two_axis_identity P.J hs P.κ P.ρ P.F P.R P.t P.k
    (r.readout () P g)

/-- This faithful source substitution also leaves the companion-axis law valid
for every replacement output family. -/
theorem registration_obstruction :
    ¬ Nonempty (Registration arena.{u,v} sourceScope.{u,v}) := by
  rintro ⟨r⟩
  obtain ⟨bad, hbad⟩ := r.variation.2
  exact hbad (every_readout bad)

end ComplexAxes
end Reg.D5.S3.Quantum.Algebra.PBFixedOutputGram
