import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.ActualSpectralMixtureUpper
import Reg.Support.DependentFamily

open scoped ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix Filter Finset
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open _root_.D5.S3.Quantum.Information.ActualSpectralMixtureUpper
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
namespace Reg.D5.S3.Quantum.Information.ActualSpectralMixtureUpper
noncomputable section

/-- A matrix dimension with its finite structure and the actual source point. -/
structure MatrixPoint where
  Index : Type u
  finite : Fintype Index
  decidable : DecidableEq Index
  point : ℝ

/-- The observation domain retains every actual curve in each matrix dimension. -/
def signature : Signature where
  Params := MatrixPoint.{u}
  State p := ℝ → Matrix p.Index p.Index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.Index p.Index ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := by
  refine realize signature ?_ (fun e => nomatch e)
  intro _ p curve
  letI := p.finite
  letI := p.decidable
  change Matrix p.Index p.Index ℂ
  change ℝ → Matrix p.Index p.Index ℂ at curve
  exact deriv curve p.point

/-- The law preserves the full source telescope and both occurrences of the actual mixture derivative. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {J : Type v} [Fintype n] [DecidableEq n] [Fintype J]
    (rho : J → ℝ → Matrix n n ℂ) (g : J → ℝ → ℝ) (t : ℝ)
    (hrd : ∀ i, DifferentiableAt ℝ (rho i) t)
    (hgd : ∀ i, DifferentiableAt ℝ (g i) t)
    (hr : ∀ᶠ u in 𝓝 t, ∀ i, (rho i u).PosSemidef ∧ trace (rho i u) = 1)
    (hg : ∀ᶠ u in 𝓝 t, ∑ i, g i u ^ 2 = 1),
    let M : ℝ → Matrix n n ℂ := fun u => ∑ i, (g i u ^ 2) • rho i u
    ∃ hM : (M t).PosSemidef, trace (M t) = 1 ∧ DifferentiableAt ℝ M t ∧
      R.readout () ⟨n, inferInstance, inferInstance, t⟩ M =
        ∑ i, ((2 * g i t * deriv (g i) t) • rho i t +
          (g i t ^ 2) • deriv (rho i) t) ∧
      spectralQFI (M t) (R.readout () ⟨n, inferInstance, inferInstance, t⟩ M) hM ≤
        (∑ i, g i t ^ 2 * spectralQFI (rho i t) (deriv (rho i) t) (hr.self_of_nhds i).1) +
        4 * ∑ i, deriv (g i) t ^ 2

/-- The actual observation reconstructs the complete original proposition. -/
def sourceBridge : (type_of% @actual_spectral_mixture_upper.{u,v}) ↔
    arena.{u,v}.Law actual := Iff.rfl

#print axioms sourceBridge
end
end Reg.D5.S3.Quantum.Information.ActualSpectralMixtureUpper
