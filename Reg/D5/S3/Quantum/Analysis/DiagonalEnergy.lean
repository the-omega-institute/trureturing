import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.DiagonalEnergy
import Reg.Support.DependentFamily
open Filter
open scoped Topology ENNReal NNReal InnerProductSpace ComplexConjugate lp ComplexOrder
open MarkovProcess.Semigroup
open _root_.D5.S3.Quantum.Analysis.DiagonalHeat
open _root_.D5.S3.Quantum.Analysis.DiagonalEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Analysis.DiagonalEnergy

private def cap_product_traceClass {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) (m : ℝ) (hm : 0 < m)
    (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) : IsTraceClass (cap e h hh m hm * ρ) := by
  simpa only [mul_one] using (isTraceClass_mul_mul (A := cap e h hh m hm) (B := 1) hρ)

namespace HeatTrace
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hs : ∀ β : ℝ, 0 < β → Summable (fun i => Real.exp (-β*h i)))
    (β : ℝ≥0) (hβ : 0 < β),
    ∃ ht : IsTraceClass (heat e h hh β),
      HasSum (fun i => R.readout () () (Real.exp (-(β : ℝ)*h i) : ℂ)) (trace (heat e h hh β) ht) ∧
      HasSum (fun i => Real.exp (-(β : ℝ)*h i)) (trace (heat e h hh β) ht).re

theorem actual_law : arena.{u,v}.Law actual := @heat_trace.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℂ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end HeatTrace

namespace ResolventInverse
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m),
    (∀ x, (hamiltonian e h) (resolventVector e h hh m hm x) +
      R.readout () () m • resolvent e h hh m hm x = x) ∧
    (∀ y : (hamiltonian e h).domain,
      resolvent e h hh m hm ((hamiltonian e h) y + m • (y : H)) = y) ∧
    (∀ A : H →L[ℂ] H,
      (∀ x, (A x,x-m • A x) ∈ (hamiltonian e h).graph) → A = resolvent e h hh m hm)

theorem actual_law : arena.{u,v}.Law actual := @resolvent_inverse.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end ResolventInverse

namespace DiagonalResolventEnergy
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hs : ∀ β : ℝ, 0 < β → Summable (fun i => Real.exp (-β*h i)))
    (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) (hp : ρ.IsPositive),
    (∀ β : ℝ≥0, 0 < β → ∃ ht : IsTraceClass (heat e h hh β),
      HasSum (fun i => (Real.exp (-(β : ℝ)*h i) : ℂ)) (trace (heat e h hh β) ht) ∧
      HasSum (fun i => Real.exp (-(β : ℝ)*h i)) (trace (heat e h hh β) ht).re) ∧
    (∀ (m : ℝ) (hm : 0 < m),
      (∀ x, (hamiltonian e h) (resolventVector e h hh m hm x) + m • resolvent e h hh m hm x = x) ∧
      (∀ y : (hamiltonian e h).domain,
        resolvent e h hh m hm ((hamiltonian e h) y + m • (y : H)) = y) ∧
      IsSelfAdjoint (cap e h hh m hm) ∧ 0 ≤ cap e h hh m hm ∧
      cap e h hh m hm ≤ m • ContinuousLinearMap.id ℂ H ∧
      (∀ (b : ℝ) (hb : 0 < b), m ≤ b → cap e h hh m hm ≤ cap e h hh b hb) ∧
      (∀ (x : H) (i : ι), e.repr (cap e h hh m hm x) i =
        (capCoeff m (h i) : ℂ)*e.repr x i) ∧
      ∃ ht : IsTraceClass (cap e h hh m hm * ρ),
        HasSum (fun i => (capCoeff m (h i) : ℂ)*⟪e i,ρ (e i)⟫_ℂ)
          (trace (cap e h hh m hm * ρ) ht) ∧
        HasSum (fun i => capCoeff m (h i)*(⟪e i,ρ (e i)⟫_ℂ).re)
          (trace (cap e h hh m hm * ρ) ht).re) ∧
    Monotone (fun n : ℕ => ENNReal.ofReal (trace (cap e h hh (n+1) (by positivity) * ρ)
      (cap_product_traceClass e h hh (n+1) (by positivity) ρ hρ)).re) ∧
    stateEnergy e h hh ρ hρ = ∑' i, ENNReal.ofReal (R.readout () () (h i*(⟪e i,ρ (e i)⟫_ℂ).re)) ∧
    ((∀ i, 1 ≤ h i) → ∀ x : (hamiltonian e h).domain,
      ‖(x : H)‖^2 ≤ (⟪(x : H),(hamiltonian e h) x⟫_ℂ).re)

theorem actual_law : arena.{u,v}.Law actual := @diagonal_resolvent_energy.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end DiagonalResolventEnergy
end Reg.D5.S3.Quantum.Analysis.DiagonalEnergy
