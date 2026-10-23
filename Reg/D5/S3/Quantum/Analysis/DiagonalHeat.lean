import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.DiagonalHeat
import Reg.Support.DependentFamily
open Filter
open scoped Topology ENNReal NNReal InnerProductSpace ComplexConjugate lp ComplexOrder
open MarkovProcess.Semigroup
open _root_.D5.S3.Quantum.Analysis.DiagonalHeat
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Analysis.DiagonalHeat

namespace FiniteBasis
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
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (i : ι),
    finiteOperator e h ⟨e i, Submodule.subset_span ⟨i,rfl⟩⟩ = (R.readout () () (h i) : ℂ) • e i

theorem actual_law : arena.{u,v}.Law actual := @finite_basis.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end FiniteBasis

namespace MultiplierCoeff
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
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (a : ι → ℝ) (M : ℝ≥0)
    (ha : ∀ i, |a i| ≤ M) (x : H) (i : ι),
    e.repr (multiplier e a M ha x) i = (R.readout () () (a i : ℂ)) * e.repr x i

theorem actual_law : arena.{u,v}.Law actual := @multiplier_coeff.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℂ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end MultiplierCoeff

namespace MultiplierBasis
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
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (a : ι → ℝ) (M : ℝ≥0)
    (ha : ∀ i, |a i| ≤ M) (i : ι),
    multiplier e a M ha (e i) = R.readout () () (a i) • e i

theorem actual_law : arena.{u,v}.Law actual := @multiplier_basis.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end MultiplierBasis

namespace MultiplierPositive
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
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (a : ι → ℝ) (M : ℝ≥0)
    (ha : ∀ i, |a i| ≤ M) (hpos : ∀ i, 0 ≤ a i),
    (multiplier e a M ha).IsSymmetric ∧
    ∀ x, 0 ≤ R.readout () () ((multiplier e a M ha).reApplyInnerSelf x)

theorem actual_law : arena.{u,v}.Law actual := @multiplier_positive.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end MultiplierPositive

namespace DiagonalHeat
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
    [InnerProductSpace ℂ H] [CompleteSpace H], ∀ (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i),
    IsSelfAdjoint (hamiltonian e h) ∧
    Dense ((hamiltonian e h).domain : Set H) ∧
    (∀ x y, (x,y) ∈ (hamiltonian e h).graph ↔
      ∀ i, e.repr y i = (h i : ℂ) * e.repr x i) ∧
    (∀ x, x ∈ (hamiltonian e h).domain ↔
      Memℓp (fun i => (h i : ℂ) * e.repr x i) 2) ∧
    (∀ t x i, e.repr (heat e h hh t x) i =
      R.readout () () (Real.exp (-(t : ℝ)*h i) : ℂ)*e.repr x i) ∧
    (∀ t, (heat e h hh t).IsPositive) ∧
    ∃ S : StronglyContinuousContractionSemigroup H,
      (∀ t, S t = (heat e h hh t).restrictScalars ℝ) ∧
      (∀ x v : H, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (heat e h hh t x-x))
        (𝓝[>] 0) (𝓝 v) ↔ (x,-v) ∈ (hamiltonian e h).graph) ∧
      (∀ R : StronglyContinuousContractionSemigroup H,
        (∀ x v, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t x-x))
          (𝓝[>] 0) (𝓝 v) ↔ (x,-v) ∈ (hamiltonian e h).graph) → R = S)

theorem actual_law : arena.{u,v}.Law actual := @diagonal_heat.{u,v}
theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  change (0 : ℂ) ≠ 1
  exact zero_ne_one

-- The positive law preserves the entire source telescope. Whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
end DiagonalHeat
end Reg.D5.S3.Quantum.Analysis.DiagonalHeat
