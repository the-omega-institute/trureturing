import D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of path-power graphs, fit radii and edge potentials. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open SimpleGraph SimpleGraph.PathPower
open _root_.Reg.Support

noncomputable section

universe u

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound

namespace Elimination

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun n => SimpleGraph (Fin n))

def actual : Realization signature :=
  realize signature (fun _ n k => pathPower n k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n _ => cycleGraph n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k, (R.readout () n k).IsChordal

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let G := cycleGraph 4
  let e₀ : G.Adj 0 1 := by decide
  let e₁ : G.Adj 1 2 := by decide
  let e₂ : G.Adj 2 3 := by decide
  let e₃ : G.Adj 3 0 := by decide
  let p : G.Walk 0 0 := .cons e₀ (.cons e₁ (.cons e₂ e₃.toWalk))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [Walk.isPath_def]
      decide
    · decide
  have hall : ∀ a b : Fin 4, G.Adj a b → s(a, b) ∈ p.edges := by decide
  obtain ⟨a, b, _, _, ha, hn⟩ := (h 4 0) p hp (by decide)
  exact hn (hall a b ha)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨2, 0, 1, ?_⟩
  intro h
  have h₁ : (pathPower 2 1).Adj 0 1 := by
    change (0 : Fin 2) ≠ 1 ∧ (0 : ℤ).natAbs.succ ≤ 1
    decide
  have h₀ : ¬ (pathPower 2 0).Adj 0 1 := by
    change ¬ ((0 : Fin 2) ≠ 1 ∧ (1 : ℤ).natAbs ≤ 0)
    decide
  change pathPower 2 0 = pathPower 2 1 at h
  exact h₀ (h.symm ▸ h₁)

def family : Registration arena (type_of% (@pathPower_isChordal)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathPower_isChordal, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pathPower_isChordal) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.PathPower.pathPower_isChordal.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound.Elimination.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Elimination
namespace Upper

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => 2 * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] (n k : ℕ) (_hk : 1 ≤ k)
    (g : Fin n → Fin n → H) (ε : ℝ) (_hε : 0 ≤ ε)
    (_hrev : ∀ i j, (pathPower n k).Adj i j → g j i = (g i j)⁻¹)
    (_htri : ∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → Dist.dist (g i j * g j l) (g i l) ≤ ε),
    ∃ φ : Fin n → H, ∀ i j, (pathPower n k).Adj i j →
      Dist.dist (g i j) ((φ i)⁻¹ * φ j) ≤ R.readout () () ε

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let H := PUnit.{u+1}
  let : IsIsometricSMul H H := ⟨fun _ => Isometry.of_dist_eq fun _ _ => rfl⟩
  let : IsIsometricSMul Hᵐᵒᵖ H := ⟨fun _ => Isometry.of_dist_eq fun _ _ => rfl⟩
  obtain ⟨φ, hφ⟩ := h (H := H) 2 1 le_rfl (fun _ _ => 1) 0 le_rfl
    (by simp) (by simp [_root_.dist_self])
  have he : (pathPower 2 1).Adj 0 1 := by
    change (0 : Fin 2) ≠ 1 ∧ (1 : ℤ).natAbs ≤ 1
    decide
  have hb := hφ 0 1 he
  change (0 : ℝ) ≤ -1 at hb
  norm_num at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (type_of% (@pathPower_exists_two_approximate_gain_potential.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathPower_exists_two_approximate_gain_potential.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pathPower_exists_two_approximate_gain_potential.{u}) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.PathPower.pathPower_exists_two_approximate_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound.Upper.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Upper


private def varyingPotential {n : ℕ} (φ : Fin n → IntegralCycles) (i j : Fin n) :
    IntegralCycles := (φ i)⁻¹ * φ j

private theorem varyingPotential_ne {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ∃ φ : Fin n → IntegralCycles, varyingPotential φ a a ≠ varyingPotential φ a b := by
  let v : IntegralCycles := Multiplicative.ofAdd (fun _ : Fin 19 => (1 : ℤ))
  let φ : Fin n → IntegralCycles := fun j => if j = a then 1 else v
  refine ⟨φ, ?_⟩
  simp only [varyingPotential, φ, ite_eq_left rfl, ite_eq_right hab.symm, inv_one, one_mul]
  intro he
  have hz := congrArg (fun x : IntegralCycles => Multiplicative.toAdd x (0 : Fin 19)) he
  change (0 : ℤ) = 1 at hz
  omega

namespace Base

abbrev Params := Σ _ : (Fin 12 → IntegralCycles), Fin 12
abbrev signature := SingleDependentReadout.signature Params (fun _ => Fin 12) (fun _ => IntegralCycles)

def actual : Realization signature :=
  realize signature (fun _ p j => (p.1 p.2)⁻¹ * p.1 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p j => integralGain p.2 j) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ a b, (pathPower 12 3).Adj a b → realGain b a = -realGain a b) ∧
    (∀ a b c, (pathPower 12 3).Adj a b → (pathPower 12 3).Adj b c →
      (pathPower 12 3).Adj a c → Dist.dist (realGain a b + realGain b c) (realGain a c) ≤ 1) ∧
    (∀ φ : Fin 12 → RealCycles, ∃ i j, (pathPower 12 3).Adj i j ∧
      (49 / 48 : ℝ) ≤ Dist.dist (realGain i j) (φ j - φ i)) ∧
    (∀ a b, (pathPower 12 3).Adj a b → integralGain b a = (integralGain a b)⁻¹) ∧
    (∀ a b c, (pathPower 12 3).Adj a b → (pathPower 12 3).Adj b c →
      (pathPower 12 3).Adj a c → Dist.dist (integralGain a b * integralGain b c) (integralGain a c) ≤ 1) ∧
    (∀ φ : Fin 12 → IntegralCycles, ∃ i j, (pathPower 12 3).Adj i j ∧
      2 ≤ Dist.dist (integralGain i j) (R.readout () ⟨φ, i⟩ j))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, _, _, _, _, h⟩
  obtain ⟨i, j, _, hbad⟩ := h (fun _ => 1)
  change (2 : ℝ) ≤ Dist.dist (integralGain i j) (integralGain i j) at hbad
  rw [_root_.dist_self] at hbad
  norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨φ, hφ⟩ := varyingPotential_ne (0 : Fin 12) 1 (by decide)
  exact ⟨⟨φ, 0⟩, 0, 1, hφ⟩

def family : Registration arena (type_of% (@pathPower_three_banach_and_integral_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathPower_three_banach_and_integral_lower_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pathPower_three_banach_and_integral_lower_bound) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.PathPower.pathPower_three_banach_and_integral_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound.Base.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Base

namespace Sharp

abbrev Params := Σ n : ℕ, Σ _ : (Fin n → IntegralCycles), Fin n
abbrev signature := SingleDependentReadout.signature Params
  (fun p => Fin p.1) (fun _ => IntegralCycles)

def actual : Realization signature :=
  realize signature (fun _ p j => (p.2.1 p.2.2)⁻¹ * p.2.1 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p j => integralGain p.2.2 j) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 12 ≤ n →
    (∀ a b, (pathPower n 3).Adj a b → integralGain b a = (integralGain a b)⁻¹) ∧
    (∀ a b c, (pathPower n 3).Adj a b → (pathPower n 3).Adj b c →
      (pathPower n 3).Adj a c → Dist.dist (integralGain a b * integralGain b c) (integralGain a c) ≤ 1) ∧
    (∀ φ : Fin n → IntegralCycles, ∃ i j, (pathPower n 3).Adj i j ∧
      2 ≤ Dist.dist (integralGain i j) (R.readout () ⟨n, φ, i⟩ j)) ∧
    (∃ φ : Fin n → IntegralCycles, ∀ i j, (pathPower n 3).Adj i j →
      Dist.dist (integralGain i j) ((φ i)⁻¹ * φ j) ≤ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨i, j, _, hbad⟩ := (h 12 le_rfl).2.2.1 (fun _ => 1)
  change (2 : ℝ) ≤ Dist.dist (integralGain i j) (integralGain i j) at hbad
  rw [_root_.dist_self] at hbad
  norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨φ, hφ⟩ := varyingPotential_ne (0 : Fin 12) 1 (by decide)
  exact ⟨⟨12, φ, 0⟩, 0, 1, hφ⟩

def family : Registration arena (type_of% (@pathPower_three_exact_two)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathPower_three_exact_two, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pathPower_three_exact_two) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.PathPower.pathPower_three_exact_two.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound.Sharp.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sharp

end Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBound
