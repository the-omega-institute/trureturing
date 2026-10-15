import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass

open _root_.D5.S3.Arith.FibonacciAtomic
open Geometry.FiniteSourceMass
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open Geometry.AncestorAreaInstability (T)
open Observer.NativeRankedNavigationCompiler (pathCost)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

/-- Two actual source observations over the full address family. -/
@[reducible] def signature : Signature where
  Params := ℕ
  State _ := Address
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output i _ := match i with
    | false => Option Source
    | true => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i n p => match i with
    | false => subtree p (T n)
    | true => mass n p) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R :=
    (∀ (n : ℕ) (p : Address), p ≠ [] →
      ((∃ U, R.readout false n p = some U) ↔
        pathCost p ≤ n ∧ pathCost p.dropLast+2 ≤ n)) ∧
    (∀ (n : ℕ) (p : Address), p ≠ [] → pathCost p ≤ n → pathCost p.dropLast+2 ≤ n →
      R.readout false n p = some (T (n-pathCost p)) ∧
      R.readout true n p = (N (n-pathCost p) : ℝ)/(N n : ℝ)) ∧
    (∀ (n : ℕ) (p : Address), R.readout false n p = none → R.readout true n p = (0:ℝ)) ∧
    (∀ (n : ℕ) (p : Address), (R.readout true n p : ℝ) ≤ 2*Real.goldenRatio*a^p.length) ∧
    (∀ (n : ℕ) (p : Address), (μ n {x | p.IsPrefix x.val}).toReal = R.readout true n p) ∧
    (∀ (n : ℕ) (x : Node n), μ n {x} = (N n : ℝ≥0∞)⁻¹) ∧
    (∀ (n : ℕ) (p : Address), R.readout false n p = some (T (n-pathCost p)) →
      readout p (T n) = if n-pathCost p = 0 then Reply.alpha
        else if n-pathCost p = 1 then Reply.beta else Reply.branch) ∧
    (∀ (n : ℕ) (p : Address) (b : Bool), R.readout false n p = some (.of b) →
      ∀ q : Address, q ≠ [] → R.readout false n (p++q) = none) ∧
    (∀ n : ℕ, R.readout true n [] = (1:ℝ) ∧ readout [] (T n) =
      if n = 0 then Reply.alpha else if n = 1 then Reply.beta else Reply.branch)

def subtreeBad : Realization signature := realize signature
  (fun i n p => match i with
    | false => none
    | true => mass n p) (fun e => nomatch e)

def massBad : Realization signature := realize signature
  (fun i n p => match i with
    | false => subtree p (T n)
    | true => (2:ℝ)) (fun e => nomatch e)

private theorem subtree_bad : ¬ arena.Law subtreeBad := by
  intro h
  have he := (h.2.1 2 [true] (by decide) (by decide) (by decide)).1
  cases he

private theorem mass_bad : ¬ arena.Law massBad := by
  intro h
  have he := (h.2.2.2.2.2.2.2.2 0).1
  norm_num [massBad,realize] at he

/-- Complete native theorem telescope, bridge and family interventions. -/
def familyRegistration : Registration arena (type_of% finite_source_masses) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_source_masses, subtreeBad, subtree_bad⟩
  sensitivity := ⟨by
    intro i
    cases i with
    | false =>
      refine ⟨subtreeBad, ?_, rfl, subtree_bad⟩
      intro j hj
      cases j
      · exact False.elim (hj rfl)
      · rfl
    | true =>
      refine ⟨massBad, ?_, rfl, mass_bad⟩
      intro j hj
      cases j
      · rfl
      · exact False.elim (hj rfl), fun e => nomatch e⟩
  dependence := by
    intro i
    cases i with
    | false =>
      refine ⟨0, [], [false], ?_⟩
      change some (T 0) ≠ none
      simp
    | true =>
      refine ⟨0, [], [false], ?_⟩
      change mass 0 [] ≠ mass 0 [false]
      rw [(finite_source_masses.2.2.2.2.2.2.2.2 0).1,
        finite_source_masses.2.2.1 0 [false] (by rfl)]
      norm_num
}

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass
