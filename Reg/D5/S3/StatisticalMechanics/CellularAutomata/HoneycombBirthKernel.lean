import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel
import Reg.Support.SingleDependentReadout

/-! Source registrations for HoneycombBirthKernel. -/

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination (Vertex honeycombGraph)
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [local instance] repositoryAdjacency

open Polynomial

/-- The single height-one pair of adjacent cuts contains the seed and its first neighbor. -/
private theorem tiny_cuts :
    omegaDomain 1 0 = {A 0 0, B 0 0} ∧ omegaDomain 1 1 = {A 0 0} := by
  constructor <;> ext v <;> obtain ⟨p, x, y⟩ := v <;> cases p <;>
    simp [omegaDomain, heightSum, g, part, A, B, Prod.mk.injEq] <;> omega

private theorem signed_at_tick_one :
    signedWeight honeycombGraph 1 0 1 (A 0 0) = 0 ∧
    signedWeight honeycombGraph 1 0 1 (B 0 0) = 1 := by
  rw [signedWeight, signedWeight, tiny_cuts.1, tiny_cuts.2]
  decide

private theorem tiny_coeff (j : ℕ) :
    (delta honeycombGraph 1 0).coeff j =
      ∑ v ∈ ({A 0 0, B 0 0} : Finset Vertex), signedWeight honeycombGraph 1 0 j v :=
  coeff_delta_on (by rw [tiny_cuts.1]) j

private theorem tiny_coeff_one : (delta honeycombGraph 1 0).coeff 1 = 1 := by
  rw [tiny_coeff, Finset.sum_insert (by decide), Finset.sum_singleton,
    signed_at_tick_one.1, signed_at_tick_one.2, zero_add]

private theorem tiny_coeff_two : (delta honeycombGraph 1 0).coeff 2 = 0 := by
  rw [tiny_coeff, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [signedWeight, tiny_cuts.1, tiny_cuts.2]
  decide

private theorem zero_coeff : (delta honeycombGraph 0 0).coeff 1 = 0 := by
  have dom : omegaDomain 0 0 = ∅ := by
    ext v
    change v ∈ domain 0 0 ↔ _
    simp only [mem_domain, Finset.notMem_empty, iff_false]
    obtain ⟨p, x, y⟩ := v
    simp only [heightSum]
    omega
  simpa using (coeff_delta_on (G := honeycombGraph) (a := 0) (d := 0)
    (U := ∅) (by simp [dom]) 1)

abbrev GraphWithDecision := Σ G : SimpleGraph Vertex, DecidableRel G.Adj

abbrev WeightParams :=
  Σ G : SimpleGraph Vertex, Σ _ : DecidableRel G.Adj, Σ _ : ℕ, Σ _ : ℕ, ℕ
namespace AdjacentCopy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature GraphWithDecision (fun _ => ℕ) (fun _ => ℕ → ℤ[X])

def actual : Realization signature :=
  realize signature (fun _ p a => @delta p.1 p.2 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p a c => @delta p.1 p.2 a c + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : SimpleGraph Vertex} [i : DecidableRel G.Adj], NeighborLaws G → EarliestBirthIff G →
    ∀ {b a c : ℕ}, 0 < a → 2 ^ b ∣ a → c + 1 ≤ 2 ^ b →
      R.readout () ⟨G, i⟩ a c = X ^ (2 * (a - 2 ^ b)) * delta G (2 ^ b) c

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h repositoryNeighborLaws (earliestBirthIff_of_neighborLaws repositoryNeighborLaws)
    (b := 0) (a := 1) (c := 0) (by decide) (by decide) (by decide)
  change delta honeycombGraph 1 0 + 1 = X ^ (2 * (1 - 2 ^ 0)) * delta honeycombGraph 1 0 at hh
  norm_num at hh

def family : Registration arena (type_of% @adjacent_copy_of_earliest) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjacent_copy_of_earliest, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨⟨honeycombGraph, repositoryAdjacency⟩, 0, 1, ?_⟩
    intro eq
    have read := congrArg (fun p : ℤ[X] => p.coeff 1) (congrFun eq 0)
    change (delta honeycombGraph 0 0).coeff 1 = (delta honeycombGraph 1 0).coeff 1 at read
    rw [zero_coeff, tiny_coeff_one] at read
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@adjacent_copy_of_earliest) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel.AdjacentCopy.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel.AdjacentCopy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => @delta p.1 p.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AdjacentCopy

namespace CoefficientReadout

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature GraphWithDecision (fun _ => ℕ) (fun _ => ℕ → ℤ)

def actual : Realization signature :=
  realize signature (fun _ p j => @kernelEntry p.1 p.2 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p j d => @kernelEntry p.1 p.2 j d + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : SimpleGraph Vertex} [i : DecidableRel G.Adj], NeighborLaws G → EarliestBirthIff G →
    ∀ {b d : ℕ} (j : ℕ), d < 2 ^ b →
      R.readout () ⟨G, i⟩ j d = (delta G (2 ^ b) d).coeff (2 * 2 ^ b - d - 1 + j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have first := earliestBirthIff_of_neighborLaws repositoryNeighborLaws
  have hh := h repositoryNeighborLaws first (b := 0) (d := 0) 0 (by decide)
  rw [← kernelEntry_eq_coeff repositoryNeighborLaws first (b := 0) (d := 0) 0 (by decide)] at hh
  change kernelEntry honeycombGraph 0 0 + 1 = kernelEntry honeycombGraph 0 0 at hh
  omega

def family : Registration arena (type_of% @kernelEntry_eq_coeff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernelEntry_eq_coeff, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨⟨honeycombGraph, repositoryAdjacency⟩, 0, 1, ?_⟩
    intro eq
    have first := earliestBirthIff_of_neighborLaws repositoryNeighborLaws
    have h := congrFun eq 0
    change kernelEntry honeycombGraph 0 0 = kernelEntry honeycombGraph 1 0 at h
    rw [kernelEntry_eq_coeff repositoryNeighborLaws first (b := 0) 0 (by decide),
      kernelEntry_eq_coeff repositoryNeighborLaws first (b := 0) 1 (by decide)] at h
    change (delta honeycombGraph 1 0).coeff 1 = (delta honeycombGraph 1 0).coeff 2 at h
    rw [tiny_coeff_one, tiny_coeff_two] at h
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@kernelEntry_eq_coeff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel.CoefficientReadout.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel.CoefficientReadout.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p j => @kernelEntry p.1 p.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoefficientReadout

namespace SignedCoefficient

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature WeightParams (fun _ => Vertex) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ p v => @signedWeight p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p v => @signedWeight p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 v + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : SimpleGraph Vertex} [i : DecidableRel G.Adj]
      {U : Finset Vertex} {a d : ℕ}, omegaDomain a d ⊆ U → ∀ t : ℕ,
      (delta G a d).coeff t = ∑ v ∈ U, R.readout () ⟨G, i, a, d, t⟩ v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have domeq : omegaDomain 1 0 ⊆ ({A 0 0, B 0 0} : Finset Vertex) := by rw [tiny_cuts.1]
  have hh := @h honeycombGraph repositoryAdjacency {A 0 0, B 0 0} 1 0 domeq 1
  rw [tiny_coeff_one, Finset.sum_insert (by decide), Finset.sum_singleton] at hh
  change 1 = signedWeight honeycombGraph 1 0 1 (A 0 0) + 1 +
    (signedWeight honeycombGraph 1 0 1 (B 0 0) + 1) at hh
  rw [signed_at_tick_one.1, signed_at_tick_one.2] at hh
  omega

def family : Registration arena (type_of% @coeff_delta_on) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coeff_delta_on, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨⟨honeycombGraph, repositoryAdjacency, 1, 0, 1⟩, A 0 0, B 0 0, ?_⟩
    change signedWeight honeycombGraph 1 0 1 (A 0 0) ≠
      signedWeight honeycombGraph 1 0 1 (B 0 0)
    rw [signed_at_tick_one.1, signed_at_tick_one.2]
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@coeff_delta_on) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel.SignedCoefficient.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel.SignedCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => @signedWeight p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel
    definition := none
    coordinates := #[0, 3, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedCoefficient


end

end Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel
