import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge

/-! The full source family observes the exact signed charge of actual configurations.
Raw source-coordinate and escape-origin fields remain unspecified in this audit attempt. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge

open scoped BigOperators
open Finset
open _root_.D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge
open _root_.D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open _root_.D5.S3.StatisticalMechanics.HardCore.GibbsOccupation
open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit

universe u

structure Inputs where
  Carrier : Type u
  finiteCarrier : Fintype Carrier
  equality : DecidableEq Carrier
  graph : SimpleGraph Carrier
  adjacency : DecidableRel graph.Adj
  lam : ℝ
  positive : 0 < lam

abbrev signature : DependentFamily.Signature where
  Params := Inputs.{u}
  State P := Finset P.Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def charge (P : Inputs.{u}) (J : Finset P.Carrier) : ℝ :=
  @configurationCharge P.Carrier P.finiteCarrier P.graph P.adjacency P.lam J

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P J => charge P J) (fun a => nomatch a)

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P J => charge P J + 1) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law r := ∀ P : Inputs.{u},
    letI := P.finiteCarrier
    letI := P.equality
    letI := P.adjacency
    occupationDefect P.graph P.lam =
      ∑ J ∈ configurations P.graph univ,
        (gibbsPMF P.graph univ P.lam P.positive.le J).toReal * r.readout () P J

abbrev sourceScope := type_of% (@defect_eq_expected_charge.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.Carrier P.finiteCarrier P.equality P.graph P.adjacency P.lam P.positive
  · intro h Carrier finiteCarrier equality graph adjacency lam positive
    exact h ⟨Carrier, finiteCarrier, equality, graph, adjacency, lam, positive⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@defect_eq_expected_charge.{u})

def star : SimpleGraph (ULift.{u} (Fin 3)) where
  Adj x y := (x.down = 0 ∧ y.down ≠ 0) ∨ (y.down = 0 ∧ x.down ≠ 0)
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro x; simp⟩

instance starDecidable : DecidableRel star.{u}.Adj := fun x y =>
  inferInstanceAs (Decidable ((x.down = 0 ∧ y.down ≠ 0) ∨ (y.down = 0 ∧ x.down ≠ 0)))

def sample : Inputs.{u} where
  Carrier := ULift.{u} (Fin 3)
  finiteCarrier := inferInstance
  equality := inferInstance
  graph := star
  adjacency := starDecidable
  lam := 1
  positive := zero_lt_one

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have ha := actual_positive sample.{u}
  have hb := h sample.{u}
  change occupationDefect star 1 =
    ∑ J ∈ configurations star univ,
      (gibbsPMF star univ 1 zero_le_one J).toReal * charge sample J at ha
  change occupationDefect star 1 =
    ∑ J ∈ configurations star univ,
      (gibbsPMF star univ 1 zero_le_one J).toReal * (charge sample J + 1) at hb
  simp only [mul_add, mul_one, sum_add_distrib, gibbs_pmf_toReal,
    gibbs_mass_sum star univ 1 zero_le_one] at ha hb
  linarith

theorem observation_dependence : DependentFamily.ObservationalDependence
    signature.{u} actual.{u} := by
  classical
  intro i
  let J : Finset (ULift.{u} (Fin 3)) := {ULift.up 1, ULift.up 2}
  refine ⟨sample.{u}, ∅, J, ?_⟩
  change charge sample ∅ ≠ charge sample J
  dsimp [J]
  have hU : (univ : Finset (ULift.{u} (Fin 3))) =
      {ULift.up 0, ULift.up 1, ULift.up 2} := by decide
  dsimp [charge, sample, configurationCharge]
  rw [hU]
  norm_num [degreeWeight, occupiedNeighbors, SimpleGraph.degree,
    SimpleGraph.neighborFinset_eq_filter, hU, star]

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro a
      exact nomatch a
  dependence := observation_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@defect_eq_expected_charge.{u})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge.defect_eq_expected_charge.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature.{u}
    (fun _ P J => charge P J) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.StatisticalMechanics.HardCore.ConfigurationCharge
