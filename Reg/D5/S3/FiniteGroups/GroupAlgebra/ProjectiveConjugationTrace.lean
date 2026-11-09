import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
import Reg.Support.DependentFamily

/-! Native registration for the complete arbitrary-coefficient projectivity criterion. -/

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace

open _root_.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped MonoidAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe uR uG uV

structure Criterion where
  R : Type uR
  G : Type uG
  V : Type uV
  [commRing : CommRing R]
  [group : Group G]
  [fintype : Fintype G]
  [addCommGroup : AddCommGroup V]
  [module : Module R V]
  rho : Representation R G V

def projectivePart (c : Criterion.{uR, uG, uV}) : Prop :=
  letI := c.commRing
  letI := c.group
  letI := c.fintype
  letI := c.addCommGroup
  letI := c.module
  Module.Projective c.R[c.G] c.rho.asModule

def tracePart (c : Criterion.{uR, uG, uV}) : Prop :=
  letI := c.commRing
  letI := c.group
  letI := c.fintype
  letI := c.addCommGroup
  letI := c.module
  Module.Projective c.R c.V ∧
    ∃ t : Module.End c.R c.V,
      (∑ g : c.G, (c.rho g).comp (t.comp (c.rho g⁻¹))) = LinearMap.id

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3 × Criterion.{uR, uG, uV}
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uR, uG, uV} :=
  realize signature
    (fun role _ state =>
      if state.1 = 0 then
        match role with
        | false => by classical exact decide (projectivePart state.2)
        | true => by classical exact decide (tracePart state.2)
      else if state.1 = 1 then true else false)
    (fun e => nomatch e)

def rejected : Realization signature.{uR, uG, uV} :=
  realize signature (fun role _ _ => if role then true else false)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{uR, uG, uV}
  Law R := ∀ state, R.readout false () state = R.readout true () state

abbrev criterionStatement : Prop :=
  ∀ {R : Type uR} {G : Type uG} {V : Type uV}
    [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V]
    (rho : Representation R G V),
    Module.Projective R[G] rho.asModule ↔
      Module.Projective R V ∧
        ∃ t : Module.End R V,
          (∑ g : G, (rho g).comp (t.comp (rho g⁻¹))) = LinearMap.id

theorem bridge :
    criterionStatement.{uR, uG, uV} ↔ arena.{uR, uG, uV}.Law actual := by
  classical
  constructor
  · intro h state
    rcases state with ⟨slot, c⟩
    by_cases h0 : slot = 0
    · letI := c.commRing
      letI := c.group
      letI := c.fintype
      letI := c.addCommGroup
      letI := c.module
      have hc := h (R := c.R) (G := c.G) (V := c.V) c.rho
      simp only [actual, realize, h0, if_pos]
      change projectivePart c ↔ tracePart c at hc
      exact Bool.decide_congr hc
    · by_cases h1 : slot = 1
      · simp [actual, realize, h0, h1]
      · simp [actual, realize, h0, h1]
  · intro h R G V commRing group fintype addCommGroup module rho
    let c : Criterion.{uR, uG, uV} := {
      R := R, G := G, V := V, commRing := commRing, group := group,
      fintype := fintype, addCommGroup := addCommGroup, module := module, rho := rho }
    have hc := h (0, c)
    letI := commRing
    letI := group
    letI := fintype
    letI := addCommGroup
    letI := module
    change decide (projectivePart c) = decide (tracePart c) at hc
    have hiff : decide (projectivePart c) = true ↔ decide (tracePart c) = true :=
      Bool.eq_iff_iff.mp hc
    have hiff' : projectivePart c ↔ tracePart c := by
      simpa only [Bool.decide_iff] using hiff
    simpa only [projectivePart, tracePart] using hiff'

theorem actualLaw : arena.{uR, uG, uV}.Law actual := by
  apply bridge.mp
  intro R G V commRing group fintype addCommGroup module rho
  exact projective_iff_projective_and_conjugation_trace_one rho

private def witness : Criterion.{uR, uG, uV} := {
  R := ULift.{uR} ℤ, G := PUnit.{uG + 1}, V := PUnit.{uV + 1},
  rho := (1 : Representation (ULift.{uR} ℤ) PUnit.{uG + 1} PUnit.{uV + 1}) }

private theorem rejected_not_law : ¬ arena.{uR, uG, uV}.Law rejected := by
  intro h
  have hh := h (1, witness)
  change false = true at hh
  cases hh

private theorem sensitivity : Sensitivity arena.{uR, uG, uV} actual := by
  classical
  constructor
  · intro i
    let bad : Realization signature.{uR, uG, uV} := {
      readout := fun j p state =>
        if j = i then
          match i with
          | false => !(actual.readout true p state)
          | true => !(actual.readout false p state)
        else actual.readout j p state
      anchor := fun e => nomatch e }
    refine ⟨bad, ?_, rfl, ?_⟩
    · intro j hj
      funext p state
      simp [bad, hj]
    · intro hlaw
      have hh := hlaw (1, witness)
      cases i <;> simpa [bad, actual] using hh
  · intro i
    exact nomatch i

private theorem dependence : ObservationalDependence signature.{uR, uG, uV} actual := by
  classical
  intro i
  cases i with
  | false =>
      refine ⟨(), (1, witness), (2, witness), ?_⟩
      simp [actual, realize]
  | true =>
      refine ⟨(), (1, witness), (2, witness), ?_⟩
      simp [actual, realize]

def source_registration : Registration arena.{uR, uG, uV}
    criterionStatement.{uR, uG, uV} where
  actual := actual
  bridge := bridge
  variation := ⟨actualLaw, rejected, rejected_not_law⟩
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@projective_iff_projective_and_conjugation_trace_one)
      (Realization signature.{uR, uG, uV}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace.unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uR, uG, uV}⟩
  objectArena := .source ⟨arena.{uR, uG, uV}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uR, uG, uV} ⟨source_registration.{uR, uG, uV}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
