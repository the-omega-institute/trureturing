import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget
import Reg.Support.DependentFamily

/-! Changing the realized events can invalidate the eventual budget assertion. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget

open Finset
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget
open _root_.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration (Orbit orbit orbitCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v w

noncomputable section

set_option linter.checkUnivs false in
abbrev signature : Signature where
  Params := Σ _ : Type v, Type w
  State p := p.2 → Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2 → Finset p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v,w} :=
  realize signature (fun _ _ E => E) (fun e => nomatch e)

def emptyEvents : Realization signature.{v,w} :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

set_option linter.checkUnivs false in
open Classical in
abbrev arena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {T : Type v} {I : Type w}
      [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)] [Fintype I]
      (E : I → Finset T) (q : I → ℚ),
      (∃ i, E i = univ ∧ q i = 1) →
      (∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
        ∀ i, ∑ o, (orbitCount (E i) o : ℝ) * x o = (q i : ℝ)) →
      let m := (univ : Finset I).lcm fun i => (q i).den
      ∃ z : I → ℤ, (∀ i, (z i : ℚ) = m * q i) ∧
        let M := restrictedOrbitMap (G := G) E z
        let h := addOrderOf (QuotientAddGroup.mk z : (I → ℤ) ⧸ M.range)
        0 < h ∧
          (∀ N : ℕ, 0 < N → EventBudget (G := G) E q N → m * h ∣ N) ∧
          ∃ threshold : ℕ, ∀ t : ℕ, 0 < t → threshold ≤ t →
            EventBudget (G := G) (R.readout () ⟨T, I⟩ E) q (m * (h * t))

@[instance_reducible] private def trivialAction (G A : Type*) [Monoid G] : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private theorem empty_events_fail : ¬ arena.{u,v,w}.Law emptyEvents := by
  classical
  intro law
  let G := PUnit.{u+1}
  let T := PUnit.{v+1}
  let I := PUnit.{w+1}
  let _ : Group G := inferInstanceAs (Group PUnit)
  let _ : Fintype T := inferInstanceAs (Fintype PUnit)
  let _ : Fintype I := inferInstanceAs (Fintype PUnit)
  let _ : MulAction G T := trivialAction G T
  let _ : Fintype (Orbit G T) := Fintype.ofFinite _
  let _ : Unique (Orbit G T) := ⟨⟨orbit (G := G) PUnit.unit⟩, fun _ => Subsingleton.elim _ _⟩
  have feasible : ∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
      ∀ _ : I, ∑ o, (orbitCount (univ : Finset T) o : ℝ) * x o = 1 := by
    refine ⟨fun _ => 1, fun _ => zero_le_one, fun _ => ?_⟩
    rw [Fintype.sum_unique]
    have one (o : Orbit G T) : orbitCount (univ : Finset T) o = 1 := by
      unfold orbitCount
      apply Finset.card_eq_one.mpr
      refine ⟨PUnit.unit, ?_⟩
      ext t
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact iff_of_true (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    simp only [one, Nat.cast_one, mul_one]
  obtain ⟨z, _, _, _, threshold, tail⟩ :=
    law (G := G) (T := T) (I := I) (fun _ => univ) (fun _ => 1)
      ⟨PUnit.unit, rfl, rfl⟩ (by simpa only [Rat.cast_one] using feasible)
  obtain ⟨S, _, _, f, _, _, _, counts⟩ :=
    tail (threshold + 1) (Nat.zero_lt_succ _) (Nat.le_succ _)
  have impossible := counts PUnit.unit
  change ((∑ s : S, if f s ∈ (∅ : Finset T) then (1 : ℕ) else 0) : ℚ) / _ = 1
    at impossible
  simp at impossible

def family : Registration arena.{u,v,w} (type_of% (@eventual_uniform_event_budgets)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventual_uniform_event_budgets, emptyEvents, empty_events_fail⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨emptyEvents, ?_, rfl, empty_events_fail⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨⟨PUnit.{v+1}, PUnit.{w+1}⟩, fun _ => ∅, fun _ => {PUnit.unit}, ?_⟩
    intro equal
    have events := congrFun equal PUnit.unit
    change (∅ : Finset PUnit.{v+1}) = {PUnit.unit} at events
    exact Finset.empty_ne_singleton _ events


def budgetRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventual_uniform_event_budgets) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget.eventualBudgets
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ E => E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget
    definition := none
    coordinates := #[1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "arg",
          "arg", "arg", "body", "body", "body", "body", "fn", "fn", "arg"]
        stateBinder := 8
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ActiveOrbitBudget
