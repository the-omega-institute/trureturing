import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
import Reg.Support.DependentFamily

/-! Translating the event tests changes the integer count equations. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts

open Finset
open _root_.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
open _root_.D5.S3.ConceptDynamics.Attribution.UniformTableCalibration (Orbit orbit orbitCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees (countedDegrees)

universe u v w

noncomputable section

abbrev signature : Signature where
  Params := Type v
  State T := Finset T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := Finset T
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def emptyEvent : Realization signature.{v} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

open Classical in
abbrev replicateArena : Arena where
  signature := signature.{v}
  Law R :=
    ∀ {G : Type u} {T : Type v} [Group G] [Fintype T] [MulAction G T]
      [Fintype (Orbit G T)] (n : Orbit G T → ℕ),
      ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
        (∀ (g : G) s, f (g • s) = g • f s) ∧
        (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
          ∀ h : H, (h : G) • f s = f s) ∧
        ∀ A : Finset T, (∑ s : S, if f s ∈ R.readout () T A then (1 : ℕ) else 0) =
          ∑ o : Orbit G T, orbitCount A o * n o

open Classical in
abbrev fiberArena : Arena where
  signature := signature.{v}
  Law R :=
    ∀ {G : Type u} {T : Type v} {S : Type w}
      [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
      [Fintype S] [MulAction G S] (f : S → T),
      (∀ (g : G) s, f (g • s) = g • f s) →
      ∃ n : Orbit G T → ℕ, ∀ A : Finset T,
        (∑ s : S, if f s ∈ A then (1 : ℕ) else 0) =
          ∑ o, orbitCount (R.readout () T A) o * n o

@[instance_reducible] private def trivialAction (G A : Type*) [Monoid G] : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private theorem empty_replicate_fails : ¬ replicateArena.{u,v}.Law emptyEvent := by
  classical
  intro law
  let G := PUnit.{u+1}
  let T := PUnit.{v+1}
  let _ : Group G := inferInstanceAs (Group PUnit)
  let _ : MulAction G T := trivialAction G T
  let _ : Fintype T := inferInstanceAs (Fintype PUnit)
  let _ : Fintype (Orbit G T) := Fintype.ofFinite _
  obtain ⟨S, _, _, f, _, _, counts⟩ := law (G := G) (T := T) (fun _ => 1)
  have impossible := counts univ
  change (∑ s : S, if f s ∈ (∅ : Finset T) then 1 else 0) =
    ∑ o : Orbit G T, orbitCount univ o * 1 at impossible
  have positive : 0 < ∑ o : Orbit G T, orbitCount (univ : Finset T) o * 1 := by
    apply Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _ ) |>.mpr
    refine ⟨orbit (G := G) PUnit.unit, mem_univ _, ?_⟩
    rw [Nat.mul_one, orbitCount]
    exact Finset.card_pos.mpr ⟨PUnit.unit, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  simp only [notMem_empty, ↓reduceIte, sum_const_zero] at impossible
  exact positive.ne' impossible.symm

private theorem empty_fibers_fail : ¬ fiberArena.{u,v,w}.Law emptyEvent := by
  classical
  intro law
  let G := PUnit.{u+1}
  let T := PUnit.{v+1}
  let S := PUnit.{w+1}
  let _ : Group G := inferInstanceAs (Group PUnit)
  let _ : MulAction G T := trivialAction G T
  let _ : MulAction G S := trivialAction G S
  let _ : Fintype T := inferInstanceAs (Fintype PUnit)
  let _ : Fintype S := inferInstanceAs (Fintype PUnit)
  let _ : Fintype (Orbit G T) := Fintype.ofFinite _
  obtain ⟨n, counts⟩ := law (G := G) (S := S) (T := T) (fun _ => PUnit.unit) (fun _ _ => rfl)
  have impossible := counts (univ : Finset T)
  have fixedReadout : emptyEvent.readout () T (univ : Finset T) = ∅ := rfl
  rw [fixedReadout] at impossible
  simp [orbitCount, S] at impossible
  exact impossible (Subsingleton.elim _ _)

private theorem event_dependence : ∀ role : signature.{v}.Role,
    ∃ T : signature.{v}.Params, ∃ A B : signature.{v}.State T,
      actual.readout role T A ≠ actual.readout role T B := by
  intro _
  let T := PUnit.{v+1}
  refine ⟨T, ∅, {PUnit.unit}, ?_⟩
  change (∅ : Finset T) ≠ {PUnit.unit}
  simp

def replicateFamily : Registration replicateArena.{u,v}
    (type_of% (@realize_orbit_copy_counts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realize_orbit_copy_counts, emptyEvent, empty_replicate_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨emptyEvent, ?_, rfl, empty_replicate_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := event_dependence

def fiberFamily : Registration fiberArena.{u,v,w} (type_of% (@count_seed_fibers_by_orbit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_seed_fibers_by_orbit, emptyEvent, empty_fibers_fail⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨emptyEvent, ?_, rfl, empty_fibers_fail⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := event_dependence


def replicateRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@realize_orbit_copy_counts) (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts.replicateEventCounts
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts.replicateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨replicateArena.{u,v}⟩
  objectArena := .source ⟨replicateArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source replicateArena.{u,v} ⟨replicateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn",
        "arg", "arg", "body", "fn", "fn", "fn", "arg", "fn", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def fiberRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@count_seed_fibers_by_orbit) (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts.fiberEventCounts
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts.fiberFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fiberArena.{u,v,w}⟩
  objectArena := .source ⟨fiberArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fiberArena.{u,v,w} ⟨fiberFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "body", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option linter.checkUnivs false in
abbrev degreeEventSignature : Signature where
  Params := Σ _ : Type v, Type w
  State p := p.2 → Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2 → Finset p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def degreeEventActual : Realization degreeEventSignature.{v,w} :=
  realize degreeEventSignature (fun _ _ E => E) (fun e => nomatch e)

def degreeEventEmpty : Realization degreeEventSignature.{v,w} :=
  realize degreeEventSignature (fun _ _ _ _ => ∅) (fun e => nomatch e)

set_option linter.checkUnivs false in
open Classical in
abbrev degreeEventArena : Arena where
  signature := degreeEventSignature.{v,w}
  Law R :=
    ∀ {G : Type u} {T : Type v} {I : Type w}
      [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
      (E : I → Finset T) (w : I → ℤ) (k : ℕ),
      k ∈ countedDegrees (orbitEventMatrix (G := G) E) w ↔
        ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
          (∀ (g : G) s, f (g • s) = g • f s) ∧
          (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
            ∀ h : H, (h : G) • f s = f s) ∧
          ∀ i, ((∑ s : S, if f s ∈ R.readout () ⟨T, I⟩ E i then (1 : ℕ) else 0) : ℤ) =
            (k : ℤ) * w i

private theorem empty_degree_event_fails : ¬ degreeEventArena.{u,v,w}.Law degreeEventEmpty := by
  classical
  intro law
  let G := PUnit.{u+1}
  let T := PUnit.{v+1}
  let I := PUnit.{w+1}
  let _ : Group G := inferInstanceAs (Group PUnit)
  let _ : Fintype T := inferInstanceAs (Fintype PUnit)
  let _ : MulAction G T := trivialAction G T
  let _ : Fintype (Orbit G T) := Fintype.ofFinite _
  let _ : Unique (Orbit G T) := ⟨⟨orbit (G := G) PUnit.unit⟩, fun _ => Subsingleton.elim _ _⟩
  have feasible : 1 ∈ countedDegrees (orbitEventMatrix (G := G) (fun _ : I => (univ : Finset T)))
      (fun _ => 1) := by
    refine ⟨fun _ => 1, fun _ => zero_le_one, ?_⟩
    ext i
    change (∑ o : Orbit G T, (orbitCount (univ : Finset T) o : ℤ) * 1) = 1
    rw [Fintype.sum_unique]
    have one (o : Orbit G T) : orbitCount (univ : Finset T) o = 1 := by
      unfold orbitCount
      apply Finset.card_eq_one.mpr
      refine ⟨PUnit.unit, ?_⟩
      ext t
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact iff_of_true (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    simp only [one, Nat.cast_one, mul_one]
  obtain ⟨S, _, _, f, _, _, counts⟩ :=
    (law (G := G) (T := T) (I := I) (fun _ => univ) (fun _ => 1) 1).mp feasible
  have impossible := counts PUnit.unit
  have empty : degreeEventEmpty.readout () ⟨T, I⟩ (fun _ => univ) PUnit.unit = ∅ := rfl
  rw [empty] at impossible
  simp at impossible

def degreeEventFamily : Registration degreeEventArena.{u,v,w}
    (type_of% (@orbit_event_counts_match_fiber)) where
  actual := degreeEventActual
  bridge := Iff.rfl
  variation := ⟨@orbit_event_counts_match_fiber, degreeEventEmpty, empty_degree_event_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨degreeEventEmpty, ?_, rfl, empty_degree_event_fails⟩
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

def degreeEventRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@orbit_event_counts_match_fiber) (Realization degreeEventSignature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts.degreeEventCounts
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts.degreeEventFamily
  realizationSource := none
  generated := false
  arena := .source ⟨degreeEventArena.{u,v,w}⟩
  objectArena := .source ⟨degreeEventArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source degreeEventArena.{u,v,w} ⟨degreeEventFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize degreeEventSignature (fun _ _ E => E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
    definition := none
    coordinates := #[1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg",
          "arg", "body", "fn", "arg", "arg", "body", "fn", "fn", "fn", "arg",
          "fn", "arg", "fn"]
        stateBinder := 7
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts
