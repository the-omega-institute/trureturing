import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.PeriodicOrbits.OrbitCounting

namespace Reg.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting

open LeanInformationAudit Function
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
open _root_.D5.S1.Descent.FiniteSelfMapConjugacy (cycleLengthMultiplicity)

noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State X := X → X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X → X
  Anchor := Empty
  finiteAnchor := inferInstance

def noAnchor : ∀ (_ : Empty) (X : Type u), X → X := fun e => nomatch e

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f) noAnchor.{u}

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => id) noAnchor.{u}

def flip : ULift.{u} Bool → ULift.{u} Bool := fun x => ⟨!x.down⟩

abbrev sample := ULift.{u} Bool

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨sample, id, flip, ?_⟩
  intro h
  have hx := congrArg (fun f => (f (ULift.up false)).down) h
  change false = true at hx
  cases hx

private theorem stratum_flip_one :
    Fintype.card (Stratum flip.{u} 1) = 0 := by
  letI : IsEmpty (Stratum flip.{u} 1) := ⟨fun x =>
    Bool.not_ne_self x.val.down
      (congrArg ULift.down (minimalPeriod_eq_one_iff_isFixedPt.mp x.property))⟩
  exact Fintype.card_eq_zero

private theorem stratum_id_one :
    Fintype.card (Stratum (id : ULift.{u} Bool → _) 1) = 2 := by
  let e : Stratum (id : ULift.{u} Bool → _) 1 ≃ ULift.{u} Bool :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, by simp⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (by simp)

private theorem multiplicity_flip_one : cycleLengthMultiplicity flip.{u} 1 = 0 := by
  classical
  change (Finset.univ.filter (fun x => minimalPeriod flip x = 1)).card / 1 = 0
  rw [← Fintype.card_subtype]
  exact Nat.div_one _ ▸ stratum_flip_one

private theorem multiplicity_id_one :
    cycleLengthMultiplicity (id : ULift.{u} Bool → _) 1 = 2 := by
  classical
  simp [cycleLengthMultiplicity]

private theorem fixed_flip_one : fixedCount flip.{u} 1 = 0 := by
  classical
  unfold fixedCount
  have h : ∀ x : ULift.{u} Bool, flip x ≠ x := fun x hx =>
    Bool.not_ne_self x.down (congrArg ULift.down hx)
  simp [h]

private theorem fixed_id_one : fixedCount (id : ULift.{u} Bool → _) 1 = 2 := by
  classical
  simp [fixedCount]

abbrev stratumArena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (f : X → X) [Fintype X] {n : ℕ}, 0 < n →
    Fintype.card (Stratum (R.readout () X f) n) = n * Fintype.card (Orbits f n)

abbrev stratumScope := type_of% (@stratum_card.{u})

private theorem stratum_bridge : stratumScope.{u} ↔ stratumArena.{u}.Law actual := by
  rfl

private theorem stratum_rejected : ¬ stratumArena.{u}.Law rejected := by
  intro h
  have hbad := h flip (n := 1) (by decide)
  have hgood := stratum_card flip (n := 1) (by decide)
  have he := hbad.trans hgood.symm
  change Fintype.card (Stratum (id : ULift.{u} Bool → _) 1) =
    Fintype.card (Stratum flip 1) at he
  rw [stratum_id_one, stratum_flip_one] at he
  omega

def stratumFamily : Registration stratumArena.{u} stratumScope.{u} where
  actual := actual
  bridge := stratum_bridge
  variation := ⟨stratum_bridge.mp (@stratum_card.{u}), rejected, stratum_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, stratum_rejected⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def stratumRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@stratum_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.stratum_card.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.stratumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨stratumArena.{u}⟩
  objectArena := .source ⟨stratumArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stratumArena ⟨stratumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u} (fun _ _ f => f) noAnchor.{u})
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev multiplicityArena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (f : X → X) [Fintype X] {n : ℕ}, 0 < n →
    cycleLengthMultiplicity (R.readout () X f) n = Fintype.card (Orbits f n)

abbrev multiplicityScope := type_of% (@multiplicity_eq_orbit_card.{u})

private theorem multiplicity_bridge : multiplicityScope.{u} ↔ multiplicityArena.{u}.Law actual := by
  rfl

private theorem multiplicity_rejected : ¬ multiplicityArena.{u}.Law rejected := by
  intro h
  have hbad := h flip (n := 1) (by decide)
  have hgood := multiplicity_eq_orbit_card flip (n := 1) (by decide)
  have he := hbad.trans hgood.symm
  change cycleLengthMultiplicity (id : ULift.{u} Bool → _) 1 =
    cycleLengthMultiplicity flip 1 at he
  rw [multiplicity_id_one, multiplicity_flip_one] at he
  omega

def multiplicityFamily : Registration multiplicityArena.{u} multiplicityScope.{u} where
  actual := actual
  bridge := multiplicity_bridge
  variation := ⟨multiplicity_bridge.mp (@multiplicity_eq_orbit_card.{u}), rejected, multiplicity_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, multiplicity_rejected⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def multiplicityRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@multiplicity_eq_orbit_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.multiplicity_eq_orbit_card.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.multiplicityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨multiplicityArena.{u}⟩
  objectArena := .source ⟨multiplicityArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source multiplicityArena ⟨multiplicityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u} (fun _ _ f => f) noAnchor.{u})
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev fixedArena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (f : X → X) [Fintype X] {n : ℕ}, 0 < n →
    fixedCount (R.readout () X f) n = ∑ d ∈ n.divisors, d * cycleLengthMultiplicity f d

abbrev fixedScope := type_of% (@fixed_count_divisor_sum.{u})

private theorem fixed_bridge : fixedScope.{u} ↔ fixedArena.{u}.Law actual := by
  rfl

private theorem fixed_rejected : ¬ fixedArena.{u}.Law rejected := by
  intro h
  have hbad := h flip (n := 1) (by decide)
  have hgood := fixed_count_divisor_sum flip (n := 1) (by decide)
  have he := hbad.trans hgood.symm
  change fixedCount (id : ULift.{u} Bool → _) 1 = fixedCount flip 1 at he
  rw [fixed_id_one, fixed_flip_one] at he
  omega

def fixedFamily : Registration fixedArena.{u} fixedScope.{u} where
  actual := actual
  bridge := fixed_bridge
  variation := ⟨fixed_bridge.mp (@fixed_count_divisor_sum.{u}), rejected, fixed_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, fixed_rejected⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def fixedRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fixed_count_divisor_sum.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.fixed_count_divisor_sum.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.fixedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fixedArena.{u}⟩
  objectArena := .source ⟨fixedArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fixedArena ⟨fixedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u} (fun _ _ f => f) noAnchor.{u})
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev deltaArena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (f : X → X) [Fintype X] {n : ℕ}, 0 < n →
    delta (fixedCount (R.readout () X f)) n = (n : ℤ) * (cycleLengthMultiplicity f n : ℤ)

abbrev deltaScope := type_of% (@delta_fixed_count.{u})

private theorem delta_bridge : deltaScope.{u} ↔ deltaArena.{u}.Law actual := by
  rfl

private theorem delta_rejected : ¬ deltaArena.{u}.Law rejected := by
  intro h
  have hbad := h flip (n := 1) (by decide)
  have hgood := delta_fixed_count flip (n := 1) (by decide)
  have he := hbad.trans hgood.symm
  change delta (fixedCount (id : ULift.{u} Bool → _)) 1 = delta (fixedCount flip) 1 at he
  simp [delta, fixed_id_one, fixed_flip_one] at he

def deltaFamily : Registration deltaArena.{u} deltaScope.{u} where
  actual := actual
  bridge := delta_bridge
  variation := ⟨delta_bridge.mp (@delta_fixed_count.{u}), rejected, delta_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, delta_rejected⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def deltaRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@delta_fixed_count.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.delta_fixed_count.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.deltaFamily
  realizationSource := none
  generated := false
  arena := .source ⟨deltaArena.{u}⟩
  objectArena := .source ⟨deltaArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deltaArena ⟨deltaFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u} (fun _ _ f => f) noAnchor.{u})
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Phase

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (f : X → X) {n : ℕ}, 0 < n →
    ∃ e : (Orbits f n × Fin n) ≃ Stratum f n,
      ∀ o i, (e (o, i)).val =
        (R.readout () X f)^[i.val] (representative f n o).val

abbrev sourceScope := type_of% (@orbit_phase_decomposition.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := by
  rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hmin (x : ULift.{u} Bool) : minimalPeriod flip x = 2 := by
    apply minimalPeriod_eq_prime (p := 2)
    · change flip (flip x) = x
      simp [flip]
    · intro hx
      exact Bool.not_ne_self x.down (congrArg ULift.down hx)
  let x : Stratum flip.{u} 2 := ⟨⟨false⟩, hmin _⟩
  let o : Orbits flip.{u} 2 := ⟨periodicOrbit flip x.val, ⟨x, rfl⟩⟩
  obtain ⟨e, he⟩ := h flip (n := 2) (by decide)
  have hzero := he o (0 : Fin 2)
  have hone := he o (1 : Fin 2)
  simp only [rejected, realize, iterate_id, id_eq] at hzero hone
  have heq := e.injective (Subtype.ext (hzero.trans hone.symm))
  have hfin := congrArg (fun p => p.2.val) heq
  norm_num at hfin

def familyRegistration : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@orbit_phase_decomposition.{u}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨sample, id, flip, ?_⟩
    intro h
    have hx := congrArg (fun f => (f (ULift.up false)).down) h
    change false = true at hx
    cases hx

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@orbit_phase_decomposition.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.orbit_phase_decomposition.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.Phase.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u} (fun _ _ f => f) noAnchor.{u})
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "arg", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Phase
end
end Reg.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
