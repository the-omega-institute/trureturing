import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import Reg.Support.DependentFamily

/-! Budget sensitivity of the zero fixed-count condition. -/

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n k => decide (Odd (n + 2) ∨ Even k)) (fun e => nomatch e)

def alwaysFalse : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k, RealizableSeedCounts n k (fun _ => 0) ↔ R.readout () n k = true

private theorem always_false_fails : ¬ arena.Law alwaysFalse := by
  intro law
  have existsZero := (zero_coordinate_counts_iff 0 2).2 (Or.inr ⟨1, rfl⟩)
  exact Bool.false_ne_true ((law 0 2).1 existsZero)

def family : Registration arena (type_of% zero_coordinate_counts_iff) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using zero_coordinate_counts_iff,
    alwaysFalse, always_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨alwaysFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, always_false_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    intro role
    cases role
    refine ⟨0, 1, 2, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    zero_coordinate_counts_iff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.zeroCondition
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => decide (Odd (n + 2) ∨ Even k))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev additionSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def addBudgets : Realization additionSignature :=
  realize additionSignature (fun _ l k => k + l) (fun e => nomatch e)

def zeroBudget : Realization additionSignature :=
  realize additionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev additionArena : Arena where
  signature := additionSignature
  Law R := ∀ {n k l : ℕ} {x y : Fin (n + 2) → ℕ},
    RealizableSeedCounts n k x → RealizableSeedCounts n l y →
      RealizableSeedCounts n (R.readout () l k) (fun j => x j + y j)

private def firstOnly : Fin 2 → ℕ := ![4, 0]

private theorem first_only_exists : RealizableSeedCounts 0 1 firstOnly := by
  exact (exact_two_coordinate_counts 1 _).mpr ⟨1, 0, rfl, by decide, Or.inr (by decide)⟩

private theorem zero_budget_fails : ¬ additionArena.Law zeroBudget := by
  intro law
  have doubled := law first_only_exists first_only_exists
  obtain ⟨a, b, counts, bound, _⟩ := (exact_two_coordinate_counts 0 _).mp doubled
  have atFirst := congrFun counts 0
  simp [firstOnly] at atFirst
  omega

def additionFamily : Registration additionArena (type_of% (@add_realizable_seed_counts)) where
  actual := addBudgets
  bridge := Iff.rfl
  variation := ⟨@add_realizable_seed_counts, zeroBudget, zero_budget_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroBudget, ?_, rfl, zero_budget_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨0, 0, 1, by decide⟩

def additionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@add_realizable_seed_counts) (Realization additionSignature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.addedBudget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.additionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨additionArena⟩
  objectArena := .source ⟨additionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source additionArena ⟨additionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize additionSignature (fun _ l k => k + l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev relabelSignature : Signature where
  Params := ℕ
  State n := Equiv.Perm (Fin (n + 2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin (n + 2) → Fin (n + 2)
  Anchor := Empty
  finiteAnchor := inferInstance

def relabelCoordinates : Realization relabelSignature :=
  realize relabelSignature (fun _ _ p => ⇑p) (fun e => nomatch e)

def useFirstCoordinate : Realization relabelSignature :=
  realize relabelSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev relabelArena : Arena where
  signature := relabelSignature
  Law R := ∀ {n k : ℕ} (p : Equiv.Perm (Fin (n + 2))) {v : Fin (n + 2) → ℕ},
    RealizableSeedCounts n k v → RealizableSeedCounts n k (v ∘ R.readout () n p)

private theorem first_coordinate_fails : ¬ relabelArena.Law useFirstCoordinate := by
  intro law
  have repeated := law (Equiv.refl (Fin 2)) first_only_exists
  obtain ⟨a, b, counts, bound, _⟩ := (exact_two_coordinate_counts 1 _).mp repeated
  have atFirst := congrFun counts 0
  have atSecond := congrFun counts 1
  change 4 = 4 * a at atFirst
  change 4 = 4 * b at atSecond
  omega

def relabelFamily : Registration relabelArena
    (type_of% (@ParitySeedCoordinateRelabel.realizable_relabel)) where
  actual := relabelCoordinates
  bridge := Iff.rfl
  variation := ⟨@ParitySeedCoordinateRelabel.realizable_relabel,
    useFirstCoordinate, first_coordinate_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨useFirstCoordinate, ?_, rfl, first_coordinate_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    refine ⟨0, Equiv.refl (Fin 2), Equiv.swap (0 : Fin 2) 1, ?_⟩
    intro same
    have atFirst := congrFun same 0
    simpa [relabelCoordinates, realize] using atFirst

def relabelRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ParitySeedCoordinateRelabel.realizable_relabel) (Realization relabelSignature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.coordinatePermutation
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.relabelFamily
  realizationSource := none
  generated := false
  arena := .source ⟨relabelArena⟩
  objectArena := .source ⟨relabelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source relabelArena ⟨relabelFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relabelSignature (fun _ _ p => ⇑p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

structure CoordinateParameters where
  n : ℕ
  State : Type
  action : MulAction (Acting (Fin (n + 2))) State
  i : Fin (n + 2)

abbrev fixationSignature : Signature where
  Params := CoordinateParameters
  State p := p.State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
def observesGenerator : Realization fixationSignature :=
  realize fixationSignature
    (fun _ p s => letI := p.action; decide (generator p.i • s = s)) (fun e => nomatch e)

def ignoresGenerator : Realization fixationSignature :=
  realize fixationSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev fixationArena : Arena where
  signature := fixationSignature
  Law R := ∀ {n : ℕ} {S : Type} [action : MulAction (Acting (Fin (n + 2))) S]
      (i : Fin (n + 2)) (s : S),
    (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s) ↔
      R.readout () ⟨n, S, action, i⟩ s = true

private def fixedPair : Pair 0 :=
  (⟨⟨![true, true], 0⟩, by
    change parity (bitProfile _) = 0
    rw [parity, Fin.sum_univ_two]
    rfl⟩,
    ⟨⟨![true, false], 0⟩, by
      change parity (bitProfile _) = 1
      rw [parity, Fin.sum_univ_two]
      rfl⟩)

private theorem fixed_pair_generator : generator (0 : Fin 2) • fixedPair = fixedPair :=
  (coordinate_fixed_iff_generator (n := 0) 0 fixedPair).mp
    ((pair_fixed_coordinate (n := 0) fixedPair 0).mpr ⟨rfl, rfl⟩)

private theorem ignoring_generator_fails : ¬ fixationArena.Law ignoresGenerator := by
  intro law
  have all := (coordinate_fixed_iff_generator (n := 0) 0 fixedPair).mpr fixed_pair_generator
  exact Bool.false_ne_true ((law (n := 0) 0 fixedPair).mp all)

def fixationFamily : Registration fixationArena
    (type_of% (@coordinate_fixed_iff_generator)) where
  actual := observesGenerator
  bridge := by
    simp [observesGenerator, realize]
  variation := ⟨by
    intro n S action i s
    simpa [observesGenerator, realize] using coordinate_fixed_iff_generator i s,
    ignoresGenerator, ignoring_generator_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨ignoresGenerator, ?_, rfl, ignoring_generator_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    let p : CoordinateParameters := ⟨0, Pair 0, inferInstance, 0⟩
    let moved : Pair 0 := (⟨⟨![false, false], 0⟩, by
      change parity (bitProfile _) = 0
      rw [parity, Fin.sum_univ_two]
      rfl⟩, fixedPair.2)
    have moves : ¬ generator (0 : Fin 2) • moved = moved := by
      intro fixed
      have all := (coordinate_fixed_iff_generator (n := 0) 0 moved).mpr fixed
      have bit : false = true := ((pair_fixed_coordinate moved 0).mp all).1
      exact Bool.false_ne_true bit
    exact ⟨p, fixedPair, moved, by simp [observesGenerator, realize, p, fixed_pair_generator, moves]⟩

open Classical in
def fixationRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coordinate_fixed_iff_generator) (Realization fixationSignature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.generatorFixation
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.fixationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fixationArena⟩
  objectArena := .source ⟨fixationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fixationArena ⟨fixationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fixationSignature
    (fun _ p s => letI := p.action; decide (generator p.i • s = s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
