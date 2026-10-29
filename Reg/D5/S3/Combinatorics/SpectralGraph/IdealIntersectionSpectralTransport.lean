import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport

/-! Candidate source-bound observations of actual adjacency and ideal-fiber sizes.
The source selectors and all proof terms require current native validation.
The whole spectral record has a faithful Boolean attempt below; its observation
dependence fails, so no completed registration for it is claimed here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport

structure PrimeData where
  p : Fin 3 → ℕ
  hp : ∀ i, (p i).Prime
  hi : Function.Injective p

private def basePrimes : PrimeData where
  p := ![2, 3, 5]
  hp := by intro i; fin_cases i <;> norm_num
  hi := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

private def baseK : Fin 3 → ℕ := fun _ => 2

private def leftVertex : ExponentVertex baseK :=
  ⟨![0, 2, 2], by
    constructor
    · intro h
      have hh := congrArg (fun f => (f 1).val) h
      norm_num [zeroCoordinate] at hh
    · intro h
      have hh := congrArg (fun f => (f 0).val) h
      norm_num [lastCoordinate, baseK] at hh⟩

private def rightVertex : ExponentVertex baseK :=
  ⟨![1, 2, 2], by
    constructor
    · intro h
      have hh := congrArg (fun f => (f 0).val) h
      norm_num [zeroCoordinate] at hh
    · intro h
      have hh := congrArg (fun f => (f 0).val) h
      norm_num [lastCoordinate, baseK] at hh⟩

private theorem base_overlap : leftVertex ≠ rightVertex ∧
    (support baseK leftVertex.val ∩ support baseK rightVertex.val).Nonempty := by
  constructor
  · intro h
    have hh := congrArg (fun v => (v.val 0).val) h
    norm_num [leftVertex, rightVertex] at hh
  · exact ⟨0, by decide⟩

structure AdjacencyParams where
  primes : PrimeData
  k : Fin 3 → ℕ
  first : ExponentVertex k

abbrev adjacencySignature : Signature where
  Params := AdjacencyParams
  State d := ExponentVertex d.k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def adjacencyActual : Realization adjacencySignature :=
  realize adjacencySignature (fun _ d second =>
    @decide ((idealGraph (primeProduct d.primes.p d.k)).Adj
      (idealEquiv d.primes.p d.k d.primes.hp d.primes.hi d.first)
      (idealEquiv d.primes.p d.k d.primes.hp d.primes.hi second))
      (Classical.propDecidable _)) (fun e => nomatch e)

def adjacencyRejected : Realization adjacencySignature :=
  realize adjacencySignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev adjacencyArena : Arena where
  signature := adjacencySignature
  Law r := ∀ (d : AdjacencyParams) (second : ExponentVertex d.k),
    r.readout () d second = true ↔ d.first ≠ second ∧
      (support d.k d.first.val ∩ support d.k second.val).Nonempty

private def adjacencyBase : AdjacencyParams := ⟨basePrimes, baseK, leftVertex⟩

private theorem adjacency_rejected : ¬ adjacencyArena.Law adjacencyRejected := by
  intro h
  have hh := (h adjacencyBase rightVertex).mpr base_overlap
  exact Bool.noConfusion hh

private theorem adjacency_dependence :
    ObservationalDependence adjacencySignature adjacencyActual := by
  intro i
  refine ⟨adjacencyBase, leftVertex, rightVertex, ?_⟩
  have hf : adjacencyActual.readout i adjacencyBase leftVertex = false := by
    simp [adjacencyActual, realize, adjacencyBase, idealGraph]
  have ht : adjacencyActual.readout i adjacencyBase rightVertex = true := by
    simp only [adjacencyActual, realize, decide_eq_true_eq]
    exact (actual_adjacency basePrimes.p baseK basePrimes.hp basePrimes.hi
      leftVertex rightVertex).mpr base_overlap
  rw [hf, ht]
  decide

def adjacencySource : Registration adjacencyArena (type_of% @actual_adjacency) where
  actual := adjacencyActual
  bridge := by
    constructor
    · intro h d second
      simpa only [adjacencyActual, realize, decide_eq_true_eq] using
        h d.primes.p d.k d.primes.hp d.primes.hi d.first second
    · intro h p k hp hi first second
      have hh := h ⟨⟨p, hp, hi⟩, k, first⟩ second
      simpa only [adjacencyActual, realize, decide_eq_true_eq] using hh
  variation := ⟨by
    intro d second
    simpa only [adjacencyActual, realize, decide_eq_true_eq] using
      actual_adjacency d.primes.p d.k d.primes.hp d.primes.hi d.first second,
    adjacencyRejected, adjacency_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨adjacencyRejected, ?_, rfl, adjacency_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := adjacency_dependence

structure ProperParams where
  primes : PrimeData
  k : Fin 3 → ℕ
  hk : ∀ i, 0 < k i

abbrev properSignature : Signature where
  Params := ProperParams
  State _ := Fin 6
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def properActual : Realization properSignature :=
  realize properSignature (fun _ d j =>
    Nat.card {I : IdealVertex (primeProduct d.primes.p d.k) //
      actualSupport d.primes.p d.k d.primes.hp d.primes.hi I = properSupports j})
    (fun e => nomatch e)

def properRejected : Realization properSignature :=
  realize properSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev properArena : Arena where
  signature := properSignature
  Law r := ∀ (d : ProperParams) (j : Fin 6), r.readout () d j = cellSizes d.k j

private def properBase : ProperParams where
  primes := basePrimes
  k := ![1, 2, 3]
  hk := by intro i; fin_cases i <;> norm_num

private theorem proper_rejected : ¬ properArena.Law properRejected := by
  intro h
  have hh := h properBase 0
  norm_num [properRejected, realize, properBase, cellSizes] at hh

private theorem proper_dependence : ObservationalDependence properSignature properActual := by
  intro i
  refine ⟨properBase, 0, 1, ?_⟩
  change Nat.card _ ≠ Nat.card _
  rw [proper_fiber_card basePrimes.p properBase.k basePrimes.hp basePrimes.hi properBase.hk,
    proper_fiber_card basePrimes.p properBase.k basePrimes.hp basePrimes.hi properBase.hk]
  norm_num [properBase]

def properSource : Registration properArena (type_of% @proper_fiber_card) where
  actual := properActual
  bridge := by
    constructor
    · intro h d j
      exact h d.primes.p d.k d.primes.hp d.primes.hi d.hk j
    · intro h p k hp hi hk j
      exact h ⟨⟨p, hp, hi⟩, k, hk⟩ j
  variation := ⟨fun d j => proper_fiber_card d.primes.p d.k d.primes.hp d.primes.hi d.hk j,
    properRejected, proper_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨properRejected, ?_, rfl, proper_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := proper_dependence

abbrev fullSignature : Signature where
  Params := PrimeData
  State _ := Fin 3 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def fullActual : Realization fullSignature :=
  realize fullSignature (fun _ d k =>
    Nat.card {I : IdealVertex (primeProduct d.p k) //
      actualSupport d.p k d.hp d.hi I = Finset.univ}) (fun e => nomatch e)

def fullRejected : Realization fullSignature :=
  realize fullSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev fullArena : Arena where
  signature := fullSignature
  Law r := ∀ (d : PrimeData) (k : Fin 3 → ℕ), (∀ i, 0 < k i) →
    r.readout () d k = universalOrder k

private theorem full_rejected : ¬ fullArena.Law fullRejected := by
  intro h
  have hh := h basePrimes baseK (by intro i; exact Nat.zero_lt_two)
  norm_num [fullRejected, realize, baseK, universalOrder] at hh

private theorem full_dependence : ObservationalDependence fullSignature fullActual := by
  intro i
  refine ⟨basePrimes, (fun _ => 1), baseK, ?_⟩
  change Nat.card _ ≠ Nat.card _
  rw [full_fiber_card basePrimes.p (fun _ => 1) basePrimes.hp basePrimes.hi
    (by intro j; exact Nat.zero_lt_one),
    full_fiber_card basePrimes.p baseK basePrimes.hp basePrimes.hi
      (by intro j; exact Nat.zero_lt_two)]
  norm_num [baseK]

def fullSource : Registration fullArena (type_of% @full_fiber_card) where
  actual := fullActual
  bridge := by
    constructor
    · intro h d k hk
      exact h d.p k d.hp d.hi hk
    · intro h p k hp hi hk
      exact h ⟨p, hp, hi⟩ k hk
  variation := ⟨fun d k hk => full_fiber_card d.p k d.hp d.hi hk,
    fullRejected, full_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fullRejected, ?_, rfl, full_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := full_dependence

def adjacencyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@actual_adjacency) (Realization adjacencySignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport.adjacencyUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport.adjacencySource
  realizationSource := none
  generated := false
  arena := .source ⟨adjacencyArena⟩
  objectArena := .source ⟨adjacencyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source adjacencyArena ⟨adjacencySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature adjacencyActual.readout adjacencyActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def properRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@proper_fiber_card) (Realization properSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport.properUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport.properSource
  realizationSource := none
  generated := false
  arena := .source ⟨properArena⟩
  objectArena := .source ⟨properArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source properArena ⟨properSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize properSignature properActual.readout properActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def fullRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@full_fiber_card) (Realization fullSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport.fullUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport.fullSource
  realizationSource := none
  generated := false
  arena := .source ⟨fullArena⟩
  objectArena := .source ⟨fullArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fullArena ⟨fullSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fullSignature fullActual.readout fullActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


/-- A faithful direct proposition readout for the whole spectral record.  This
attempt preserves the exact theorem and demonstrates why its Boolean readout
cannot supply observation dependence.  It is not a valid four-slot registration. -/
private structure PositiveExponents where
  k : Fin 3 → ℕ
  hk : ∀ i, 0 < k i

private abbrev spectralBooleanSignature : Signature where
  Params := PrimeData
  State _ := PositiveExponents
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def spectralBooleanAttempt : Realization spectralBooleanSignature :=
  realize spectralBooleanSignature (fun _ d s =>
    @decide (SpectralRealization d.p s.k d.hp d.hi) (Classical.propDecidable _))
    (fun e => nomatch e)

private theorem spectralBooleanAttempt_true (d : PrimeData) (s : PositiveExponents) :
    spectralBooleanAttempt.readout () d s = true := by
  simp only [spectralBooleanAttempt, realize, decide_eq_true_eq]
  exact spectral_realization d.p s.k d.hp d.hi s.hk

private theorem spectralBooleanAttempt_no_dependence :
    ¬ ObservationalDependence spectralBooleanSignature spectralBooleanAttempt := by
  intro h
  obtain ⟨d, s, t, hst⟩ := h ()
  exact hst ((spectralBooleanAttempt_true d s).trans
    (spectralBooleanAttempt_true d t).symm)


#print axioms adjacencySource
#print axioms properSource
#print axioms fullSource

end Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSpectralTransport
