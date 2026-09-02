/- GID: D5/S3/Observer/Hankel/HankelMinimalStateDimension
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/HankelMinimalStateDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hankel rank is the attained minimum; raw state size varies by presentation. -/

import D5.S3.Observer.Hankel.HankelRankMinimality
import D5.S3.Observer.Linear.ReachableObservableQuotientDescent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.HankelMinimalStateDimension

open D5.S3.Observer.Hankel.HankelRankMinimality
open D5.S3.Observer.Linear.ReachableObservableQuotientDescent
open D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
open D5.S3.Observer.LinearMemory.ZeroMemoryCriterion
open Module

universe u

private theorem descent_reachable_eq_reachableSubspace
    {K V U : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) :
    Submodule.span K
        (Set.range fun input : Nat × U => (A ^ input.1) (B input.2)) =
      reachableSubspace A B := by
  rw [reachableSubspace]
  apply congrArg (Submodule.span K)
  ext state
  constructor
  · rintro ⟨⟨k, input⟩, rfl⟩
    exact ⟨k, input, rfl⟩
  · rintro ⟨k, input, rfl⟩
    exact ⟨⟨k, input⟩, rfl⟩

private theorem descent_hidden_eq_eventualKernel
    {K V Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (C : V →ₗ[K] Y) :
    (⨅ k : Nat, LinearMap.ker (C.comp (A ^ k))) = eventualKernel C A := by
  ext state
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  change (∀ k : Nat, C ((A ^ k) state) = 0) ↔
    ∀ k : Nat, C ((A^[k]) state) = 0
  simp only [Module.End.pow_apply]

/-- The frozen quotient-descent theorem, transported to the repository-owned
`reachableSubspace` and `eventualKernel` definitions. -/
theorem canonical_reachable_observable_quotient_descent
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    let reachable := reachableSubspace A B
    let hidden := eventualKernel C A
    let residual : Submodule K reachable := hidden.comap reachable.subtype
    Set.MapsTo A reachable reachable ∧
      Set.MapsTo A hidden hidden ∧
      LinearMap.range B ≤ reachable ∧
      residual ≤ LinearMap.ker (C.domRestrict reachable) ∧
      (∃! inducedDynamics : (reachable ⧸ residual) →ₗ[K] (reachable ⧸ residual),
        ∀ x : reachable, ∀ hx : A x ∈ reachable,
          inducedDynamics (residual.mkQ x) =
            residual.mkQ (⟨A x, hx⟩ : reachable)) ∧
      (∃! descendedInput : U →ₗ[K] (reachable ⧸ residual),
        ∀ input : U, ∀ hinput : B input ∈ reachable,
          descendedInput input =
            residual.mkQ (⟨B input, hinput⟩ : reachable)) ∧
      ∃! descendedOutput : (reachable ⧸ residual) →ₗ[K] Y,
        ∀ x : reachable,
          descendedOutput (residual.mkQ x) = C x := by
  have descent := reachable_observable_quotient_descent A B C
  dsimp only at descent ⊢
  rw [descent_reachable_eq_reachableSubspace A B,
    descent_hidden_eq_eventualKernel A C] at descent
  exact descent

/-- The source residual `R ∩ N`, represented inside the reachable subspace. -/
abbrev MinimalResidual
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    Submodule K (reachableSubspace A B) :=
  (eventualKernel C A).comap (reachableSubspace A B).subtype

/-- The source quotient `X_min = R / (R ∩ N)`, lines 19792--19800. -/
abbrev MinimalStateSpace
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :=
  (reachableSubspace A B) ⧸ MinimalResidual A B C

/-- The induced dynamics `A_min`, selected from the unique map supplied by the
frozen quotient-descent theorem. -/
def minimalDynamics
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    MinimalStateSpace A B C →ₗ[K] MinimalStateSpace A B C :=
  Classical.choose
    (canonical_reachable_observable_quotient_descent A B C).2.2.2.2.1

/-- The descended input map `B_min`, selected from the frozen descent theorem. -/
def minimalInput
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    U →ₗ[K] MinimalStateSpace A B C :=
  Classical.choose
    (canonical_reachable_observable_quotient_descent A B C).2.2.2.2.2.1

/-- The descended output map `C_min`, selected from the frozen descent theorem. -/
def minimalOutput
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    MinimalStateSpace A B C →ₗ[K] Y :=
  Classical.choose
    (canonical_reachable_observable_quotient_descent A B C).2.2.2.2.2.2

private theorem minimalDynamics_mkQ
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (state : reachableSubspace A B)
    (hstate : A state ∈ reachableSubspace A B) :
    minimalDynamics A B C ((MinimalResidual A B C).mkQ state) =
      (MinimalResidual A B C).mkQ
        (⟨A state, hstate⟩ : reachableSubspace A B) := by
  exact
    (Classical.choose_spec
      (canonical_reachable_observable_quotient_descent A B C).2.2.2.2.1).1
      state hstate

private theorem minimalInput_apply
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (input : U) (hinput : B input ∈ reachableSubspace A B) :
    minimalInput A B C input =
      (MinimalResidual A B C).mkQ
        (⟨B input, hinput⟩ : reachableSubspace A B) := by
  exact
    (Classical.choose_spec
      (canonical_reachable_observable_quotient_descent A B C).2.2.2.2.2.1).1
      input hinput

private theorem minimalOutput_mkQ
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (state : reachableSubspace A B) :
    minimalOutput A B C ((MinimalResidual A B C).mkQ state) = C state := by
  exact
    (Classical.choose_spec
      (canonical_reachable_observable_quotient_descent A B C).2.2.2.2.2.2).1
      state

private theorem minimal_iterate_input
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (k : Nat) (input : U) :
    (minimalDynamics A B C ^ k) (minimalInput A B C input) =
      (MinimalResidual A B C).mkQ (reachableGenerator A B k input) := by
  induction k with
  | zero =>
      have inputInReachable : B input ∈ reachableSubspace A B := by
        exact Submodule.subset_span ⟨0, input, by simp⟩
      simpa [reachableGenerator] using
        minimalInput_apply A B C input inputInReachable
  | succ k inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
      have mappedInReachable :
          A (reachableGenerator A B k input) ∈ reachableSubspace A B :=
        (canonical_reachable_observable_quotient_descent A B C).1
          (reachableGenerator A B k input).property
      rw [minimalDynamics_mkQ A B C
        (reachableGenerator A B k input) mappedInReachable]
      apply congrArg (MinimalResidual A B C).mkQ
      apply Subtype.ext
      simp only [reachableGenerator]
      rw [pow_succ', Module.End.mul_apply]

/-- The named quotient realization has every Markov parameter equal to that
of the original system. This is complete input-output behavior at source lines
19866--19872. -/
theorem minimal_markovParameter_eq
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) (k : Nat) :
    markovParameter (minimalDynamics A B C) (minimalInput A B C)
        (minimalOutput A B C) k = markovParameter A B C k := by
  ext input
  simp only [markovParameter, LinearMap.comp_apply]
  rw [minimal_iterate_input A B C k input,
    minimalOutput_mkQ A B C (reachableGenerator A B k input)]
  rfl

/-- A bundled finite-dimensional realization, used only to define the set of
all dimensions presenting one complete Markov behavior. -/
structure FiniteLinearRealization
    (K U Y : Type u) [Field K]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y] where
  State : Type u
  [stateAddCommGroup : AddCommGroup State]
  [stateModule : Module K State]
  [stateFinite : FiniteDimensional K State]
  dynamics : State →ₗ[K] State
  input : U →ₗ[K] State
  output : State →ₗ[K] Y

attribute [instance] FiniteLinearRealization.stateAddCommGroup
attribute [instance] FiniteLinearRealization.stateModule
attribute [instance] FiniteLinearRealization.stateFinite

namespace FiniteLinearRealization

/-- The complete input-output behavior of a bundled realization. -/
def behavior
    {K U Y : Type u} [Field K]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (system : FiniteLinearRealization K U Y) : Nat → (U →ₗ[K] Y) :=
  fun k => markovParameter system.dynamics system.input system.output k

/-- The finite state dimension of a bundled realization. -/
def stateDimension
    {K U Y : Type u} [Field K]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (system : FiniteLinearRealization K U Y) : Nat :=
  finrank K system.State

end FiniteLinearRealization

/-- A system written as a bundled finite-dimensional realization. -/
def realizationOfMaps
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    FiniteLinearRealization K U Y where
  State := V
  dynamics := A
  input := B
  output := C

/-- The named quotient carrier together with `A_min`, `B_min`, and `C_min`. -/
def minimalRealization
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    FiniteLinearRealization K U Y where
  State := MinimalStateSpace A B C
  dynamics := minimalDynamics A B C
  input := minimalInput A B C
  output := minimalOutput A B C

/-- All finite state dimensions that realize the same complete Markov behavior. -/
def sameBehaviorDimensions
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) : Set Nat :=
  {dimension | ∃ system : FiniteLinearRealization K U Y,
    system.behavior = (fun k => markovParameter A B C k) ∧
      system.stateDimension = dimension}

/-- Raw state dimension is a behavior invariant at `target` when any two
finite-dimensional presentations of `target` have equal state dimension. -/
def StateDimensionInvariantAt
    {K U Y : Type u} [Field K]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (target : Nat → (U →ₗ[K] Y)) : Prop :=
  ∀ first second : FiniteLinearRealization K U Y,
    first.behavior = target → second.behavior = target →
      first.stateDimension = second.stateDimension

private theorem hankelRank_le_realizationDimension
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (system : FiniteLinearRealization K U Y)
    (sameBehavior : system.behavior = fun k => markovParameter A B C k)
    (rows columns : Nat) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
      system.stateDimension := by
  have hankelEquality :
      finiteHankel system.dynamics system.input system.output rows columns =
        finiteHankel A B C rows columns := by
    apply LinearMap.ext
    intro input
    funext row
    simp only [finiteHankel, LinearMap.pi_apply, LinearMap.lsum_apply,
      LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro column _
    exact LinearMap.congr_fun (congrFun sameBehavior _) _
  rw [← hankelEquality,
    finiteHankel_eq_observability_comp_controllability,
    LinearMap.range_comp]
  exact
    (Submodule.finrank_map_le
      (finiteObservability system.dynamics system.output rows)
      (LinearMap.range
        (finiteControllability system.dynamics system.input columns))).trans
      (LinearMap.range
        (finiteControllability system.dynamics system.input columns)).finrank_le

private theorem quotient_finrank_eq_hankelRank
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : Nat)
    (rowsLarge : finrank K V ≤ rows)
    (columnsLarge : finrank K V ≤ columns) :
    finrank K (MinimalStateSpace A B C) =
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) := by
  let reachable := reachableSubspace A B
  let invisible := eventualKernel C A
  let residual : Submodule K reachable := invisible.comap reachable.subtype
  change finrank K (reachable ⧸ residual) =
    finrank K (LinearMap.range (finiteHankel A B C rows columns))
  have residualFinrank :
      finrank K residual =
        finrank K (reachable ⊓ invisible : Submodule K V) := by
    calc
      finrank K residual = finrank K (residual.map reachable.subtype) := by
        symm
        exact Submodule.finrank_map_subtype_eq reachable residual
      _ = finrank K (reachable ⊓ invisible : Submodule K V) := by
        change
          finrank K
              ((invisible.comap reachable.subtype).map reachable.subtype) =
            finrank K (reachable ⊓ invisible : Submodule K V)
        rw [Submodule.map_comap_subtype]
  rw [Submodule.finrank_quotient, residualFinrank]
  simpa only [reachable, invisible] using
    (hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim
      A B C rows columns rowsLarge columnsLarge).symm

private theorem padded_iterate_input
    {K V U : Type u} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (k : Nat) (input : U) :
    (A.prodMap (0 : K →ₗ[K] K) ^ k)
        (B.prod (0 : U →ₗ[K] K) input) = ((A ^ k) (B input), 0) := by
  induction k with
  | zero => simp
  | succ k inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]
      simp only [LinearMap.prodMap_apply, map_zero]
      rw [pow_succ', Module.End.mul_apply]

private theorem padded_markovParameter_eq
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) (k : Nat) :
    markovParameter (A.prodMap (0 : K →ₗ[K] K))
        (B.prod (0 : U →ₗ[K] K))
        (C.coprod (0 : K →ₗ[K] Y)) k = markovParameter A B C k := by
  ext input
  simp only [markovParameter, LinearMap.comp_apply]
  rw [padded_iterate_input A B k input]
  simp only [LinearMap.coprod_apply, map_zero, add_zero]

/-- A concrete same-behavior presentation with one redundant state direction. -/
def paddedRealization
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    FiniteLinearRealization K U Y where
  State := V × K
  dynamics := A.prodMap (0 : K →ₗ[K] K)
  input := B.prod (0 : U →ₗ[K] K)
  output := C.coprod (0 : K →ₗ[K] Y)

/-- The named padded realization preserves the complete behavior and adds
exactly one redundant state dimension. -/
theorem paddedRealization_certificate
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    (paddedRealization A B C).behavior =
        (fun k => markovParameter A B C k) ∧
      (paddedRealization A B C).stateDimension = finrank K V + 1 := by
  constructor
  · funext k
    exact padded_markovParameter_eq A B C k
  · change finrank K (V × K) = finrank K V + 1
    rw [Module.finrank_prod, Module.finrank_self]

private theorem stateDimension_not_invariant
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    ¬ StateDimensionInvariantAt (fun k => markovParameter A B C k) := by
  intro invariant
  have paddingCertificate := paddedRealization_certificate A B C
  have dimensionEquality := invariant
    (realizationOfMaps A B C) (paddedRealization A B C) rfl
      paddingCertificate.1
  change finrank K V = (paddedRealization A B C).stateDimension at dimensionEquality
  rw [paddingCertificate.2] at dimensionEquality
  omega

/-- Corollary 244.1, source lines 19958--19970. The four public leaves are:
(A1) every finite-dimensional same-behavior realization has dimension at least
the stable Hankel rank; (A2) the named quotient realization has the same full
Markov behavior and attains that rank; (A3) raw state dimension is not a
behavior invariant, witnessed by one-dimensional padding; and (A4) the
minimum of all same-behavior realization dimensions is the Hankel rank. -/
theorem hankel_rank_lower_bound_and_quotient_attainment
    {K V V' U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (A' : V' →ₗ[K] V') (B' : U →ₗ[K] V') (C' : V' →ₗ[K] Y)
    (sameBehavior : ∀ k : Nat,
      markovParameter A' B' C' k = markovParameter A B C k)
    (rows columns : Nat)
    (rowsLarge : finrank K V ≤ rows)
    (columnsLarge : finrank K V ≤ columns) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
        finrank K V' ∧
      ((fun k => markovParameter (minimalDynamics A B C) (minimalInput A B C)
          (minimalOutput A B C) k),
        finrank K (MinimalStateSpace A B C)) =
        ((fun k => markovParameter A B C k),
          finrank K (LinearMap.range (finiteHankel A B C rows columns))) ∧
      ¬ StateDimensionInvariantAt (fun k => markovParameter A B C k) ∧
      sInf (sameBehaviorDimensions A B C) =
        finrank K (LinearMap.range (finiteHankel A B C rows columns)) := by
  have lowerBound :
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
        finrank K V' := by
    have hankelEquality :
        finiteHankel A' B' C' rows columns =
          finiteHankel A B C rows columns := by
      apply LinearMap.ext
      intro input
      funext row
      simp only [finiteHankel, LinearMap.pi_apply, LinearMap.lsum_apply,
        LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro column _
      rw [sameBehavior]
    rw [← hankelEquality,
      finiteHankel_eq_observability_comp_controllability,
      LinearMap.range_comp]
    exact
      (Submodule.finrank_map_le
        (finiteObservability A' C' rows)
        (LinearMap.range (finiteControllability A' B' columns))).trans
        (LinearMap.range (finiteControllability A' B' columns)).finrank_le
  have attainment :
      finrank K (MinimalStateSpace A B C) =
        finrank K (LinearMap.range (finiteHankel A B C rows columns)) :=
    quotient_finrank_eq_hankelRank A B C rows columns rowsLarge columnsLarge
  have quotientSignature :
      ((fun k => markovParameter (minimalDynamics A B C) (minimalInput A B C)
          (minimalOutput A B C) k),
        finrank K (MinimalStateSpace A B C)) =
        ((fun k => markovParameter A B C k),
          finrank K (LinearMap.range (finiteHankel A B C rows columns))) := by
    apply Prod.ext
    · funext k
      exact minimal_markovParameter_eq A B C k
    · exact attainment
  have quotientDimensionMember :
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) ∈
        sameBehaviorDimensions A B C := by
    refine ⟨minimalRealization A B C, ?_, ?_⟩
    · funext k
      exact minimal_markovParameter_eq A B C k
    · change finrank K (MinimalStateSpace A B C) =
        finrank K (LinearMap.range (finiteHankel A B C rows columns))
      exact attainment
  have dimensionsNonempty : (sameBehaviorDimensions A B C).Nonempty :=
    ⟨_, quotientDimensionMember⟩
  have infimumLowerBound :
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
        sInf (sameBehaviorDimensions A B C) := by
    rcases Nat.sInf_mem dimensionsNonempty with
      ⟨system, systemBehavior, systemDimension⟩
    rw [← systemDimension]
    exact hankelRank_le_realizationDimension A B C system systemBehavior
      rows columns
  have minimumEquality :
      sInf (sameBehaviorDimensions A B C) =
        finrank K (LinearMap.range (finiteHankel A B C rows columns)) :=
    le_antisymm (Nat.sInf_le quotientDimensionMember) infimumLowerBound
  exact ⟨lowerBound, quotientSignature,
    stateDimension_not_invariant A B C, minimumEquality⟩

#print axioms hankel_rank_lower_bound_and_quotient_attainment

/- Reverse probe for CAS-A1: the first public leaf recovers the lower bound. -/
example
    {K V V' U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V']
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : Nat)
    (publicConclusion :
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
          finrank K V' ∧
        True ∧ True ∧ True) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) ≤
      finrank K V' :=
  publicConclusion.1

/- Reverse probe for CAS-A2: the quotient signature leaf yields both complete
Markov behavior and attained state dimension. -/
example
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : Nat)
    (attainment :
      ((fun k => markovParameter (minimalDynamics A B C) (minimalInput A B C)
          (minimalOutput A B C) k),
        finrank K (MinimalStateSpace A B C)) =
        ((fun k => markovParameter A B C k),
          finrank K (LinearMap.range (finiteHankel A B C rows columns)))) :
    (∀ k, markovParameter (minimalDynamics A B C) (minimalInput A B C)
          (minimalOutput A B C) k = markovParameter A B C k) ∧
      finrank K (MinimalStateSpace A B C) =
        finrank K (LinearMap.range (finiteHankel A B C rows columns)) := by
  constructor
  · intro k
    exact congrFun (congrArg Prod.fst attainment) k
  · exact congrArg Prod.snd attainment

/- Reverse probe for CAS-A4: the fourth public leaf is the explicit minimum
state-dimension invariant, not merely one quotient finrank equality. -/
example
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : Nat)
    (minimumLeaf : sInf (sameBehaviorDimensions A B C) =
      finrank K (LinearMap.range (finiteHankel A B C rows columns))) :
    sInf (sameBehaviorDimensions A B C) =
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) :=
  minimumLeaf

/- Padding probe for CAS-A3: the named redundant-state system has the same
complete behavior while its raw state dimension is larger by one. -/
example
    {K V U Y : Type u} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    (paddedRealization A B C).behavior =
        (fun k => markovParameter A B C k) ∧
      (paddedRealization A B C).stateDimension = finrank K V + 1 :=
  paddedRealization_certificate A B C

/- Trivialization probe for CAS-A1: a zero-dimensional state cannot reproduce
the nonzero Markov behavior of the one-dimensional identity input/readout
system, so same behavior rules out the zero-state collapse. -/
example :
    ¬ ∀ k : Nat,
      markovParameter
          (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin 0 → ℚ))
          (0 : ℚ →ₗ[ℚ] (Fin 0 → ℚ))
          (0 : (Fin 0 → ℚ) →ₗ[ℚ] ℚ) k =
        markovParameter
          (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id LinearMap.id k := by
  intro sameBehavior
  have atZero := congrArg (fun map : ℚ →ₗ[ℚ] ℚ => map 1) (sameBehavior 0)
  norm_num [markovParameter] at atZero

end D5.S3.Observer.Hankel.HankelMinimalStateDimension
