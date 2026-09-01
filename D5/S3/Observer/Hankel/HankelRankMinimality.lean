/- GID: D5/S3/Observer/Hankel/HankelRankMinimality
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/HankelRankMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable finite Hankel rank equals reachable dimension modulo invisible reachability. -/

import D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * The imported D5 module owns `reachableSubspace`; its dependency
     `ZeroMemoryCriterion` owns `eventualKernel`. No D5 module owns the finite
     Markov, observability, controllability, or block-Hankel families below.
   * Pinned Mathlib supplies `LinearMap.pow_eq_aeval_mod_charpoly`,
     `Polynomial.aeval_eq_sum_range'`, `LinearMap.lsum`, `LinearMap.pi`,
     `LinearMap.range_comp`, `LinearMap.ker_domRestrict`, and
     `LinearMap.finrank_range_add_finrank_ker`. No packaged Hankel-rank theorem
     or finite control-system definition family was found. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.HankelRankMinimality

open D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
open D5.S3.Observer.LinearMemory.ZeroMemoryCriterion
open Module

/-- The Markov parameter `C A^k B` from source lines 19866--19872. -/
def markovParameter
    {K V U Y : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid U] [Module K U]
    [AddCommMonoid Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) (k : ℕ) :
    U →ₗ[K] Y :=
  C.comp ((A ^ k).comp B)

/-- The finite observability map from source lines 19887--19897. -/
def finiteObservability
    {K V Y : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid Y] [Module K Y]
    (A : V →ₗ[K] V) (C : V →ₗ[K] Y) (horizon : ℕ) :
    V →ₗ[K] (Fin horizon → Y) :=
  LinearMap.pi fun time : Fin horizon => C.comp (A ^ (time : ℕ))

/-- The finite controllability map from source lines 19900--19910. -/
def finiteControllability
    {K V U : Type*} [CommSemiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid U] [Module K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (horizon : ℕ) :
    (Fin horizon → U) →ₗ[K] V :=
  LinearMap.lsum K (fun _ : Fin horizon => U) K fun time =>
    (A ^ (time : ℕ)).comp B

/-- The block Hankel map with `(i,j)` block `C A^(i+j) B`, from source
lines 19874--19884. -/
def finiteHankel
    {K V U Y : Type*} [CommSemiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid U] [Module K U]
    [AddCommMonoid Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : ℕ) : (Fin columns → U) →ₗ[K] (Fin rows → Y) :=
  LinearMap.pi fun row : Fin rows =>
    LinearMap.lsum K (fun _ : Fin columns => U) K fun column =>
      markovParameter A B C ((row : ℕ) + (column : ℕ))

/-- The source factorization `H_(r,s) = O_r C_s`, lines 19913--19918. -/
theorem finiteHankel_eq_observability_comp_controllability
    {K V U Y : Type*} [CommSemiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid U] [Module K U]
    [AddCommMonoid Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : ℕ) :
    finiteHankel A B C rows columns =
      (finiteObservability A C rows).comp
        (finiteControllability A B columns) := by
  ext input row
  simp only [finiteHankel, finiteObservability, finiteControllability,
    markovParameter, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.proj_apply]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro column _
  rw [pow_add, Module.End.mul_apply]

private theorem finiteObservability_ker_eq_eventualKernel
    {K V Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (C : V →ₗ[K] Y) (horizon : ℕ)
    (large : finrank K V ≤ horizon) :
    LinearMap.ker (finiteObservability A C horizon) = eventualKernel C A := by
  let n := finrank K V
  apply le_antisymm
  · intro state stateInKernel
    change ∀ exponent : ℕ, (A^[exponent]) state ∈ LinearMap.ker C
    by_cases dimensionZero : n = 0
    · let subsingletonV : Subsingleton V :=
        Module.finrank_zero_iff.mp dimensionZero
      intro exponent
      rw [LinearMap.mem_ker]
      have iterateZero : (A^[exponent]) state = 0 :=
        @Subsingleton.elim V subsingletonV _ _
      rw [iterateZero, map_zero]
    · have coordinateZero :
          ∀ time : Fin horizon, C ((A ^ (time : ℕ)) state) = 0 := by
        intro time
        have mapZero := (LinearMap.mem_ker.mp stateInKernel)
        have atTime := congrFun mapZero time
        change C ((A ^ (time : ℕ)) state) = 0 at atTime
        exact atTime
      intro exponent
      rw [LinearMap.mem_ker, ← Module.End.pow_apply]
      let reduced := Polynomial.X ^ exponent %ₘ A.charpoly
      have charpolyNotOne : A.charpoly ≠ 1 := by
        intro charpolyOne
        have degreeEquality := congrArg Polynomial.natDegree charpolyOne
        rw [A.charpoly_natDegree, Polynomial.natDegree_one] at degreeEquality
        exact dimensionZero degreeEquality
      have reducedDegree : reduced.natDegree < n := by
        simpa only [reduced, n, A.charpoly_natDegree] using
          Polynomial.natDegree_modByMonic_lt
            (Polynomial.X ^ exponent) A.charpoly_monic charpolyNotOne
      have powerReduction :
          A ^ exponent =
            ∑ i ∈ Finset.range n, reduced.coeff i • A ^ i := by
        calc
          A ^ exponent = Polynomial.aeval A reduced :=
            A.pow_eq_aeval_mod_charpoly exponent
          _ = ∑ i ∈ Finset.range n, reduced.coeff i • A ^ i :=
            Polynomial.aeval_eq_sum_range' reducedDegree A
      rw [powerReduction]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        map_sum, map_smul]
      apply Finset.sum_eq_zero
      intro i iInRange
      have iLtHorizon : i < horizon :=
        (Finset.mem_range.mp iInRange).trans_le large
      rw [coordinateZero ⟨i, iLtHorizon⟩, smul_zero]
  · intro state stateEventuallyInvisible
    rw [LinearMap.mem_ker]
    funext time
    change C ((A ^ (time : ℕ)) state) = 0
    have invisibleAtTime := stateEventuallyInvisible (time : ℕ)
    rw [LinearMap.mem_ker] at invisibleAtTime
    simpa only [Module.End.pow_apply] using invisibleAtTime

private theorem finiteControllability_range_eq_reachableSubspace
    {K V U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (horizon : ℕ)
    (large : finrank K V ≤ horizon) :
    LinearMap.range (finiteControllability A B horizon) =
      reachableSubspace A B := by
  let n := finrank K V
  apply le_antisymm
  · rintro state ⟨input, rfl⟩
    rw [finiteControllability, LinearMap.lsum_apply]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    apply Submodule.sum_mem
    intro time _
    exact Submodule.subset_span ⟨(time : ℕ), input time, rfl⟩
  · rw [reachableSubspace]
    apply Submodule.span_le.2
    rintro state ⟨exponent, input, rfl⟩
    by_cases dimensionZero : n = 0
    · let subsingletonV : Subsingleton V :=
        Module.finrank_zero_iff.mp dimensionZero
      have stateZero : (A ^ exponent) (B input) = 0 :=
        @Subsingleton.elim V subsingletonV _ _
      rw [stateZero]
      exact Submodule.zero_mem _
    · have finiteGeneratorInRange (i : ℕ) (iLt : i < n) :
          (A ^ i) (B input) ∈
            LinearMap.range (finiteControllability A B horizon) := by
        let time : Fin horizon := ⟨i, iLt.trans_le large⟩
        refine ⟨Pi.single time input, ?_⟩
        rw [finiteControllability, LinearMap.lsum_piSingle]
        rfl
      let reduced := Polynomial.X ^ exponent %ₘ A.charpoly
      have charpolyNotOne : A.charpoly ≠ 1 := by
        intro charpolyOne
        have degreeEquality := congrArg Polynomial.natDegree charpolyOne
        rw [A.charpoly_natDegree, Polynomial.natDegree_one] at degreeEquality
        exact dimensionZero degreeEquality
      have reducedDegree : reduced.natDegree < n := by
        simpa only [reduced, n, A.charpoly_natDegree] using
          Polynomial.natDegree_modByMonic_lt
            (Polynomial.X ^ exponent) A.charpoly_monic charpolyNotOne
      have powerReduction :
          A ^ exponent =
            ∑ i ∈ Finset.range n, reduced.coeff i • A ^ i := by
        calc
          A ^ exponent = Polynomial.aeval A reduced :=
            A.pow_eq_aeval_mod_charpoly exponent
          _ = ∑ i ∈ Finset.range n, reduced.coeff i • A ^ i :=
            Polynomial.aeval_eq_sum_range' reducedDegree A
      rw [powerReduction]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      apply Submodule.sum_mem
      intro i iInRange
      exact Submodule.smul_mem _ _
        (finiteGeneratorInRange i (Finset.mem_range.mp iInRange))

/-- For every finite-dimensional discrete linear system, once both horizons
reach the state-space finrank, the block Hankel rank is the reachable dimension
minus the dimension of the reachable directions invisible at all future times.
This is theorem 244.1 at source lines 19921--19956. -/
theorem hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : ℕ)
    (rowsLarge : finrank K V ≤ rows)
    (columnsLarge : finrank K V ≤ columns) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) =
      finrank K (reachableSubspace A B) -
        finrank K
          ((reachableSubspace A B) ⊓ eventualKernel C A : Submodule K V) := by
  let reachable := reachableSubspace A B
  let unobservable := eventualKernel C A
  let observability := finiteObservability A C rows
  have controllabilityRange :
      LinearMap.range (finiteControllability A B columns) = reachable := by
    simpa only [reachable] using
      finiteControllability_range_eq_reachableSubspace
        A B columns columnsLarge
  have observabilityKernel : LinearMap.ker observability = unobservable := by
    simpa only [observability, unobservable] using
      finiteObservability_ker_eq_eventualKernel A C rows rowsLarge
  have hankelRange :
      LinearMap.range (finiteHankel A B C rows columns) =
        LinearMap.range (observability.domRestrict reachable) := by
    rw [finiteHankel_eq_observability_comp_controllability,
      LinearMap.range_comp, controllabilityRange,
      LinearMap.range_domRestrict]
  have restrictedKernel :
      LinearMap.ker (observability.domRestrict reachable) =
        unobservable.comap reachable.subtype := by
    rw [LinearMap.ker_domRestrict, observabilityKernel]
  have restrictedKernelFinrank :
      finrank K (LinearMap.ker (observability.domRestrict reachable)) =
        finrank K (reachable ⊓ unobservable : Submodule K V) := by
    rw [restrictedKernel]
    calc
      finrank K (unobservable.comap reachable.subtype) =
          finrank K ((unobservable.comap reachable.subtype).map
            reachable.subtype) := by
        symm
        exact Submodule.finrank_map_subtype_eq reachable
          (unobservable.comap reachable.subtype)
      _ = finrank K (reachable ⊓ unobservable : Submodule K V) := by
        rw [Submodule.map_comap_subtype]
  have rankNullity :=
    (observability.domRestrict reachable).finrank_range_add_finrank_ker
  rw [restrictedKernelFinrank] at rankNullity
  rw [hankelRange]
  simpa only [reachable, unobservable] using Nat.eq_sub_of_add_eq rankNullity

#print axioms hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim

/- Reverse probe for CAS-A1: the public equality recovers the dimension balance
after adding back the reachable directions that are forever invisible. -/
example
    {K V U Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y)
    (rows columns : ℕ)
    (rankFormula :
      finrank K (LinearMap.range (finiteHankel A B C rows columns)) =
        finrank K (reachableSubspace A B) -
          finrank K
            ((reachableSubspace A B) ⊓ eventualKernel C A : Submodule K V)) :
    finrank K (LinearMap.range (finiteHankel A B C rows columns)) +
        finrank K
          ((reachableSubspace A B) ⊓ eventualKernel C A : Submodule K V) =
      finrank K (reachableSubspace A B) := by
  have invisibleLeReachable :
      finrank K
          ((reachableSubspace A B) ⊓ eventualKernel C A : Submodule K V) ≤
        finrank K (reachableSubspace A B) :=
    Submodule.finrank_mono inf_le_left
  omega

/- Carrier-replacement probe for CAS-A1: in the one-dimensional system with
`A = 0` and identity input/readout, the reachable space is full and the
all-future invisible space is zero. An arbitrary zero map therefore cannot be
substituted for the source-defined Hankel map. -/
example :
    finrank ℚ
        (LinearMap.range
          (0 : (Fin 1 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ))) ≠
      finrank ℚ
          (reachableSubspace (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id) -
        finrank ℚ
          ((reachableSubspace (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id) ⊓
            eventualKernel LinearMap.id (0 : ℚ →ₗ[ℚ] ℚ) :
              Submodule ℚ ℚ) := by
  have reachableFull :
      reachableSubspace (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id = ⊤ := by
    apply eq_top_iff.mpr
    intro state _
    exact Submodule.subset_span ⟨0, state, by simp⟩
  have invisibleZero :
      eventualKernel LinearMap.id (0 : ℚ →ₗ[ℚ] ℚ) = ⊥ := by
    apply le_antisymm
    · simpa using eventualKernel_le_ker
        (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (0 : ℚ →ₗ[ℚ] ℚ)
    · exact bot_le
  rw [reachableFull, invisibleZero, LinearMap.range_zero, inf_bot_eq,
    finrank_bot]
  norm_num

end D5.S3.Observer.Hankel.HankelRankMinimality
