/- GID: D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-map transfer decomposes into transient and periodic-core restrictions. -/

/- Library-search audit trail (2026-08-22):
   * Repository search found the canonical `transferOperator`, `PeriodicCore`, and stable-image
     theorem used below, but no theorem packaging this full decomposition.
   * Pinned Mathlib supplies `range_lmapDomain`, `isCompl_iff_disjoint`,
     `finrank_range_add_finrank_ker`, `injective_iff_surjective`,
     `iterate_injective`, `linearEquivFunOnFinite`, `linearMap`, and
     `bijOn_periodicPts`; each hit is applied directly.
   * Searches for an exact kernel/range, nilpotent, and periodic-basis decomposition theorem
     found no equal or stronger declaration in either the repository or pinned Mathlib.
-/

import D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
import D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore
import D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics
import Mathlib.LinearAlgebra.Finsupp.Pi

namespace D5.S3.ObserverMemory.FunctionalGraphs.FiniteFunctionalGraphFittingDecomposition

open D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
open D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore
open D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The transient carrier obtained by aggregating coefficients after the finite stabilization
exponent. This is constructed directly from the iterated source update. -/
def transientSubspace {Y : Type*} (tau : Y -> Y) (n : Nat) :
    Submodule ℂ (Y →₀ ℂ) :=
  LinearMap.ker (Finsupp.lmapDomain ℂ ℂ (tau^[n]))

/-- The span of the canonical basis vectors indexed by periodic states. -/
def periodicCoreSubspace {Y : Type*} (tau : Y -> Y) :
    Submodule ℂ (Y →₀ ℂ) :=
  Submodule.span ℂ
    (Set.range fun point : PeriodicCore tau => Finsupp.single point.1 1)

/-- The permutation induced by the update on its periodic core. -/
noncomputable def periodicCorePermutation {Y : Type*} (tau : Y -> Y) :
    Equiv.Perm (PeriodicCore tau) :=
  Equiv.ofBijective
    (fun point : PeriodicCore tau =>
      ⟨tau point.1, (Function.bijOn_periodicPts tau).mapsTo point.2⟩)
    (by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact (Function.bijOn_periodicPts tau).injOn a.2 b.2
          (congrArg Subtype.val hab)
      · intro b
        obtain ⟨a, ha, hab⟩ := (Function.bijOn_periodicPts tau).surjOn b.2
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩)

/-- The periodic basis vector inside the periodic-core span. -/
def periodicBasisVector {Y : Type*} (tau : Y -> Y) (point : PeriodicCore tau) :
    periodicCoreSubspace tau :=
  ⟨Finsupp.single point.1 1, Submodule.subset_span ⟨point, rfl⟩⟩

private theorem transfer_operator_pow {Y : Type*} (tau : Y -> Y) (n : Nat) :
    transferOperator tau ^ n = Finsupp.lmapDomain ℂ ℂ (tau^[n]) := by
  induction n with
  | zero => simp [transferOperator, Module.End.one_eq_id]
  | succ n ih =>
      rw [pow_succ, ih, Module.End.mul_eq_comp]
      unfold transferOperator
      rw [<- Finsupp.lmapDomain_comp, Function.iterate_succ]

private theorem transfer_operator_single {Y : Type*} (tau : Y -> Y)
    (y : Y) (c : ℂ) :
    transferOperator tau (Finsupp.single y c) = Finsupp.single (tau y) c := by
  rw [transferOperator, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private theorem range_transfer_eq_periodic_core
    {Y : Type*} (tau : Y -> Y) {n : Nat}
    (hstable : Set.range (tau^[n]) = Function.periodicPts tau) :
    LinearMap.range (transferOperator tau ^ n) = periodicCoreSubspace tau := by
  classical
  rw [transfer_operator_pow, Finsupp.range_lmapDomain, periodicCoreSubspace]
  apply congrArg (Submodule.span ℂ)
  ext vector
  constructor
  · rintro ⟨y, rfl⟩
    have hperiodic : (tau^[n]) y ∈ Function.periodicPts tau := by
      rw [<- hstable]
      exact ⟨y, rfl⟩
    exact ⟨⟨(tau^[n]) y, hperiodic⟩, rfl⟩
  · rintro ⟨point, rfl⟩
    have hpoint : point.1 ∈ Set.range (tau^[n]) := by
      rw [hstable]
      exact point.property
    obtain ⟨y, hy⟩ := hpoint
    exact ⟨y, by
      simpa only using congrArg (fun z => Finsupp.single z (1 : ℂ)) hy⟩

private theorem transient_subspace_eq_kernel {Y : Type*}
    (tau : Y -> Y) (n : Nat) :
    transientSubspace tau n = LinearMap.ker (transferOperator tau ^ n) := by
  rw [transientSubspace, transfer_operator_pow]

private theorem transfer_maps_transient {Y : Type*}
    (tau : Y -> Y) (n : Nat) :
    Set.MapsTo (transferOperator tau) (transientSubspace tau n)
      (transientSubspace tau n) := by
  rw [transient_subspace_eq_kernel]
  intro vector hvector
  change (transferOperator tau ^ n) vector = 0 at hvector
  change (transferOperator tau ^ n) (transferOperator tau vector) = 0
  calc
    (transferOperator tau ^ n) (transferOperator tau vector) =
        (transferOperator tau)^[n + 1] vector := by
          rw [Module.End.pow_apply, Function.iterate_succ_apply]
    _ = transferOperator tau
          ((transferOperator tau)^[n] vector) := by
          rw [Function.iterate_succ_apply']
    _ = 0 := by rw [<- Module.End.pow_apply, hvector, map_zero]

/-- The source transfer restricted to the independently constructed transient carrier. -/
noncomputable def transientTransfer {Y : Type*} (tau : Y -> Y) (n : Nat) :
    Module.End ℂ (transientSubspace tau n) :=
  (transferOperator tau).restrict (fun x hx => transfer_maps_transient tau n hx)

private theorem transfer_maps_periodic_core {Y : Type*}
    (tau : Y -> Y) :
    Set.MapsTo (transferOperator tau) (periodicCoreSubspace tau)
      (periodicCoreSubspace tau) := by
  intro vector hvector
  refine Submodule.span_induction
    (p := fun v _ => transferOperator tau v ∈ periodicCoreSubspace tau)
    ?_ ?_ ?_ ?_ hvector
  · intro vector hgenerator
    obtain ⟨point, rfl⟩ := hgenerator
    rw [transfer_operator_single]
    apply Submodule.subset_span
    exact ⟨periodicCorePermutation tau point, rfl⟩
  · exact (periodicCoreSubspace tau).zero_mem
  · intro x y _ _ hx hy
    rw [map_add]
    exact (periodicCoreSubspace tau).add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact (periodicCoreSubspace tau).smul_mem c hx

/-- The source transfer restricted to the periodic-core span. -/
noncomputable def periodicCoreTransfer {Y : Type*} (tau : Y -> Y) :
    Module.End ℂ (periodicCoreSubspace tau) :=
  (transferOperator tau).restrict (fun x hx => transfer_maps_periodic_core tau hx)

private theorem transient_transfer_nilpotent {Y : Type*}
    (tau : Y -> Y) (n : Nat) : IsNilpotent (transientTransfer tau n) := by
  refine ⟨n, ?_⟩
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  rw [transientTransfer,
    Module.End.pow_restrict n (fun x hx => transfer_maps_transient tau n hx)]
  have hvector := vector.property
  change Finsupp.lmapDomain ℂ ℂ (tau^[n]) vector.1 = 0 at hvector
  rw [<- transfer_operator_pow] at hvector
  exact hvector

private theorem periodic_core_transfer_bijective {Y : Type*} [Finite Y]
    (tau : Y -> Y) : Function.Bijective (periodicCoreTransfer tau) := by
  letI := Fintype.ofFinite Y
  have hsurjective : Function.Surjective (periodicCoreTransfer tau) := by
    intro vector
    have hstableCard := (iterate_range_card_antitone_and_stable tau).2
      (Fintype.card Y) (le_refl _)
    have hstableSucc := (iterate_range_card_antitone_and_stable tau).2
      (Fintype.card Y + 1) (by omega)
    have hrangeSucc : vector.1 ∈
        LinearMap.range (transferOperator tau ^ (Fintype.card Y + 1)) := by
      rw [range_transfer_eq_periodic_core tau hstableSucc]
      exact vector.property
    obtain ⟨source, hsource⟩ := hrangeSucc
    let preimageValue := (transferOperator tau ^ Fintype.card Y) source
    have hpreimage : preimageValue ∈ periodicCoreSubspace tau := by
      rw [<- range_transfer_eq_periodic_core tau hstableCard]
      exact ⟨source, rfl⟩
    refine ⟨⟨preimageValue, hpreimage⟩, ?_⟩
    apply Subtype.ext
    change transferOperator tau preimageValue = vector.1
    rw [<- hsource]
    simp only [preimageValue, pow_succ', Module.End.mul_apply]
  have hinjective : Function.Injective (periodicCoreTransfer tau) :=
    (LinearMap.injective_iff_surjective
      (K := ℂ) (V := periodicCoreSubspace tau)
      (f := periodicCoreTransfer tau)).mpr hsurjective
  exact ⟨hinjective, hsurjective⟩

private theorem periodic_core_transfer_pow_coe
    {Y : Type*} (tau : Y -> Y) (n : Nat)
    (vector : periodicCoreSubspace tau) :
    (((periodicCoreTransfer tau) ^ n) vector).1 =
      (transferOperator tau ^ n) vector.1 := by
  rw [periodicCoreTransfer,
    Module.End.pow_restrict n (fun x hx => transfer_maps_periodic_core tau hx)]
  rfl

private theorem fitting_at_stable_image
    {Y : Type*} [Finite Y] (tau : Y -> Y) {n : Nat}
    (hstable : Set.range (tau^[n]) = Function.periodicPts tau) :
    IsCompl (LinearMap.ker (transferOperator tau ^ n))
      (LinearMap.range (transferOperator tau ^ n)) := by
  have hrange := range_transfer_eq_periodic_core tau hstable
  rw [hrange]
  have hbijective := periodic_core_transfer_bijective tau
  have hdisjoint : Disjoint
      (LinearMap.ker (transferOperator tau ^ n))
      (periodicCoreSubspace tau) := by
    refine Submodule.disjoint_def.mpr ?_
    intro vector hkernel hcore
    have hpow :
        ((periodicCoreTransfer tau) ^ n) ⟨vector, hcore⟩ = 0 := by
      apply Subtype.ext
      rw [periodic_core_transfer_pow_coe]
      exact LinearMap.mem_ker.mp hkernel
    have hsubtype : (⟨vector, hcore⟩ : periodicCoreSubspace tau) = 0 :=
      (Module.End.iterate_injective hbijective.1 n) (by simpa using hpow)
    exact congrArg Subtype.val hsubtype
  have hrank :=
    (transferOperator tau ^ n).finrank_range_add_finrank_ker
  rw [hrange] at hrank
  have hdim : Module.finrank ℂ (Y →₀ ℂ) <=
      Module.finrank ℂ (LinearMap.ker (transferOperator tau ^ n)) +
        Module.finrank ℂ (periodicCoreSubspace tau) := by
    omega
  exact (Submodule.isCompl_iff_disjoint _ _ hdim).2 hdisjoint

private theorem periodic_core_transfer_basis_action
    {Y : Type*} (tau : Y -> Y) (point : PeriodicCore tau) :
    periodicCoreTransfer tau (periodicBasisVector tau point) =
      periodicBasisVector tau (periodicCorePermutation tau point) := by
  apply Subtype.ext
  change transferOperator tau (Finsupp.single point.1 1) =
    Finsupp.single (periodicCorePermutation tau point).1 1
  rw [transfer_operator_single]
  rfl

private theorem transfer_operator_function_bridge
    {Y : Type*} [Finite Y] (tau : Y -> Y) (vector : Y →₀ ℂ) :
    Finsupp.linearEquivFunOnFinite ℂ ℂ Y (transferOperator tau vector) =
      FunOnFinite.linearMap ℂ ℂ tau
        (Finsupp.linearEquivFunOnFinite ℂ ℂ Y vector) := by
  simp [FunOnFinite.linearMap, transferOperator]

/-- The transfer linearization of a finite self-map splits into its kernel and stable range.
The transient carrier is exactly that kernel and carries a nilpotent restriction. The stable
range is exactly the periodic-core span, where the restriction is bijective and acts on the
canonical periodic basis through the update-induced permutation. -/
theorem finite_functional_graph_fitting_decomposition
    {Y : Type*} [Finite Y] (tau : Y -> Y) (n : Nat)
    (hstable : Set.range (tau^[n]) = Function.periodicPts tau) :
    IsCompl
        (LinearMap.ker (transferOperator tau ^ n))
        (LinearMap.range (transferOperator tau ^ n)) /\
      transientSubspace tau n = LinearMap.ker (transferOperator tau ^ n) /\
      IsNilpotent (transientTransfer tau n) /\
      LinearMap.range (transferOperator tau ^ n) =
        periodicCoreSubspace tau /\
      Function.Bijective (periodicCoreTransfer tau) /\
      (forall point : PeriodicCore tau,
        periodicCoreTransfer tau (periodicBasisVector tau point) =
          periodicBasisVector tau (periodicCorePermutation tau point)) /\
      (forall vector : Y →₀ ℂ,
        Finsupp.linearEquivFunOnFinite ℂ ℂ Y (transferOperator tau vector) =
          FunOnFinite.linearMap ℂ ℂ tau
            (Finsupp.linearEquivFunOnFinite ℂ ℂ Y vector)) := by
  exact ⟨fitting_at_stable_image tau hstable,
    transient_subspace_eq_kernel tau n,
    transient_transfer_nilpotent tau n,
    range_transfer_eq_periodic_core tau hstable,
    periodic_core_transfer_bijective tau,
    periodic_core_transfer_basis_action tau,
    transfer_operator_function_bridge tau⟩

end

end D5.S3.ObserverMemory.FunctionalGraphs.FiniteFunctionalGraphFittingDecomposition
