/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCohomologyBPZNondegenerate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCohomologyBPZNondegenerate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas]
   utility: none
   digest: Vanishing of both radicals of native relative BRST cohomology BPZ. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTShellBPZ
import Batteries.Tactic.OpenPrivate

/-! Perfect BPZ pairings on opposite finite shells identify cycle annihilators
with differential images. Finite momentum support lifts these shell boundaries
to boundaries of the native relative complex. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCohomologyBPZNondegenerate

open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open OriginalOrbifoldCriticalMatter (Matter State Q hyperbolicData)
open OriginalOrbifoldBRSTDescent (relativeStates relativeDifferential relativeDifferential_square
  relativeCycles relativeBoundaries)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTBPZWard (betaRelTotal)
open OriginalOrbifoldBRSTPhysicalPairing (cohomologyBPZ cohomologyBPZ_mk)
open OriginalOrbifoldBRSTShellBPZ (shellBPZ shellBPZ_isPerfPair shellBPZ_left_cycle_annihilator)
open OriginalOrbifoldRelativeMassShell (fixedMomentum relativeMassShell differential)
open LatticeGeneratingFieldLocality (Charge)

open private Q_parity from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private momentumPart momentumPart_mem cyclePart momentumSupport sum_cyclePart from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
open private betaRelTotal_eq_zero_of_momentum from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalPairing
open private shellInclusion shellState shellParity shellParity_square shellBPZ_ward from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTShellBPZ

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

private def shellParityMap (p : UCharge) : Module.End ℂ (relativeMassShell p) :=
  parity.restrict (fun x hx => (shellParity p ⟨x, hx⟩).property)

private theorem shellParityMap_apply (p : UCharge) (x : relativeMassShell p) :
    shellParityMap p x = shellParity p x :=
  Subtype.ext rfl

private theorem shellDifferential_parity (p : UCharge) (x : relativeMassShell p) :
    differential p (shellParity p x) = -shellParity p (differential p x) := by
  apply Subtype.ext
  change Q (parity (x : State)) = -parity (Q (x : State))
  exact Q_parity (x : State)

private theorem shellBPZ_right_differential (p : UCharge) (x : relativeMassShell p)
    (y : relativeMassShell (-p)) :
    shellBPZ p x (differential (-p) y) = shellBPZ p (differential p (shellParity p x)) y := by
  rw [shellBPZ_ward, shellParity_square]

/-- The right annihilator of native shell cycles is the native boundary image in the opposite shell. -/
theorem shellBPZ_right_cycle_annihilator (p : UCharge) :
    (LinearMap.ker (differential p)).dualAnnihilator.comap (shellBPZ p).flip =
      LinearMap.range (differential (-p)) := by
  letI : (shellBPZ p).IsPerfPair := shellBPZ_isPerfPair p
  have perfectRight := LinearMap.IsPerfPair.bijective_right (shellBPZ p)
  apply Submodule.ext
  intro y
  change (shellBPZ p).flip y ∈ (LinearMap.ker (differential p)).dualAnnihilator ↔
    y ∈ LinearMap.range (differential (-p))
  constructor
  · intro hy
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hy
    obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp hy
    obtain ⟨u, hu⟩ := perfectRight.surjective (-(ψ.comp (shellParityMap p)))
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    apply perfectRight.injective
    apply LinearMap.ext
    intro x
    change shellBPZ p x (differential (-p) u) = shellBPZ p x y
    calc
      shellBPZ p x (differential (-p) u) =
          shellBPZ p (differential p (shellParity p x)) u := shellBPZ_right_differential p x u
      _ = -ψ (shellParity p (differential p (shellParity p x))) := by
        simpa only [LinearMap.flip_apply, LinearMap.neg_apply, LinearMap.comp_apply,
          shellParityMap_apply] using LinearMap.congr_fun hu (differential p (shellParity p x))
      _ = ψ (differential p x) := by
        rw [shellDifferential_parity]
        change -ψ (shellParityMap p (-shellParity p (differential p x))) = _
        rw [map_neg, shellParityMap_apply, shellParity_square, map_neg, neg_neg]
      _ = shellBPZ p x y := by
        simpa only [LinearMap.dualMap_apply, LinearMap.flip_apply] using
          LinearMap.congr_fun hψ x
  · intro hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hPx : differential p (shellParity p x) = 0 := by
      rw [shellDifferential_parity, LinearMap.mem_ker.mp hx]
      change -(shellParityMap p 0) = 0
      rw [map_zero, neg_zero]
    change shellBPZ p x (differential (-p) u) = 0
    rw [shellBPZ_right_differential, hPx, map_zero, LinearMap.zero_apply]

private def shellCycleToRelative (p : UCharge) (x : relativeMassShell p)
    (hx : x ∈ LinearMap.ker (differential p)) : relativeCycles := by
  refine ⟨shellInclusion p x, LinearMap.mem_ker.mpr ?_⟩
  apply relativeStates.subtype_injective
  change Q (x : State) = 0
  exact congrArg (fun v : relativeMassShell p => (v : State)) (LinearMap.mem_ker.mp hx)

private theorem cyclePart_mem_fixedMomentum (p : UCharge) (z : relativeCycles) :
    ((cyclePart p z).1 : State) ∈ fixedMomentum p := by
  change momentumPart p (z.1 : State) ∈ fixedMomentum p
  exact momentumPart_mem p (z.1 : State)

private def cyclePartInShell (p : UCharge) (z : relativeCycles) : relativeMassShell p :=
  shellState p (relativeCycles.subtype (cyclePart p z)) (cyclePart_mem_fixedMomentum p z)

private theorem cyclePart_mem_boundaries_of_mem_range (p : UCharge) (z : relativeCycles)
    (hz : cyclePartInShell p z ∈ LinearMap.range (differential p)) :
    cyclePart p z ∈ relativeBoundaries := by
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hz
  change ∃ w : relativeStates,
    boundaryMap (R := ℂ) relativeDifferential relativeDifferential_square w = cyclePart p z
  refine ⟨shellInclusion p u, ?_⟩
  apply relativeCycles.subtype_injective
  apply relativeStates.subtype_injective
  change Q (u : State) = ((cyclePart p z).1 : State)
  exact congrArg (fun v : relativeMassShell p => (v : State)) hu

private theorem cyclePart_left_boundary (z : relativeCycles)
    (hz : ∀ c, cohomologyBPZ (relativeBoundaries.mkQ z) c = 0)
    (p : UCharge) (hp : p ∈ momentumSupport (z.1 : State)) :
    cyclePart p z ∈ relativeBoundaries := by
  refine cyclePart_mem_boundaries_of_mem_range p z ?_
  rw [← shellBPZ_left_cycle_annihilator p]
  change shellBPZ p (cyclePartInShell p z) ∈
    (LinearMap.ker (differential (-p))).dualAnnihilator
  rw [Submodule.mem_dualAnnihilator]
  intro y hy
  let f : relativeCycles →ₗ[ℂ] ℂ :=
    (betaRelTotal.flip (shellInclusion (-p) y)).comp relativeCycles.subtype
  have htest : f z = 0 := by
    have h := hz (relativeBoundaries.mkQ (shellCycleToRelative (-p) y hy))
    rw [cohomologyBPZ_mk] at h
    exact h
  have hsum : (∑ q ∈ momentumSupport (z.1 : State), f (cyclePart q z)) = 0 := by
    rw [← map_sum, sum_cyclePart]
    exact htest
  rw [Finset.sum_eq_single_of_mem p hp] at hsum
  · change f (cyclePart p z) = 0
    exact hsum
  · intro q _ hqp
    change betaRelTotal (relativeCycles.subtype (cyclePart q z)) (shellInclusion (-p) y) = 0
    exact betaRelTotal_eq_zero_of_momentum
      (x := relativeCycles.subtype (cyclePart q z)) (y := shellInclusion (-p) y)
      (fun h => hqp (neg_injective h.symm)) (cyclePart_mem_fixedMomentum q z) y.property.1.1

private theorem cyclePart_neg_right_boundary (z : relativeCycles)
    (hz : ∀ c, cohomologyBPZ c (relativeBoundaries.mkQ z) = 0)
    (p : UCharge) (hp : -p ∈ momentumSupport (z.1 : State)) :
    cyclePart (-p) z ∈ relativeBoundaries := by
  refine cyclePart_mem_boundaries_of_mem_range (-p) z ?_
  rw [← shellBPZ_right_cycle_annihilator p]
  change (shellBPZ p).flip (cyclePartInShell (-p) z) ∈
    (LinearMap.ker (differential p)).dualAnnihilator
  rw [Submodule.mem_dualAnnihilator]
  intro x hx
  let f : relativeCycles →ₗ[ℂ] ℂ :=
    (betaRelTotal (shellInclusion p x)).comp relativeCycles.subtype
  have htest : f z = 0 := by
    have h := hz (relativeBoundaries.mkQ (shellCycleToRelative p x hx))
    rw [cohomologyBPZ_mk] at h
    exact h
  have hsum : (∑ q ∈ momentumSupport (z.1 : State), f (cyclePart q z)) = 0 := by
    rw [← map_sum, sum_cyclePart]
    exact htest
  rw [Finset.sum_eq_single_of_mem (-p) hp] at hsum
  · change f (cyclePart (-p) z) = 0
    exact hsum
  · intro q _ hqp
    change betaRelTotal (shellInclusion p x) (relativeCycles.subtype (cyclePart q z)) = 0
    exact betaRelTotal_eq_zero_of_momentum
      (x := shellInclusion p x) (y := relativeCycles.subtype (cyclePart q z))
      hqp x.property.1.1 (cyclePart_mem_fixedMomentum q z)

private theorem mkQ_eq_zero_of_cycleParts_mem_boundaries (z : relativeCycles)
    (hz : ∀ p ∈ momentumSupport (z.1 : State), cyclePart p z ∈ relativeBoundaries) :
    relativeBoundaries.mkQ z = 0 := by
  have hsum : (∑ p ∈ momentumSupport (z.1 : State), cyclePart p z) ∈ relativeBoundaries :=
    relativeBoundaries.sum_mem hz
  rw [sum_cyclePart] at hsum
  exact (Submodule.Quotient.mk_eq_zero (p := relativeBoundaries)).mpr hsum

/-- Both radicals of the inserted BPZ pairing vanish on native relative BRST cohomology. -/
theorem cohomologyBPZ_nondegenerate : cohomologyBPZ.Nondegenerate := by
  constructor
  · intro c hc
    obtain ⟨z, rfl⟩ := relativeBoundaries.mkQ_surjective c
    exact mkQ_eq_zero_of_cycleParts_mem_boundaries z (cyclePart_left_boundary z hc)
  · intro c hc
    obtain ⟨z, rfl⟩ := relativeBoundaries.mkQ_surjective c
    apply mkQ_eq_zero_of_cycleParts_mem_boundaries
    intro p hp
    have hneg : -(-p) ∈ momentumSupport (z.1 : State) := by simpa only [neg_neg] using hp
    simpa only [neg_neg] using cyclePart_neg_right_boundary z hc (-p) hneg

#print axioms shellBPZ_right_cycle_annihilator
#print axioms cohomologyBPZ_nondegenerate

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCohomologyBPZNondegenerate
