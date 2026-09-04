/- GID: D5/S3/ContinuousObservables/FreePermutationObserverDistance
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/FreePermutationObserverDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Free update orbits have exact integer distance;
     both off-orbit sectors are infinitely far. -/

import D5.S3.ContinuousObservables.PermutationOrbitHorizon

/- Library-search audit trail (2026-09-04):
   * Repository searches found `PermutationOrbitHorizon`, which proves the signed
     orbit upper bound and characterizes infinite distance by distinct update
     orbits, but not equality on a general free orbit.
   * `ObserverDistanceClassification` gives exact equality only on its separate
     integer carrier.  It is used directly for the invariant-fiber separation.
   * Pinned Mathlib searches for free permutation orbit coordinates and exact
     observable distances found no matching theorem.  The proof constructs the
     missing bounded clipped-coordinate observable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped ENNReal

namespace D5.S3.ContinuousObservables.FreePermutationObserverDistance

open D5.S3.ContinuousObservables.ObserverDistanceClassification
open D5.S3.ContinuousObservables.PermutationOrbitHorizon

private def InOrbit {I : Type*} (tau : Equiv.Perm I) (x y : I) : Prop :=
  Exists fun n : Int => (tau ^ n) x = y

private noncomputable def orbitIndex {I : Type*} (tau : Equiv.Perm I)
    (x y : I) : Int := by
  classical
  exact if h : InOrbit tau x y then Classical.choose h else 0

private theorem inOrbit_step_iff {I : Type*} (tau : Equiv.Perm I) (x y : I) :
    InOrbit tau x (tau y) ↔ InOrbit tau x y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n - 1, ?_⟩
    calc
      (tau ^ (n - 1)) x = tau.symm ((tau ^ n) x) := by
        rw [show n - 1 = (-1 : Int) + n by omega, zpow_add,
          Equiv.Perm.mul_apply]
        simp
      _ = y := by simpa using congrArg tau.symm hn
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    calc
      (tau ^ (n + 1)) x = tau ((tau ^ n) x) := by
        rw [show n + 1 = (1 : Int) + n by omega, zpow_add,
          Equiv.Perm.mul_apply]
        simp
      _ = tau y := congrArg tau hn

private theorem orbitIndex_power {I : Type*} (tau : Equiv.Perm I) (x : I)
    (hfree : Function.Injective fun n : Int => (tau ^ n) x) (n : Int) :
    orbitIndex tau x ((tau ^ n) x) = n := by
  rw [orbitIndex, dif_pos ⟨n, rfl⟩]
  apply hfree
  exact Classical.choose_spec (show InOrbit tau x ((tau ^ n) x) from ⟨n, rfl⟩)

private theorem orbitIndex_step {I : Type*} (tau : Equiv.Perm I) (x y : I)
    (hfree : Function.Injective fun n : Int => (tau ^ n) x)
    (hy : InOrbit tau x y) :
    orbitIndex tau x (tau y) = orbitIndex tau x y + 1 := by
  rcases hy with ⟨n, rfl⟩
  have hstep : tau ((tau ^ n) x) = (tau ^ (n + 1)) x := by
    rw [show n + 1 = (1 : Int) + n by omega, zpow_add,
      Equiv.Perm.mul_apply]
    simp
  rw [hstep, orbitIndex_power tau x hfree, orbitIndex_power tau x hfree]

private noncomputable def clippedOrbitObservable {I : Type*}
    (tau : Equiv.Perm I) (x : I) (radius : Nat) (y : I) : Real := by
  classical
  exact if InOrbit tau x y then
      min (dist (orbitIndex tau x y : Real) 0) radius
    else
      0

private theorem clippedOrbitObservable_bounded {I : Type*}
    (tau : Equiv.Perm I) (x : I) (radius : Nat) :
    Bornology.IsBounded (Set.range (clippedOrbitObservable tau x radius)) := by
  apply (Metric.isBounded_Icc (0 : Real) radius).subset
  rintro _ ⟨y, rfl⟩
  by_cases hy : InOrbit tau x y
  · simp only [clippedOrbitObservable, if_pos hy]
    exact ⟨le_min dist_nonneg (Nat.cast_nonneg radius), min_le_right _ _⟩
  · simp [clippedOrbitObservable, hy]

private theorem clippedOrbitObservable_admissible {I : Type*}
    (tau : Equiv.Perm I) (x : I)
    (hfree : Function.Injective fun n : Int => (tau ^ n) x) (radius : Nat) :
    edgeAdmissible tau (clippedOrbitObservable tau x radius) := by
  refine ⟨clippedOrbitObservable_bounded tau x radius, ?_⟩
  intro y
  by_cases hy : InOrbit tau x y
  · have hty : InOrbit tau x (tau y) := (inOrbit_step_iff tau x y).2 hy
    have hindex := orbitIndex_step tau x y hfree hy
    have hlipschitz :=
      ((LipschitzWith.dist_right (0 : Real)).min_const (radius : Real)).dist_le_mul
        (orbitIndex tau x (tau y) : Real) (orbitIndex tau x y : Real)
    have hdist :
        dist (min (dist (orbitIndex tau x (tau y) : Real) 0) radius)
            (min (dist (orbitIndex tau x y : Real) 0) radius) ≤ 1 := by
      calc
        _ ≤ 1 * dist (orbitIndex tau x (tau y) : Real)
            (orbitIndex tau x y : Real) := by simpa using hlipschitz
        _ = 1 := by rw [hindex]; norm_num [Real.dist_eq]
    simpa [clippedOrbitObservable, hy, hty, Real.dist_eq,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hdist
  · have hty : ¬InOrbit tau x (tau y) := by
      simpa [inOrbit_step_iff tau x y] using hy
    simp [clippedOrbitObservable, hy, hty]

private theorem clippedOrbitObservable_gap {I : Type*}
    (tau : Equiv.Perm I) (x : I)
    (hfree : Function.Injective fun n : Int => (tau ^ n) x) (n : Int) :
    dist (clippedOrbitObservable tau x n.natAbs x)
        (clippedOrbitObservable tau x n.natAbs ((tau ^ n) x)) = n.natAbs := by
  have hx : InOrbit tau x x := ⟨0, by simp⟩
  have hn : InOrbit tau x ((tau ^ n) x) := ⟨n, rfl⟩
  have hzero : orbitIndex tau x x = 0 := by
    simpa using orbitIndex_power tau x hfree 0
  simp only [clippedOrbitObservable, if_pos hx, if_pos hn]
  rw [hzero, orbitIndex_power tau x hfree]
  norm_num [Real.dist_eq]

private theorem exact_signed_orbit_distance {I : Type*}
    (tau : Equiv.Perm I) (x : I)
    (hfree : Function.Injective fun n : Int => (tau ^ n) x) (n : Int) :
    observerDistance tau x ((tau ^ n) x) = (n.natAbs : ENNReal) := by
  apply le_antisymm
  · exact (permutation_observer_horizon_eq_orbit_complement
      tau x ((tau ^ n) x) x).2.1 n rfl
  · unfold observerDistance
    let witness : {f : I → Real // edgeAdmissible tau f} :=
      ⟨clippedOrbitObservable tau x n.natAbs,
        clippedOrbitObservable_admissible tau x hfree n.natAbs⟩
    refine le_trans ?_ (le_iSup (fun f : {f : I → Real // edgeAdmissible tau f} =>
      ENNReal.ofReal (dist (f.1 x) (f.1 ((tau ^ n) x)))) witness)
    rw [show witness.1 = clippedOrbitObservable tau x n.natAbs from rfl,
      clippedOrbitObservable_gap tau x hfree n, ENNReal.ofReal_natCast]

private theorem mem_cyclic_orbit_iff {I : Type*} (tau : Equiv.Perm I)
    (x y : I) :
    y ∈ MulAction.orbit (Subgroup.zpowers tau) x ↔ InOrbit tau x y := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨n, ?_⟩
    simpa [MulAction.subgroup_smul_def, Equiv.Perm.smul_def, hn] using hg
  · rintro ⟨n, rfl⟩
    exact MulAction.mem_orbit_iff.mpr
      ⟨⟨tau ^ n, Subgroup.zpow_mem_zpowers tau n⟩, rfl⟩

/-- If every integer update orbit is free, its full-readout observer distance is
exactly the number of bookkeeping steps.  A point in the same visible fiber but
outside that orbit is infinitely far (flowline type), and distinct invariant
fibers are infinitely far (central type). -/
theorem free_permutation_observer_distance
    {I Fiber : Type*} (tau : Equiv.Perm I)
    (hfree : ∀ x, Function.Injective fun n : Int => (tau ^ n) x)
    (fiber : I → Fiber) (hFiberInvariant : ∀ x, fiber (tau x) = fiber x) :
    (∀ x (n : Int), observerDistance tau x ((tau ^ n) x) =
      (n.natAbs : ENNReal)) ∧
      (∀ x y, fiber x = fiber y → (∀ n : Int, y ≠ (tau ^ n) x) →
        observerDistance tau x y = ⊤) ∧
      (∀ x y, fiber x ≠ fiber y → observerDistance tau x y = ⊤) := by
  refine ⟨fun x n => exact_signed_orbit_distance tau x (hfree x) n, ?_, ?_⟩
  · intro x y _ hOutside
    apply (permutation_observer_horizon_eq_orbit_complement tau x y x).1.mpr
    intro equalOrbits
    have hy : y ∈ MulAction.orbit (Subgroup.zpowers tau) x := by
      rw [equalOrbits]
      exact MulAction.mem_orbit_self y
    obtain ⟨n, hn⟩ := (mem_cyclic_orbit_iff tau x y).mp hy
    exact hOutside n hn.symm
  · intro x y hDifferent
    exact (permutation_observer_distance_classification
      tau fiber hFiberInvariant hDifferent (M := 1) 0 0 0 0).1

/-- Integer translation supplies a concrete free update orbit, so the exact
distance clause is nonvacuous. -/
example :
    observerDistance (Equiv.addRight (1 : Int)) 0
      (((Equiv.addRight (1 : Int)) ^ (3 : Int)) 0) = 3 := by
  have hfree : ∀ x : Int,
      Function.Injective fun n : Int => ((Equiv.addRight (1 : Int)) ^ n) x := by
    intro x m n hmn
    simpa using congrArg (fun z : Int => z - x) hmn
  simpa using exact_signed_orbit_distance
    (Equiv.addRight (1 : Int)) 0 (hfree 0) 3

#print axioms free_permutation_observer_distance

end D5.S3.ContinuousObservables.FreePermutationObserverDistance
