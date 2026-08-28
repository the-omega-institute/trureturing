/- GID: D5/S3/ContinuousObservables/PermutationOrbitHorizon
   generality: I
   mirror-B: D5/B/S3/ContinuousObservables/PermutationOrbitHorizon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full permutation readouts place the horizon exactly outside the cyclic update orbit. -/

import D5.S3.ContinuousObservables.ObserverDistanceClassification
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches for `horizonSet`, `visibleBall`, `finiteDistanceBall`, and the
     body `{x | observerDistance tau o x = top}` found no D5 declaration.  The source's
     formalization note explicitly prescribes that body for `horizonSet`.
   * Body-shape searches for integer permutation orbits found no D5 wrapper.  Mathlib's
     canonical `MulAction.orbit (Subgroup.zpowers tau)` and `Subgroup.mem_zpowers_iff`
     exactly encode the source set of all signed iterates, so they are used directly.
   * `ObserverDistanceClassification.permutation_observer_distance_classification`
     supplies the exact different-invariant-leaf infinite-distance implication.  No
     library theorem supplies the signed telescope bound or the two set equalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped ENNReal

namespace D5.S3.ContinuousObservables.PermutationOrbitHorizon

open D5.S3.ContinuousObservables.ObserverDistanceClassification

/-- Points at infinite full-readout observer distance from the chosen origin. -/
def horizonSet {I : Type*} (tau : Equiv.Perm I) (o : I) : Set I :=
  {x | observerDistance tau o x = ⊤}

/-- Points at finite full-readout observer distance from the chosen origin. -/
def finiteDistanceBall {I : Type*} (tau : Equiv.Perm I) (o : I) : Set I :=
  {x | observerDistance tau o x ≠ ⊤}

private theorem edge_distance_le {I : Type*} (tau : Equiv.Perm I)
    (f : I → Real) (hf : edgeAdmissible tau f) (i : I) :
    dist (f (tau i)) (f i) ≤ 1 := by
  simpa [Real.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using hf.2 i

private theorem forward_power_distance_le {I : Type*} (tau : Equiv.Perm I)
    (f : I → Real) (hf : edgeAdmissible tau f) (x : I) :
    ∀ n : Nat, dist (f ((tau ^ n) x)) (f x) ≤ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        dist (f ((tau ^ (n + 1)) x)) (f x) ≤
            dist (f ((tau ^ (n + 1)) x)) (f ((tau ^ n) x)) +
              dist (f ((tau ^ n) x)) (f x) := dist_triangle _ _ _
        _ ≤ 1 + (n : Real) := by
          exact add_le_add
            (by simpa [pow_succ', Equiv.Perm.mul_apply] using
              edge_distance_le tau f hf ((tau ^ n) x)) ih
        _ = (n + 1 : Nat) := by
          rw [Nat.cast_add, Nat.cast_one, add_comm]

private theorem signed_power_distance_le {I : Type*} (tau : Equiv.Perm I)
    (f : I → Real) (hf : edgeAdmissible tau f) (x : I) (n : Int) :
    dist (f ((tau ^ n) x)) (f x) ≤ n.natAbs := by
  cases n with
  | ofNat n =>
      simpa [zpow_natCast] using forward_power_distance_le tau f hf x n
  | negSucc n =>
      have hforward :=
        forward_power_distance_le tau f hf ((tau ^ Int.negSucc n) x) (n + 1)
      have hreturn :
          (tau ^ (n + 1)) ((tau ^ Int.negSucc n) x) = x := by
        rw [← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add]
        have hexponent : ((n + 1 : Nat) : Int) + Int.negSucc n = 0 := by omega
        rw [hexponent]
        simp
      rw [hreturn, dist_comm] at hforward
      simpa using hforward

private theorem observerDistance_signed_power_le {I : Type*}
    (tau : Equiv.Perm I) (x : I) (n : Int) :
    observerDistance tau x ((tau ^ n) x) ≤ (n.natAbs : ENNReal) := by
  unfold observerDistance
  apply iSup_le
  intro f
  rw [dist_comm]
  simpa [ENNReal.ofReal_natCast] using
    ENNReal.ofReal_mono (signed_power_distance_le tau f.1 f.2 x n)

private theorem mem_cyclic_orbit_iff {I : Type*} (tau : Equiv.Perm I)
    (x y : I) :
    y ∈ MulAction.orbit (Subgroup.zpowers tau) x ↔
      ∃ n : Int, (tau ^ n) x = y := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨n, ?_⟩
    simpa [MulAction.subgroup_smul_def, Equiv.Perm.smul_def, hn] using hg
  · rintro ⟨n, rfl⟩
    exact MulAction.mem_orbit_iff.mpr
      ⟨⟨tau ^ n, Subgroup.zpow_mem_zpowers tau n⟩, rfl⟩

private theorem observerDistance_top_iff_orbit_ne {I : Type*}
    (tau : Equiv.Perm I) (x y : I) :
    observerDistance tau x y = ⊤ ↔
      MulAction.orbit (Subgroup.zpowers tau) x ≠
        MulAction.orbit (Subgroup.zpowers tau) y := by
  let leaf : I → MulAction.orbitRel.Quotient (Subgroup.zpowers tau) I :=
    fun i => Quotient.mk'' i
  have hLeafInvariant : ∀ i, leaf (tau i) = leaf i := by
    intro i
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨tau, Subgroup.mem_zpowers tau⟩, rfl⟩
  constructor
  · intro htop hOrbit
    have hy : y ∈ MulAction.orbit (Subgroup.zpowers tau) x := by
      rw [hOrbit]
      exact MulAction.mem_orbit_self y
    obtain ⟨n, hn⟩ := (mem_cyclic_orbit_iff tau x y).mp hy
    have hbound := observerDistance_signed_power_le tau x n
    rw [hn] at hbound
    rw [htop] at hbound
    simp at hbound
  · intro hOrbit
    have hLeafDifferent : leaf x ≠ leaf y := by
      intro hxy
      apply hOrbit
      have hRelated : MulAction.orbitRel (Subgroup.zpowers tau) I x y :=
        Quotient.exact hxy
      exact MulAction.orbit_eq_iff.mpr hRelated
    exact (permutation_observer_distance_classification
      tau leaf hLeafInvariant hLeafDifferent (M := 1) 0 0 0 0).1

/-- For the full family of bounded unit-edge readouts, infinite distance is exactly
separation of cyclic update orbits.  Signed iterates have their expected path-length
upper bound, so the horizon and finite-distance ball are respectively the complement
and the body of the origin's orbit. -/
theorem permutation_observer_horizon_eq_orbit_complement {I : Type*}
    (tau : Equiv.Perm I) (x y o : I) :
    (observerDistance tau x y = ⊤ ↔
      MulAction.orbit (Subgroup.zpowers tau) x ≠
        MulAction.orbit (Subgroup.zpowers tau) y) ∧
    (∀ n : Int, y = (tau ^ n) x →
      observerDistance tau x y ≤ (n.natAbs : ENNReal)) ∧
    horizonSet tau o =
      (MulAction.orbit (Subgroup.zpowers tau) o)ᶜ ∧
    finiteDistanceBall tau o =
      MulAction.orbit (Subgroup.zpowers tau) o := by
  have htop := observerDistance_top_iff_orbit_ne tau
  refine ⟨htop x y, ?_, ?_, ?_⟩
  · intro n hn
    subst y
    exact observerDistance_signed_power_le tau x n
  · ext z
    simp only [horizonSet, mem_setOf_eq, mem_compl_iff]
    rw [htop o z]
    simpa [eq_comm] using
      not_congr (MulAction.orbit_eq_iff
        (G := Subgroup.zpowers tau) (a := z) (b := o))
  · ext z
    simp only [finiteDistanceBall, mem_setOf_eq]
    exact (not_congr (htop o z)).trans <| by
      simpa [eq_comm] using
        MulAction.orbit_eq_iff (G := Subgroup.zpowers tau) (a := z) (b := o)

#print axioms permutation_observer_horizon_eq_orbit_complement

end D5.S3.ContinuousObservables.PermutationOrbitHorizon
