/- GID: D5/S3/Combinatorics/Graph/Eccentric/DePatraConjecture
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Eccentric/DePatraConjecture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict eccentric connected-subgraph sum under contraction of a qualifying bridge. -/
import D5.S3.Combinatorics.Graph.Eccentric.DePatraCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Eccentric.DePatraConjecture

open SimpleGraph DePatraBridge DePatraCounting Classical
open scoped BigOperators
noncomputable section
variable {V : Type} {G : SimpleGraph V}


theorem rootedCount_self (S : Set V) (r : V) :
    rootedCount G S r {r} = rootedCount G S r ∅ :=
  rooted_targets_root {r} (Set.Subset.refl _)

/-- A local minimum is over every non-root vertex of the actual component. -/
def IsLocalMinimum (G : SimpleGraph V) (S : Set V) (r : V) (p : ℕ) : Prop :=
  (∀ x ∈ S, x ≠ r → p ≤ rootedCount G S r {x}) ∧
    ∃ x ∈ S, x ≠ r ∧ rootedCount G S r {x} = p

theorem local_minimum_le_all {S : Set V} {r : V} {p : ℕ}
    (hp : IsLocalMinimum G S r p) (hpa : p ≤ rootedCount G S r ∅)
    (x : V) (hx : x ∈ S) : p ≤ rootedCount G S r {x} := by
  by_cases hxr : x = r
  · subst x
    rw [rootedCount_self]
    exact hpa
  · exact hp.1 x hx hxr

theorem bridge_endpoint_minimum [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (p q : ℕ)
    (hp : IsLocalMinimum G (deletedSide G u v u) u p)
    (hq : IsLocalMinimum G (deletedSide G u v v) v q)
    (hpa : p ≤ rootedCount G (deletedSide G u v u) u ∅)
    (hqb : q ≤ rootedCount G (deletedSide G u v v) v ∅) :
    eccentricity G u = min ((rootedCount G (deletedSide G u v v) v ∅ + 1) * p)
      (rootedCount G (deletedSide G u v u) u ∅ * q) := by
  have hu : u ∈ deletedSide G u v u := Reachable.rfl
  apply le_antisymm
  · obtain ⟨x, hx, hxu, hxp⟩ := hp.2
    obtain ⟨y, hy, hyv, hyq⟩ := hq.2
    apply le_min
    · have hh := eccentricity_le_pairCount G u x
      rw [bridge_root_pair_left h hx, hxp] at hh
      simpa only [Nat.mul_comm, Nat.add_comm] using hh
    · have hh := eccentricity_le_pairCount G u y
      rw [bridge_pair_cross h hu hy, rootedCount_self, hyq] at hh
      exact hh
  · apply le_eccentricity
    intro y
    rcases (qualifying_components h).2.1 y with hy | hy
    · rw [bridge_root_pair_left h hy]
      have hm := local_minimum_le_all hp hpa y hy
      exact (min_le_left _ _).trans (by nlinarith)
    · rw [bridge_pair_cross h hu hy, rootedCount_self]
      have hm := local_minimum_le_all hq hqb y hy
      exact (min_le_right _ _).trans (Nat.mul_le_mul_left _ hm)

/-- A pair count is bounded by the diagonal count, even though the diagonal includes a singleton. -/
theorem pairCount_le_diagonal [Finite V] (G : SimpleGraph V) (x y : V) :
    pairCount G x y ≤ pairCount G y y := by
  apply countContaining_antitone
  intro z hz
  have hz : z = y := by simpa using hz
  subst z
  simp

/-- The fresh-leaf pair formula on the opposite component follows by endpoint relabeling. -/
theorem shift_pair_leaf_right [Finite V] {u v y : V} (h : QualifyingBridge G u v)
    (hy : y ∈ deletedSide G u v v) (hyv : y ≠ v) :
    pairCount (bridgeShift G u v) y v =
      rootedCount G (deletedSide G u v u) u ∅ * rootedCount G (deletedSide G u v v) v {y} := by
  have hyu : y ≠ u := fun he => (bridge_pendant_data h).2.1 (he ▸ hy)
  have hh := shift_pair_leaf (qualifyingBridge_swap h)
    (x := y) (by rw [deletedSide_swap (G := G) u v v]; exact hy)
  rw [deletedSide_swap (G := G) u v v, deletedSide_swap (G := G) u v u] at hh
  have hi := pairCount_iso (bridgeShiftSwapIso (G := G) u v (qualifying_components h).1.ne) y v
  change pairCount (bridgeShift G u v) y v =
    pairCount (bridgeShift G v u) (Equiv.swap u v y) (Equiv.swap u v v) at hi
  rw [Equiv.swap_apply_of_ne_of_ne hyu hyv, Equiv.swap_apply_right] at hi
  rw [hi, hh, Nat.mul_comm]

theorem shift_root_endpoint_minimum [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (p q : ℕ)
    (hp : IsLocalMinimum G (deletedSide G u v u) u p)
    (hq : IsLocalMinimum G (deletedSide G u v v) v q)
    (hpa : p ≤ rootedCount G (deletedSide G u v u) u ∅)
    (hqb : q ≤ rootedCount G (deletedSide G u v v) v ∅) :
    eccentricity (bridgeShift G u v) u =
      min (min (2 * rootedCount G (deletedSide G u v v) v ∅ * p)
        (2 * rootedCount G (deletedSide G u v u) u ∅ * q))
        (rootedCount G (deletedSide G u v u) u ∅ * rootedCount G (deletedSide G u v v) v ∅) := by
  have hu : u ∈ deletedSide G u v u := Reachable.rfl
  apply le_antisymm
  · obtain ⟨x, hx, hxu, hxp⟩ := hp.2
    obtain ⟨y, hy, hyv, hyq⟩ := hq.2
    apply le_min
    · apply le_min
      · have hh := eccentricity_le_pairCount (bridgeShift G u v) u x
        rw [shift_root_pair_left h hx, hxp] at hh
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hh
      · have hh := eccentricity_le_pairCount (bridgeShift G u v) u y
        rw [shift_pair_cross h hu hy hyv, rootedCount_self, hyq] at hh
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hh
    · have hh := eccentricity_le_pairCount (bridgeShift G u v) u v
      rw [shift_pair_leaf h hu, rootedCount_self] at hh
      exact hh
  · apply le_eccentricity
    intro y
    by_cases hyv : y = v
    · subst y
      rw [shift_pair_leaf h hu, rootedCount_self]
      exact min_le_right _ _
    · rcases (qualifying_components h).2.1 y with hy | hy
      · rw [shift_root_pair_left h hy]
        have hm := local_minimum_le_all hp hpa y hy
        exact ((min_le_left _ _).trans (min_le_left _ _)).trans (by nlinarith)
      · rw [shift_pair_cross h hu hy hyv, rootedCount_self]
        have hm := local_minimum_le_all hq hqb y hy
        exact ((min_le_left _ _).trans (min_le_right _ _)).trans (by nlinarith)

theorem shift_leaf_endpoint_minimum [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (p q : ℕ)
    (hp : IsLocalMinimum G (deletedSide G u v u) u p)
    (hq : IsLocalMinimum G (deletedSide G u v v) v q)
    (hpa : p ≤ rootedCount G (deletedSide G u v u) u ∅)
    (hqb : q ≤ rootedCount G (deletedSide G u v v) v ∅) :
    eccentricity (bridgeShift G u v) v =
      min (rootedCount G (deletedSide G u v v) v ∅ * p)
        (rootedCount G (deletedSide G u v u) u ∅ * q) := by
  have hu : u ∈ deletedSide G u v u := Reachable.rfl
  apply le_antisymm
  · obtain ⟨x, hx, hxu, hxp⟩ := hp.2
    obtain ⟨y, hy, hyv, hyq⟩ := hq.2
    apply le_min
    · have hh := eccentricity_le_pairCount (bridgeShift G u v) v x
      rw [pairCount_symm, shift_pair_leaf h hx, hxp] at hh
      simpa only [Nat.mul_comm] using hh
    · have hh := eccentricity_le_pairCount (bridgeShift G u v) v y
      rw [pairCount_symm, shift_pair_leaf_right h hy hyv, hyq] at hh
      exact hh
  · apply le_eccentricity
    intro y
    by_cases hyv : y = v
    · subst y
      have hh := pairCount_le_diagonal (bridgeShift G u v) u v
      rw [shift_pair_leaf h hu, rootedCount_self] at hh
      exact (min_le_left _ _).trans ((by nlinarith :
        rootedCount G (deletedSide G u v v) v ∅ * p ≤
          rootedCount G (deletedSide G u v u) u ∅ * rootedCount G (deletedSide G u v v) v ∅).trans hh)
    · rw [pairCount_symm]
      rcases (qualifying_components h).2.1 y with hy | hy
      · rw [shift_pair_leaf h hy]
        have hm := local_minimum_le_all hp hpa y hy
        exact (min_le_left _ _).trans (by nlinarith)
      · rw [shift_pair_leaf_right h hy hyv]
        have hm := local_minimum_le_all hq hqb y hy
        exact (min_le_right _ _).trans (Nat.mul_le_mul_left _ hm)


/-- Both endpoint contributions improve jointly; no monotonicity is asserted for the leaf alone. -/
theorem shift_endpoints_strict [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    eccentricity G u + eccentricity G v <
      eccentricity (bridgeShift G u v) u + eccentricity (bridgeShift G u v) v := by
  have parts := qualifying_components h
  obtain ⟨p, hppos, hpa, ha, hpall, hpw⟩ := local_root_minimum
    (show u ∈ deletedSide G u v u from Reachable.rfl) (bridge_component_connected h)
    parts.2.2.2.2.2.1
  have connB : (G.induce (deletedSide G u v v)).Connected := by
    have hh := bridge_component_connected (qualifyingBridge_swap h)
    rw [deletedSide_swap (G := G) u v v] at hh
    exact hh
  obtain ⟨q, hqpos, hqb, hb, hqall, hqw⟩ := local_root_minimum
    (show v ∈ deletedSide G u v v from Reachable.rfl) connB parts.2.2.2.2.2.2
  have hp : IsLocalMinimum G (deletedSide G u v u) u p := ⟨hpall, hpw⟩
  have hq : IsLocalMinimum G (deletedSide G u v v) v q := ⟨hqall, hqw⟩
  have hp' : IsLocalMinimum G (deletedSide G v u u) u p := by
    rw [deletedSide_swap (G := G) u v u]; exact hp
  have hq' : IsLocalMinimum G (deletedSide G v u v) v q := by
    rw [deletedSide_swap (G := G) u v v]; exact hq
  have hpa' : p ≤ rootedCount G (deletedSide G v u u) u ∅ := by
    rw [deletedSide_swap (G := G) u v u]; exact hpa.le
  have hqb' : q ≤ rootedCount G (deletedSide G v u v) v ∅ := by
    rw [deletedSide_swap (G := G) u v v]; exact hqb.le
  have oldv := bridge_endpoint_minimum (qualifyingBridge_swap h) q p hq' hp' hqb' hpa'
  rw [deletedSide_swap (G := G) u v u, deletedSide_swap (G := G) u v v] at oldv
  rw [bridge_endpoint_minimum h p q hp hq hpa.le hqb.le, oldv,
    shift_root_endpoint_minimum h p q hp hq hpa.le hqb.le,
    shift_leaf_endpoint_minimum h p q hp hq hpa.le hqb.le]
  have hh := endpoint_minima_strict (rootedCount G (deletedSide G u v u) u ∅)
    (rootedCount G (deletedSide G u v v) v ∅) p q ha hb hppos hqpos hpa hqb
  simpa only [min_comm] using hh

/-- The entire De–Patra bridge inequality on the original vertex labels. -/
theorem dePatra_conjecture_2_9_shift [Fintype V] {u v : V} (h : QualifyingBridge G u v) :
    eccentricSum G < eccentricSum (bridgeShift G u v) := by
  have huv : u ≠ v := (qualifying_components h).1.ne
  have hsum : (∑ x ∈ (Finset.univ.erase u).erase v, eccentricity G x) ≤
      ∑ x ∈ (Finset.univ.erase u).erase v, eccentricity (bridgeShift G u v) x := by
    apply Finset.sum_le_sum
    intro x hx
    have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    exact (shift_nonendpoint_strict h hxu hxv).le
  have oldsum := Finset.sum_erase_add (Finset.univ.erase u) (eccentricity G)
    (show v ∈ Finset.univ.erase u from Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩)
  have newsum := Finset.sum_erase_add (Finset.univ.erase u) (eccentricity (bridgeShift G u v))
    (show v ∈ Finset.univ.erase u from Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩)
  have oldu := Finset.sum_erase_add Finset.univ (eccentricity G) (Finset.mem_univ u)
  have newu := Finset.sum_erase_add Finset.univ (eccentricity (bridgeShift G u v))
    (Finset.mem_univ u)
  have hend := shift_endpoints_strict h
  unfold eccentricSum
  omega

/-- De–Patra arXiv:2610.19694v1 Conjecture 2.9 for every qualifying finite simple connected
 graph and bridge: contraction followed by one genuinely fresh leaf strictly increases ES. -/
theorem dePatra_conjecture_2_9 [Fintype V] {u v : V} (h : QualifyingBridge G u v) :
    eccentricSum G < eccentricSum (contractAddLeaf G u v (qualifying_components h).1.ne) := by
  rw [← eccentricSum_iso (bridgeShiftIso G u v (qualifying_components h).1.ne)]
  exact dePatra_conjecture_2_9_shift h

#print axioms dePatra_conjecture_2_9
#print axioms dePatra_conjecture_2_9_shift
#print axioms shift_endpoints_strict
#print axioms shift_nonendpoint_strict

end
end D5.S3.Combinatorics.Graph.Eccentric.DePatraConjecture
