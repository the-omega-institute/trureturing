/- GID: D5/S1/Depth/FiniteMetric
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The finite phase fiber carries a cyclic distance; depth values inherit its max metric. -/

import D5.S1.Depth.JointCoordinates
import Mathlib.Data.Nat.Dist

namespace D5.S1.Depth

/-- The linear distance on the finite phase fiber: `|a - b|` read off the two
representatives, with no wrap. It is defined here only to be compared against
`phaseDist` and then rejected; `phaseDist_lt_linearPhaseDist_wrap` exhibits a pair
where it disagrees with the phase semantics. -/
def linearPhaseDist {k : ℕ} (a b : Fin k) : ℕ :=
  Nat.dist a.val b.val

/--
The cyclic distance on the finite phase fiber `Fin k`, `min |a - b| (k - |a - b|)`.

The wrap is not decoration. The fiber quantizes `phaseCoordinate`, whose codomain is
`AddCircle (1 : ℝ)`, i.e. the quotient `ℝ ⧸ ℤ`; `finitePhase` cuts that circle into `k`
half-open arcs through the representative chosen by `AddCircle.equivIco (1 : ℝ) 0`. The
cut point is a choice of fundamental domain, not a feature of the space: arcs `k - 1`
and `0` meet at it. The same reading is already load-bearing elsewhere in this stratum
-- `D5/S1/Phase/ThreeDistance` measures the golden orbit with `ThreeGap.gaps`,
whose gap list includes the last-to-first gap. A distance that reports `k - 1` for that
adjacency would contradict the object it is meant to measure, which is why
`linearPhaseDist` is rejected. `phaseDist_rotate` records the structural counterpart:
this distance does not depend on where the fundamental domain was cut.
-/
def phaseDist {k : ℕ} (a b : Fin k) : ℕ :=
  min (Nat.dist a.val b.val) (k - Nat.dist a.val b.val)

@[simp] theorem phaseDist_self {k : ℕ} (a : Fin k) : phaseDist a a = 0 := by
  simp [phaseDist, Nat.dist]

theorem phaseDist_comm {k : ℕ} (a b : Fin k) : phaseDist a b = phaseDist b a := by
  simp only [phaseDist, Nat.dist_comm]

/-- Separation: the cyclic distance vanishes exactly on the diagonal. -/
theorem phaseDist_eq_zero_iff {k : ℕ} (a b : Fin k) : phaseDist a b = 0 ↔ a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [phaseDist, Nat.dist, Fin.mk.injEq]
  omega

/-- Triangle inequality for the cyclic distance. -/
theorem phaseDist_triangle {k : ℕ} (a b c : Fin k) :
    phaseDist a c ≤ phaseDist a b + phaseDist b c := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  simp only [phaseDist, Nat.dist]
  omega

/-- The cyclic distance never exceeds the linear one. -/
theorem phaseDist_le_linearPhaseDist {k : ℕ} (a b : Fin k) :
    phaseDist a b ≤ linearPhaseDist a b := by
  simp only [phaseDist, linearPhaseDist]
  exact min_le_left _ _

/-- The circle signature: the fiber has diameter at most `k / 2`, so no two phases are
farther apart than half a turn. The linear distance has diameter `k - 1` instead. -/
theorem two_mul_phaseDist_le {k : ℕ} (a b : Fin k) : 2 * phaseDist a b ≤ k := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [phaseDist, Nat.dist]
  omega

/-- Rotation of the finite phase fiber by `c` buckets. -/
def rotate {k : ℕ} (c : ℕ) (a : Fin k) : Fin k :=
  ⟨(a.val + c) % k, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩

/-- Reduction of `x + c` modulo `k` when `x` and `c % k` are both below `k`. -/
private theorem add_mod_eq_of_lt {k x c : ℕ} (hx : x < k) (hc : c < k) :
    (x + c) % k = if x + c < k then x + c else x + c - k := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic distance is rotation invariant, so it does not depend on where
`AddCircle.equivIco` cut the circle into a fundamental domain. The linear distance is
not rotation invariant, which is the structural reason it is rejected. -/
theorem phaseDist_rotate {k : ℕ} (c : ℕ) (a b : Fin k) :
    phaseDist (rotate c a) (rotate c b) = phaseDist a b := by
  obtain ⟨x, hx⟩ := a
  obtain ⟨y, hy⟩ := b
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hx
  have hc : c % k < k := Nat.mod_lt _ hk
  have hxc : (x + c) % k = (x + c % k) % k := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_eq_of_lt hx]
  have hyc : (y + c) % k = (y + c % k) % k := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_eq_of_lt hy]
  simp only [rotate, phaseDist, Nat.dist, hxc, hyc,
    add_mod_eq_of_lt hx hc, add_mod_eq_of_lt hy hc]
  split <;> split <;> omega

/-- Forced check on the wrap: buckets `0` and `11` of a twelve-bucket fiber are one step
apart on the circle. `linearPhaseDist` answers `11` here, so this equation fails for the
rejected definition; a wrap written `k + 1 - d` answers `2` and one written `k - 1 - d`
answers `0`, so it pins the modulus too. -/
theorem phaseDist_wrap_adjacent : phaseDist (0 : Fin 12) 11 = 1 := by
  decide

/-- Forced check that the wrap is a strict change, not a relabelling. -/
theorem phaseDist_lt_linearPhaseDist_wrap :
    phaseDist (0 : Fin 12) 11 < linearPhaseDist (0 : Fin 12) 11 := by
  decide

/-- Forced check that `phaseDist_triangle` is sharp: at this instance the inequality is an
equality, so the bound is not a loose one that a strictly subadditive distance could also
satisfy. -/
theorem phaseDist_triangle_tight :
    phaseDist (0 : Fin 12) 4 = phaseDist (0 : Fin 12) 2 + phaseDist (2 : Fin 12) 4 := by
  decide

/--
The distance between two finite depth values: the max over the three coordinates, with
the cyclic distance on the phase fiber. The max is the product metric of the three
component distances, so each projection is 1-Lipschitz and no coordinate can be traded
against another.
-/
noncomputable def depthDist {q0 : ℤ} {n : ℕ+} (u v : DepthValue q0 n) : ℕ :=
  max (u.1 - v.1).natAbs (max (Nat.dist u.2.1 v.2.1) (phaseDist u.2.2 v.2.2))

@[simp] theorem depthDist_self {q0 : ℤ} {n : ℕ+} (u : DepthValue q0 n) :
    depthDist u u = 0 := by
  simp [depthDist, Nat.dist]

theorem depthDist_comm {q0 : ℤ} {n : ℕ+} (u v : DepthValue q0 n) :
    depthDist u v = depthDist v u := by
  simp only [depthDist, Nat.dist_comm, phaseDist_comm u.2.2 v.2.2]
  omega

/-- The scale projection is 1-Lipschitz. -/
theorem scaleDist_le_depthDist {q0 : ℤ} {n : ℕ+} (u v : DepthValue q0 n) :
    (u.1 - v.1).natAbs ≤ depthDist u v := by
  simp only [depthDist]
  omega

/-- The digit-length projection is 1-Lipschitz. -/
theorem digitDist_le_depthDist {q0 : ℤ} {n : ℕ+} (u v : DepthValue q0 n) :
    Nat.dist u.2.1 v.2.1 ≤ depthDist u v := by
  simp only [depthDist]
  omega

/-- The phase projection is 1-Lipschitz: two depth values that differ in phase are
separated by at least their phase distance. -/
theorem phaseDist_le_depthDist {q0 : ℤ} {n : ℕ+} (u v : DepthValue q0 n) :
    phaseDist u.2.2 v.2.2 ≤ depthDist u v := by
  simp only [depthDist]
  omega

/-- Separation at the depth interface: the distance vanishes exactly on equal depth
values. -/
theorem depthDist_eq_zero_iff {q0 : ℤ} {n : ℕ+} (u v : DepthValue q0 n) :
    depthDist u v = 0 ↔ u = v := by
  constructor
  · obtain ⟨s, d, p⟩ := u
    obtain ⟨t, e, q⟩ := v
    intro h
    simp only [depthDist, Nat.dist] at h
    have hphase : phaseDist p q = 0 := by omega
    have hscale : s = t := by omega
    have hdigit : d = e := by omega
    subst hscale
    subst hdigit
    rw [(phaseDist_eq_zero_iff p q).mp hphase]
  · rintro rfl
    exact depthDist_self _

/-- Triangle inequality at the depth interface. -/
theorem depthDist_triangle {q0 : ℤ} {n : ℕ+} (u v w : DepthValue q0 n) :
    depthDist u w ≤ depthDist u v + depthDist v w := by
  have hscale := scaleDist_le_depthDist u v
  have hscale' := scaleDist_le_depthDist v w
  have hdigit := digitDist_le_depthDist u v
  have hdigit' := digitDist_le_depthDist v w
  have hphase := phaseDist_le_depthDist u v
  have hphase' := phaseDist_le_depthDist v w
  have hphaseTriangle := phaseDist_triangle u.2.2 v.2.2 w.2.2
  have hdigitTriangle : Nat.dist u.2.1 w.2.1 ≤ Nat.dist u.2.1 v.2.1 + Nat.dist v.2.1 w.2.1 :=
    Nat.dist.triangle_inequality _ _ _
  show max (u.1 - w.1).natAbs (max (Nat.dist u.2.1 w.2.1) (phaseDist u.2.2 w.2.2))
      ≤ depthDist u v + depthDist v w
  refine max_le ?_ (max_le ?_ ?_) <;> omega

/-- Forced check that the phase coordinate is not discarded by the max: depth values
that agree on scale and digit length but differ in phase are strictly separated. This
fails for a `depthDist` that projected the phase away. -/
theorem depthDist_pos_of_phase_ne {q0 : ℤ} {n : ℕ+} (u v : DepthValue q0 n)
    (h : u.2.2 ≠ v.2.2) : 0 < depthDist u v := by
  have hphase : phaseDist u.2.2 v.2.2 ≠ 0 := fun hzero =>
    h ((phaseDist_eq_zero_iff _ _).mp hzero)
  have := phaseDist_le_depthDist u v
  omega

end D5.S1.Depth
