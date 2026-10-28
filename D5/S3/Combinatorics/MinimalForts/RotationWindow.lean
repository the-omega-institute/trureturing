/- GID: D5/S3/Combinatorics/MinimalForts/RotationWindow
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/RotationWindow
   mirror-E: none(waiver:compactness-proof)
   anchors: [mathlib/module/Mathlib.Topology.Instances.AddCircle.DenseSubgroup]
   utility: none
   digest: Irrational circle rotations approximate all targets uniformly in translated finite windows. -/

import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! Compactness turns a dense integer rotation into a uniformly bounded approximation window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.RotationWindow

/-- Every sufficiently large translated window approximates every point of the circle. -/
private theorem uniform_rotation_window (p b : ℝ) (hp : 0 < p) (hb : Irrational (b / p)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ∀ q : AddCircle p, ∃ x : ℤ,
        (N : ℤ) ≤ x ∧ x ≤ 3 * (N : ℤ) ∧ dist (x • (b : AddCircle p)) q < ε := by
  classical
  letI : Fact (0 < p) := ⟨hp⟩
  have hd : DenseRange (fun j : ℤ => j • (b : AddCircle p)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hb
  intro ε hε
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun j : ℤ => Metric.ball (j • (b : AddCircle p)) ε)
    (fun _ => Metric.isOpen_ball) (by
      intro q _
      obtain ⟨j, hj⟩ := hd.exists_dist_lt q hε
      exact Set.mem_iUnion.mpr ⟨j, hj⟩)
  refine ⟨s.sup Int.natAbs, ?_⟩
  intro N hN q
  have hc := hs (Set.mem_univ (q - (2 * (N : ℤ)) • (b : AddCircle p)))
  obtain ⟨j, hj, hdist⟩ := Set.mem_iUnion₂.mp hc
  have hjabs : j.natAbs ≤ N := (Finset.le_sup (f := Int.natAbs) hj).trans hN
  have hjbound : |j| ≤ (N : ℤ) := by
    have hc : (j.natAbs : ℤ) ≤ (N : ℤ) := Int.ofNat_le.mpr hjabs
    simpa only [Int.natCast_natAbs] using hc
  have hjlo := (abs_le.mp hjbound).1
  have hjhi := (abs_le.mp hjbound).2
  refine ⟨j + 2 * (N : ℤ), by omega, by omega, ?_⟩
  have he : dist ((j + 2 * (N : ℤ)) • (b : AddCircle p)) q =
      dist (q - (2 * (N : ℤ)) • (b : AddCircle p)) (j • (b : AddCircle p)) := by
    calc
      dist ((j + 2 * (N : ℤ)) • (b : AddCircle p)) q =
          dist q (j • (b : AddCircle p) + (2 * (N : ℤ)) • (b : AddCircle p)) := by
            rw [add_zsmul, dist_comm]
      _ = _ := by
        simp only [dist_eq_norm]
        congr 1
        abel
  rw [he]
  exact hdist

/-- Circle approximation lifts to an actual integer multiple of the period in real units. -/
theorem uniform_real_window (p b : ℝ) (hp : 0 < p) (hb : Irrational (b / p)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N : ℕ, M ≤ N → ∀ T : ℝ,
      ∃ x z : ℤ, (N : ℤ) ≤ x ∧ x ≤ 3 * (N : ℤ) ∧
        |(x : ℝ) * b + (z : ℝ) * p - T| < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := uniform_rotation_window p b hp hb ε hε
  refine ⟨M, fun N hN T => ?_⟩
  obtain ⟨x, hxlo, hxhi, hx⟩ := hM N hN (T : AddCircle p)
  let z : ℤ := -round (p⁻¹ * ((x : ℝ) * b - T))
  refine ⟨x, z, hxlo, hxhi, ?_⟩
  have he : dist (x • (b : AddCircle p)) (T : AddCircle p) =
      |(x : ℝ) * b + (z : ℝ) * p - T| := by
    rw [dist_eq_norm, ← AddCircle.coe_zsmul, zsmul_eq_mul, ← AddCircle.coe_sub,
      AddCircle.norm_eq]
    dsimp [z]
    push_cast
    congr 1
    ring
  rwa [← he]

end D5.S3.Combinatorics.MinimalForts.RotationWindow
