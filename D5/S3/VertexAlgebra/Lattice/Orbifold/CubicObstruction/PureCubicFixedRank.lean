/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/PureCubicFixedRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed ranks of three cubics in a commuting coset sum to the ambient rank. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
import Mathlib.Tactic.Abel
import OmegaBuild.Commands

/-!
The cyclic fixed-space averages for `A`, `A * C`, and `A * C ^ 2` sum to
the identity when `C` has zero cyclic norm and commutes with `A`. Taking
traces computes their total fixed rank. In the application to P48p, the
group structure and the allowed ranks come from Nebe (arXiv:1212.0865,
Theorem 3.6, proof (B), and Proposition 4.8).
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.PureCubicFixedRank

open private orderThree_fixedRank_eq_trace_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

private theorem cubic_averages_add_eq_one
    (A C : Module.End K V) (hC : C ^ 3 = 1) (hComm : Commute A C)
    (hNorm : 1 + C + C ^ 2 = 0) :
    let average (T : Module.End K V) := (3 : K)⁻¹ • (1 + T + T ^ 2)
    average A + average (A * C) + average (A * C ^ 2) = 1 := by
  dsimp only
  have hCfour : (C ^ 2) ^ 2 = C := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_succ, hC, one_mul]
  have hNormSq : 1 + C ^ 2 + (C ^ 2) ^ 2 = 0 := by
    rw [hCfour, add_right_comm, hNorm]
  have hSum :
      (1 + A + A ^ 2) + (1 + A * C + (A * C) ^ 2) + (1 + A * C ^ 2 + (A * C ^ 2) ^ 2) =
        (1 + 1 + 1 : Module.End K V) := by
    rw [hComm.mul_pow, (hComm.pow_right 2).mul_pow]
    calc
      _ = 1 + 1 + 1 + A * (1 + C + C ^ 2) + A ^ 2 * (1 + C ^ 2 + (C ^ 2) ^ 2) := by
        simp only [mul_add, mul_one]
        abel
      _ = _ := by rw [hNorm, hNormSq, mul_zero, mul_zero, add_zero, add_zero]
  have hThree : (1 + 1 + 1 : Module.End K V) = (3 : K) • (1 : Module.End K V) := by
    rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  rw [← smul_add, ← smul_add, hSum, hThree, smul_smul,
    inv_mul_cancel₀ (by norm_num : (3 : K) ≠ 0), one_smul]

/-- The three endomorphisms in this cubic coset have total fixed rank equal
to the ambient dimension. -/
theorem fixed_rank_sum_of_commuting_cubics [FiniteDimensional K V]
    (A C : Module.End K V) (hA : A ^ 3 = 1) (hC : C ^ 3 = 1) (hComm : Commute A C)
    (hNorm : 1 + C + C ^ 2 = 0) :
    Module.finrank K (LinearMap.ker (A - 1)) +
      Module.finrank K (LinearMap.ker (A * C - 1)) +
      Module.finrank K (LinearMap.ker (A * C ^ 2 - 1)) = Module.finrank K V := by
  have hAC : (A * C) ^ 3 = 1 := by rw [hComm.mul_pow, hA, hC, one_mul]
  have hACSq : (A * C ^ 2) ^ 3 = 1 := by
    rw [(hComm.pow_right 2).mul_pow, pow_right_comm C 2 3, hA, hC, one_pow, one_mul]
  have hTrace (T : Module.End K V) (hT : T ^ 3 = 1) :
      LinearMap.trace K V ((3 : K)⁻¹ • (1 + T + T ^ 2)) =
        (Module.finrank K (LinearMap.ker (T - 1)) : K) := by
    rw [map_smul, map_add, map_add, LinearMap.trace_one]
    exact (orderThree_fixedRank_eq_trace_sum T hT).symm
  have h := congrArg (LinearMap.trace K V) (cubic_averages_add_eq_one A C hC hComm hNorm)
  dsimp only at h
  rw [map_add, map_add, hTrace A hA, hTrace (A * C) hAC, hTrace (A * C ^ 2) hACSq,
    LinearMap.trace_one] at h
  exact_mod_cast h

/-- In dimension 48, if the only allowed fixed ranks in the cubic coset
are zero and sixteen, each of its three fixed ranks is sixteen. -/
theorem pure_cubic_fixed_ranks_eq_sixteen [FiniteDimensional K V]
    (A C : Module.End K V) (hA : A ^ 3 = 1) (hC : C ^ 3 = 1) (hComm : Commute A C)
    (hNorm : 1 + C + C ^ 2 = 0) (hDim : Module.finrank K V = 48)
    (hRanks : ∀ T ∈ ({A, A * C, A * C ^ 2} : Set (Module.End K V)),
      Module.finrank K (LinearMap.ker (T - 1)) = 0 ∨
        Module.finrank K (LinearMap.ker (T - 1)) = 16) :
    Module.finrank K (LinearMap.ker (A - 1)) = 16 ∧
      Module.finrank K (LinearMap.ker (A * C - 1)) = 16 ∧
      Module.finrank K (LinearMap.ker (A * C ^ 2 - 1)) = 16 := by
  have hSum := fixed_rank_sum_of_commuting_cubics A C hA hC hComm hNorm
  have hRankA := hRanks A (by simp)
  have hRankAC := hRanks (A * C) (by simp)
  have hRankACSq := hRanks (A * C ^ 2) (by simp)
  omega

#print axioms fixed_rank_sum_of_commuting_cubics
#print axioms pure_cubic_fixed_ranks_eq_sixteen

end D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.PureCubicFixedRank
