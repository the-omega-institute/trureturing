/- GID: D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Quadratic witnesses for a maximally mixed qubit endpoint. -/

import D5.S3.Quantum.Entanglement.Marginals.RationalQubitProjector
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.SumFourSquares

/-! A four-squares construction of the rational projector witness for a mixed endpoint. -/

open Matrix
open scoped ComplexOrder Quaternion
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension (RationalEntry)
open D5.S3.Quantum.Entanglement.Marginals.RationalQubitProjector
open D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint

private abbrev Bloch := Fin 3 → ℚ

private theorem four_rational_squares (q : ℚ) (hq : 0 ≤ q) :
    ∃ p r s t : ℚ, p ^ 2 + r ^ 2 + s ^ 2 + t ^ 2 = q := by
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  obtain ⟨p, r, s, t, h⟩ := Nat.sum_four_squares (q.num.toNat * q.den)
  have hnat : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hcast : (p : ℚ) ^ 2 + (r : ℚ) ^ 2 + (s : ℚ) ^ 2 + (t : ℚ) ^ 2 =
      (q.num : ℚ) * (q.den : ℚ) := by
    have hc := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at hc
    rw [hnat] at hc
    exact hc
  have hqeq : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden).mp q.num_div_den
  rw [hqeq] at hcast
  refine ⟨p / (q.den : ℚ), r / (q.den : ℚ), s / (q.den : ℚ),
    t / (q.den : ℚ), ?_⟩
  field_simp
  linear_combination hcast

private theorem exists_nonzero_perpendicular (c u : Bloch) :
    ∃ v : Bloch, v ≠ 0 ∧ c ⬝ᵥ v = 0 ∧ u ⬝ᵥ v = 0 := by
  let A : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of ![c, u]
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro hk
    have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hk)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
    omega
  obtain ⟨v, hv, hv_ne⟩ := (LinearMap.ker A.mulVecLin).ne_bot_iff.mp hker
  have hv_eq : A *ᵥ v = 0 := LinearMap.mem_ker.mp hv
  exact ⟨v, hv_ne, congrFun hv_eq 0, congrFun hv_eq 1⟩

private theorem mixed_endpoint_witness (c : Bloch) (hunit : c ⬝ᵥ c < 1) :
    ∃ y v : Bloch, 0 < y ⬝ᵥ y ∧ c ⬝ᵥ v = 0 ∧
      y ⬝ᵥ y = (1 - c ⬝ᵥ c) * (v ⬝ᵥ v) := by
  let d : ℚ := 1 - c ⬝ᵥ c
  have hd : 0 < d := sub_pos.mpr hunit
  obtain ⟨p, r, s, t, hsum⟩ := four_rational_squares d hd.le
  let H : ℍ[ℚ] := ⟨p, r, s, t⟩
  let u : Bloch := ![r, s, t]
  obtain ⟨v, hv, hcv, huv⟩ := exists_nonzero_perpendicular c u
  let V : ℍ[ℚ] := ⟨0, v 0, v 1, v 2⟩
  let W := H * V
  let y : Bloch := ![W.imI, W.imJ, W.imK]
  have hw : W.re = 0 := by
    simp only [W, Quaternion.re_mul, H, V, mul_zero, zero_sub]
    simp [u, dotProduct, Fin.sum_univ_three] at huv
    linarith only [huv]
  have hH : Quaternion.normSq H = d := by
    simpa only [Quaternion.normSq_def', H] using hsum
  have hnorm : y ⬝ᵥ y = d * (v ⬝ᵥ v) := by
    have hmul := map_mul Quaternion.normSq H V
    rw [← show W = H * V from rfl, hH, Quaternion.normSq_def', hw] at hmul
    simpa [Quaternion.normSq_def', V, y, dotProduct,
      Fin.sum_univ_three, pow_two] using hmul
  have hv_pos : 0 < v ⬝ᵥ v := by
    have hv_nonneg : 0 ≤ v ⬝ᵥ v := by
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    exact lt_of_le_of_ne hv_nonneg (Ne.symm fun h => hv (dotProduct_self_eq_zero.mp h))
  exact ⟨y, v, hnorm.symm ▸ mul_pos hd hv_pos, hcv, hnorm⟩

/-- A maximally mixed endpoint and a distinct positive-definite endpoint
with rational Bloch coordinates have a rational joint state of rank exactly two. -/
theorem rational_rank_two_of_maximally_mixed_endpoint (c : Fin 3 → ℚ)
    (hc : 0 < c ⬝ᵥ c) (hunit : c ⬝ᵥ c < 1) :
    ∃ T : Matrix (Bool × Bool) (Bool × Bool) ℂ, T.PosSemidef ∧ T.rank = 2 ∧
      (∀ i j, RationalEntry (T i j)) ∧
      partialTraceRight T = (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) ∧
      partialTraceLeft T = (1 / 2 : ℂ) • (1 + rationalBlochMatrix c) := by
  obtain ⟨y, v, hy, hcv, hq⟩ := mixed_endpoint_witness c hunit
  have hstrict : (0 : Bloch) ⬝ᵥ 0 < c ⬝ᵥ c := by simpa only [zero_dotProduct] using hc
  have hzero : rationalBlochMatrix 0 = 0 := by
    unfold rationalBlochMatrix
    have heq : (WithLp.toLp 2 fun _ : Fin 3 => (0 : ℝ)) =
        (0 : EuclideanSpace ℝ (Fin 3)) := by
      apply (WithLp.equiv 2 _).injective
      funext i
      simp
    simp [heq]
  simpa only [hzero, add_zero] using
    rational_rank_two_of_quadratic_witness 0 c y v hstrict hy
      (by simp only [zero_dotProduct, hcv]) (by simpa only [hcv, zero_pow (by decide : 2 ≠ 0),
        add_zero] using hq)

end D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint
