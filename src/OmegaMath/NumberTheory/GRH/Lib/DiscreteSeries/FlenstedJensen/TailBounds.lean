import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.CuspKernel.SchurOrthogonality
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Explicit Lipschitz bound for the coefficient; crude bound for degree times tail
integrals. -/

open Fintype GlModule MatMul MeasureTheory Ring U Matrix.Norms.L2Operator

variable {n} [Fintype n] {ε l} [Nonempty n] {B} [hg : @HCParam.HasLargeGap n _ ε l B] {L : ℕ}
  (hL : ∀ a, |l a| ≤ L) (x g : USign ε)

include B hL

/-- Let n ≥ 1 and l = 2λ be a parameter of gap 500n³ + B with all |l_a| ≤ L. For x, g in U(diag
ε): |ψ_λ(xg) − ψ_λ(x)| ≤ 100(n+L+1)⁵‖g − 1‖, in the operator norm. -/
lemma norm_dsCoeff_sub_le : ‖l.dsCoeff (x * g :) - l.dsCoeff x‖ ≤ 100 *
  (card n + L + 1) ^ 5 * ‖g.1.1 - 1‖ := by
  let A := g.1.1 - 1; by_cases! a : 1 ≤ ‖A‖
  grw [norm_sub_le, norm_dsCoeff_le_one, norm_dsCoeff_le_one, ← a] <;> norm_cast; lia
  let c (t : ℝ) : USign ε :=
    of IsHermInvolution.isUnit (1 + t • A * (1 - ((t - 1) * 2⁻¹) • A)⁻¹ʳ) (by
    unfold inverse; split <;> [nth_rw 1 3 [← ‹IsUnit _›.mul_val_inv]; simp]
    rw [← add_mul, gram_mul, gram_inv_of_gram_eq]
    simp [A, mem_U.1]; module)
  refine (forall₂_and.1 ?_).elim
    (by simpa [A, c] using (convex_Icc ..).norm_image_sub_le_of_norm_deriv_le (f :=
    (l.dsCoeffSmooth.1 <| x * c ·)) · · unitInterval.zero_mem unitInterval.one_mem)
  intro t ⟨_, ht⟩; have b : ‖((t - 1) * 2⁻¹) • A‖ ≤ 2⁻¹ := by grw [norm_smul, a]; simp; grind
  let u := Units.oneSub _ (b.trans_lt (by bound))
  obtain ⟨j : ‖u⁻¹.1‖ ≤ 2, ⟨v, _, w⟩, _⟩ := tsum_of_norm_bounded hasSum_geometric_two (by
    grw [norm_pow_le _ ·, b]; simp), hg.isUnitaryCasimirGe_dsAction,
    hasFDerivAt_ringInverse (𝕜 := ℝ) u
  refine (fun d ↦ ⟨d.differentiableAt, d.deriv ▸ (w ..).trans
    (((isKHighest_dsGenerator hg).norm_apply_le_of_mem_filtration v (abs_lowestKType_le
    hg hL) (s := 0) self_mem_filtration _).2.trans ?_)⟩) (hasDerivAt_curve _ (.congr_deriv
    (HasFDerivAt.hasDerivAt (by simp [c]; fun_prop)) (Units.mul_inv_cancel_left ..).symm))
  simp [-Matrix.coe_units_inv]
  repeat first | grw [norm_mul_le] | grw [norm_add_le] | simp only [*, c, val_of_coe,
    ← Subgroup.coe_inv, U.norm_inv, norm_smul, Real.norm_of_nonneg] | erw [inverse_unit u]
  nth_grw 1 2 4 [a, j, j, ht, ht]; simp [A, ← sub_nonneg]; ring; bound

lemma half_le_norm_dsCoeff {β : ℝ} (b : card n + L + 1 ≤ β) {g : USign ε} (h : ‖g.1.1 - 1‖ ≤
  (200 * β ^ 5)⁻¹) : 2⁻¹ ≤ ‖l.dsCoeff g‖ := have t := norm_dsCoeff_sub_le hL 1 g
  by grw [← abs_norm_sub_norm_le, h, ← b] at t
     simp [field] at t; grind

lemma measure_ball_le_integral_dsCoeff {S} [Group.{0} S] [MeasurableSpace S] [MeasurableMul S] (ν :
  Measure S) [ν.IsMulRightInvariant] (j : S →* USign ε) (i : Integrable (‖l.dsCoeff <| j ·‖ ^ 2) ν)
  r (hr : r ≥ 1) : ν {s | ‖(j s).1.1‖ ≤ r} ≤ .ofReal ((2000 * (card n + L + 1) ^ 6 * r ^ 2) ^
  (2 * card n ^ 2)) * .ofReal (∫ s, 4 * ‖l.dsCoeff (j s)‖ ^ 2 ∂ν) := by
  grw [← (i.const_mul _).measure_le_integral (.of_forall (by simp)) fun _ ↦
    (by grw [← half_le_norm_dsCoeff hL le_rfl ·]; grind)]
  apply (measure_ball_le_covering ν j 1 (by bound) hr _).trans' <;> simp [field]; grind

/-- For l=2λ of gap 500n³+B with all |l_a| ≤ L and a natural number c > 8n², the function
deg_λ·(2/‖g‖)^c is integrable on U(diag ε), with integral at most 8(2000(n+L+1)⁶)^{2n²}·2^c. -/
lemma integral_tail_le c (hc : 8 * card n ^ 2 < c) : let f (g : USign ε) :=
    l.formalDegree * (2 / ‖g.1.1‖) ^
    c; Integrable f ∧ ∫ g, f g ≤ 8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ c := by
  rcases formalDegree_pos hg, integral_rpow_neg_le_of_layers c (one_le_norm ·)
    (measure_ball_le_integral_dsCoeff hL _ (.id _)
    (hg.memLp l.dsGenerator).norm.integrable_sq) 2 nofun
  simp_all [formalDegree, div_eq_mul_inv, mul_pow, Integrable.const_mul, le_of_lt]
  field; grind
