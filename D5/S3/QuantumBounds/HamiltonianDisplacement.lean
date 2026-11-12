/- GID: D5/S3/QuantumBounds/HamiltonianDisplacement
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/HamiltonianDisplacement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered Hamiltonian evolution bounds the actual overlap angle at every real time. -/

import D5.S3.QuantumBounds.FubiniStudyRecordTime
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! The actual Hamiltonian exponential satisfies the centered energy-variance angle bound. -/

set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousLinearMap.topologicalSpace
attribute [-instance] ContinuousLinearMap.uniformSpace

open Filter
open scoped Topology ComplexConjugate

noncomputable section
namespace D5.S3.QuantumBounds.HamiltonianDisplacement

private theorem projected_tangent_bound {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (a x w : V) (ha : ‖a‖ = 1) (hx : ‖x‖ = 1)
    (hw : inner ℝ x w = 0) :
    |inner ℝ a w| ≤ ‖w‖ * Real.sqrt (1 - (inner ℝ a x) ^ 2) := by
  have hp : ‖a - (inner ℝ a x) • x‖ ^ 2 = 1 - (inner ℝ a x) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, ha, hx]
    simp only [Real.norm_eq_abs, mul_one, one_pow, sq_abs]
    ring
  have hn : ‖a - (inner ℝ a x) • x‖ = Real.sqrt (1 - (inner ℝ a x) ^ 2) := by
    rw [← hp, Real.sqrt_sq (norm_nonneg _)]
  have hi : inner ℝ (a - (inner ℝ a x) • x) w = inner ℝ a w := by
    simp only [inner_sub_left, real_inner_smul_left, hw, mul_zero, sub_zero]
  calc
    |inner ℝ a w| = |inner ℝ (a - (inner ℝ a x) • x) w| := congrArg abs hi.symm
    _ ≤ ‖a - (inner ℝ a x) • x‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ = ‖w‖ * Real.sqrt (1 - (inner ℝ a x) ^ 2) := by rw [hn, mul_comm]

private theorem arccos_of_differential_bound (r d : ℝ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hr0 : r 0 = 1) (hr : ∀ s, |r s| ≤ 1)
    (hd : ∀ s, HasDerivAt r (d s) s)
    (hb : ∀ s, |d s| ≤ c * Real.sqrt (1 - (r s) ^ 2)) (t : ℝ) :
    Real.arccos (r t) ≤ c * |t| := by
  have hq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
      Real.arccos (q * r t) ≤ Real.arccos q + c * |t| := by
    have hi (s : ℝ) : |q * r s| < 1 := by
      rw [abs_mul, abs_of_nonneg hq0]
      exact (mul_le_mul_of_nonneg_left (hr s) hq0).trans_lt (by simpa using hq1)
    have hs (s : ℝ) : 0 < 1 - (q * r s) ^ 2 := by
      exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr (hi s))
    have hroot (s : ℝ) : q * Real.sqrt (1 - (r s) ^ 2) ≤
        Real.sqrt (1 - (q * r s) ^ 2) := by
      have hrs : 0 ≤ 1 - (r s) ^ 2 := by
        exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (hr s))
      have hq2 : q ^ 2 ≤ 1 := (sq_le_one_iff₀ hq0).mpr hq1.le
      have ha := Real.sq_sqrt hrs
      have hb' := Real.sq_sqrt (hs s).le
      have hleft : 0 ≤ q * Real.sqrt (1 - (r s) ^ 2) :=
        mul_nonneg hq0 (Real.sqrt_nonneg _)
      have hright := Real.sqrt_nonneg (1 - (q * r s) ^ 2)
      have hsq : (q * Real.sqrt (1 - (r s) ^ 2)) ^ 2 ≤
          (Real.sqrt (1 - (q * r s) ^ 2)) ^ 2 := by
        rw [mul_pow, ha, hb']
        nlinarith
      exact (sq_le_sq₀ hleft hright).mp hsq
    let f' := fun s => -(1 / Real.sqrt (1 - (q * r s) ^ 2)) * (q * d s)
    have hder (s : ℝ) : HasDerivAt (fun u => Real.arccos (q * r u)) (f' s) s := by
      have hh := HasDerivAt.comp (h := fun u : ℝ => q * r u) (h₂ := Real.arccos) s
        (Real.hasDerivAt_arccos (ne_of_gt (abs_lt.mp (hi s)).1)
          (ne_of_lt (abs_lt.mp (hi s)).2)) ((hd s).const_mul q)
      exact hh
    have hnorm (s : ℝ) : ‖f' s‖ ≤ c := by
      have hpos : 0 < Real.sqrt (1 - (q * r s) ^ 2) := Real.sqrt_pos.2 (hs s)
      have heq : ‖f' s‖ = q * |d s| / Real.sqrt (1 - (q * r s) ^ 2) := by
        dsimp [f']
        rw [abs_mul, abs_neg, abs_div, abs_one,
          abs_of_pos hpos, abs_mul, abs_of_nonneg hq0]
        ring
      rw [heq]
      apply (div_le_iff₀ hpos).2
      calc
        q * |d s| ≤ q * (c * Real.sqrt (1 - (r s) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hb s) hq0
        _ = c * (q * Real.sqrt (1 - (r s) ^ 2)) := by ring
        _ ≤ c * Real.sqrt (1 - (q * r s) ^ 2) :=
          mul_le_mul_of_nonneg_left (hroot s) hc
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (fun s _ => (hder s).hasDerivWithinAt)
      (fun s _ => hnorm s) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
    simp only [hr0, mul_one, sub_zero, Real.norm_eq_abs] at hm
    have := (le_abs_self (Real.arccos (q * r t) - Real.arccos q)).trans hm
    linarith
  have hseq := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hl : Tendsto (fun n : ℕ => Real.arccos (((n : ℝ) / (n + 1)) * r t))
      atTop (𝓝 (Real.arccos (r t))) := by
    simpa [Function.comp_def] using
      Real.continuous_arccos.continuousAt.tendsto.comp (hseq.mul_const (r t))
  have hu : Tendsto (fun n : ℕ => Real.arccos ((n : ℝ) / (n + 1)) + c * |t|)
      atTop (𝓝 (c * |t|)) := by
    simpa [Function.comp_def] using
      (Real.continuous_arccos.continuousAt.tendsto.comp hseq).add_const (c * |t|)
  exact le_of_tendsto_of_tendsto hl hu (Filter.Eventually.of_forall fun n =>
    hq _ (by positivity) ((div_lt_one (by positivity : (0 : ℝ) < n + 1)).2 (by linarith)))

/-- The Mandelstam–Tamm displacement bound for the actual exponential of a
finite-dimensional self-adjoint Hamiltonian. The fluctuation is centered in the
same initial unit vector; zero fluctuation and every real time are included. -/
theorem hamiltonian_displacement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (psi : E) (hpsi : ‖psi‖ = 1)
    (hbar : ℝ) (hhbar : 0 < hbar) (t : ℝ) :
    let mu : ℝ := (inner ℂ psi (A psi)).re
    let Delta : ℝ := ‖A psi - (mu : ℂ) • psi‖
    FubiniStudyRecordTime.fsAngle psi
      ((NormedSpace.exp ((-Complex.I * (t : ℂ) / (hbar : ℂ)) • A)) psi) ≤
      |t| * Delta / hbar := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  letI := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  let mu : ℝ := (inner ℂ psi (A psi)).re
  let B : E →L[ℂ] E := A - (mu : ℂ) • (1 : E →L[ℂ] E)
  let G : E →L[ℂ] E := (-Complex.I / (hbar : ℂ)) • B
  let U : ℝ → E →L[ℂ] E := fun s => NormedSpace.exp (s • G)
  let v : ℝ → E := fun s => U s psi
  let w : ℝ → E := fun s => U s (G psi)
  let c : ℝ := ‖A psi - (mu : ℂ) • psi‖ / hbar
  have hc : 0 ≤ c := div_nonneg (norm_nonneg _) hhbar.le
  have hB : IsSelfAdjoint B := by
    change star (A - (mu : ℂ) • (1 : E →L[ℂ] E)) = A - (mu : ℂ) • 1
    simp only [star_sub, star_smul, hA.star_eq, star_one, Complex.star_def,
      Complex.conj_ofReal]
  have hunit (s : ℝ) : U s ∈ unitary (E →L[ℂ] E) := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    have hg : G ∈ skewAdjoint (E →L[ℂ] E) :=
      IsSelfAdjoint.smul_mem_skewAdjoint (by
        change star (-Complex.I / (hbar : ℂ)) = -(-Complex.I / (hbar : ℂ))
        simp [star_div₀, neg_div]) hB
    change star (s • G) = -(s • G)
    rw [star_smul, star_trivial, show star G = -G from hg, smul_neg]
  have hv (s : ℝ) : ‖v s‖ = 1 := by
    exact (ContinuousLinearMap.norm_map_of_mem_unitary (hunit s) psi).trans hpsi
  have hspeed (s : ℝ) : ‖w s‖ = c := by
    rw [show w s = U s (G psi) from rfl,
      ContinuousLinearMap.norm_map_of_mem_unitary (hunit s)]
    dsimp [G, B, c]
    simp only [smul_apply, sub_apply,
      one_apply_eq_self, norm_smul, norm_div, norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhbar, one_div]
    ring
  have hmu : (mu : ℂ) = inner ℂ psi (A psi) :=
    hA.isSymmetric.coe_re_inner_self_apply psi
  have hhorizontal : inner ℂ psi (G psi) = 0 := by
    change inner ℂ psi ((-Complex.I / (hbar : ℂ)) •
      (A psi - (mu : ℂ) • psi)) = 0
    rw [inner_smul_right, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hpsi]
    simp [hmu]
  have horth (s : ℝ) : inner ℂ (v s) (w s) = 0 := by
    exact (ContinuousLinearMap.inner_map_map_of_mem_unitary (hunit s) psi (G psi)).trans
      hhorizontal
  have hder (s : ℝ) : HasDerivAt v (w s) s := by
    let L : (E →L[ℂ] E) →L[ℝ] E := (ContinuousLinearMap.apply ℂ E psi).restrictScalars ℝ
    exact L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_exp_smul_const G s)
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let r : ℝ → ℝ := fun s => inner ℝ psi (v s)
  let d : ℝ → ℝ := fun s => inner ℝ psi (w s)
  have hr0 : r 0 = 1 := by
    simp [r, v, U, hpsi]
  have hr (s : ℝ) : |r s| ≤ 1 := by
    have := abs_real_inner_le_norm psi (v s)
    simpa [r, hpsi, hv s] using this
  have hd (s : ℝ) : HasDerivAt r (d s) s := by
    simpa [r, d] using (hasDerivAt_const s psi).inner ℝ (hder s)
  have hb (s : ℝ) : |d s| ≤ c * Real.sqrt (1 - (r s) ^ 2) := by
    have ho : inner ℝ (v s) (w s) = 0 := by
      change (inner ℂ (v s) (w s)).re = 0
      rw [horth, Complex.zero_re]
    simpa [d, r, hspeed s] using projected_tangent_bound psi (v s) (w s) hpsi (hv s) ho
  have hangle : Real.arccos (r t) ≤ c * |t| :=
    arccos_of_differential_bound r d c hc hr0 hr hd hb t
  let alpha : ℂ := -Complex.I * (t : ℂ) / (hbar : ℂ)
  let beta : ℂ := Complex.I * ((t * mu / hbar : ℝ) : ℂ)
  have hsplit : t • G = alpha • A + beta • (1 : E →L[ℂ] E) := by
    change t • ((-Complex.I / (hbar : ℂ)) •
      (A - (mu : ℂ) • (1 : E →L[ℂ] E))) = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, smul_sub, smul_smul]
    have hcoef : (t : ℂ) * (-Complex.I / (hbar : ℂ)) = alpha := by
      dsimp [alpha]
      ring
    have hphasecoef : -(alpha * (mu : ℂ)) = beta := by
      dsimp [alpha, beta]
      push_cast
      ring
    change ((t : ℂ) * (-Complex.I / (hbar : ℂ))) • A -
      (((t : ℂ) * (-Complex.I / (hbar : ℂ))) * (mu : ℂ)) • (1 : E →L[ℂ] E) = _
    rw [hcoef, sub_eq_add_neg, ← neg_smul, hphasecoef]
  have hcomm : Commute (alpha • A) (beta • (1 : E →L[ℂ] E)) := by
    change (alpha • A) * (beta • 1) = (beta • 1) * (alpha • A)
    simp [smul_smul, mul_comm]
  have hephase : NormedSpace.exp (beta • (1 : E →L[ℂ] E)) =
      Complex.exp beta • (1 : E →L[ℂ] E) := by
    simpa only [Algebra.algebraMap_eq_smul_one, Complex.exp_eq_exp_ℂ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := E →L[ℂ] E) beta).symm
  have hvphase : v t = Complex.exp beta • (NormedSpace.exp (alpha • A) psi) := by
    change (NormedSpace.exp (t • G)) psi = _
    rw [hsplit, NormedSpace.exp_add_of_commute hcomm, hephase]
    simp
  have hphase : ‖Complex.exp beta‖ = 1 := by
    exact Complex.norm_exp_I_mul_ofReal (t * mu / hbar)
  have hoverlap : ‖inner ℂ psi (v t)‖ =
      ‖inner ℂ psi ((NormedSpace.exp (alpha • A)) psi)‖ := by
    rw [hvphase, inner_smul_right, norm_mul, hphase, one_mul]
  have hreal : r t ≤ ‖inner ℂ psi (v t)‖ := Complex.re_le_norm _
  dsimp only
  change Real.arccos ‖inner ℂ psi ((NormedSpace.exp (alpha • A)) psi)‖ ≤ _
  calc
    _ = Real.arccos ‖inner ℂ psi (v t)‖ := congrArg Real.arccos hoverlap.symm
    _ ≤ Real.arccos (r t) := Real.arccos_le_arccos hreal
    _ ≤ c * |t| := hangle
    _ = |t| * ‖A psi - (mu : ℂ) • psi‖ / hbar := by dsimp [c]; ring

#print axioms projected_tangent_bound
#print axioms arccos_of_differential_bound
#print axioms hamiltonian_displacement

end D5.S3.QuantumBounds.HamiltonianDisplacement
