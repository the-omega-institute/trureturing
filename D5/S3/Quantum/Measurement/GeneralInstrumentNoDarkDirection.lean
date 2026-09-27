/- GID: D5/S3/Quantum/Measurement/GeneralInstrumentNoDarkDirection
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/GeneralInstrumentNoDarkDirection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A general instrument has no definite dark direction iff its limit effect vanishes iff Tr(rho F) = 0 for every density rho. -/

import D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit

variable {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]

/-- **No definite dark direction.** For no-click Kraus operators `Q_a` and click Kraus operators
`L_i` with `∑ₐ Q_aᴴ Q_a + ∑ᵢ L_iᴴ L_i = I` and the limit `F` of the survival effects `S_N`, the
following are equivalent: the stable dark layer `D_d` is zero; `F = 0`; `I - S_d` is positive
definite; every density matrix `ρ` has `Tr(ρ F) = 0`. -/
theorem no_dark_direction_tfae (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : Tendsto (survival Q) atTop (𝓝 F)) :
    List.TFAE [darkLayer Q L d = ⊥, F = 0, (1 - survival Q d).PosDef,
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 → (ρ * F).trace = 0] := by
  classical
  obtain ⟨F', hF', hchain, hF'0, -, hfix', -, -⟩ := survival_tendsto_maximal_fixed_effect Q L hcomp
  obtain rfl : F = F' := tendsto_nhds_unique hF hF'
  obtain ⟨hlayer, hstable, -, -, hmaxV⟩ := darkLayer_closure Q L hcomp
  have hFpsd : F.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hF'0
  -- the quadratic form of a conjugated operator
  have hquad : ∀ (B P : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ),
      star v ⬝ᵥ ((Bᴴ * P * B) *ᵥ v) = star (B *ᵥ v) ⬝ᵥ (P *ᵥ (B *ᵥ v)) := by
    intro B P v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.star_mulVec]
  -- (i) the limit effect fixes every vector of the stable dark layer
  have hfixD : ∀ v ∈ darkLayer Q L d, F *ᵥ v = v := by
    intro v hv
    have hlim : Tendsto (fun N => survival Q N *ᵥ v) atTop (𝓝 (F *ᵥ v)) :=
      ((continuous_id.matrix_mulVec continuous_const).tendsto F).comp hF
    have hev : ∀ᶠ N in atTop, survival Q N *ᵥ v = v := by
      refine eventually_atTop.mpr ⟨d, fun N hN => ?_⟩
      have hmem : v ∈ darkLayer Q L N := by rw [hstable N hN]; exact hv
      rw [hlayer N, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hmem
      exact hmem.symm
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun N hN => hN.symm))
  -- (ii) a nonzero limit effect has a nonzero invariant dark subspace
  have hFzero : darkLayer Q L d = ⊥ → F = 0 := by
    intro hD
    by_contra hF0
    -- a vector with positive quadratic form
    obtain ⟨v, hv⟩ : ∃ v : Fin d → ℂ, F *ᵥ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hF0 (Matrix.ext fun i j => by simpa [Matrix.mulVec_single] using congrFun (h (Pi.single j 1)) i)
    let n : (Fin d → ℂ) → ℂ := fun w => star w ⬝ᵥ w
    let q : Matrix (Fin d) (Fin d) ℂ → (Fin d → ℂ) → ℂ := fun A w => star w ⬝ᵥ (A *ᵥ w)
    have hn_nonneg : ∀ w, 0 ≤ n w := fun w => dotProduct_star_self_nonneg w
    have hn_real : ∀ w, n w = ((n w).re : ℂ) := fun w =>
      Complex.ext rfl (by simpa using ((Complex.nonneg_iff.mp (hn_nonneg w)).2).symm)
    have hq_real : ∀ w, q F w = ((q F w).re : ℂ) := fun w =>
      Complex.ext rfl (by simpa using ((Complex.nonneg_iff.mp
        (hFpsd.dotProduct_mulVec_nonneg w)).2).symm)
    have hn_pos : ∀ w, w ≠ 0 → 0 < (n w).re := by
      intro w hw
      exact (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hw)).1
    have hscale : ∀ (t : ℝ) (w : Fin d → ℂ), q F ((t : ℂ) • w) = ((t ^ 2 : ℝ) : ℂ) * q F w ∧
        n ((t : ℂ) • w) = ((t ^ 2 : ℝ) : ℂ) * n w := by
      intro t w
      simp only [q, n, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      constructor <;> ring
    -- the Rayleigh quotient attains its maximum on the unit sphere
    let R : (Fin d → ℂ) → ℝ := fun w => (q F w).re / (n w).re
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    let _ : Nontrivial (Fin d → ℂ) := ⟨⟨v, 0, hv0⟩⟩
    have hsphere_ne : (Metric.sphere (0 : Fin d → ℂ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hRcont : ContinuousOn R (Metric.sphere (0 : Fin d → ℂ) 1) := by
      have hqc : Continuous fun w : Fin d → ℂ => (q F w).re :=
        Complex.continuous_re.comp (continuous_star.dotProduct (continuous_const.matrix_mulVec continuous_id))
      have hnc : Continuous fun w : Fin d → ℂ => (n w).re :=
        Complex.continuous_re.comp (continuous_star.dotProduct continuous_id)
      refine hqc.continuousOn.div hnc.continuousOn fun w hw => (hn_pos w ?_).ne'
      rintro rfl
      simp at hw
    obtain ⟨v₀, hv₀, hmax⟩ := (isCompact_sphere (0 : Fin d → ℂ) 1).exists_isMaxOn hsphere_ne hRcont
    set lam := R v₀ with hlam
    have hv₀ne : v₀ ≠ 0 := by rintro rfl; simp at hv₀
    have hRscale : ∀ w, w ≠ 0 → R ((((‖w‖⁻¹ : ℝ)) : ℂ) • w) = R w := by
      intro w hw
      simp only [R, (hscale _ _).1, (hscale _ _).2, Complex.re_ofReal_mul]
      have ht : (‖w‖⁻¹ : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr hw))
      field_simp
    have hbound : ∀ w, (q F w).re ≤ lam * (n w).re := by
      intro w
      by_cases hw : w = 0
      · subst hw; simp [q, n]
      · have hmem : (((‖w‖⁻¹ : ℝ)) : ℂ) • w ∈ Metric.sphere (0 : Fin d → ℂ) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
        have h : R ((((‖w‖⁻¹ : ℝ)) : ℂ) • w) ≤ lam := hmax hmem
        rw [hRscale w hw] at h
        have hpos := hn_pos w hw
        have : (q F w).re / (n w).re ≤ lam := h
        rwa [div_le_iff₀ hpos] at this
    have hlam_pos : 0 < lam := by
      have hqpos : 0 < (q F v).re := by
        have h0 := (Complex.nonneg_iff.mp (hFpsd.dotProduct_mulVec_nonneg v)).1
        refine lt_of_le_of_ne h0 fun h => hv ?_
        have : q F v = 0 := by rw [hq_real v, ← h]; simp
        exact (hFpsd.dotProduct_mulVec_zero_iff v).mp this
      have := hbound v
      have hnv := hn_pos v hv0
      nlinarith
    -- the gap operator `λI - F` is positive semidefinite
    let P : Matrix (Fin d) (Fin d) ℂ := (lam : ℂ) • 1 - F
    have hqP : ∀ w, q P w = (lam : ℂ) * n w - q F w := by
      intro w
      simp only [q, n, P, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
    have hPpsd : P.PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
      · simp only [P, IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
          Complex.star_def, Complex.conj_ofReal, hFpsd.1.eq]
      · change 0 ≤ q P w
        rw [hqP, hn_real w, hq_real w, Complex.nonneg_iff]
        refine ⟨?_, ?_⟩
        · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero]
          linarith [hbound w]
        · simp
    have hv₀P : P *ᵥ v₀ = 0 := by
      have heq : (q F v₀).re = lam * (n v₀).re := by
        rw [hlam]
        simp only [R]
        field_simp [(hn_pos v₀ hv₀ne).ne']
      let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) F
      let x₀ : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 v₀
      have hT : IsSelfAdjoint T :=
        hFpsd.1.isSelfAdjoint.map (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
      have hTq : ∀ x : EuclideanSpace ℂ (Fin d),
          T.reApplyInnerSelf x = (q F (WithLp.ofLp x)).re := by
        intro x
        rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
        rw [← WithLp.toLp_ofLp (p := 2) x]
        simp only [T, q, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp,
          dotProduct_comm]
        rfl
      have hn' : ∀ x : EuclideanSpace ℂ (Fin d), (n (WithLp.ofLp x)).re = ‖x‖ ^ 2 := by
        intro x
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
        rw [← WithLp.toLp_ofLp (p := 2) x]
        simp only [n, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
        rfl
      have hmaxT : IsMaxOn T.reApplyInnerSelf (Metric.sphere 0 ‖x₀‖) x₀ := by
        intro x hx
        change T.reApplyInnerSelf x ≤ T.reApplyInnerSelf x₀
        rw [hTq, hTq]
        have hxnorm : ‖x‖ = ‖x₀‖ := by
          simpa only [mem_sphere_zero_iff_norm] using hx
        calc
          (q F (WithLp.ofLp x)).re ≤ lam * (n (WithLp.ofLp x)).re := hbound _
          _ = lam * ‖x‖ ^ 2 := by rw [hn']
          _ = lam * ‖x₀‖ ^ 2 := by rw [hxnorm]
          _ = lam * (n v₀).re := by rw [hn' x₀]
          _ = (q F v₀).re := heq.symm
      have hx₀ne : x₀ ≠ 0 := by simpa only [x₀, ne_eq, WithLp.toLp_eq_zero]
      have hray : T.rayleighQuotient x₀ = lam := by
        change T.reApplyInnerSelf x₀ / ‖x₀‖ ^ 2 = lam
        rw [hTq]
        change (q F v₀).re / ‖x₀‖ ^ 2 = lam
        rw [heq, hn' x₀]
        field_simp [norm_ne_zero_iff.mpr hx₀ne]
      have heig := hT.eq_smul_self_of_isLocalExtrOn (Or.inr hmaxT.localize)
      rw [hray] at heig
      have hFv : F *ᵥ v₀ = (lam : ℂ) • v₀ := by
        have h := congrArg WithLp.ofLp heig
        simp only [T, x₀, Matrix.toEuclideanCLM_toLp, WithLp.ofLp_toLp,
          WithLp.ofLp_smul] at h
        ext i
        exact congrFun h i
      simp only [P, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hFv, sub_self]
    -- the kernel of the gap operator is killed by every click and invariant under every no-click
    let M : Submodule ℂ (Fin d → ℂ) := LinearMap.ker P.mulVecLin
    have hM : ∀ w ∈ M, (∀ i, L i *ᵥ w = 0) ∧ ∀ a, Q a *ᵥ w ∈ M := by
      intro w hw
      have hPw : P *ᵥ w = 0 := hw
      have hqw : q P w = 0 := by simp [q, hPw]
      have hfixq : q F w = ∑ a, q F (Q a *ᵥ w) := by
        conv_lhs => rw [← hfix']
        simp only [q, noClickDual, Matrix.sum_mulVec, dotProduct_sum, hquad]
      have hcompq : n w = ∑ a, n (Q a *ᵥ w) + ∑ i, n (L i *ᵥ w) := by
        have h := congrArg (fun A => star w ⬝ᵥ (A *ᵥ w)) hcomp
        simp only [Matrix.add_mulVec, Matrix.sum_mulVec, dotProduct_add, dotProduct_sum,
          Matrix.one_mulVec] at h
        have hQn : ∀ a, star w ⬝ᵥ (((Q a)ᴴ * Q a) *ᵥ w) = n (Q a *ᵥ w) := fun a => by
          simpa [n] using hquad (Q a) 1 w
        have hLn : ∀ i, star w ⬝ᵥ (((L i)ᴴ * L i) *ᵥ w) = n (L i *ᵥ w) := fun i => by
          simpa [n] using hquad (L i) 1 w
        simp only [hQn, hLn] at h
        exact h.symm
      have hsplit : ∀ a, q F (Q a *ᵥ w) = (lam : ℂ) * n (Q a *ᵥ w) - q P (Q a *ᵥ w) := by
        intro a; rw [hqP]; ring
      have hzero : (lam : ℂ) * ∑ i, n (L i *ᵥ w) + ∑ a, q P (Q a *ᵥ w) = 0 := by
        have h1 : q F w = (lam : ℂ) * n w := by rw [hqP] at hqw; linear_combination -hqw
        rw [hfixq, hcompq, Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sub_distrib,
          ← Finset.mul_sum] at h1
        linear_combination -h1
      have hlamC : (0 : ℂ) ≤ (lam : ℂ) := Complex.zero_le_real.mpr hlam_pos.le
      have hnn1 : 0 ≤ (lam : ℂ) * ∑ i, n (L i *ᵥ w) :=
        mul_nonneg hlamC (Finset.sum_nonneg fun i _ => hn_nonneg _)
      have hnn2 : 0 ≤ ∑ a, q P (Q a *ᵥ w) :=
        Finset.sum_nonneg fun a _ => hPpsd.dotProduct_mulVec_nonneg _
      obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg hnn1 hnn2).mp hzero
      have hlamne : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam_pos.ne'
      have h1' : ∑ i, n (L i *ᵥ w) = 0 := (mul_eq_zero.mp h1).resolve_left hlamne
      refine ⟨fun i => ?_, fun a => ?_⟩
      · have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hn_nonneg (L i *ᵥ w)).mp h1' i
          (Finset.mem_univ i)
        exact dotProduct_star_self_eq_zero.mp this
      · have := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
          hPpsd.dotProduct_mulVec_nonneg (Q a *ᵥ w)).mp h2 a (Finset.mem_univ a)
        exact (hPpsd.dotProduct_mulVec_zero_iff _).mp this
    have hMle : M ≤ darkLayer Q L d :=
      hmaxV M (fun i w hw => (hM w hw).1 i) (fun a w hw => (hM w hw).2 a)
    have : v₀ ∈ darkLayer Q L d := hMle hv₀P
    rw [hD] at this
    exact hv₀ne ((Submodule.mem_bot ℂ).mp this)
  -- (iii) the survival defect at `d` is positive semidefinite with kernel the dark layer
  have hdefect : (1 - survival Q d).PosSemidef := Matrix.le_iff.mp (hchain d).2.2.1
  have hkerd : ∀ v, v ∈ darkLayer Q L d ↔ (1 - survival Q d) *ᵥ v = 0 := by
    intro v
    rw [hlayer d, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  -- (iv) testing against rank-one densities
  tfae_have 1 → 2 := hFzero
  tfae_have 2 → 1 := by
    intro hF0
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have := hfixD v hv
    rw [hF0, Matrix.zero_mulVec] at this
    exact this.symm
  tfae_have 1 → 3 := by
    intro hD
    refine PosDef.of_dotProduct_mulVec_pos hdefect.1 fun x hx => ?_
    refine lt_of_le_of_ne (hdefect.dotProduct_mulVec_nonneg x) fun h => hx ?_
    have hk : (1 - survival Q d) *ᵥ x = 0 := (hdefect.dotProduct_mulVec_zero_iff x).mp h.symm
    have hmem := (hkerd x).mpr hk
    rw [hD] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  tfae_have 3 → 1 := by
    intro hpd
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    by_contra hv0
    have hk := (hkerd v).mp hv
    have := hpd.dotProduct_mulVec_pos hv0
    rw [hk, dotProduct_zero] at this
    exact lt_irrefl 0 this
  tfae_have 2 → 4 := by
    intro hF0 ρ _ _
    rw [hF0, Matrix.mul_zero, Matrix.trace_zero]
  tfae_have 4 → 2 := by
    intro hρ
    have hFw : ∀ w : Fin d → ℂ, F *ᵥ w = 0 := by
      intro w
      by_cases hw : w = 0
      · rw [hw, Matrix.mulVec_zero]
      · have hnw : 0 < (star w ⬝ᵥ w).re := by
          exact (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hw)).1
        have hnwC : star w ⬝ᵥ w = ((star w ⬝ᵥ w).re : ℂ) := Complex.ext rfl
          (by simpa using ((Complex.nonneg_iff.mp (dotProduct_star_self_nonneg w)).2).symm)
        let c : ℂ := (((star w ⬝ᵥ w).re)⁻¹ : ℝ)
        have hc : (0 : ℂ) ≤ c := Complex.zero_le_real.mpr (inv_nonneg.mpr hnw.le)
        let ρ : Matrix (Fin d) (Fin d) ℂ := c • vecMulVec w (star w)
        have hρpsd : ρ.PosSemidef := (posSemidef_vecMulVec_self_star w).smul hc
        have hρtr : ρ.trace = 1 := by
          simp only [ρ, Matrix.trace_smul, smul_eq_mul, c]
          rw [Matrix.trace_vecMulVec, dotProduct_comm w (star w)]
          rw [hnwC]
          push_cast
          simp only [Complex.ofReal_re]
          exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hnw.ne')
        have h := hρ ρ hρpsd hρtr
        simp only [ρ, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h
        rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
          dotProduct_comm w (star w ᵥ* F), ← dotProduct_mulVec] at h
        have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hnw.ne')
        exact (hFpsd.dotProduct_mulVec_zero_iff w).mp ((mul_eq_zero.mp h).resolve_left hc0)
    exact Matrix.ext fun i j => by
      simpa [Matrix.mulVec_single] using congrFun (hFw (Pi.single j 1)) i
  tfae_finish

#print axioms no_dark_direction_tfae

end D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
