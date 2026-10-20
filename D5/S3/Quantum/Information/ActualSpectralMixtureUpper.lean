/- GID: D5/S3/Quantum/Information/ActualSpectralMixtureUpper
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualSpectralMixtureUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed amplitude mixtures satisfy the pointwise spectral SLD upper bound. -/

import D5.S3.Quantum.Information.ActualPureQubitGeometry
open scoped InnerProductSpace ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.ActualSpectralMixtureUpper
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

/-- The actual matrix mixture obeys extended convexity at singular and rank-changing points. -/
theorem actual_spectral_mixture_upper {n J : Type*} [Fintype n] [DecidableEq n] [Fintype J]
    (rho : J → ℝ → Matrix n n ℂ) (g : J → ℝ → ℝ) (t : ℝ)
    (hrd : ∀ i, DifferentiableAt ℝ (rho i) t)
    (hgd : ∀ i, DifferentiableAt ℝ (g i) t)
    (hr : ∀ᶠ u in 𝓝 t, ∀ i, (rho i u).PosSemidef ∧ trace (rho i u) = 1)
    (hg : ∀ᶠ u in 𝓝 t, ∑ i, g i u ^ 2 = 1) :
    let M : ℝ → Matrix n n ℂ := fun u => ∑ i, (g i u ^ 2) • rho i u
    ∃ hM : (M t).PosSemidef, trace (M t) = 1 ∧ DifferentiableAt ℝ M t ∧
      deriv M t = ∑ i, ((2 * g i t * deriv (g i) t) • rho i t +
        (g i t ^ 2) • deriv (rho i) t) ∧
      spectralQFI (M t) (deriv M t) hM ≤
        (∑ i, g i t ^ 2 * spectralQFI (rho i t) (deriv (rho i) t) (hr.self_of_nhds i).1) +
        4 * ∑ i, deriv (g i) t ^ 2 := by
  classical
  have exists_hermitian_sld_of_psd_curve : ∀ (rho : ℝ → Matrix n n ℂ) (B : Matrix n n ℂ) (t : ℝ)
        (hd : HasDerivAt rho B t)
        (hp : ∀ᶠ s in 𝓝 t, (rho s).PosSemidef),
        ∃ L : Matrix n n ℂ, L.IsHermitian ∧ L * rho t + rho t * L = (2 : ℂ) • B := by
    classical
    intro rho B t hd hp
    classical
    have he (i j : n) : HasDerivAt (fun s => rho s i j) (B i j) t :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
    have hB : B.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      apply (he j i).star.unique
      apply (he i j).congr_of_eventuallyEq
      filter_upwards [hp] with s hs
      exact hs.isHermitian.apply i j
    have hqzero : ∀ v : n → ℂ, rho t *ᵥ v = 0 → star v ⬝ᵥ (B *ᵥ v) = 0 := by
      intro v hv
      have hq : HasDerivAt (fun s => star v ⬝ᵥ (rho s *ᵥ v))
          (star v ⬝ᵥ (B *ᵥ v)) t := by
        unfold dotProduct Matrix.mulVec
        apply HasDerivAt.fun_sum
        intro i _
        apply HasDerivAt.const_mul
        apply HasDerivAt.fun_sum
        intro j _
        exact (he i j).mul_const (v j)
      have hqr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hq
      have hmin : IsLocalMin (fun s => (star v ⬝ᵥ (rho s *ᵥ v)).re) t := by
        filter_upwards [hp] with s hs
        simp only [hv, dotProduct_zero, Complex.zero_re]
        exact (Complex.nonneg_iff.mp (hs.dotProduct_mulVec_nonneg v)).1
      apply Complex.ext
      · exact hmin.hasDerivAt_eq_zero hqr
      · exact hB.im_star_dotProduct_mulVec_self v

    have hA : (rho t).PosSemidef := hp.self_of_nhds
    let U : Matrix.unitaryGroup n ℂ := hA.isHermitian.eigenvectorUnitary
    let d : n → ℂ := fun i => (hA.isHermitian.eigenvalues i : ℂ)
    let M : Matrix n n ℂ := star (U : Matrix n n ℂ) * B * U
    have hspec : rho t = (U : Matrix n n ℂ) * diagonal d * star (U : Matrix n n ℂ) := by
      simpa [Unitary.conjStarAlgAut_apply, U, d, Function.comp_def] using
        hA.isHermitian.spectral_theorem
    have hM : M.IsHermitian := by
      exact Matrix.isHermitian_conjTranspose_mul_mul _ hB
    have hqM (v : n → ℂ) (hv : diagonal d *ᵥ v = 0) :
        star v ⬝ᵥ (M *ᵥ v) = 0 := by
      have hk : rho t *ᵥ ((U : Matrix n n ℂ) *ᵥ v) = 0 := by
        rw [hspec]
        simp only [← mulVec_mulVec]
        have huv : star (U : Matrix n n ℂ) *ᵥ ((U : Matrix n n ℂ) *ᵥ v) = v := by
          rw [mulVec_mulVec, Unitary.coe_star_mul_self, one_mulVec]
        rw [huv, hv, mulVec_zero]
      have hz := hqzero ((U : Matrix n n ℂ) *ᵥ v) hk
      simpa only [M, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
        Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using hz
    have hdiag (i : n) (hi : d i = 0) : M i i = 0 := by
      have hz := hqM (Pi.single i 1) (by simp [hi])
      simpa using hz
    have hzero (i j : n) (hi : d i = 0) (hj : d j = 0) : M i j = 0 := by
      have hsum := hqM (Pi.single i 1 + Pi.single j 1) (by
        simp [mulVec_add, hi, hj])
      have him := hqM (Pi.single i 1 + Complex.I • Pi.single j 1) (by
        simp [mulVec_add, mulVec_smul, hi, hj])
      simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add, star_smul,
        mulVec_smul, smul_dotProduct, dotProduct_smul] at hsum him
      simp [hdiag i hi, hdiag j hj] at hsum him
      linear_combination (norm := ring_nf) (1 / 2 : ℂ) * hsum + (-(Complex.I) / 2) * him
      simp only [Complex.I_sq]
      ring
    let T : Matrix n n ℂ := fun i j => 2 * M i j / (d i + d j)
    have hT : T.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      simp only [T, star_div₀, star_mul, star_ofNat, star_add, hM.apply]
      have hdstar (k : n) : star (d k) = d k := by simp [d]
      rw [hdstar i, hdstar j, add_comm (d j), mul_comm (M i j)]
    have hsolve : T * diagonal d + diagonal d * T = (2 : ℂ) • M := by
      ext i j
      simp only [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
      by_cases hz : d i + d j = 0
      · have hr : hA.isHermitian.eigenvalues i + hA.isHermitian.eigenvalues j = 0 := by
          change (hA.isHermitian.eigenvalues i : ℂ) + (hA.isHermitian.eigenvalues j : ℂ) = 0 at hz
          exact_mod_cast hz
        have hi : d i = 0 := by
          have := hA.eigenvalues_nonneg i
          have := hA.eigenvalues_nonneg j
          simp only [d, Complex.ofReal_eq_zero]
          linarith
        have hj : d j = 0 := by rw [hi, zero_add] at hz; exact hz
        simp [hi, hj, hzero i j hi hj]
      · dsimp [T]
        field_simp
        ring
    refine ⟨(U : Matrix n n ℂ) * T * star (U : Matrix n n ℂ), ?_, ?_⟩
    · exact Matrix.isHermitian_mul_mul_conjTranspose _ hT
    · rw [hspec]
      calc
        _ = (U : Matrix n n ℂ) * (T * diagonal d + diagonal d * T) *
            star (U : Matrix n n ℂ) := by
          have hu (X : Matrix n n ℂ) : star (U : Matrix n n ℂ) * ((U : Matrix n n ℂ) * X) = X := by
            rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul]
          simp only [mul_add, add_mul, Matrix.mul_assoc, hu]
        _ = (2 : ℂ) • B := by
          rw [hsolve]
          have hu : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
            U.property.2
          simp only [M, mul_smul_comm, smul_mul_assoc, ← Matrix.mul_assoc, hu, one_mul]
          simp only [Matrix.mul_assoc, hu, mul_one]

  have spectral_energy (rho B L : Matrix n n ℂ) (hp : rho.PosSemidef)
      (hL : L.IsHermitian) (hsolve : L * rho + rho * L = (2 : ℂ) • B) :
      (L * rho * L).trace.re = spectralQFI rho B hp := by
    classical
    let U := hp.isHermitian.eigenvectorUnitary
    let d : n → ℂ := fun i => (hp.isHermitian.eigenvalues i : ℂ)
    let M := star (U : Matrix n n ℂ) * B * U
    let N := star (U : Matrix n n ℂ) * L * U
    have hs : rho = (U : Matrix n n ℂ) * diagonal d * star (U : Matrix n n ℂ) := by
      simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def] using hp.isHermitian.spectral_theorem
    have hN : N.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul _ hL
    have hu : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := U.property.1
    have hu' : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := U.property.2
    have hdiag : star (U : Matrix n n ℂ) * rho * (U : Matrix n n ℂ) = diagonal d := by
      rw [hs]
      simp only [← Matrix.mul_assoc, hu, one_mul]
      simp only [Matrix.mul_assoc, hu, mul_one]
    have hentry (i j : n) : N i j * (d i + d j) = 2 * M i j := by
      have he := congrArg (fun X : Matrix n n ℂ =>
        (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j) hsolve
      have heq : star (U : Matrix n n ℂ) * (L * rho + rho * L) * U =
          N * diagonal d + diagonal d * N := by
        rw [← hdiag]
        dsimp only [N]
        simp only [mul_add, add_mul, Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hu', one_mul]
      rw [heq] at he
      change (N * diagonal d + diagonal d * N) i j = _ at he
      simp only [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at he
      change N i j * d j + d i * N i j = 2 * M i j at he
      linear_combination he
    have hterm (i j : n) :
        2 * Complex.normSq (M i j) /
          (hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j) =
        (hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j) / 2 *
          Complex.normSq (N i j) := by
      have he := hentry i j
      have hm : M i j = ((d i + d j) / 2) * N i j := by linear_combination -he / 2
      rw [hm, map_mul]
      have hd : (d i + d j) / 2 =
          (((hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j) / 2 : ℝ) : ℂ) := by
        simp [d]
      rw [hd, Complex.normSq_ofReal]
      by_cases hz : hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j = 0
      · simp [hz]
      · field_simp
        <;> ring
    have heTrace : (L * rho * L).trace = (N * diagonal d * N).trace := by
      rw [← hdiag]
      dsimp only [N]
      simp only [Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hu', one_mul]
      rw [trace_mul_comm (star (U : Matrix n n ℂ))]
      simp only [Matrix.mul_assoc, hu', mul_one]
    have heSum : (L * rho * L).trace.re =
        ∑ i, ∑ j, hp.isHermitian.eigenvalues j * Complex.normSq (N i j) := by
      rw [heTrace]
      simp only [Matrix.trace, Matrix.diag]
      simp only [Matrix.mul_apply (M := N * diagonal d) (N := N), mul_diagonal, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hn : N j i = star (N i j) := by simpa using (hN.apply j i).symm
      rw [hn]
      have : N i j * d j * star (N i j) = d j * (Complex.normSq (N i j) : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]
        change _ = d j * (star (N i j) * N i j)
        ring
      rw [this]
      simp [d]
    have hswap : (∑ i, ∑ j, hp.isHermitian.eigenvalues i * Complex.normSq (N i j)) =
        ∑ i, ∑ j, hp.isHermitian.eigenvalues j * Complex.normSq (N i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hN.apply i j]
      simp only [Complex.star_def, Complex.normSq_conj]
    rw [heSum]
    unfold spectralQFI
    change _ = ∑ i, ∑ j, 2 * Complex.normSq (M i j) / _
    simp_rw [hterm, add_div, add_mul]
    simp only [Finset.sum_add_distrib, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [hswap]
    ring

  let M : ℝ → Matrix n n ℂ := fun u => ∑ i, (g i u ^ 2) • rho i u
  have hpos : ∀ᶠ u in 𝓝 t, (M u).PosSemidef := by
    filter_upwards [hr] with u hu
    exact Matrix.posSemidef_sum _ (fun i _ => (hu i).1.smul (sq_nonneg _))
  have htrace : trace (M t) = 1 := by
    simp only [M, trace_sum, trace_smul, (hr.self_of_nhds _).2, Complex.real_smul, mul_one]
    exact_mod_cast hg.self_of_nhds
  let B : Matrix n n ℂ := ∑ i, ((2 * g i t * deriv (g i) t) • rho i t +
    (g i t ^ 2) • deriv (rho i) t)
  have hd : HasDerivAt M B t := by
    apply HasDerivAt.fun_sum
    intro i _
    convert ((hgd i).hasDerivAt.pow 2).smul (hrd i).hasDerivAt using 1
    simp [Pi.pow_apply]
    rw [add_comm]
    rfl
  have hdt : deriv M t = B := hd.deriv
  obtain ⟨L, hL, hsolve⟩ := exists_hermitian_sld_of_psd_curve M B t hd hpos
  have hLi : ∀ i, ∃ Li : Matrix n n ℂ, Li.IsHermitian ∧
      Li * rho i t + rho i t * Li = (2 : ℂ) • deriv (rho i) t := by
    intro i
    exact exists_hermitian_sld_of_psd_curve (rho i) (deriv (rho i) t) t
      (hrd i).hasDerivAt (hr.mono fun u hu => (hu i).1)
  choose Li hLi hsoli using hLi
  have htrB (i : J) : trace (deriv (rho i) t) = 0 := by
    have he (a b : n) : HasDerivAt (fun u => rho i u a b) (deriv (rho i) t a b) t :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp (hrd i).hasDerivAt a) b
    have ht : HasDerivAt (fun u => trace (rho i u)) (trace (deriv (rho i) t)) t := by
      apply HasDerivAt.fun_sum
      intro a _
      exact he a a
    exact (ht.congr_of_eventuallyEq (hr.mono fun u hu => (hu i).2.symm)).unique
      (hasDerivAt_const t (1 : ℂ))
  have htrLi (i : J) : (trace (Li i * rho i t)).re = 0 := by
    have hh := congrArg (fun X : Matrix n n ℂ => (trace X).re) (hsoli i)
    rw [trace_add, trace_mul_comm (rho i t), trace_smul, htrB] at hh
    simp only [Complex.add_re, smul_zero, Complex.zero_re] at hh
    linarith
  have hcross (i : J) :
      (trace (Li i * rho i t * L)).re + (trace (L * rho i t * Li i)).re =
        2 * (trace (deriv (rho i) t * L)).re := by
    have hh := congrArg (fun X : Matrix n n ℂ => (trace (X * L)).re) (hsoli i)
    simpa [add_mul, trace_add, Complex.add_re, trace_mul_cycle (rho i t) (Li i) L,
      smul_mul_assoc, trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero] using hh
  have hterm (i : J) :
      2 * (trace (((2 * g i t * deriv (g i) t) • rho i t +
        (g i t ^ 2) • deriv (rho i) t) * L)).re -
        g i t ^ 2 * (trace (L * rho i t * L)).re ≤
      g i t ^ 2 * spectralQFI (rho i t) (deriv (rho i) t) (hr.self_of_nhds i).1 +
        4 * deriv (g i) t ^ 2 := by
    let A : Matrix n n ℂ := g i t • Li i +
      (2 * deriv (g i) t) • 1 - g i t • L
    have hA : A.IsHermitian :=
      ((hLi i).smul (isSelfAdjoint_iff.mpr (by simp))).add
        (isHermitian_one.smul (isSelfAdjoint_iff.mpr (by simp))) |>.sub
        (hL.smul (isSelfAdjoint_iff.mpr (by simp)))
    have hnn := (hr.self_of_nhds i).1.mul_mul_conjTranspose_same A |>.trace_nonneg
    rw [hA.eq] at hnn
    have hn : 0 ≤ (trace (A * rho i t * A)).re := (Complex.nonneg_iff.mp hnn).1
    have hexp : (trace (A * rho i t * A)).re =
        g i t ^ 2 * (trace (Li i * rho i t * Li i)).re + 4 * deriv (g i) t ^ 2 +
        g i t ^ 2 * (trace (L * rho i t * L)).re -
        2 * (trace (((2 * g i t * deriv (g i) t) • rho i t +
          (g i t ^ 2) • deriv (rho i) t) * L)).re := by
      dsimp only [A]
      simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one, trace_sub, trace_add, trace_smul, Complex.sub_re,
        Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero]
      simp only [trace_mul_comm (rho i t) (Li i), trace_mul_comm (rho i t) L,
        htrLi i, (hr.self_of_nhds i).2, Complex.one_re, mul_zero, zero_mul]
      linear_combination -(g i t ^ 2) * hcross i
    rw [hexp] at hn
    rw [spectral_energy (rho i t) (deriv (rho i) t) (Li i)
      (hr.self_of_nhds i).1 (hLi i) (hsoli i)] at hn
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hsumB : (∑ i, (trace (((2 * g i t * deriv (g i) t) • rho i t +
      (g i t ^ 2) • deriv (rho i) t) * L)).re) = (trace (B * L)).re := by
    simp only [B, Finset.sum_mul, trace_sum, Complex.re_sum]
  have hsumM : (∑ i, g i t ^ 2 * (trace (L * rho i t * L)).re) =
      (trace (L * M t * L)).re := by
    simp only [M, Finset.mul_sum, Finset.sum_mul, trace_sum, Complex.re_sum,
      mul_smul_comm, smul_mul_assoc, trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have henergy : (trace (B * L)).re = (trace (L * M t * L)).re := by
    have hh := congrArg (fun X : Matrix n n ℂ => (trace (X * L)).re) hsolve
    rw [add_mul, trace_add, trace_mul_cycle (M t) L L] at hh
    simp only [smul_mul_assoc, trace_smul, Complex.add_re, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hh
    norm_num at hh
    linarith
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [hsumB, hsumM, henergy] at hs
  have hbound : spectralQFI (M t) (deriv M t) hpos.self_of_nhds ≤
      (∑ i, g i t ^ 2 * spectralQFI (rho i t) (deriv (rho i) t) (hr.self_of_nhds i).1) +
      4 * ∑ i, deriv (g i) t ^ 2 := by
    rw [hdt, ← spectral_energy (M t) B L hpos.self_of_nhds hL hsolve]
    linarith
  exact ⟨hpos.self_of_nhds, htrace, hd.differentiableAt, hdt, hbound⟩

#print axioms actual_spectral_mixture_upper
end D5.S3.Quantum.Information.ActualSpectralMixtureUpper
