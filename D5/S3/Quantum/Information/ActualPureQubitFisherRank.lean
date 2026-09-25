/- GID: D5/S3/Quantum/Information/ActualPureQubitFisherRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualPureQubitFisherRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral Fisher lower bounds and the rank alternative for pure-qubit readouts. -/

import D5.S3.Quantum.Information.ActualPureQubitGeometry
open scoped InnerProductSpace ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.ActualPureQubitCostInfimum

theorem actual_fisher : ∀ {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
      (N : ι → Matrix n n ℂ) (rho : ℝ → Matrix n n ℂ) (p v : ι → ℝ)
      (hN : ∀ j, (N j).PosSemidef) (hNsum : ∑ j, N j = 1)
      (hp : ∀ j, 0 < p j) (hd : DifferentiableAt ℝ rho 0)
      (hpos : ∀ᶠ u in 𝓝 0, (rho u).PosSemidef)
      (hread : ∀ᶠ u in 𝓝 0, ∀ j, (trace (N j * rho u)).re = p j + u*v j),
      (∑ j, v j^2/p j) ≤ spectralQFI (rho 0) (deriv rho 0)
        hpos.self_of_nhds := by
  classical
  have exists_hermitian_sld_of_psd_curve : ∀ {n : Type} [Fintype n] (rho : ℝ → Matrix n n ℂ) (B : Matrix n n ℂ) (t : ℝ)
        (hd : HasDerivAt rho B t)
        (hp : ∀ᶠ s in 𝓝 t, (rho s).PosSemidef),
        ∃ L : Matrix n n ℂ, L.IsHermitian ∧ L * rho t + rho t * L = (2 : ℂ) • B := by
    classical
    intro n inst rho B t hd hp
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

  have spectral_energy {n : Type} [Fintype n] [DecidableEq n] (rho B L : Matrix n n ℂ) (hp : rho.PosSemidef)
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

  intro n ι instN instD instI N rho p v hN hNsum hp hd hpos hread
  classical
  let D := deriv rho 0
  obtain ⟨L,hL,hSLD⟩ := exists_hermitian_sld_of_psd_curve
    rho D 0 hd.hasDerivAt hpos
  have hprob (j : ι) : (trace (N j * rho 0)).re = p j := by
    simpa using hread.self_of_nhds j
  have hvel (j : ι) : (trace (N j * D)).re = v j := by
    have he (a b : n) : HasDerivAt (fun u => rho u a b) (D a b) 0 :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hd.hasDerivAt a) b
    have ht : HasDerivAt (fun u => trace (N j*rho u)) (trace (N j*D)) 0 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      apply HasDerivAt.fun_sum
      intro a _
      apply HasDerivAt.fun_sum
      intro b _
      exact (he b a).const_mul (N j a b)
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 ht
    have ha : HasDerivAt (fun u : ℝ => p j+u*v j) (v j) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v j)).const_add (p j)
    exact (hr.congr_of_eventuallyEq (hread.mono fun u hu => (hu j).symm)).unique ha
  have hcross (j : ι) :
      (trace (N j*(L*rho 0))).re + (trace (N j*(rho 0*L))).re = 2*v j := by
    have hh := congrArg (fun X : Matrix n n ℂ => (trace (N j*X)).re) hSLD
    simpa [mul_add, trace_add, Matrix.mul_smul, trace_smul,
      smul_eq_mul, Complex.mul_re, hvel] using hh
  have hterm (j : ι) : v j^2/p j ≤ (trace (N j*(L*rho 0*L))).re := by
    let s := v j/p j
    let A := L-(s:ℂ) • (1 : Matrix n n ℂ)
    have hA : A.IsHermitian := hL.sub (isHermitian_one.smul (isSelfAdjoint_iff.mpr (by simp)))
    have hps : (A*rho 0*A).PosSemidef := by
      simpa only [hA.eq] using hpos.self_of_nhds.mul_mul_conjTranspose_same A
    have hnn := RHLinalg.trace_mul_nonneg_of_posSemidef (hN j) hps
    have hexp : (trace (N j*(A*rho 0*A))).re =
        (trace (N j*(L*rho 0*L))).re - 2*s*v j + s^2*p j := by
      dsimp only [A]
      simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
        trace_sub, trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, mul_zero, zero_mul, sub_zero]
      rw [hprob]
      linear_combination -s * hcross j
    change 0 ≤ (trace (N j*(A*rho 0*A))).re at hnn
    rw [hexp] at hnn
    have heq : 2*s*v j-s^2*p j = v j^2/p j := by
      dsimp [s]
      field_simp
      <;> ring
    linarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
  have heq : (∑ j, (trace (N j*(L*rho 0*L))).re) = (trace (L*rho 0*L)).re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, hNsum, one_mul]
  rw [heq, spectral_energy (rho 0) D L hpos.self_of_nhds hL hSLD] at hsum
  exact hsum

theorem actual_rank_alternative : ∀ {m : ℕ}
      (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
      (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (p v : Fin m → ℝ) (I : Set ℝ)
      (hI : IsOpen I) (h0 : 0 ∈ I) (hv : v ≠ 0) (hp : ∀ j, 0<p j)
      (hN : ∀ j, (N j).PosSemidef)
      (hc : ContDiffOn ℝ 1 rho I)
      (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ trace (rho u)=1 ∧ rho u*rho u=rho u)
      (hread : ∀ u ∈ I, ∀ j, (trace (N j*rho u)).re=p j+u*v j)
      (lo hi : Fin m) (hlo : v lo/p lo<0) (hhi : 0<v hi/p hi),
      Module.finrank ℝ (effectReadout N).range = 2 ∨
      -(v lo/p lo)*(v hi/p hi) ≤
        spectralQFI (rho 0) (deriv rho 0) (hrho 0 h0).1 := by
  classical
  have strict_visible_interior
      {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F]
      (A : E →ₗ[ℝ] F) (r : ℝ → E) (p v : F) (I : Set ℝ)
      (hI : IsOpen I) (hv : v ≠ 0)
      (hpure : ∀ u ∈ I, ‖r u‖ = 1)
      (hread : ∀ u ∈ I, A (r u) = p + u • v) :
      ∀ u ∈ I, ‖(LinearMap.ker A)ᗮ.starProjection (r u)‖ < 1 := by
    intro u hu
    obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hI u hu
    let t := δ / 2
    have ht : 0 < t := half_pos hδ
    have hm : u - t ∈ I := hb (by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [t]
      rw [show u - δ / 2 - u = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]
      linarith)
    have hplus : u + t ∈ I := hb (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show u + t - u = t by ring, abs_of_pos ht]
      dsimp [t]; linarith)
    have hne : r (u - t) ≠ r (u + t) := by
      intro heq
      have he := congrArg A heq
      rw [hread _ hm, hread _ hplus] at he
      have hz : (-2 * t) • v = 0 := by
        calc
          (-2 * t) • v = (u - t) • v - (u + t) • v := by rw [← sub_smul]; congr 1 <;> ring
          _ = 0 := sub_eq_zero.mpr (add_left_cancel he)
      exact hv ((smul_eq_zero.mp hz).resolve_left (by nlinarith))
    let mid := (1 / 2 : ℝ) • (r (u - t) + r (u + t))
    have hmid : ‖mid‖ < 1 := by
      have h := (norm_midpoint_lt_iff ((hpure _ hm).trans (hpure _ hplus).symm)).mpr hne
      simpa only [hpure _ hm] using h
    have hker : r u - mid ∈ LinearMap.ker A := by
      rw [LinearMap.mem_ker]
      simp only [map_sub, mid, map_smul, map_add, hread _ hm, hread _ hplus, hread _ hu]
      module
    have hproj : (LinearMap.ker A)ᗮ.starProjection (r u) =
        (LinearMap.ker A)ᗮ.starProjection mid := by
      rw [← sub_eq_zero, ← map_sub]
      have hz : (LinearMap.ker A)ᗮ.orthogonalProjectionOnto (r u - mid) = 0 :=
        Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (by simpa using hker)
      exact congrArg Subtype.val hz
    rw [hproj]
    exact lt_of_le_of_lt (Submodule.norm_starProjection_apply_le _ _) hmid

  have matrix_bloch_geometry (M : Matrix (Fin 2) (Fin 2) ℂ)
      (hM : M.IsHermitian) :
      M = blochMatrix (Matrix.trace M).re (bloch M) ∧
      (Matrix.trace M = 1 → M * M = M → ‖bloch M‖ = 1) := by
    have h00 : (M 0 0).im = 0 := by
      have h := congrArg Complex.im (hM.apply 0 0)
      simp at h
      linarith
    have h11 : (M 1 1).im = 0 := by
      have h := congrArg Complex.im (hM.apply 1 1)
      simp at h
      linarith
    have h10r : (M 1 0).re = (M 0 1).re := by
      have h := congrArg Complex.re (hM.apply 1 0)
      simpa using h.symm
    have h10i : (M 1 0).im = -(M 0 1).im := by
      have h := congrArg Complex.im (hM.apply 1 0)
      simpa using h.symm
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [blochMatrix, bloch, Matrix.trace, Fin.sum_univ_two, h00, h11, h10r, h10i] <;> ring
    · intro ht hp
      have htr := congrArg Complex.re ht
      have hsq := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => (Matrix.trace X).re) hp
      simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, h00, h11, h10r, h10i] at htr hsq
      have hnorm : ‖bloch M‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [bloch, Fin.sum_univ_succ]
        nlinarith [hsq, sq_nonneg ((M 0 0).re - (M 1 1).re)]
      nlinarith [norm_nonneg (bloch M)]

  have trace_bloch_pairing (M N : Matrix (Fin 2) (Fin 2) ℂ)
      (hM : M.IsHermitian) (hN : N.IsHermitian) :
      (Matrix.trace (M * N)).re =
        ((Matrix.trace M).re * (Matrix.trace N).re + ⟪bloch M, bloch N⟫_ℝ) / 2 := by
    obtain ⟨hM', _⟩ := matrix_bloch_geometry M hM
    obtain ⟨hN', _⟩ := matrix_bloch_geometry N hN
    conv_lhs => rw [hM', hN']
    simp [blochMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      PiLp.inner_apply, Fin.sum_univ_succ, RCLike.inner_apply]
    ring

  have visible_affine
      {F : Type} [AddCommGroup F] [Module ℝ F]
      (A : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] F) (r : ℝ → (EuclideanSpace ℝ (Fin 3))) (p v : F) (I : Set ℝ)
      (hI : IsOpen I) (hne : I.Nonempty) (hv : v ≠ 0)
      (hread : ∀ u ∈ I, A (r u) = p + u • v) :
      ∃ a d : (EuclideanSpace ℝ (Fin 3)), a ∈ (LinearMap.ker A)ᗮ ∧ d ∈ (LinearMap.ker A)ᗮ ∧
        d ≠ 0 ∧ ∀ u ∈ I, (LinearMap.ker A)ᗮ.starProjection (r u) = a + u • d := by
    let K := LinearMap.ker A
    let P := Kᗮ.starProjection
    obtain ⟨u₀, hu₀⟩ := hne
    obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hI u₀ hu₀
    let t := u₀ + δ / 2
    have ht : 0 < t - u₀ := by dsimp [t]; linarith
    have hti : t ∈ I := hb (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos ht]
      dsimp [t]; linarith)
    let w := (t-u₀)⁻¹ • (r t - r u₀)
    have hAw : A w = v := by
      simp only [w, map_smul, map_sub, hread _ hti, hread _ hu₀]
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
    have hAP (z : (EuclideanSpace ℝ (Fin 3))) : A (P z) = A z := by
      have hz : z - P z ∈ K := by
        simpa only [Submodule.orthogonal_orthogonal] using
          (Submodule.sub_starProjection_mem_orthogonal (K := Kᗮ) z)
      have hz' := LinearMap.mem_ker.mp hz
      exact (sub_eq_zero.mp (by simpa only [map_sub] using hz')).symm
    have hPker {z : (EuclideanSpace ℝ (Fin 3))} (hz : A z = 0) : P z = 0 := by
      have h := Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        (show z ∈ Kᗮᗮ by simpa [K] using (LinearMap.mem_ker.mpr hz))
      exact congrArg Subtype.val h
    refine ⟨P (r u₀) - u₀ • P w, P w, ?_, Submodule.starProjection_apply_mem _ _, ?_, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _)
        (Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _))
    · intro hz
      apply hv
      rw [← hAw, ← hAP, hz, map_zero]
    · intro u hu
      have hz : A (r u - r u₀ - (u-u₀) • w) = 0 := by
        simp only [map_sub, map_smul, hread _ hu, hread _ hu₀, hAw]
        module
      have h := hPker hz
      simp only [map_sub, map_smul] at h
      have h' := sub_eq_zero.mp h
      rw [sub_smul] at h'
      calc
        P (r u) = (u • P w - u₀ • P w) + P (r u₀) := sub_eq_iff_eq_add.mp h'
        _ = _ := by abel

  have actual_matrix_visible_interior {m : ℕ}
      (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
      (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (p v : Fin m → ℝ) (I : Set ℝ)
      (hI : IsOpen I) (hv : v ≠ 0)
      (hN : ∀ j, (N j).PosSemidef)
      (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ Matrix.trace (rho u) = 1 ∧ rho u * rho u = rho u)
      (hread : ∀ u ∈ I, ∀ j, (Matrix.trace (N j * rho u)).re = p j + u * v j) :
      ∀ u ∈ I, ‖(effectReadout N).kerᗮ.starProjection (bloch (rho u))‖ < 1 := by
    apply strict_visible_interior (effectReadout N) (fun u => bloch (rho u))
      (fun j => p j - (Matrix.trace (N j)).re / 2) v I hI hv
    · intro u hu
      exact (matrix_bloch_geometry (rho u) (hrho u hu).1.isHermitian).2
        (hrho u hu).2.1 (hrho u hu).2.2
    · intro u hu
      ext j
      have h := trace_bloch_pairing (N j) (rho u) (hN j).isHermitian (hrho u hu).1.isHermitian
      rw [(hrho u hu).2.1] at h
      have hr := hread u hu j
      change ⟪bloch (N j), bloch (rho u)⟫_ℝ / 2 = p j - (Matrix.trace (N j)).re / 2 + u * v j
      simp only [Complex.one_re, mul_one] at h
      linarith

  have blochMatrix_properties (a : ℝ) (r : (EuclideanSpace ℝ (Fin 3))) :
      (blochMatrix a r).IsHermitian ∧
      Matrix.trace (blochMatrix a r) = (a : ℂ) ∧
      bloch (blochMatrix a r) = r ∧
      (Matrix.det (blochMatrix a r)).re = (a^2 - ‖r‖^2) / 4 ∧
      ((blochMatrix a r).PosSemidef ↔ ‖r‖ ≤ a) := by
    have hh : (blochMatrix a r).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMatrix]
    have ht : Matrix.trace (blochMatrix a r) = (a : ℂ) := by
      apply Complex.ext <;> simp [blochMatrix, Matrix.trace, Fin.sum_univ_two] <;> ring
    have hb : bloch (blochMatrix a r) = r := by
      ext i
      fin_cases i <;> simp [bloch, blochMatrix] <;> ring
    have hd : (Matrix.det (blochMatrix a r)).re = (a^2 - ‖r‖^2)/4 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [blochMatrix, Matrix.det_fin_two, Fin.sum_univ_three]
      ring
    refine ⟨hh, ht, hb, hd, ?_⟩
    constructor
    · intro hp
      have htpos := (Complex.nonneg_iff.mp hp.trace_nonneg).1
      have hdpos := (Complex.nonneg_iff.mp hp.det_nonneg).1
      rw [ht] at htpos
      rw [hd] at hdpos
      simp only [Complex.ofReal_re] at htpos
      nlinarith [norm_nonneg r]
    · intro hbound
      apply hh.posSemidef_iff_eigenvalues_nonneg.mpr
      have hs := congrArg Complex.re hh.trace_eq_sum_eigenvalues
      rw [ht] at hs
      simp only [Fin.sum_univ_two, Complex.add_re, Complex.ofReal_re] at hs
      have hp := congrArg Complex.re hh.det_eq_prod_eigenvalues
      rw [hd] at hp
      simp only [Fin.prod_univ_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] at hp
      change a = hh.eigenvalues 0 + hh.eigenvalues 1 at hs
      change (a^2 - ‖r‖^2) / 4 = hh.eigenvalues 0 * hh.eigenvalues 1 - 0*0 at hp
      simp only [mul_zero, sub_zero] at hp
      have htr : 0 ≤ a := (norm_nonneg r).trans hbound
      have hdet : 0 ≤ hh.eigenvalues 0 * hh.eigenvalues 1 := by nlinarith [norm_nonneg r]
      intro i
      fin_cases i
      · by_contra h
        have hi : hh.eigenvalues 0 < 0 := lt_of_not_ge h
        have hj : 0 < hh.eigenvalues 1 := by linarith
        exact (not_lt_of_ge hdet) (mul_neg_of_neg_of_pos hi hj)
      · by_contra h
        have hi : hh.eigenvalues 1 < 0 := lt_of_not_ge h
        have hj : 0 < hh.eigenvalues 0 := by linarith
        exact (not_lt_of_ge hdet) (mul_neg_of_pos_of_neg hj hi)

  have actual_rank_one_or_two {m : ℕ}
      (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
      (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (p v : Fin m → ℝ) (I : Set ℝ)
      (hI : IsOpen I) (h0 : 0 ∈ I) (hv : v ≠ 0)
      (hN : ∀ j, (N j).PosSemidef)
      (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ trace (rho u) = 1 ∧ rho u*rho u=rho u)
      (hread : ∀ u ∈ I, ∀ j, (trace (N j*rho u)).re=p j+u*v j) :
      Module.finrank ℝ (effectReadout N).range = 1 ∨
      Module.finrank ℝ (effectReadout N).range = 2 := by
    let A := effectReadout N
    have hbr : ∀ u ∈ I, A (bloch (rho u)) =
        (fun j => p j-(trace (N j)).re/2) + u • v := by
      intro u hu
      ext j
      have hh := trace_bloch_pairing (N j) (rho u) (hN j).isHermitian (hrho u hu).1.isHermitian
      rw [(hrho u hu).2.1] at hh
      have hr := hread u hu j
      change ⟪bloch (N j),bloch (rho u)⟫_ℝ/2 = _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.one_re, mul_one] at *
      linarith
    obtain ⟨a,d,ha,hd,hd0,heq⟩ := visible_affine A (fun u => bloch (rho u))
      (fun j => p j-(trace (N j)).re/2) v I hI ⟨0,h0⟩ hv hbr
    have hdim := A.finrank_range_add_finrank_ker
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [h3] at hdim
    have hn0 : Module.finrank ℝ A.range ≠ 0 := by
      intro hz
      have hrange : A.range = ⊥ := Submodule.finrank_eq_zero.mp hz
      have hAz : A = 0 := LinearMap.range_eq_bot.mp hrange
      have hk : A.ker = ⊤ := by rw [hAz]; simp
      have : d=0 := by simpa [hk] using hd
      exact hd0 this
    have hn3 : Module.finrank ℝ A.range ≠ 3 := by
      intro hz
      have hk : A.ker=⊥ := Submodule.finrank_eq_zero.mp (by omega)
      have hi := actual_matrix_visible_interior N rho p v I hI hv hN hrho hread 0 h0
      change ‖A.kerᗮ.starProjection (bloch (rho 0))‖ < 1 at hi
      simp only [hk, Submodule.bot_orthogonal_eq_top, Submodule.starProjection_top, ContinuousLinearMap.id_apply] at hi
      have hn := (matrix_bloch_geometry (rho 0) (hrho 0 h0).1.isHermitian).2
        (hrho 0 h0).2.1 (hrho 0 h0).2.2
      simpa [hn] using hi
    change Module.finrank ℝ A.range=1 ∨ Module.finrank ℝ A.range=2
    omega

  have rank_one_frame {m : ℕ}
      (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
      (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (p v : Fin m → ℝ) (I : Set ℝ)
      (hI : IsOpen I) (h0 : 0 ∈ I) (hv : v ≠ 0)
      (hN : ∀ j, (N j).PosSemidef)
      (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ trace (rho u)=1 ∧ rho u*rho u=rho u)
      (hread : ∀ u ∈ I, ∀ j, (trace (N j*rho u)).re=p j+u*v j)
      (hrank : Module.finrank ℝ (effectReadout N).range=1) :
      ∃ (e : (EuclideanSpace ℝ (Fin 3))) (x c : ℝ), ‖e‖=1 ∧ 0<c ∧ |x|<1 ∧
        (∀ u ∈ I, ⟪e,bloch (rho u)⟫_ℝ=x+u*c) ∧
        (∀ j, 0 ≤ p j+(1-x)/c*v j ∧ 0 ≤ p j+(-1-x)/c*v j) := by
    let A := effectReadout N
    let K := A.kerᗮ
    have hbr : ∀ u ∈ I, A (bloch (rho u)) =
        (fun j => p j-(trace (N j)).re/2)+u • v := by
      intro u hu
      ext j
      have hh := trace_bloch_pairing (N j) (rho u) (hN j).isHermitian (hrho u hu).1.isHermitian
      rw [(hrho u hu).2.1] at hh
      have hr := hread u hu j
      change ⟪bloch (N j),bloch (rho u)⟫_ℝ/2 = _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.one_re, mul_one] at *
      linarith
    obtain ⟨a,d,ha,hd,hd0,heq⟩ := visible_affine A (fun u => bloch (rho u))
      (fun j => p j-(trace (N j)).re/2) v I hI ⟨0,h0⟩ hv hbr
    let c := ‖d‖
    let e := c⁻¹ • d
    have hc : 0<c := norm_pos_iff.mpr hd0
    have he : ‖e‖=1 := by simp [e,c,norm_smul,norm_ne_zero_iff.mpr hd0]
    have hed : d=c • e := by simp [e,hc.ne']
    have heK : e ∈ K := K.smul_mem _ hd
    have hdim : Module.finrank ℝ K=1 := by
      have h1 := A.finrank_range_add_finrank_ker
      have h2 := A.ker.finrank_add_finrank_orthogonal
      have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))=3 := by simp
      change Module.finrank ℝ A.range=1 at hrank
      dsimp [K]
      omega
    have hspan : K=ℝ ∙ e := eq_span_singleton_of_mem_of_finrank_eq_one hdim heK
      (by intro hz; simpa [hz] using he)
    obtain ⟨x,hax⟩ := Submodule.mem_span_singleton.mp (hspan ▸ (show a ∈ K from ha))
    have hcoord (u : ℝ) (hu : u ∈ I) : ⟪e,bloch (rho u)⟫_ℝ=x+u*c := by
      have horth := K.starProjection_inner_eq_zero (bloch (rho u)) e heK
      rw [inner_sub_left, real_inner_comm e (bloch (rho u)),
        real_inner_comm e (K.starProjection (bloch (rho u)))] at horth
      have hh := heq u hu
      change K.starProjection (bloch (rho u))=a+u • d at hh
      have hee : ⟪e,e⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
      have hde : ⟪e,d⟫_ℝ=c := by rw [hed,inner_smul_right,hee,mul_one]
      rw [hh, ← hax, inner_add_right] at horth
      have hxe : ⟪e,x • e⟫_ℝ=x := by simpa only [inner_smul_right,hee,mul_one]
      have hud : ⟪e,u • d⟫_ℝ=u*c := by simp only [inner_smul_right,hde]
      rw [hxe,hud] at horth
      nlinarith
    have hx : |x|<1 := by
      have hi := actual_matrix_visible_interior N rho p v I hI hv hN hrho hread 0 h0
      rw [heq 0 h0] at hi
      simpa [← hax,norm_smul,he] using hi
    refine ⟨e,x,c,he,hc,hx,hcoord,?_⟩
    intro j
    have hjK' : bloch (N j) ∈ A.kerᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      have hh := congrFun (LinearMap.mem_ker.mp hz) j
      change ⟪bloch (N j),z⟫_ℝ/2=0 at hh
      linarith
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (hspan ▸ (show bloch (N j) ∈ K from hjK'))
    have hn : |b| ≤ (trace (N j)).re := by
      have hm := (matrix_bloch_geometry (N j) (hN j).isHermitian).1
      have hp := hN j
      rw [hm, (blochMatrix_properties _ _).2.2.2.2] at hp
      simpa [← hb,norm_smul,he] using hp
    have hscalar (u : ℝ) (hu : u ∈ I) :
        p j+u*v j=((trace (N j)).re+b*(x+u*c))/2 := by
      rw [← hread u hu j,trace_bloch_pairing _ _ (hN j).isHermitian (hrho u hu).1.isHermitian,
        (hrho u hu).2.1, ← hb, inner_smul_left, hcoord u hu]
      simp
    have hbase := hscalar 0 h0
    obtain ⟨δ,hδ,hδI⟩ := Metric.isOpen_iff.mp hI 0 h0
    have hδm : δ/2 ∈ I := hδI (by simp [Metric.mem_ball,Real.dist_eq,abs_of_pos hδ]; linarith)
    have hstep := hscalar (δ/2) hδm
    have hvel : b*c=2*v j := by nlinarith
    have hplus : p j+(1-x)/c*v j=((trace (N j)).re+b)/2 := by
      apply (mul_left_cancel₀ hc.ne')
      field_simp
      linear_combination 2*c*hbase + (x-1)*hvel
    have hminus : p j+(-1-x)/c*v j=((trace (N j)).re-b)/2 := by
      apply (mul_left_cancel₀ hc.ne')
      field_simp
      linear_combination 2*c*hbase + (x+1)*hvel
    rw [hplus,hminus]
    constructor <;> linarith [le_abs_self b,neg_le_abs b]

  have actual_rank_one_lower {m : ℕ}
      (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
      (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (p v : Fin m → ℝ) (I : Set ℝ)
      (hI : IsOpen I) (h0 : 0 ∈ I) (hv : v ≠ 0) (hp : ∀ j, 0<p j)
      (hN : ∀ j, (N j).PosSemidef)
      (hc : ContDiffOn ℝ 1 rho I)
      (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ trace (rho u)=1 ∧ rho u*rho u=rho u)
      (hread : ∀ u ∈ I, ∀ j, (trace (N j*rho u)).re=p j+u*v j)
      (hrank : Module.finrank ℝ (effectReadout N).range=1)
      (lo hi : Fin m) (hlo : v lo/p lo<0) (hhi : 0<v hi/p hi) :
      -(v lo/p lo)*(v hi/p hi) ≤
        spectralQFI (rho 0) (deriv rho 0) (hrho 0 h0).1 := by
    obtain ⟨e,x,c,he,hcpos,hx,hcoord,hend⟩ :=
      rank_one_frame N rho p v I hI h0 hv hN hrho hread hrank
    let E : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![blochMatrix 1 e,blochMatrix 1 (-e)]
    let b : Fin 2 → ℝ := ![(1+x)/2,(1-x)/2]
    let w : Fin 2 → ℝ := ![c/2,-c/2]
    have hxp : -1<x ∧ x<1 := abs_lt.mp hx
    have hEp : ∀ j, (E j).PosSemidef := by
      intro j; fin_cases j
      · exact (blochMatrix_properties _ _).2.2.2.2.mpr (by simpa using he.le)
      · exact (blochMatrix_properties _ _).2.2.2.2.mpr (by simp [he])
    have hEs : ∑ j, E j=1 := by
      ext a k; fin_cases a <;> fin_cases k <;> apply Complex.ext <;>
        simp [E,Fin.sum_univ_two,blochMatrix] <;> ring
    have hbp : ∀ j, 0<b j := by intro j; fin_cases j <;> simp [b] <;> linarith
    have hEr : ∀ u ∈ I, ∀ j, (trace (E j*rho u)).re=b j+u*w j := by
      intro u hu j
      have hr := (hrho u hu).1.isHermitian
      fin_cases j
      · change (trace (blochMatrix 1 e*rho u)).re=(1+x)/2+u*(c/2)
        rw [trace_bloch_pairing _ _ (blochMatrix_properties 1 e).1 hr,
          (blochMatrix_properties 1 e).2.1,(blochMatrix_properties 1 e).2.2.1,
          (hrho u hu).2.1,hcoord u hu]
        simp [b,w]
        ring
      · change (trace (blochMatrix 1 (-e)*rho u)).re=(1-x)/2+u*(-c/2)
        rw [trace_bloch_pairing _ _ (blochMatrix_properties 1 (-e)).1 hr,
          (blochMatrix_properties 1 (-e)).2.1,(blochMatrix_properties 1 (-e)).2.2.1,
          (hrho u hu).2.1,inner_neg_left,hcoord u hu]
        simp [b,w]
        ring
    have hdiff := (hc.differentiableOn (by norm_num) 0 h0).differentiableAt (hI.mem_nhds h0)
    have hpos : ∀ᶠ u in 𝓝 0, (rho u).PosSemidef :=
      (show ∀ᶠ u in 𝓝 (0:ℝ), u ∈ I from hI.mem_nhds h0).mono fun u hu => (hrho u hu).1
    have hf := actual_fisher (n := Fin 2) (ι := Fin 2) E rho b w hEp hEs hbp hdiff hpos
      ((show ∀ᶠ u in 𝓝 (0:ℝ), u ∈ I from hI.mem_nhds h0).mono fun u hu => hEr u hu)
    have hden : 0<1-x^2 := by nlinarith [sq_nonneg (1+x),sq_nonneg (1-x)]
    have hfval : (∑ j, w j^2/b j)=c^2/(1-x^2) := by
      simp only [Fin.sum_univ_two,w,b,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
      have ha : 1+x≠0 := by linarith [hxp.1]
      have hb : 1-x≠0 := by linarith [hxp.2]
      field_simp [ha,hb,hden.ne']
      <;> ring
    rw [hfval] at hf
    have hhi' : (1+x)*(v hi/p hi) ≤ c := by
      have hh := (hend hi).2
      have hp' := hp hi
      have hc' := hcpos.ne'
      have heq : p hi+(-1-x)/c*v hi = p hi/c*(c-(1+x)*(v hi/p hi)) := by
        field_simp
        <;> ring
      rw [heq] at hh
      have := nonneg_of_mul_nonneg_right hh (div_pos hp' hcpos)
      linarith
    have hlo' : (1-x)*(-(v lo/p lo)) ≤ c := by
      have hh := (hend lo).1
      have hp' := hp lo
      have heq : p lo+(1-x)/c*v lo = p lo/c*(c-(1-x)*(-(v lo/p lo))) := by
        field_simp
        <;> ring
      rw [heq] at hh
      have := nonneg_of_mul_nonneg_right hh (div_pos hp' hcpos)
      linarith
    have hprod := mul_le_mul hhi' hlo' (mul_nonneg (sub_nonneg.mpr hxp.2.le) (neg_nonneg.mpr hlo.le)) hcpos.le
    have hq : -(v lo/p lo)*(v hi/p hi) ≤ c^2/(1-x^2) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [hprod]
    exact hq.trans hf

  intro m N rho p v I hI h0 hv hp hN hc hrho hread lo hi hlo hhi
  rcases actual_rank_one_or_two N rho p v I hI h0 hv hN hrho hread with h | h
  · exact Or.inr (actual_rank_one_lower N rho p v I hI h0 hv hp hN hc hrho hread h lo hi hlo hhi)
  · exact Or.inl h
end D5.S3.Quantum.Information.ActualPureQubitCostInfimum
