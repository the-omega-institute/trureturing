/- GID: D5/S3/Quantum/Information/ActualPureQubitCostInfimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualPureQubitCostInfimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Full finite affine-readout pure-qubit spectral-information cost infimum. -/

import Mathlib
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Weil.ZetaLinear.RankTrace
open scoped InnerProductSpace ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.ActualPureQubitCostInfimum

def spectralQFI {n : Type*} [Fintype n] [DecidableEq n] (rho B : Matrix n n ℂ) (hp : rho.PosSemidef) : ℝ :=
  let U := hp.isHermitian.eigenvectorUnitary
  let M := star (U : Matrix n n ℂ) * B * U
  ∑ i, ∑ j, 2 * Complex.normSq (M i j) /
    (hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j)
def guardedInfimum (S : Set ℝ) : ℝ := by
  classical
  exact if h : S.Nonempty ∧ BddBelow S then sInf S else 0

open scoped MatrixOrder in
/-- Every PSD trace-one matrix is exactly the matrix of a canonical density state. -/
def densityBridge (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef)
    (ht : trace M=1) : {rho : DensityState (Fin 2) // CStarMatrix.ofMatrix.symm rho.1=M} := by
  refine ⟨⟨CStarMatrix.ofMatrix M, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg, ht⟩,rfl⟩

def IsProgram {m : ℕ} (p v : Fin m → ℝ) (R : ℝ)
    (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : Set ℝ) (Q : ℝ) : Prop :=
  IsOpen I ∧ IsPreconnected I ∧ Icc (-R) R ⊆ I ∧
  (∀ j, (N j).PosSemidef) ∧ (∑ j,N j=1) ∧ ContDiffOn ℝ 1 rho I ∧
  (∀ u ∈ I, (rho u).PosSemidef ∧ trace (rho u)=1 ∧ rho u*rho u=rho u ∧
    ∃ r : DensityState (Fin 2), CStarMatrix.ofMatrix.symm r.1=rho u) ∧
  (∀ u ∈ I, ∀ j, trace (N j*rho u)=((p j+u*v j:ℝ):ℂ) ∧ 0<p j+u*v j) ∧
  (∀ h : (rho 0).PosSemidef, spectralQFI (rho 0) (deriv rho 0) h=Q)
def costs {m : ℕ} (p v : Fin m → ℝ) (R : ℝ) : Set ℝ :=
  {Q | ∃ N rho I, IsProgram p v R N rho I Q}

def C2 {m : ℕ} (p v : Fin m → ℝ) (R : ℝ) : ℝ :=
  guardedInfimum (costs p v R)

def bloch (M : Matrix (Fin 2) (Fin 2) ℂ) : (EuclideanSpace ℝ (Fin 3)) :=
  WithLp.toLp 2 ![2 * (M 0 1).re, -2 * (M 0 1).im, (M 0 0).re - (M 1 1).re]

def blochMatrix (a : ℝ) (r : (EuclideanSpace ℝ (Fin 3))) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((a + r 2 : ℝ) : ℂ) / 2, ((r 0 : ℂ) - (r 1 : ℂ) * Complex.I) / 2;
      ((r 0 : ℂ) + (r 1 : ℂ) * Complex.I) / 2, ((a - r 2 : ℝ) : ℂ) / 2]

def effectReadout {m : ℕ} (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ) :
    (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (Fin m → ℝ) := {
  toFun r j := ⟪bloch (N j), r⟫_ℝ / 2
  map_add' r s := by ext j; simp [inner_add_right, add_div]
  map_smul' c r := by ext j; simp [inner_smul_right, mul_div_assoc]
}

def reframe (O : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)))
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  blochMatrix (Matrix.trace M).re (O (bloch M))

def blochLinear : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3)) := {
  toFun := bloch
  map_add' M N := by ext i; fin_cases i <;> simp [bloch] <;> ring
  map_smul' c M := by ext i; fin_cases i <;> simp [bloch] <;> ring
}

def reframeLinear (O : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3))) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := {
  toFun := reframe O
  map_add' M N := by
    have hb : bloch (M + N) = bloch M + bloch N := blochLinear.map_add M N
    ext i j
    simp only [reframe, Matrix.trace_add, Complex.add_re, hb, map_add]
    fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring
  map_smul' c M := by
    have hb : bloch (c • M) = c • bloch M := blochLinear.map_smul c M
    ext i j
    simp only [reframe, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hb, map_smul]
    fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring
}

def root (p d α e w : ℝ) : ℝ :=
  2*(1-e)*w^2*d^2 / ((p-α*e*w*d) +
    Real.sqrt ((p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2))

def radiusMap (B α : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (2*t*Real.sqrt (1-t^2)-|α| *t^2)*w (t^2)/((1+t)*Real.sqrt B)

def extendedCost (B α : ℝ) (w : ℝ → ℝ) (e : ℝ) : ℝ :=
  B/(w e)^2*(4*(1-e))/(4*(1-e)-α^2*e)

def upperDiag (p d α e w : ℝ) : ℝ :=
  ((p-α*e*w*d)+Real.sqrt ((p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2))/(2*(1-e))

def effect (p d α e w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(upperDiag p d α e w : ℂ), (w*d : ℝ); (w*d : ℝ), (root p d α e w : ℂ)]

def arc (e x c u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  blochMatrix 1 (WithLp.toLp 2 ![x+c*u,Real.sqrt (4*e*(1-e)-(x+c*u)^2),1-2*e])

theorem actual_rank_two_parameters : ∀ {m : ℕ}
    (N : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (p v : Fin m → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hcI : IsPreconnected I) (h0 : 0 ∈ I) (hv : v ≠ 0)
    (hN : ∀ j, (N j).PosSemidef) (hnorm : ∑ j, N j = 1)
    (hc : ContDiffOn ℝ 1 rho I)
    (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ Matrix.trace (rho u) = 1 ∧ rho u * rho u = rho u)
    (hread : ∀ u ∈ I, ∀ j, (Matrix.trace (N j * rho u)).re = p j + u * v j)
    (hrank : Module.finrank ℝ (effectReadout N).range = 2),
    ∃ (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (x c ε s : ℝ)
      (A q b : Fin m → ℝ),
      0 < c ∧ 0 < ε ∧ ε ≤ 1/2 ∧ (s = 1 ∨ s = -1) ∧
      (∀ j, 0 ≤ q j ∧ 0 ≤ A j ∧ b j^2 ≤ A j*q j ∧
        b j = v j/c ∧ A j = (p j-b j*x-ε*q j)/(1-ε)) ∧
      (∑ j, q j=1) ∧
      (∀ u ∈ I, reframe basis.repr (rho u) = blochMatrix 1 (WithLp.toLp 2
        ![x+c*u,s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2),1-2*ε])) ∧
      (∀ u ∈ I, (x+c*u)^2 < 4*ε*(1-ε)) ∧
      (∀ R : ℝ, 0 ≤ R → Icc (-R) R ⊆ I → |x|+c*R < Real.sqrt (4*ε*(1-ε))) := by
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

  have fixed_frame
      {F : Type} [AddCommGroup F] [Module ℝ F]
      (A : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] F) (a d : (EuclideanSpace ℝ (Fin 3)))
      (ha : a ∈ A.kerᗮ) (hd : d ∈ A.kerᗮ) (hd0 : d ≠ 0)
      (hrank : Module.finrank ℝ A.range = 2) :
      ∃ b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
        A.ker = ℝ ∙ b 1 ∧ b 0 = ‖d‖⁻¹ • d ∧
        0 ≤ ⟪b 2, a⟫_ℝ := by
    classical
    have hdim : Module.finrank ℝ A.ker = 1 := by
      have h := A.finrank_range_add_finrank_ker
      rw [hrank] at h
      have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
      rw [h3] at h
      omega
    letI : Nontrivial A.ker := Module.nontrivial_of_finrank_pos (R := ℝ) (M := A.ker) (by omega)
    obtain ⟨k, hk⟩ := exists_norm_eq A.ker (show (0 : ℝ) ≤ 1 by norm_num)
    let e : (EuclideanSpace ℝ (Fin 3)) := ‖d‖⁻¹ • d
    have he : ‖e‖ = 1 := by simp [e, norm_smul, norm_ne_zero_iff.mpr hd0]
    have hek : ⟪e, (k : (EuclideanSpace ℝ (Fin 3)))⟫_ℝ = 0 := by
      dsimp only [e]
      rw [inner_smul_left, Submodule.inner_left_of_mem_orthogonal k.property hd]
      simp
    have hk' : ‖(k : (EuclideanSpace ℝ (Fin 3)))‖ = 1 := hk
    have hke : ⟪(k : (EuclideanSpace ℝ (Fin 3))), e⟫_ℝ = 0 := (real_inner_comm _ _).trans hek
    let w : Fin 3 → (EuclideanSpace ℝ (Fin 3)) := ![e, k, 0]
    have hon : Orthonormal ℝ (({0, 1} : Set (Fin 3)).domRestrict w) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
        simp [Set.domRestrict, w, real_inner_self_eq_norm_sq, he, hk', hek, hke]
    obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
    have hb0 : b 0 = e := hb 0 (by simp)
    have hb1 : b 1 = k := hb 1 (by simp)
    have hspan : A.ker = ℝ ∙ b 1 := by
      apply eq_span_singleton_of_mem_of_finrank_eq_one hdim
      · rw [hb1]; exact k.property
      · intro hz
        have := b.orthonormal.norm_eq_one 1
        rw [hz, norm_zero] at this
        norm_num at this
    by_cases hz : 0 ≤ ⟪b 2, a⟫_ℝ
    · exact ⟨b, hspan, hb0, hz⟩
    · let w' : Fin 3 → (EuclideanSpace ℝ (Fin 3)) := ![b 0, b 1, -b 2]
      have hw' : Orthonormal ℝ w' := by
        rw [orthonormal_iff_ite]
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [w', orthonormal_iff_ite.mp b.orthonormal]
      let b' := OrthonormalBasis.mk hw'
        (hw'.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
      have hb' (i : Fin 3) : b' i = w' i := by simp [b']
      refine ⟨b', ?_, ?_, ?_⟩
      · simpa [hb', w'] using hspan
      · simpa [hb', w'] using hb0
      · simp [hb', w']
        linarith

  have geometric_normal_form
      {F : Type} [AddCommGroup F] [Module ℝ F]
      (A : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] F) (r : ℝ → (EuclideanSpace ℝ (Fin 3))) (p v : F) (I : Set ℝ)
      (hI : IsOpen I) (hcI : IsPreconnected I) (hne : I.Nonempty) (hv : v ≠ 0)
      (hc : ContinuousOn r I) (hpure : ∀ u ∈ I, ‖r u‖ = 1)
      (hread : ∀ u ∈ I, A (r u) = p + u • v)
      (hrank : Module.finrank ℝ A.range = 2) :
      ∃ (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (x c ε s : ℝ),
        0 < c ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ (s = 1 ∨ s = -1) ∧
        A.ker = ℝ ∙ b 1 ∧
        (∀ u ∈ I, b.repr (r u) = WithLp.toLp 2
          ![x + c * u, s * Real.sqrt (4 * ε * (1 - ε) - (x + c * u)^2), 1 - 2 * ε]) ∧
        (∀ u ∈ I, (x + c * u)^2 < 4 * ε * (1 - ε)) ∧
        (∀ R : ℝ, 0 ≤ R → Set.Icc (-R) R ⊆ I →
          |x| + c * R < Real.sqrt (4 * ε * (1 - ε))) := by
    obtain ⟨a, d, ha, hd, hd0, hP⟩ := visible_affine A r p v I hI hne hv hread
    obtain ⟨u₀, hu₀⟩ := hne
    obtain ⟨b, hK, hb0, hz⟩ := fixed_frame A a d ha hd hd0 hrank
    let c := ‖d‖
    let x := ⟪b 0, a⟫_ℝ
    let z := ⟪b 2, a⟫_ℝ
    have hcpos : 0 < c := norm_pos_iff.mpr hd0
    have hd_eq : d = c • b 0 := by rw [hb0, smul_smul]; simp [c, ne_of_gt hcpos]
    have hbmem (i : Fin 3) (hi : i ≠ 1) : b i ∈ A.kerᗮ := by
      rw [hK, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact b.orthonormal.inner_eq_zero (Ne.symm hi)
    have hip (i : Fin 3) (hi : i ≠ 1) (u : ℝ) (hu : u ∈ I) :
        ⟪b i, r u⟫_ℝ = ⟪b i, a + u • d⟫_ℝ := by
      have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
        (K := A.kerᗮ) ⟨b i, hbmem i hi⟩ (r u)
      change ⟪b i, A.kerᗮ.starProjection (r u)⟫_ℝ = ⟪b i, r u⟫_ℝ at h
      rw [hP u hu] at h
      exact h.symm
    have hX (u : ℝ) (hu : u ∈ I) : ⟪b 0, r u⟫_ℝ = x + c * u := by
      rw [hip 0 (by decide) u hu, inner_add_right, inner_smul_right, hd_eq, inner_smul_right]
      simp [x, orthonormal_iff_ite.mp b.orthonormal, mul_comm]
    have hZ (u : ℝ) (hu : u ∈ I) : ⟪b 2, r u⟫_ℝ = z := by
      rw [hip 2 (by decide) u hu, inner_add_right, inner_smul_right, hd_eq, inner_smul_right]
      simp [z, orthonormal_iff_ite.mp b.orthonormal]
    have hYp (u : ℝ) : ⟪b 1, A.kerᗮ.starProjection (r u)⟫_ℝ = 0 := by
      apply Submodule.inner_right_of_mem_orthogonal (K := A.ker)
      · rw [hK]; exact Submodule.mem_span_singleton_self _
      · exact Submodule.starProjection_apply_mem _ _
    have hsphere (u : ℝ) (hu : u ∈ I) :
        (x + c * u)^2 + ⟪b 1, r u⟫_ℝ^2 + z^2 = 1 := by
      have h := b.sum_sq_inner_right (r u)
      simpa [Fin.sum_univ_succ, hX u hu, hZ u hu, hpure u hu, add_assoc] using h
    have hinterior (u : ℝ) (hu : u ∈ I) : (x + c * u)^2 + z^2 < 1 := by
      have hi := strict_visible_interior A r p v I hI hv hpure hread u hu
      have h := b.sum_sq_inner_right (A.kerᗮ.starProjection (r u))
      have hpx : ⟪b 0, A.kerᗮ.starProjection (r u)⟫_ℝ = x + c*u := by
        rw [hP u hu]; exact (hip 0 (by decide) u hu).symm.trans (hX u hu)
      have hpz : ⟪b 2, A.kerᗮ.starProjection (r u)⟫_ℝ = z := by
        rw [hP u hu]; exact (hip 2 (by decide) u hu).symm.trans (hZ u hu)
      simp only [Fin.sum_univ_three, hpx, hpz, hYp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
      nlinarith [norm_nonneg (A.kerᗮ.starProjection (r u))]
    have hyne (u : ℝ) (hu : u ∈ I) : ⟪b 1, r u⟫_ℝ ≠ 0 := by
      have hsp := hsphere u hu
      have hint := hinterior u hu
      intro heq
      simp only [heq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hsp
      linarith
    have hycont : ContinuousOn (fun u => ⟪b 1, r u⟫_ℝ) I := continuousOn_const.inner hc
    have hsign : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ u ∈ I, 0 < s * ⟪b 1, r u⟫_ℝ := by
      rcases lt_or_gt_of_ne (hyne u₀ hu₀) with hneg | hpos
      · refine ⟨-1, Or.inr rfl, ?_⟩
        intro u hu
        have hn : ⟪b 1, r u⟫_ℝ < 0 := by
          by_contra h
          obtain ⟨t, ht, hzero⟩ := hcI.intermediate_value hu₀ hu hycont
            (show (0 : ℝ) ∈ Set.Icc ⟪b 1, r u₀⟫_ℝ ⟪b 1, r u⟫_ℝ from ⟨le_of_lt hneg, le_of_not_gt h⟩)
          exact hyne t ht hzero
        nlinarith
      · refine ⟨1, Or.inl rfl, ?_⟩
        intro u hu
        have hn : 0 < ⟪b 1, r u⟫_ℝ := by
          by_contra h
          obtain ⟨t, ht, hzero⟩ := hcI.intermediate_value hu hu₀ hycont
            (show (0 : ℝ) ∈ Set.Icc ⟪b 1, r u⟫_ℝ ⟪b 1, r u₀⟫_ℝ from ⟨le_of_not_gt h, le_of_lt hpos⟩)
          exact hyne t ht hzero
        simpa using hn
    obtain ⟨s, hs, hsy⟩ := hsign
    let ε := (1 - z) / 2
    have hepos : 0 < ε := by
      dsimp only [ε]
      nlinarith only [hinterior u₀ hu₀, sq_nonneg (x+c*u₀), sq_nonneg (z-1)]
    have hele : ε ≤ 1/2 := by dsimp only [ε]; change 0 ≤ z at hz; linarith only [hz]
    have hH : 4 * ε * (1 - ε) = 1 - z^2 := by dsimp [ε]; ring
    have hzε : z = 1 - 2*ε := by dsimp [ε]; ring
    have hysqrt (u : ℝ) (hu : u ∈ I) :
        ⟪b 1, r u⟫_ℝ = s * Real.sqrt (4 * ε * (1 - ε) - (x + c*u)^2) := by
      have hy := hsphere u hu
      have hlt := hinterior u hu
      have hsq := Real.sq_sqrt (show 0 ≤ 4*ε*(1-ε)-(x+c*u)^2 by rw [hH]; linarith)
      have hn := Real.sqrt_nonneg (4*ε*(1-ε)-(x+c*u)^2)
      have hsig := hsy u hu
      rw [hH] at hsq hn ⊢
      rcases hs with rfl | rfl <;> nlinarith only [hy, hsq, hn, hsig]
    refine ⟨b, x, c, ε, s, hcpos, hepos, hele, hs, hK, ?_, ?_, ?_⟩
    · intro u hu
      ext i
      fin_cases i <;> simp [OrthonormalBasis.repr_apply_apply, hX u hu, hZ u hu, hysqrt u hu, hzε]
    · intro u hu
      rw [hH]
      linarith [hinterior u hu]
    · intro R hR hsub
      have hm := hinterior (-R) (hsub (by constructor <;> linarith))
      have hp := hinterior R (hsub (by constructor <;> linarith))
      have hh : 0 ≤ 4*ε*(1-ε) := by rw [hH]; nlinarith only [hp, sq_nonneg (x+c*R)]
      have hh2 := Real.sq_sqrt hh
      have hhn := Real.sqrt_nonneg (4*ε*(1-ε))
      rw [hH] at hh2 hhn ⊢
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        nlinarith only [hp, hh2, hhn, hx, mul_nonneg hcpos.le hR]
      · rw [abs_of_nonpos hx]
        nlinarith only [hm, hh2, hhn, hx, mul_nonneg hcpos.le hR]

  have effect_bound (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
      ‖bloch M‖ ≤ (Matrix.trace M).re := by
    have ht := (Complex.nonneg_iff.mp hM.trace_nonneg).1
    have hd := (Complex.nonneg_iff.mp hM.det_nonneg).1
    have he : (Matrix.det M).re = ((Matrix.trace M).re^2-‖bloch M‖^2)/4 := by
      conv_lhs => rw [(matrix_bloch_geometry M hM.isHermitian).1]
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [blochMatrix, Matrix.det_fin_two, Fin.sum_univ_three]
      ring
    rw [he] at hd
    nlinarith only [ht,hd,norm_nonneg (bloch M)]
  intro m N rho p v I hI hcI h0 hv hN hnorm hc hrho hread hrank
  let r := fun u => bloch (rho u)
  let p' := fun j => p j - (Matrix.trace (N j)).re / 2
  have hpure : ∀ u ∈ I, ‖r u‖ = 1 := by
    intro u hu
    exact (matrix_bloch_geometry (rho u) (hrho u hu).1.isHermitian).2
      (hrho u hu).2.1 (hrho u hu).2.2
  have hbr : ∀ u ∈ I, effectReadout N (r u) = p' + u • v := by
    intro u hu
    ext j
    have h := trace_bloch_pairing (N j) (rho u) (hN j).isHermitian (hrho u hu).1.isHermitian
    rw [(hrho u hu).2.1] at h
    have hr := hread u hu j
    change ⟪bloch (N j), bloch (rho u)⟫_ℝ / 2 = p j - (Matrix.trace (N j)).re / 2 + u * v j
    simp only [Complex.one_re, mul_one] at h
    linarith
  have hcont : ContinuousOn r I :=
    blochLinear.continuous_of_finiteDimensional.comp_continuousOn hc.continuousOn
  obtain ⟨basis,x,c,ε,s,hcpos,hepos,hele,hs,hK,hcoords,hinside,hend⟩ :=
    geometric_normal_form (effectReadout N) r p' v I hI hcI ⟨0,h0⟩ hv hcont hpure hbr hrank
  let A := fun j => ((Matrix.trace (N j)).re + basis.repr (bloch (N j)) 2)/2
  let q := fun j => ((Matrix.trace (N j)).re - basis.repr (bloch (N j)) 2)/2
  let b := fun j => basis.repr (bloch (N j)) 0/2
  have hz (j : Fin m) : basis.repr (bloch (N j)) 1 = 0 := by
    have hk : basis 1 ∈ (effectReadout N).ker := by
      rw [hK]; exact Submodule.mem_span_singleton_self _
    have hh := congrFun (LinearMap.mem_ker.mp hk) j
    change ⟪bloch (N j),basis 1⟫_ℝ/2=0 at hh
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
    linarith only [hh]
  have hdiag (j : Fin m) : 0 ≤ q j ∧ 0 ≤ A j ∧ b j^2 ≤ A j*q j := by
    have hn : ‖basis.repr (bloch (N j))‖ ≤ (Matrix.trace (N j)).re := by
      rw [basis.repr.norm_map]
      exact effect_bound (N j) (hN j)
    have ht : 0 ≤ (Matrix.trace (N j)).re := (norm_nonneg _).trans hn
    have hn2 := (sq_le_sq₀ (norm_nonneg _) ht).mpr hn
    have hsq : (basis.repr (bloch (N j)) 0)^2 + (basis.repr (bloch (N j)) 2)^2 =
        ‖basis.repr (bloch (N j))‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_three,hz j]
    dsimp [A,q,b]
    refine ⟨?_,?_,?_⟩ <;>
      nlinarith only [hn2,hsq,ht,sq_nonneg (basis.repr (bloch (N j)) 0)]
  have hformula (j : Fin m) (u : ℝ) (hu : u ∈ I) :
      A j*(1-ε)+b j*(x+c*u)+q j*ε = p j+u*v j := by
    have hh := trace_bloch_pairing (N j) (rho u) (hN j).isHermitian (hrho u hu).1.isHermitian
    rw [(hrho u hu).2.1, ← basis.repr.inner_map_map, hcoords u hu] at hh
    simp [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, hz j] at hh
    dsimp [A,q,b]
    nlinarith only [hh,hread u hu j]
  obtain ⟨δ,hδ,hδI⟩ := Metric.isOpen_iff.mp hI 0 h0
  have htmem : δ/2 ∈ I := hδI (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]
    linarith only [hδ])
  have hcoeff (j : Fin m) : b j=v j/c ∧ A j=(p j-b j*x-ε*q j)/(1-ε) := by
    have hbase := hformula j 0 h0
    have hshift := hformula j (δ/2) htmem
    have hvel : b j*c=v j := by nlinarith only [hbase,hshift,hδ]
    refine ⟨(eq_div_iff hcpos.ne').mpr hvel,?_⟩
    apply (eq_div_iff (by linarith only [hele] : 1-ε≠0)).mpr
    nlinarith only [hbase]
  have hqsum : ∑ j,q j=1 := by
    have ht : (∑ j,(Matrix.trace (N j)).re)=2 := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, hnorm]
      norm_num [Matrix.trace,Fin.sum_univ_two]
    have hvec : ∑ j,basis.repr (bloch (N j))=0 := by
      change ∑ j,basis.repr (blochLinear (N j))=0
      rw [← map_sum, ← map_sum, hnorm]
      have he : blochLinear (1 : Matrix (Fin 2) (Fin 2) ℂ)=0 := by
        ext i; fin_cases i <;> simp [blochLinear,bloch]
      rw [he,map_zero]
    have hzsum : ∑ j,basis.repr (bloch (N j)) 2=0 := by
      simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 2) hvec
    dsimp [q]
    rw [← Finset.sum_div, Finset.sum_sub_distrib,ht,hzsum]
    norm_num
  refine ⟨basis,x,c,ε,s,A,q,b,hcpos,hepos,hele,hs,?_,hqsum,?_,hinside,hend⟩
  · intro j
    exact ⟨(hdiag j).1,(hdiag j).2.1,(hdiag j).2.2,(hcoeff j).1,(hcoeff j).2⟩
  · intro u hu
    simp only [reframe,(hrho u hu).2.1,Complex.one_re]
    rw [hcoords u hu]

theorem actual_effect_family : ∀ {ι : Type} [Fintype ι]
      (p d : ι → ℝ) (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j=1) (hd0 : ∑ j, d j=0) (hd : ∑ j, d j^2/p j=1)
      (B : ℝ) (hB : 0 < B),
      let α := -2*∑ j, d j^3/(p j)^2
      ∃ w t : ℝ → ℝ, w 0=1 ∧ t 0=0 ∧
        Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/R^2) (𝓝[>] 0)
          (𝓝 (B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2))) ∧
        (∀ᶠ R in 𝓝[>] 0,
          0<R ∧ 0<t R ∧ t R<1 ∧ 0<w ((t R)^2) ∧
          (∑ j, root (p j) (d j) α ((t R)^2) (w ((t R)^2))=1) ∧
          (∀ j, (effect (p j) (d j) α ((t R)^2) (w ((t R)^2))).PosSemidef) ∧
          (∑ j, effect (p j) (d j) α ((t R)^2) (w ((t R)^2))=1) ∧
          radiusMap B α w (t R)=R ∧
          (∀ j, 0<p j-α*(t R)^2*w ((t R)^2)*d j ∧
            0<(p j-α*(t R)^2*w ((t R)^2)*d j)^2-
              4*(t R)^2*(1-(t R)^2)*(w ((t R)^2))^2*d j^2) ∧
          (∀ j, R*(1+t R)*|Real.sqrt B*d j| < p j)) := by
  classical
  have normalized_effect_family : ∀ {ι : Type} [Fintype ι]
      (p d : ι → ℝ) (α : ℝ) (hp : ∀ j, 0 < p j)
      (hp1 : ∑ j, p j = 1) (hd0 : ∑ j, d j = 0) (hd : ∑ j, d j^2/p j = 1),
      ∃ w : ℝ → ℝ, w 0 = 1 ∧
        HasStrictDerivAt w ((1 - ∑ j, d j^4/(p j)^3 - α*∑ j, d j^3/(p j)^2)/2) 0 ∧
        (∀ᶠ e in 𝓝 0, 0 < w e ∧ (∑ j, root (p j) (d j) α e (w e) = 1) ∧
          (∀ j, (effect (p j) (d j) α e (w e)).PosSemidef) ∧
          (∑ j, effect (p j) (d j) α e (w e) = 1)) := by
    classical
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

    have normalized_branch {ι : Type} [Fintype ι]
        (p d : ι → ℝ) (α : ℝ) (hp : ∀ j, 0 < p j)
        (hd : ∑ j, d j ^ 2 / p j = 1) :
        ∃ w : ℝ → ℝ, w 0 = 1 ∧ DifferentiableAt ℝ w 0 ∧
          HasStrictDerivAt w (deriv w 0) 0 ∧
          (∀ᶠ e in 𝓝 0, 0 < w e ∧ ∑ j, root (p j) (d j) α e (w e) = 1) := by
      let F : ℝ × ℝ → ℝ := fun x => ∑ j, root (p j) (d j) α x.1 x.2
      have hroot (j : ι) : ContDiffAt ℝ 1
          (fun x : ℝ × ℝ => root (p j) (d j) α x.1 x.2) (0,1) := by
        unfold root
        apply ContDiffAt.div
        · fun_prop
        · apply ContDiffAt.add
          · fun_prop
          · apply ContDiffAt.sqrt
            · fun_prop
            · simpa using pow_ne_zero 2 (hp j).ne'
        · simpa [Real.sqrt_sq (hp j).le] using (by linarith [hp j] : p j + p j ≠ 0)
      have hF : ContDiffAt ℝ 1 F (0,1) := by
        exact ContDiffAt.sum fun j _ => hroot j
      have hstrict := hF.hasStrictFDerivAt (by norm_num)
      have hzero (w : ℝ) : F (0,w) = w^2 := by
        dsimp [F, root]
        simp only [mul_zero, zero_mul, sub_zero, one_mul, mul_one, Real.sqrt_sq (hp _).le]
        calc
          (∑ j, 2*w^2*d j^2 / (p j+p j)) = ∑ j, w^2 * (d j^2/p j) := by
            apply Finset.sum_congr rfl
            intro j _
            field_simp
            <;> ring
          _ = w^2 := by rw [← Finset.mul_sum, hd, mul_one]
      have hder : fderiv ℝ F (0,1) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
          (2:ℝ) • ContinuousLinearMap.id ℝ ℝ := by
        have h := hstrict.hasFDerivAt.comp (1:ℝ)
          ((hasFDerivAt_const (0:ℝ) (1:ℝ)).prodMk (hasFDerivAt_id (1:ℝ)))
        have h' : HasFDerivAt (fun w : ℝ => F (0,w))
            ((2:ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 := by
          simp only [hzero]
          simpa using ((hasFDerivAt_id (𝕜 := ℝ) (1:ℝ)).pow 2)
        convert h.unique h' using 1
        ext x
        rfl
      have hinv : (fderiv ℝ F (0,1) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
        rw [hder]
        apply ContinuousLinearMap.IsInvertible.of_inverse (g := (1/2:ℝ) • ContinuousLinearMap.id ℝ ℝ)
        · ext x; simp
        · ext x; simp
      let w := hstrict.implicitFunctionOfProdDomain hinv
      have hw0 : w 0 = 1 :=
        (hstrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
      have hwd : DifferentiableAt ℝ w 0 :=
        (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt
      have hws := (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasStrictDerivAt
      change HasStrictDerivAt w _ 0 at hws
      have hws' : HasStrictDerivAt w (deriv w 0) 0 := by
        simpa only [hws.hasDerivAt.deriv] using hws
      refine ⟨w, hw0, hwd, hws', ?_⟩
      filter_upwards [hstrict.eventually_apply_implicitFunctionOfProdDomain hinv,
        hwd.continuousAt.eventually (lt_mem_nhds (show 0 < w 0 by rw [hw0]; norm_num))] with e he hpw
      exact ⟨hpw, he.trans (by simpa using hzero 1)⟩

    have root_deriv (p d α : ℝ) (hp : 0 < p) (w : ℝ → ℝ) (k : ℝ)
        (hw : w 0 = 1) (hk : HasDerivAt w k 0) :
        HasDerivAt (fun e => root p d α e (w e))
          ((-1+2*k)*d^2/p + α*d^3/p^2 + d^4/p^3) 0 := by
      have he := hasDerivAt_id (0:ℝ)
      have hA : HasDerivAt (fun e : ℝ => p-α*e*w e*d) (-α*d) 0 := by
        convert (hasDerivAt_const (0:ℝ) p).sub (((he.const_mul α).mul hk).mul_const d) using 1 <;> first | rfl | (simp [hw] <;> ring) | (funext e; simp; ring)
      have hD : HasDerivAt (fun e : ℝ => (p-α*e*w e*d)^2-4*e*(1-e)*(w e)^2*d^2)
          (-2*p*α*d-4*d^2) 0 := by
        convert (hA.pow 2).sub (((((he.const_mul 4).mul
          ((hasDerivAt_const (0:ℝ) 1).sub he)).mul (hk.pow 2)).mul_const (d^2))) using 1 <;> first | rfl | (simp [hw] <;> ring) | (funext e; simp; ring) <;> ring
      have hS := hD.sqrt (by simpa using pow_ne_zero 2 hp.ne')
      have hN := ((((hasDerivAt_const (0:ℝ) 1).sub he).const_mul 2).mul (hk.pow 2)).mul_const (d^2)
      have h := hN.div (hA.add hS) (by simpa [Real.sqrt_sq hp.le] using (by linarith : p+p ≠ 0))
      change HasDerivAt (fun e => root p d α e (w e)) _ 0 at h
      convert h using 1
      try dsimp
      simp only [hw, mul_zero, zero_mul, sub_zero, one_pow, mul_one, one_mul,
        Real.sqrt_sq hp.le]
      field_simp
      <;> ring

    have branch_with_derivative {ι : Type} [Fintype ι]
        (p d : ι → ℝ) (α : ℝ) (hp : ∀ j, 0 < p j)
        (hd : ∑ j, d j ^ 2 / p j = 1) :
        ∃ w : ℝ → ℝ, w 0 = 1 ∧
          HasStrictDerivAt w ((1 - ∑ j, d j^4/(p j)^3 - α*∑ j, d j^3/(p j)^2)/2) 0 ∧
          (∀ᶠ e in 𝓝 0, 0 < w e ∧ ∑ j, root (p j) (d j) α e (w e) = 1) := by
      obtain ⟨w, hw, hwd, hws, hnorm⟩ := normalized_branch p d α hp hd
      have hq := HasDerivAt.fun_sum (u := Finset.univ)
        (fun j _ => root_deriv (p j) (d j) α (hp j) w (deriv w 0) hw hwd.hasDerivAt)
      have hconst : HasDerivAt (fun e => ∑ j, root (p j) (d j) α e (w e)) 0 0 := by
        apply (hasDerivAt_const (0:ℝ) (1:ℝ)).congr_of_eventuallyEq
        filter_upwards [hnorm] with e he
        exact he.2
      have heq := hq.unique hconst
      have hk : deriv w 0 = (1 - ∑ j, d j^4/(p j)^3 - α*∑ j, d j^3/(p j)^2)/2 := by
        simp only [Finset.sum_add_distrib, mul_div_assoc, ← Finset.mul_sum, hd] at heq
        linarith
      exact ⟨w, hw, hk ▸ hws, hnorm⟩

    have root_facts (p d α e w : ℝ) (he : e < 1)
        (hA : 0 < p-α*e*w*d)
        (hD : 0 < (p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2) :
        0 < upperDiag p d α e w ∧ 0 ≤ root p d α e w ∧
        upperDiag p d α e w * root p d α e w = (w*d)^2 ∧
        (1-e)*upperDiag p d α e w + e*root p d α e w + α*e*w*d = p := by
      let A := p-α*e*w*d
      let S := Real.sqrt (A^2-4*e*(1-e)*w^2*d^2)
      have hS : 0 ≤ S := Real.sqrt_nonneg _
      have hSS : S^2=A^2-4*e*(1-e)*w^2*d^2 := Real.sq_sqrt hD.le
      have hden : A+S ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hA hS)
      have he' : 1-e ≠ 0 := ne_of_gt (sub_pos.mpr he)
      change 0 < (A+S)/(2*(1-e)) ∧ 0 ≤ 2*(1-e)*w^2*d^2/(A+S) ∧
        (A+S)/(2*(1-e))*(2*(1-e)*w^2*d^2/(A+S))=(w*d)^2 ∧
        (1-e)*((A+S)/(2*(1-e)))+e*(2*(1-e)*w^2*d^2/(A+S))+α*e*w*d=p
      refine ⟨div_pos (by linarith) (by linarith), div_nonneg (by positivity) (by linarith), ?_, ?_⟩
      · field_simp
        <;> ring
      · field_simp
        dsimp only [A] at hSS ⊢
        nlinarith only [hSS]

    have effects_are_povm {ι : Type} [Fintype ι]
        (p d : ι → ℝ) (α e w : ℝ)
        (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) (hd0 : ∑ j, d j = 0)
        (he : e < 1)
        (hA : ∀ j, 0 < p j-α*e*w*d j)
        (hD : ∀ j, 0 < (p j-α*e*w*d j)^2-4*e*(1-e)*w^2*d j^2)
        (hq : ∑ j, root (p j) (d j) α e w = 1) :
        (∀ j, (effect (p j) (d j) α e w).PosSemidef) ∧
        (∑ j, effect (p j) (d j) α e w = 1) := by
      have hf j := root_facts (p j) (d j) α e w he (hA j) (hD j)
      have ha : ∑ j, upperDiag (p j) (d j) α e w = 1 := by
        have h := congrArg (fun f : ι → ℝ => ∑ j, f j) (funext fun j => (hf j).2.2.2)
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hd0, hq, mul_zero, add_zero] at h
        nlinarith
      refine ⟨?_, ?_⟩
      · intro j
        let a := upperDiag (p j) (d j) α e w
        let q := root (p j) (d j) α e w
        let b := w*d j
        have heq : effect (p j) (d j) α e w = blochMatrix (a+q) (WithLp.toLp 2 ![2*b,0,a-q]) := by
          ext i k
          fin_cases i <;> fin_cases k <;> apply Complex.ext <;> simp [effect, blochMatrix, a,q,b] <;> ring
        rw [heq, (blochMatrix_properties _ _).2.2.2.2]
        have hn : ‖(WithLp.toLp 2 ![2*b,0,a-q] : (EuclideanSpace ℝ (Fin 3)))‖^2 = (a+q)^2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [Fin.sum_univ_three]
          have hmul : a*q=b^2 := (hf j).2.2.1
          nlinarith
        have hpos : 0 ≤ a+q := add_nonneg (hf j).1.le (hf j).2.1
        nlinarith [norm_nonneg (WithLp.toLp 2 ![2*b,0,a-q] : (EuclideanSpace ℝ (Fin 3)))]
      · ext i k
        fin_cases i <;> fin_cases k <;> simp [Matrix.sum_apply, effect, ← Complex.ofReal_sum, ha, hq,
          ← Finset.mul_sum, hd0]

    intro ι inst p d α hp hp1 hd0 hd
    obtain ⟨w, hw, hwd, hn⟩ := branch_with_derivative p d α hp hd
    have hcont : ContinuousAt w 0 := hwd.hasDerivAt.continuousAt
    have hcoeff : ∀ᶠ e in 𝓝 (0:ℝ), ∀ j,
        0<p j-α*e*w e*d j ∧
        0<(p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2 := by
      apply eventually_all.mpr
      intro j
      have hA : ContinuousAt (fun e : ℝ => p j-α*e*w e*d j) 0 := by fun_prop
      have hD : ContinuousAt (fun e : ℝ => (p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2) 0 := by fun_prop
      exact (hA.eventually (lt_mem_nhds (by simpa using hp j))).and
        (hD.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos (hp j))))
    refine ⟨w,hw,hwd,?_⟩
    filter_upwards [hn,hcoeff,gt_mem_nhds (by norm_num : (0:ℝ)<1)] with e hn he he1
    obtain ⟨hN,hN1⟩ := effects_are_povm p d α e (w e) hp hp1 hd0 he1
      (fun j => (he j).1) (fun j => (he j).2) hn.2
    exact ⟨hn.1,hn.2,hN,hN1⟩

  have radius_branch (B α : ℝ) (hB : 0 < B) (w : ℝ → ℝ) (k : ℝ)
      (hw : w 0 = 1) (hk : HasStrictDerivAt w k 0) :
      ∃ t : ℝ → ℝ, t 0 = 0 ∧ HasDerivAt t (Real.sqrt B/2) 0 ∧
        (∀ᶠ R in 𝓝 0, radiusMap B α w (t R) = R) := by
    have he := hasStrictDerivAt_id (0:ℝ)
    have hs := (((hasStrictDerivAt_const (0:ℝ) (1:ℝ)).sub (he.pow 2)).sqrt (by norm_num))
    have hkk : HasStrictDerivAt w k ((id ^ 2) (0:ℝ)) := by simpa using hk
    have hc := hkk.comp (0:ℝ) (he.pow 2)
    have hf : HasStrictDerivAt (radiusMap B α w) (2/Real.sqrt B) 0 := by
      have h := ((((he.const_mul 2).mul hs).sub ((he.pow 2).const_mul |α|)).mul hc).div
        (((hasStrictDerivAt_const (0:ℝ) (1:ℝ)).add he).mul_const (Real.sqrt B))
        (by simpa using (Real.sqrt_pos.mpr hB).ne')
      convert h using 1 <;> first | rfl | (simp [hw] <;> field_simp <;> ring)
    have hn : 2/Real.sqrt B ≠ 0 := div_ne_zero (by norm_num) (Real.sqrt_pos.mpr hB).ne'
    let t := hf.localInverse (radiusMap B α w) (2/Real.sqrt B) 0 hn
    have hzero : radiusMap B α w 0 = 0 := by simp [radiusMap]
    have ht0 : t 0 = 0 := by
      simpa only [hzero] using (hf.hasStrictFDerivAt_equiv hn).localInverse_apply_image
    have htd : HasDerivAt t (Real.sqrt B/2) 0 := by
      simpa only [hzero, inv_div] using (hf.to_localInverse hn).hasDerivAt
    exact ⟨t, ht0, htd, by simpa only [hzero] using hf.eventually_right_inverse hn⟩

  have cost_derivative (B α : ℝ) (w : ℝ → ℝ) (k : ℝ)
      (hw : w 0=1) (hk : HasDerivAt w k 0) :
      extendedCost B α w 0 = B ∧
      HasDerivAt (extendedCost B α w) (B*(-2*k+α^2/4)) 0 := by
    refine ⟨by simp [extendedCost,hw], ?_⟩
    have he := hasDerivAt_id (0:ℝ)
    have hone := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub he
    have hnum := ((hasDerivAt_const (0:ℝ) B).div (hk.pow 2) (by simp [hw])).mul (hone.const_mul 4)
    have hden := (hone.const_mul 4).sub (he.const_mul (α^2))
    have h := hnum.div hden (by norm_num)
    change HasDerivAt (extendedCost B α w) _ 0 at h
    convert h using 1 <;> first | rfl | (simp [hw] <;> ring)

  intro ι inst p d hp hp1 hd0 hd B hB
  dsimp only
  let α := -2*∑ j, d j^3/(p j)^2
  let k := (1-∑ j, d j^4/(p j)^3-α*∑ j, d j^3/(p j)^2)/2
  obtain ⟨w, hw, hkw, hn⟩ := normalized_effect_family p d α hp hp1 hd0 hd
  change HasStrictDerivAt w k 0 at hkw
  have hwcont := hkw.hasDerivAt.continuousAt
  obtain ⟨t, ht, htd, hrad⟩ := radius_branch B α hB w k hw hkw
  have htlim : Tendsto t (𝓝[>] 0) (𝓝 0) := by
    simpa [ht] using htd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have helim : Tendsto (fun R => (t R)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using htlim.pow 2
  have hwlim : Tendsto (fun R => w ((t R)^2)) (𝓝[>] 0) (𝓝 1) := by
    simpa [hw,Function.comp_def] using hkw.hasDerivAt.continuousAt.tendsto.comp helim
  have hratio : Tendsto (fun R => t R/R) (𝓝[>] 0) (𝓝 (Real.sqrt B/2)) := by
    simpa [ht, div_eq_mul_inv, mul_comm] using htd.tendsto_slope_zero_right
  have htp : ∀ᶠ R in 𝓝[>] 0, 0 < t R := by
    filter_upwards [hratio.eventually (lt_mem_nhds (by positivity : 0 < Real.sqrt B/2)),
      self_mem_nhdsWithin] with R hq hR
    exact (div_pos_iff_of_pos_right hR).mp hq
  have hepunct : Tendsto (fun R => (t R)^2) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨helim, ?_⟩
    filter_upwards [htp] with R hR
    exact pow_ne_zero 2 hR.ne'
  obtain ⟨hq0,hqd⟩ := cost_derivative B α w k hw hkw.hasDerivAt
  have hqs : Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/(t R)^2)
      (𝓝[>] 0) (𝓝 (B*(-2*k+α^2/4))) := by
    simpa [Function.comp_def, slope, hq0, div_eq_mul_inv, mul_comm] using hqd.tendsto_slope.comp hepunct
  have hlimit : Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/R^2)
      (𝓝[>] 0) (𝓝 (B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2))) := by
    have h := hqs.mul (hratio.pow 2)
    have hv : B*(-2*k+α^2/4)*(Real.sqrt B/2)^2 =
        B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2) := by
      rw [div_pow, Real.sq_sqrt hB.le]
      dsimp [α,k]
      ring
    rw [hv] at h
    apply h.congr'
    filter_upwards [htp, self_mem_nhdsWithin] with R htR hR
    try dsimp
    field_simp
  have hcoeff : ∀ᶠ e in 𝓝 (0:ℝ), ∀ j,
      0<p j-α*e*w e*d j ∧
      0<(p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2 := by
    apply (eventually_all).mpr
    intro j
    have hcA : ContinuousAt (fun e : ℝ => p j-α*e*w e*d j) 0 := by fun_prop
    have hcD : ContinuousAt (fun e : ℝ =>
        (p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2) 0 := by fun_prop
    exact (hcA.eventually (lt_mem_nhds (by simpa using hp j))).and
      (hcD.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos (hp j))))
  have hprob : ∀ᶠ R in 𝓝[>] (0:ℝ), ∀ j,
      R*(1+t R)*|Real.sqrt B*d j| < p j := by
    apply eventually_all.mpr
    intro j
    have h : Tendsto (fun R : ℝ => R*(1+t R)*|Real.sqrt B*d j|) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).mul
        (tendsto_const_nhds.add htlim)).mul_const |Real.sqrt B*d j|
    exact h.eventually (gt_mem_nhds (hp j))
  refine ⟨w,t,hw,ht,hlimit,?_⟩
  filter_upwards [self_mem_nhdsWithin, htp, htlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    helim.eventually hn, hrad.filter_mono nhdsWithin_le_nhds, helim.eventually hcoeff, hprob]
    with R hR htp ht1 hnorm hr hc hp'
  exact ⟨hR,htp,ht1,hnorm.1,hnorm.2.1,hnorm.2.2.1,hnorm.2.2.2,hr,hc,hp'⟩

theorem actual_upper_family : ∀ {m : ℕ}
      (p d : Fin m → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j, p j=1)
      (hd0 : ∑ j, d j=0) (hd : ∑ j, d j^2/p j=1) (B : ℝ) (hB : 0<B),
      ∃ (N : ℝ → Fin m → Matrix (Fin 2) (Fin 2) ℂ)
        (rho : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : ℝ → Set ℝ) (Q : ℝ → ℝ),
        Tendsto (fun R => (Q R-B)/R^2) (𝓝[>] 0)
          (𝓝 (B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2))) ∧
        (∀ᶠ R in 𝓝[>] 0, IsProgram p (fun j => Real.sqrt B*d j) R
          (N R) (rho R) (I R) (Q R)) := by
  classical
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

  have root_facts (p d α e w : ℝ) (he : e < 1)
      (hA : 0 < p-α*e*w*d)
      (hD : 0 < (p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2) :
      0 < upperDiag p d α e w ∧ 0 ≤ root p d α e w ∧
      upperDiag p d α e w * root p d α e w = (w*d)^2 ∧
      (1-e)*upperDiag p d α e w + e*root p d α e w + α*e*w*d = p := by
    let A := p-α*e*w*d
    let S := Real.sqrt (A^2-4*e*(1-e)*w^2*d^2)
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSS : S^2=A^2-4*e*(1-e)*w^2*d^2 := Real.sq_sqrt hD.le
    have hden : A+S ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hA hS)
    have he' : 1-e ≠ 0 := ne_of_gt (sub_pos.mpr he)
    change 0 < (A+S)/(2*(1-e)) ∧ 0 ≤ 2*(1-e)*w^2*d^2/(A+S) ∧
      (A+S)/(2*(1-e))*(2*(1-e)*w^2*d^2/(A+S))=(w*d)^2 ∧
      (1-e)*((A+S)/(2*(1-e)))+e*(2*(1-e)*w^2*d^2/(A+S))+α*e*w*d=p
    refine ⟨div_pos (by linarith) (by linarith), div_nonneg (by positivity) (by linarith), ?_, ?_⟩
    · field_simp
      <;> ring
    · field_simp
      dsimp only [A] at hSS ⊢
      nlinarith only [hSS]

  have arc_valid (e x c : ℝ) (I : Set ℝ) (hI : IsOpen I) (h0 : 0 ∈ I)
      (hinside : ∀ u ∈ I, (x+c*u)^2 < 4*e*(1-e)) :
      ContDiffOn ℝ 1 (arc e x c) I ∧
      (∀ u ∈ I, (arc e x c u).PosSemidef ∧ trace (arc e x c u) = 1 ∧
        arc e x c u * arc e x c u = arc e x c u) ∧
      (∀ h : (arc e x c 0).PosSemidef,
        spectralQFI (arc e x c 0) (deriv (arc e x c) 0) h =
        c^2*(4*e*(1-e))/(4*e*(1-e)-x^2)) := by
    have hr (u : ℝ) (hu : u ∈ I) :
        (Real.sqrt (4*e*(1-e)-(x+c*u)^2))^2 = 4*e*(1-e)-(x+c*u)^2 :=
      Real.sq_sqrt (sub_nonneg.mpr (hinside u hu).le)
    have hc : ContDiffOn ℝ 1 (arc e x c) I := by
      have hx : ContDiffOn ℝ 1 (fun u : ℝ => x+c*u) I := by fun_prop
      have hy : ContDiffOn ℝ 1 (fun u : ℝ => Real.sqrt (4*e*(1-e)-(x+c*u)^2)) I := by
        apply ContDiffOn.sqrt
        · fun_prop
        · intro u hu
          exact ne_of_gt (sub_pos.mpr (hinside u hu))
      have hxC := Complex.ofRealCLM.contDiff.comp_contDiffOn hx
      have hyC := Complex.ofRealCLM.contDiff.comp_contDiffOn hy
      apply contDiffOn_pi.mpr
      intro i
      apply contDiffOn_pi.mpr
      intro j
      fin_cases i <;> fin_cases j
      · simp [arc,blochMatrix]; fun_prop
      · simpa [arc,blochMatrix] using (hxC.sub (hyC.mul contDiffOn_const)).div_const (2:ℂ)
      · simpa [arc,blochMatrix] using (hxC.add (hyC.mul contDiffOn_const)).div_const (2:ℂ)
      · simp [arc,blochMatrix]; fun_prop
    have hpure (u : ℝ) (hu : u ∈ I) :
        (arc e x c u).PosSemidef ∧ trace (arc e x c u) = 1 ∧
        arc e x c u * arc e x c u = arc e x c u := by
      have hn : ‖(WithLp.toLp 2 ![x+c*u,Real.sqrt (4*e*(1-e)-(x+c*u)^2),1-2*e] : (EuclideanSpace ℝ (Fin 3)))‖ = 1 := by
        have hsq : ‖(WithLp.toLp 2 ![x+c*u,Real.sqrt (4*e*(1-e)-(x+c*u)^2),1-2*e] : (EuclideanSpace ℝ (Fin 3)))‖^2 = 1 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [Fin.sum_univ_three, hr u hu]
          ring
        nlinarith [norm_nonneg (WithLp.toLp 2 ![x+c*u,Real.sqrt (4*e*(1-e)-(x+c*u)^2),1-2*e] : (EuclideanSpace ℝ (Fin 3)))]
      refine ⟨(blochMatrix_properties _ _).2.2.2.2.mpr hn.le,
        (blochMatrix_properties _ _).2.1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [arc, blochMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
        nlinarith [hr u hu]
    refine ⟨hc,hpure,?_⟩
    intro h
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

    have energy (r d : Matrix (Fin 2) (Fin 2) ℂ) (h : d*r+r*d=d) :
        (Matrix.trace (((2:ℂ) • d)*r*((2:ℂ) • d))).re =
          2*(Matrix.trace (d*d)).re := by
      have ht := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (Matrix.trace (M*d)).re) h
      simp only [add_mul, Matrix.trace_add, Complex.add_re] at ht
      rw [← Matrix.trace_mul_cycle r d d] at ht
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re]
      norm_num
      rw [← Matrix.trace_mul_cycle r d d]
      linarith
    let y := Real.sqrt (4*e*(1-e)-x^2)
    have hinside0 : x^2 < 4*e*(1-e) := by simpa only [mul_zero, add_zero] using hinside 0 h0
    have hy : 0 < y := Real.sqrt_pos.mpr (sub_pos.mpr hinside0)
    have hy2 : y^2=4*e*(1-e)-x^2 := Real.sq_sqrt (sub_nonneg.mpr hinside0.le)
    let D := blochMatrix 0 (WithLp.toLp 2 ![c,-x*c/y,0])
    have hx : HasDerivAt (fun u : ℝ => x+c*u) c 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_mul c).const_add x
    have hys : HasDerivAt (fun u : ℝ => Real.sqrt (4*e*(1-e)-(x+c*u)^2))
        (-x*c/y) 0 := by
      have hh := ((hasDerivAt_const (0:ℝ) (4*e*(1-e))).sub (hx.pow 2)).sqrt
        (by simpa using ne_of_gt (sub_pos.mpr hinside0))
      convert hh using 1 <;> first | rfl | (dsimp [y]; ring)
    have hxC : HasDerivAt (fun u : ℝ => ((x+c*u : ℝ):ℂ)) (c:ℂ) 0 :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hx
    have hyC : HasDerivAt (fun u : ℝ => ((Real.sqrt (4*e*(1-e)-(x+c*u)^2):ℝ):ℂ))
        ((-x*c/y:ℝ):ℂ) 0 := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hys
    have hd : HasDerivAt (arc e x c) D 0 := by
      apply hasDerivAt_pi.mpr
      intro i
      apply hasDerivAt_pi.mpr
      intro j
      fin_cases i <;> fin_cases j
      · simpa [arc,blochMatrix,D] using hasDerivAt_const (0:ℝ) (((1+(1-2*e):ℝ):ℂ)/2)
      · simpa [arc,blochMatrix,D] using (hxC.sub (hyC.mul_const Complex.I)).div_const 2
      · simpa [arc,blochMatrix,D] using (hxC.add (hyC.mul_const Complex.I)).div_const 2
      · simpa [arc,blochMatrix,D] using hasDerivAt_const (0:ℝ) (((1-(1-2*e):ℝ):ℂ)/2)
    have hD : D.IsHermitian := (blochMatrix_properties _ _).1
    have he (i j : Fin 2) : HasDerivAt (fun u => arc e x c u i j) (D i j) 0 :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
    have hprod : HasDerivAt (fun u => arc e x c u * arc e x c u)
        (D*arc e x c 0+arc e x c 0*D) 0 := by
      apply hasDerivAt_pi.mpr
      intro i
      apply hasDerivAt_pi.mpr
      intro j
      simp only [Matrix.mul_apply, Matrix.add_apply]
      rw [← Finset.sum_add_distrib]
      exact HasDerivAt.fun_sum fun k _ => (he i k).mul (he k j)
    have htan : D*arc e x c 0+arc e x c 0*D=D := by
      apply hprod.unique
      apply hd.congr_of_eventuallyEq
      filter_upwards [hI.mem_nhds h0] with u hu
      exact (hpure u hu).2.2
    have hSLD : ((2:ℂ) • D)*arc e x c 0+arc e x c 0*((2:ℂ) • D)=(2:ℂ) • D := by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, htan]
    have hQ := spectral_energy (arc e x c 0) D ((2:ℂ) • D)
      h (hD.smul (by norm_num)) hSLD
    have hdd : 2*(Matrix.trace (D*D)).re = c^2+(x*c/y)^2 := by
      simp [D, blochMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hderiv : deriv (arc e x c) 0 = D := hd.deriv
    calc
      spectralQFI (arc e x c 0) (deriv (arc e x c) 0) h = spectralQFI (arc e x c 0) D h :=
        congrArg (fun d => spectralQFI (arc e x c 0) d h) hderiv
      _ = 2*(Matrix.trace (D*D)).re := hQ.symm.trans (energy _ _ htan)
      _ = c^2+(x*c/y)^2 := hdd
      _ = _ := by
        rw [div_pow, hy2]
        field_simp [ne_of_gt (sub_pos.mpr hinside0)]
        <;> ring

  have born_exact (p d α e w c u : ℝ) (he : e < 1)
      (hA : 0 < p-α*e*w*d)
      (hD : 0 < (p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2) :
      trace (effect p d α e w * arc e (α*e) c u) = ((p+u*(c*w*d):ℝ):ℂ) := by
    have h := (root_facts p d α e w he hA hD).2.2.2
    apply Complex.ext <;>
      simp [effect, arc, blochMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im] <;> nlinarith [h]

  intro m p d hp hp1 hd0 hd B hB
  let α := -2*∑ j, d j^3/(p j)^2
  obtain ⟨w,t,hw,ht,hlim,hgood⟩ := actual_effect_family p d hp hp1 hd0 hd B hB
  change Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/R^2) _ _ at hlim
  let N := fun R j => effect (p j) (d j) α ((t R)^2) (w ((t R)^2))
  let rho := fun R => arc ((t R)^2) (α*(t R)^2) (Real.sqrt B/w ((t R)^2))
  let I := fun R => Ioo (-R*(1+t R)) (R*(1+t R))
  refine ⟨N,rho,I,fun R => extendedCost B α w ((t R)^2),hlim,?_⟩
  filter_upwards [hgood] with R hg
  rcases hg with ⟨hR,hT,hT1,hW,hq,hN,hN1,hr,hcoeff,hprob⟩
  let T := t R
  let W := w (T^2)
  let c := Real.sqrt B/W
  have hBroot : 0<Real.sqrt B := Real.sqrt_pos.mpr hB
  have hc : 0<c := div_pos hBroot hW
  have he : T^2<1 := by dsimp [T]; nlinarith only [hT,hT1]
  have hep : 0<T^2 := sq_pos_of_pos hT
  have hLs : R<R*(1+T) := by nlinarith only [mul_pos hR hT]
  have hrad : |α| *T^2+c*(R*(1+T))=2*T*Real.sqrt (1-T^2) := by
    change radiusMap B α w T=R at hr
    unfold radiusMap at hr
    have hh := (div_eq_iff (ne_of_gt (mul_pos (by linarith : 0<1+T) hBroot))).mp hr
    dsimp [c,W]
    field_simp [show w (T^2) ≠ 0 from hW.ne']
    nlinarith only [hh]
  have hinside (u : ℝ) (hu : u ∈ I R) : (α*T^2+c*u)^2<4*T^2*(1-T^2) := by
    have huabs : |u|<R*(1+T) := abs_lt.mpr (by simpa [I,T,neg_mul] using hu)
    have hab : |α*T^2+c*u| < 2*T*Real.sqrt (1-T^2) := by
      calc
        |α*T^2+c*u| ≤ |α*T^2|+|c*u| := abs_add_le _ _
        _ = |α| *T^2+c*|u| := by simp only [abs_mul,abs_of_pos hc,abs_of_nonneg (sq_nonneg T)]
        _ < |α| *T^2+c*(R*(1+T)) := add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left huabs hc)
        _ = _ := hrad
    have hs := Real.sq_sqrt (sub_nonneg.mpr he.le)
    have hp : 0≤2*T*Real.sqrt (1-T^2) := by positivity
    have hsq := (sq_lt_sq₀ (abs_nonneg (α*T^2+c*u)) hp).mpr hab
    rw [sq_abs] at hsq
    have heq : (2*T*Real.sqrt (1-T^2))^2 = 4*T^2*(1-T^2) := by
      rw [mul_pow, hs]
      ring
    rwa [heq] at hsq
  have h0 : 0∈I R := by
    change -R*(1+T)<0 ∧ 0<R*(1+T)
    have hpos := mul_pos hR (show 0<1+T by linarith only [hT])
    constructor <;> linarith only [hpos]
  obtain ⟨hsmooth,hpure,hcost⟩ := arc_valid (T^2) (α*T^2) c (I R) isOpen_Ioo h0 hinside
  change IsProgram p (fun j => Real.sqrt B*d j) R (N R) (rho R) (I R) _
  refine ⟨isOpen_Ioo, isPreconnected_Ioo, ?_,hN,hN1,hsmooth,?_,?_,?_⟩
  · intro u hu
    change -R*(1+T)<u ∧ u<R*(1+T)
    constructor <;> linarith only [hu.1,hu.2,hLs]
  · intro u hu
    let r := densityBridge (arc (T^2) (α*T^2) c u) (hpure u hu).1 (hpure u hu).2.1
    exact ⟨(hpure u hu).1,(hpure u hu).2.1,(hpure u hu).2.2,r.1,r.2⟩
  · intro u hu j
    have hcW : c*W=Real.sqrt B := div_mul_cancel₀ _ hW.ne'
    have hb := born_exact (p j) (d j) α (T^2) W c u he (hcoeff j).1 (hcoeff j).2
    rw [← mul_assoc, hcW] at hb
    refine ⟨by simpa only [mul_assoc] using hb,?_⟩
    have huabs : |u|<R*(1+T) := abs_lt.mpr (by simpa [I,T,neg_mul] using hu)
    have hbound : |u*(Real.sqrt B*d j)|<p j := by
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right huabs.le (abs_nonneg _)) (hprob j)
    linarith only [hbound, neg_abs_le (u*(Real.sqrt B*d j))]
  · intro h
    rw [hcost h]
    change (Real.sqrt B/W)^2*(4*T^2*(1-T^2))/(4*T^2*(1-T^2)-(α*T^2)^2) =
      B/W^2*(4*(1-T^2))/(4*(1-T^2)-α^2*T^2)
    rw [div_pow, Real.sq_sqrt hB.le]
    rw [show 4*T^2*(1-T^2)-(α*T^2)^2 = T^2*(4*(1-T^2)-α^2*T^2) by ring]
    calc
      B/W^2*(4*T^2*(1-T^2))/(T^2*(4*(1-T^2)-α^2*T^2)) =
          (T^2*(B/W^2*(4*(1-T^2))))/(T^2*(4*(1-T^2)-α^2*T^2)) := by ring
      _ = _ := mul_div_mul_left _ _ hep.ne'

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

theorem result {m : ℕ} (p v : Fin m → ℝ)
    (hp : ∀ j,0<p j) (hp1 : ∑ j,p j=1) (hv0 : ∑ j,v j=0) (hv : v≠0)
    (hthree : ∃ i j k,v i/p i≠v j/p j ∧ v i/p i≠v k/p k ∧ v j/p j≠v k/p k) :
    let B := ∑ j,p j*(v j/p j)^2
    let V := (∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B
    0<V ∧
    (∀ᶠ R in 𝓝[>] 0,(costs p v R).Nonempty ∧ BddBelow (costs p v R) ∧
      IsGLB (costs p v R) (C2 p v R)) ∧
    Tendsto (fun R => (C2 p v R-B)/R^2) (𝓝[>] 0) (𝓝 (V/4)) := by
  classical
  revert m

  have upper_result : ∀ {m : ℕ}
        (p v : Fin m → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j, p j=1)
        (hv0 : ∑ j, v j=0) (hv : ∃ j, v j ≠ 0),
        let B := ∑ j, v j^2/p j
        let V := (∑ j, v j^4/(p j)^3)-B^2-(∑ j, v j^3/(p j)^2)^2/B
        ∃ (N : ℝ → Fin m → Matrix (Fin 2) (Fin 2) ℂ)
          (rho : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : ℝ → Set ℝ) (Q : ℝ → ℝ),
          Tendsto (fun R => (Q R-B)/R^2) (𝓝[>] 0) (𝓝 (V/4)) ∧
          (∀ᶠ R in 𝓝[>] 0, IsProgram p v R (N R) (rho R) (I R) (Q R)) := by
    intro m p v hp hp1 hv0 hv
    dsimp only
    let B := ∑ j, v j^2/p j
    have hB : 0<B := by
      obtain ⟨j,hj⟩ := hv
      exact Finset.sum_pos' (fun i _ => div_nonneg (sq_nonneg _) (hp i).le)
        ⟨j,Finset.mem_univ _, div_pos (sq_pos_of_ne_zero hj) (hp j)⟩
    let d := fun j => v j/Real.sqrt B
    have hs : Real.sqrt B ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
    have hd0 : ∑ j, d j=0 := by dsimp [d]; rw [← Finset.sum_div, hv0, zero_div]
    have hd : ∑ j, d j^2/p j=1 := by
      calc
        (∑ j, d j^2/p j) = (∑ j, v j^2/p j)/B := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j _
          dsimp [d]
          rw [div_pow, Real.sq_sqrt hB.le]
          ring
        _ = 1 := div_self hB.ne'
    obtain ⟨N,rho,I,Q,hlim,hprog⟩ := actual_upper_family p d hp hp1 hd0 hd B hB
    have hvd : (fun j => Real.sqrt B*d j)=v := by
      funext j
      dsimp [d]
      field_simp
    have hA3 : (∑ j, d j^3/(p j)^2) = (∑ j, v j^3/(p j)^2)/(Real.sqrt B)^3 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [d]
      rw [div_pow]
      ring
    have hA4 : (∑ j, d j^4/(p j)^3) = (∑ j, v j^4/(p j)^3)/(Real.sqrt B)^4 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [d]
      rw [div_pow]
      ring
    have hs4 : (Real.sqrt B)^4=B^2 := by
      calc
        (Real.sqrt B)^4=((Real.sqrt B)^2)^2 := by ring
        _=B^2 := by rw [Real.sq_sqrt hB.le]
    have hs6 : (Real.sqrt B)^6=B^3 := by
      calc
        (Real.sqrt B)^6=((Real.sqrt B)^2)^3 := by ring
        _=B^3 := by rw [Real.sq_sqrt hB.le]
    have hc : B^2/4*((∑ j, d j^4/(p j)^3)-1-(∑ j, d j^3/(p j)^2)^2) =
        ((∑ j, v j^4/(p j)^3)-B^2-(∑ j, v j^3/(p j)^2)^2/B)/4 := by
      rw [hA3,hA4,hs4,div_pow,←pow_mul]
      norm_num only [Nat.reduceMul]
      rw [hs6]
      field_simp
      <;> ring
    rw [hc] at hlim
    rw [hvd] at hprog
    exact ⟨N,rho,I,Q,hlim,hprog⟩

  have coefficient_inequality (p v b A q e c x : ℝ)
      (hp : 0 < p) (hc : 0 < c) (he : e < 1)
      (hb : b = v/c) (hAf : A = (p-b*x-e*q)/(1-e)) (hpsd : b^2 ≤ A*q) :
      e*(q/p)^2-(1-(x/c)*(v/p))*(q/p)+(1-e)*(1/c^2)*(v/p)^2 ≤ 0 := by
    clear * - p v b A q e c x hp hc he hb hAf hpsd
    have ha : 0 < 1-e := sub_pos.mpr he
    have hap := (eq_div_iff ha.ne').mp hAf
    have hh := mul_le_mul_of_nonneg_left hpsd ha.le
    have hid : (e*(q/p)^2-(1-(x/c)*(v/p))*(q/p)+(1-e)*(1/c^2)*(v/p)^2)*p^2 =
        (1-e)*b^2-(p-b*x-e*q)*q := by
      rw [hb]
      field_simp [hp.ne', hc.ne']
      ring
    have hh' : (1-e)*b^2-(p-b*x-e*q)*q ≤ 0 := by
      nlinarith only [hh, congrArg (fun r : ℝ => r*q) hap]
    rw [← hid] at hh'
    exact nonpos_of_mul_nonpos_left hh' (sq_pos_of_pos hp)

  have coefficient_degeneration {ι : Type} [Fintype ι]
      (p v : ι → ℝ) (B : ℝ)
      (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
      (hv : v ≠ 0) (hvsum : ∑ j, v j = 0)
      (hB : B = ∑ j, p j*(v j/p j)^2)
      (hthree : ∃ i j k, v i/p i ≠ v j/p j ∧ v i/p i ≠ v k/p k ∧ v j/p j ≠ v k/p k)
      (e c x Q : ℕ → ℝ) (q A b : ℕ → ι → ℝ)
      (he : ∀ n, 0 < e n ∧ e n ≤ 1/2) (hc : ∀ n, 0 < c n)
      (hq : ∀ n j, 0 ≤ q n j) (hA : ∀ n j, 0 ≤ A n j)
      (hqsum : ∀ n, ∑ j, q n j = 1)
      (hb : ∀ n j, b n j=v j/c n)
      (hAf : ∀ n j, A n j=(p j-b n j*x n-e n*q n j)/(1-e n))
      (hpsd : ∀ n j, b n j^2 ≤ A n j*q n j)
      (hinside : ∀ n, x n^2 < 4*e n*(1-e n))
      (hQf : ∀ n, Q n=c n^2*(4*e n*(1-e n))/(4*e n*(1-e n)-x n^2))
      (hQ : Tendsto Q atTop (𝓝 B)) :
      Tendsto e atTop (𝓝 0) ∧ Tendsto (fun n => c n^2) atTop (𝓝 B) ∧
      ∀ j, Tendsto (fun n => q n j) atTop (𝓝 (v j^2/(B*p j))) := by
    clear * - p v B hp hpsum hv hvsum hB hthree e c x Q q A b he hc hq hA hqsum hb hAf hpsd hinside hQf hQ coefficient_inequality
    have equality_obstruction
        (p s t : ι → ℝ) (B e u z : ℝ)
        (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
        (hsum : ∑ j, p j * s j = 0) (hB : ∑ j, p j * s j ^ 2 = B)
        (ht : ∑ j, p j * t j = 1) (hBp : 0 < B)
        (he : 0 < e) (heh : e ≤ 1/2)
        (hcost : B * ((1-e)*z-e*u^2) = 1-e)
        (hF : ∀ j, e*t j^2-(1-2*e*u*s j)*t j+(1-e)*z*s j^2 ≤ 0)
        (hthree : ∃ i j k, s i ≠ s j ∧ s i ≠ s k ∧ s j ≠ s k) : False := by
      clear * - p s t B e u z hp hpsum hsum hB ht hBp he heh hcost hF hthree
      classical
      let L := (1-e)*z-e*u^2
      let r := fun j => t j-1+u*s j
      let F := fun j => e*t j^2-(1-2*e*u*s j)*t j+(1-e)*z*s j^2
      have hL : 0 < L := by dsimp [L]; nlinarith only [hcost,hBp,heh]
      have hid (j : ι) : F j = e*(r j)^2 + L*s j^2 + (2*e-1)*t j + 2*e*u*s j-e := by
        dsimp [F,r,L]; ring
      have hsumF : (∑ j, p j * F j) = e * ∑ j, p j * (r j)^2 := by
        simp_rw [hid]
        simp_rw [mul_sub, mul_add]
        simp only [sum_sub_distrib, sum_add_distrib]
        simp_rw [show ∀ j, p j * (e*r j^2) = e*(p j*r j^2) by intro; ring,
          show ∀ j, p j * (L*s j^2) = L*(p j*s j^2) by intro; ring,
          show ∀ j, p j * ((2*e-1)*t j) = (2*e-1)*(p j*t j) by intro; ring,
          show ∀ j, p j * (2*e*u*s j) = (2*e*u)*(p j*s j) by intro; ring]
        simp only [← mul_sum, ← sum_mul, hB, ht, hsum, hpsum]
        dsimp [L]
        linear_combination hcost
      have hnonpos : (∑ j, p j * F j) ≤ 0 :=
        sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hp j)) (hF j)
      have hrnonneg : ∀ j, 0 ≤ p j * (r j)^2 := fun j => mul_nonneg (hp j).le (sq_nonneg _)
      have hrzero : (∑ j, p j * (r j)^2) = 0 := by
        rw [hsumF] at hnonpos
        nlinarith only [he,hnonpos,sum_nonneg (s := univ) (fun j _ => hrnonneg j)]
      have hr (j : ι) : r j = 0 := by
        have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => hrnonneg j)).mp hrzero j (mem_univ j)
        have : (r j)^2 = 0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hp j))
        exact sq_eq_zero_iff.mp this
      have hFzero : (∑ j, p j * F j) = 0 := by rw [hsumF,hrzero,mul_zero]
      have hroot (j : ι) : L * s j^2 + u*s j -(1-e) = 0 := by
        have hh := (sum_eq_zero_iff_of_nonpos (fun j _ =>
          mul_nonpos_of_nonneg_of_nonpos (hp j).le (hF j))).mp hFzero j (mem_univ j)
        have hh' : F j = 0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hp j))
        have htj : t j = 1-u*s j := by have := hr j; dsimp [r] at this; linarith only [this]
        rw [hid,hr,htj] at hh'
        linear_combination hh'
      obtain ⟨i,j,k,hij,hik,hjk⟩ := hthree
      have hd (a b : ι) (hab : s a ≠ s b) : L*(s a+s b)+u=0 := by
        have hh : (s a-s b)*(L*(s a+s b)+u)=0 := by
          linear_combination hroot a - hroot b
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hab)
      have hh : L*(s j-s k)=0 := by linear_combination hd i j hij - hd i k hik
      exact hjk (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hL)))

    have normalized_convergence
        (p s : ι → ℝ) (B M : ℝ)
        (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
        (hsum : ∑ j, p j * s j = 0) (hB : ∑ j, p j * s j^2 = B)
        (hBp : 0 < B)
        (hthree : ∃ i j k, s i ≠ s j ∧ s i ≠ s k ∧ s j ≠ s k)
        (e z k Q : ℕ → ℝ) (t : ℕ → ι → ℝ)
        (he : ∀ n, 0 < e n ∧ e n ≤ 1/2)
        (hz : ∀ n, 0 < z n ∧ z n ≤ M)
        (hk : ∀ n, -M ≤ k n ∧ k n ≤ M)
        (ht : ∀ n j, 0 ≤ t n j ∧ t n j ≤ 1 / p j)
        (htsum : ∀ n, ∑ j, p j*t n j = 1)
        (hF : ∀ n j, e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0)
        (hinside : ∀ n, k n^2 ≤ 4*e n*(1-e n)*z n)
        (hcost : ∀ n, Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n))
        (hlower : ∀ n, 1 ≤ Q n*z n)
        (hQ : Tendsto Q atTop (𝓝 B)) :
        Tendsto e atTop (𝓝 0) ∧ Tendsto z atTop (𝓝 (1/B)) ∧
          Tendsto k atTop (𝓝 0) ∧ ∀ j, Tendsto (fun n => t n j) atTop (𝓝 (s j^2/B)) := by
      clear * - p s B M hp hpsum hsum hB hBp hthree e z k Q t he hz hk ht htsum hF hinside hcost hlower hQ equality_obstruction
      classical
      let f : ℕ → ℝ × ℝ × ℝ × (ι → ℝ) := fun n => (e n,z n,k n,t n)
      let K : Set (ℝ × ℝ × ℝ × (ι → ℝ)) :=
        Set.Icc 0 (1/2) ×ˢ Set.Icc 0 M ×ˢ Set.Icc (-M) M ×ˢ Set.pi Set.univ (fun j => Set.Icc 0 (1/p j))
      have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod
        (isCompact_Icc.prod (isCompact_univ_pi fun j => isCompact_Icc)))
      have hfK : ∀ n, f n ∈ K := by
        intro n
        exact ⟨⟨(he n).1.le,(he n).2⟩,⟨(hz n).1.le,(hz n).2⟩,hk n,fun j _ => ht n j⟩
      have hconv : Tendsto f atTop (𝓝 (0,1/B,0,fun j => s j^2/B)) := by
        apply hK.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hfK)
        rintro ⟨E,Z,W,T⟩ hmem hcl
        obtain ⟨φ,hφ,hlim⟩ := hcl.tendsto_subseq
        have heL : Tendsto (e ∘ φ) atTop (𝓝 E) := hlim.fst_nhds
        have hzL : Tendsto (z ∘ φ) atTop (𝓝 Z) := hlim.snd_nhds.fst_nhds
        have hkL : Tendsto (k ∘ φ) atTop (𝓝 W) := hlim.snd_nhds.snd_nhds.fst_nhds
        have htL (j : ι) : Tendsto (fun n => t (φ n) j) atTop (𝓝 (T j)) :=
          (tendsto_pi_nhds.mp hlim.snd_nhds.snd_nhds.snd_nhds) j
        have hQL := hQ.comp hφ.tendsto_atTop
        have hEL : 0 ≤ E ∧ E ≤ 1/2 := hmem.1
        have hZL : 0 ≤ Z := hmem.2.1.1
        have hsumL : ∑ j, p j*T j = 1 := by
          have hh := tendsto_finsetSum Finset.univ (fun j _ => (htL j).const_mul (p j))
          exact tendsto_nhds_unique hh (by simpa only [htsum] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
        have hFL (j : ι) : E*T j^2-(1-W*s j)*T j+(1-E)*Z*s j^2 ≤ 0 := by
          apply le_of_tendsto' (((heL.mul ((htL j).pow 2)).sub
            ((tendsto_const_nhds.sub (hkL.mul_const (s j))).mul (htL j))).add
            (((tendsto_const_nhds.sub heL).mul hzL).mul_const (s j^2)))
          intro n; exact hF (φ n) j
        have hinsideL : W^2 ≤ 4*E*(1-E)*Z :=
          le_of_tendsto_of_tendsto (hkL.pow 2)
            (((heL.const_mul 4).mul (tendsto_const_nhds.sub heL)).mul hzL)
            (Eventually.of_forall fun n => hinside (φ n))
        have hcostL : B*(4*E*(1-E)*Z-W^2)=4*E*(1-E) := by
          apply tendsto_nhds_unique
            (hQL.mul ((((heL.const_mul 4).mul (tendsto_const_nhds.sub heL)).mul hzL).sub (hkL.pow 2)))
          exact (((heL.const_mul 4).mul (tendsto_const_nhds.sub heL))).congr' (Eventually.of_forall fun n => (hcost (φ n)).symm)
        have hlowL : 1 ≤ B*Z := ge_of_tendsto' (hQL.mul hzL) (fun n => hlower (φ n))
        have hE0 : E=0 := by
          by_contra hne
          have hep : 0 < E := lt_of_le_of_ne hEL.1 (Ne.symm hne)
          let u := W/(2*E)
          have hu : 2*E*u=W := by dsimp [u]; field_simp
          have hc : B*((1-E)*Z-E*u^2)=1-E := by
            have hh : 4*E*(B*((1-E)*Z-E*u^2)-(1-E))=0 := by
              linear_combination hcostL - congrArg (fun x : ℝ => B*x^2) hu
            have : B*((1-E)*Z-E*u^2)-(1-E)=0 :=
              (mul_eq_zero.mp hh).resolve_left (by positivity)
            linarith only [this]
          exact equality_obstruction p s T B E u Z hp hpsum hsum hB hsumL hBp hep hEL.2 hc
            (fun j => by rw [hu]; exact hFL j) hthree
        have hW0 : W=0 := by rw [hE0] at hinsideL; nlinarith only [hinsideL,sq_nonneg W]
        have hbound (j : ι) : Z*s j^2 ≤ T j := by
          have hh := hFL j; rw [hE0,hW0] at hh; nlinarith only [hh]
        have hZB : Z*B ≤ 1 := by
          have hh := sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
            mul_le_mul_of_nonneg_left (hbound j) (hp j).le)
          simp_rw [show ∀ j, p j*(Z*s j^2)=Z*(p j*s j^2) by intro; ring] at hh
          rw [← mul_sum,hB,hsumL] at hh
          exact hh
        have hZe : Z=1/B := by apply (eq_div_iff (ne_of_gt hBp)).mpr; nlinarith only [hZB,hlowL]
        have hT (j : ι) : T j=s j^2/B := by
          have hgap : ∀ j, 0 ≤ p j*(T j-Z*s j^2) := fun j =>
            mul_nonneg (hp j).le (sub_nonneg.mpr (hbound j))
          have hsz : (∑ j, p j*(T j-Z*s j^2))=0 := by
            simp_rw [mul_sub,show ∀ j, p j*(Z*s j^2)=Z*(p j*s j^2) by intro; ring]
            rw [sum_sub_distrib,← mul_sum,hsumL,hB]
            nlinarith only [hZB,hlowL]
          have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => hgap j)).mp hsz j (mem_univ j)
          have heq := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hp j))
          rw [hZe] at heq
          exact (sub_eq_zero.mp heq).trans (by ring)
        simp only [hE0,hZe,hW0,show T=(fun j => s j^2/B) from funext hT]
      exact ⟨hconv.fst_nhds,hconv.snd_nhds.fst_nhds,hconv.snd_nhds.snd_nhds.fst_nhds,
        fun j => (tendsto_pi_nhds.mp hconv.snd_nhds.snd_nhds.snd_nhds) j⟩
    classical
    let s := fun j => v j/p j
    let t := fun n j => q n j/p j
    let z := fun n => 1/(c n^2)
    let k := fun n => x n/c n
    obtain ⟨j₀,hvj⟩ := Function.ne_iff.mp hv
    change v j₀ ≠ 0 at hvj
    have hBp : 0 < B := by
      rw [hB]
      exact sum_pos' (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
        ⟨j₀,mem_univ _,mul_pos (hp _) (sq_pos_of_ne_zero (div_ne_zero hvj (ne_of_gt (hp _))))⟩
    have hsumS : (∑ j, p j*s j)=0 := by
      have hid (j : ι) : p j*s j=v j := by dsimp [s]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hvsum
    have htSum (n : ℕ) : (∑ j, p j*t n j)=1 := by
      have hid (j : ι) : p j*t n j=q n j := by dsimp [t]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hqsum n
    have hq1 (n : ℕ) (j : ι) : q n j ≤ 1 := by
      rw [← hqsum n]; exact single_le_sum (fun j _ => hq n j) (mem_univ _)
    have hbSum (n : ℕ) : (∑ j, b n j)=0 := by
      simp_rw [hb]; rw [← sum_div,hvsum,zero_div]
    have hASum (n : ℕ) : (∑ j, A n j)=1 := by
      have haNE : 1-e n ≠ 0 := by have := (he n).2; linarith only [this]
      simp_rw [hAf]; rw [← sum_div]
      simp_rw [sum_sub_distrib,← sum_mul,← mul_sum]
      rw [hpsum,hbSum,hqsum]
      field_simp [haNE]; ring
    have hA1 (n : ℕ) (j : ι) : A n j ≤ 1 := by
      rw [← hASum n]; exact single_le_sum (fun j _ => hA n j) (mem_univ _)
    have hzbound (n : ℕ) : z n ≤ 1/(v j₀^2) := by
      have hb1 : b n j₀^2 ≤ 1 := (hpsd n j₀).trans
        ((mul_le_mul (hA1 n j₀) (hq1 n j₀) (hq n j₀) (by norm_num)).trans (by norm_num))
      rw [hb,div_pow] at hb1
      have hc2 : 0 < c n^2 := sq_pos_of_pos (hc n)
      have hv2 : 0 < v j₀^2 := sq_pos_of_ne_zero hvj
      have hvle : v j₀^2 ≤ c n^2 := (div_le_one hc2).mp hb1
      exact one_div_le_one_div_of_le hv2 hvle
    let M := 1+1/(v j₀^2)
    have hM1 : 1 ≤ M := by
      have hh : 0 ≤ 1/(v j₀^2) := by positivity
      dsimp [M]; linarith
    have hk2 (n : ℕ) : k n^2 ≤ z n := by
      have hH : 4*e n*(1-e n) ≤ 1 := by nlinarith only [sq_nonneg (2*e n-1)]
      dsimp [k,z]; rw [div_pow]
      exact div_le_div_of_nonneg_right ((hinside n).le.trans hH) (sq_nonneg _)
    have hkn (n : ℕ) : -M ≤ k n ∧ k n ≤ M := by
      have hzM : z n ≤ M := le_trans (hzbound n) (by dsimp [M]; linarith)
      have hh := hk2 n
      constructor <;> nlinarith only [hzM,hh,hM1,sq_nonneg (k n+M),sq_nonneg (k n-M)]
    have hzn (n : ℕ) : 0 < z n ∧ z n ≤ M :=
      ⟨one_div_pos.mpr (sq_pos_of_pos (hc n)),(hzbound n).trans (by dsimp [M]; linarith)⟩
    have htn (n : ℕ) (j : ι) : 0 ≤ t n j ∧ t n j ≤ 1/p j :=
      ⟨div_nonneg (hq n j) (hp j).le,div_le_div_of_nonneg_right (hq1 n j) (hp j).le⟩
    have hfn (n : ℕ) (j : ι) :
        e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0 := by
      exact coefficient_inequality (p j) (v j) (b n j) (A n j) (q n j) (e n) (c n) (x n)
        (hp j) (hc n) (lt_of_le_of_lt (he n).2 (by norm_num)) (hb n j) (hAf n j) (hpsd n j)

    have hIn (n : ℕ) : k n^2 ≤ 4*e n*(1-e n)*z n := by
      dsimp [k,z]; rw [div_pow]
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        div_le_div_of_nonneg_right (hinside n).le (sq_nonneg (c n))
    have hCost (n : ℕ) : Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n) := by
      have hh := (eq_div_iff (ne_of_gt (sub_pos.mpr (hinside n)))).mp (hQf n)
      dsimp only [z,k]
      rw [div_pow, mul_one_div, ← sub_div, ← mul_div_assoc]
      exact (div_eq_iff (ne_of_gt (sq_pos_of_pos (hc n)))).mpr (by nlinarith only [hh])
    have hlow (n : ℕ) : 1 ≤ Q n*z n := by
      have hepos := (he n).1
      have hale : 0 < 1-e n := by have := (he n).2; linarith only [this]
      have hQpos : 0 < Q n := by
        rw [hQf]
        exact div_pos (mul_pos (sq_pos_of_pos (hc n)) (mul_pos (mul_pos (by norm_num) hepos) hale))
          (sub_pos.mpr (hinside n))
      have hh := hCost n
      have hnn := mul_nonneg hQpos.le (sq_nonneg (k n))
      have hH : 0 < 4*e n*(1-e n) := by positivity
      nlinarith only [hh,hnn,hH]
    obtain ⟨he0,hz0,hk0,ht0⟩ := normalized_convergence p s B M hp hpsum hsumS hB.symm hBp
      hthree e z k Q t he hzn hkn htn htSum hfn hIn hCost hlow hQ
    have hc0 : Tendsto (fun n => c n^2) atTop (𝓝 B) := by
      have hh := hz0.inv₀ (by positivity : (1/B : ℝ) ≠ 0)
      simpa [z] using hh
    refine ⟨he0,hc0,fun j => ?_⟩
    have hh := (ht0 j).const_mul (p j)
    convert hh using 1
    · ext n; dsimp [t]; field_simp [ne_of_gt (hp j)]
    · dsimp [s]; field_simp [ne_of_gt (hp j)]

  have coefficient_matching_lower {ι : Type} [Fintype ι]
      (p v : ι → ℝ) (B : ℝ)
      (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
      (hv : v ≠ 0) (hvsum : ∑ j, v j = 0)
      (hB : B = ∑ j, p j*(v j/p j)^2)
      (hthree : ∃ i j k, v i/p i ≠ v j/p j ∧ v i/p i ≠ v k/p k ∧ v j/p j ≠ v k/p k)
      (e c x Q : ℕ → ℝ) (q A b : ℕ → ι → ℝ)
      (he : ∀ n, 0 < e n ∧ e n ≤ 1/2) (hc : ∀ n, 0 < c n)
      (hq : ∀ n j, 0 ≤ q n j) (hA : ∀ n j, 0 ≤ A n j)
      (hqsum : ∀ n, ∑ j, q n j = 1)
      (hb : ∀ n j, b n j=v j/c n)
      (hAf : ∀ n j, A n j=(p j-b n j*x n-e n*q n j)/(1-e n))
      (hpsd : ∀ n j, b n j^2 ≤ A n j*q n j)
      (hinside : ∀ n, x n^2 < 4*e n*(1-e n))
      (hQf : ∀ n, Q n=c n^2*(4*e n*(1-e n))/(4*e n*(1-e n)-x n^2))
      (hQ : Tendsto Q atTop (𝓝 B))
      (R : ℕ → ℝ) (hR : ∀ n,0 < R n)
      (hRadius : ∀ n,c n^2*R n^2 ≤ 4*e n*(1-e n)) :
      let V := (∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B
      ∀ d : ℝ,d < V/4 → ∀ᶠ n in atTop,d ≤ (Q n-B)/R n^2 := by
    have finite_matching_gap
        (p s t : ι → ℝ) (B e z k Q c R C D : ℝ)
        (hp : ∀ j, 0 ≤ p j) (hs : ∑ j,p j*s j=0)
        (hp1 : ∑ j,p j=1) (ht1 : ∑ j,p j*t j=1)
        (hB : ∑ j,p j*s j^2=B) (hBp : 0 < B)
        (hC : C=∑ j,p j*s j*(t j-1)) (hD : D=∑ j,p j*(t j-1)^2)
        (he : 0 < e) (hea : e < 1) (hQ : 0 < Q) (hR : 0 < R)
        (hF : ∀ j,e*t j^2-(1-k*s j)*t j+(1-e)*z*s j^2 ≤ 0)
        (hcost : Q*(4*e*(1-e)*z-k^2)=4*e*(1-e))
        (hradius : c^2*R^2 ≤ 4*e*(1-e)) :
        Q*c^2*(B*D-C^2)/(4*(1-e)^2*B) ≤ (Q-B)/R^2 := by
      clear * - p s t B e z k Q c R C D hp hs hp1 ht1 hB hBp hC hD he hea hQ hR hF hcost hradius
      classical
      let F := fun j => e*t j^2-(1-k*s j)*t j+(1-e)*z*s j^2
      have hsumF : (∑ j,p j*F j)=e*D+k*C+(1-e)*z*B-(1-e) := by
        have hid (j : ι) : p j*F j = e*(p j*(t j-1)^2) + k*(p j*s j*(t j-1)) +
            ((1-e)*z)*(p j*s j^2) + (2*e-1)*(p j*t j)+k*(p j*s j)-e*p j := by dsimp [F]; ring
        simp_rw [hid]
        simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,← hC,← hD,hB,ht1,hs,hp1]
        ring
      have hFnonpos : e*D+k*C+(1-e)*z*B-(1-e) ≤ 0 := by
        rw [← hsumF]
        exact sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hp j) (hF j)
      have hres : 0 ≤ B*D-C^2 := by
        have hid (j : ι) : p j*(B*(t j-1)-C*s j)^2 =
            B^2*(p j*(t j-1)^2)-2*B*C*(p j*s j*(t j-1))+C^2*(p j*s j^2) := by ring
        have hnn : 0 ≤ ∑ j,p j*(B*(t j-1)-C*s j)^2 := sum_nonneg fun j _ => mul_nonneg (hp j) (sq_nonneg _)
        simp_rw [hid] at hnn
        simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,← hD,← hC,hB] at hnn
        have hh : 0 ≤ B*(B*D-C^2) := by nlinarith only [hnn]
        exact nonneg_of_mul_nonneg_right hh hBp
      have hgap : Q*e*(B*D-C^2) ≤ (Q-B)*(1-e)*B := by
        have hid : 4*e*((Q-B)*(1-e)*B-Q*e*(B*D-C^2)) =
            Q*(2*e*C+B*k)^2-4*e*Q*B*(e*D+k*C+(1-e)*z*B-(1-e)) := by
          linear_combination congrArg (fun x : ℝ => B^2*x) hcost
        have hnn := mul_nonneg hQ.le (sq_nonneg (2*e*C+B*k))
        have hnp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4*e*Q*B by positivity) hFnonpos
        nlinarith only [hid,hnn,hnp,he]
      have ha : 0 < 1-e := sub_pos.mpr hea
      have h1 := mul_le_mul_of_nonneg_left hradius (mul_nonneg hQ.le hres)
      have h2 := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 4*(1-e) by positivity)
      apply (div_le_div_iff₀ (by positivity : 0 < 4*(1-e)^2*B) (sq_pos_of_pos hR)).mpr
      nlinarith only [h1,h2]

    have matching_lower_of_limits
        (p s : ι → ℝ) (B : ℝ) (hp : ∀ j,0 ≤ p j)
        (hp1 : ∑ j,p j=1) (hs : ∑ j,p j*s j=0)
        (hB : ∑ j,p j*s j^2=B) (hBp : 0 < B)
        (e z k Q c R : ℕ → ℝ) (t : ℕ → ι → ℝ)
        (he : ∀ n,0 < e n ∧ e n < 1) (hQp : ∀ n,0 < Q n) (hR : ∀ n,0 < R n)
        (ht1 : ∀ n,∑ j,p j*t n j=1)
        (hF : ∀ n j,e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0)
        (hcost : ∀ n,Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n))
        (hradius : ∀ n,c n^2*R n^2 ≤ 4*e n*(1-e n))
        (he0 : Tendsto e atTop (𝓝 0)) (hQ0 : Tendsto Q atTop (𝓝 B))
        (hc0 : Tendsto (fun n => c n^2) atTop (𝓝 B))
        (ht0 : ∀ j,Tendsto (fun n => t n j) atTop (𝓝 (s j^2/B))) :
        let V := (∑ j,p j*s j^4)-B^2-(∑ j,p j*s j^3)^2/B
        ∀ d : ℝ,d < V/4 → ∀ᶠ n in atTop,d ≤ (Q n-B)/R n^2 := by
      clear * - p s B hp hp1 hs hB hBp e z k Q c R t he hQp hR ht1 hF hcost hradius he0 hQ0 hc0 ht0 finite_matching_gap
      classical
      let C := fun n => ∑ j,p j*s j*(t n j-1)
      let D := fun n => ∑ j,p j*(t n j-1)^2
      let C₀ := ∑ j,p j*s j*(s j^2/B-1)
      let D₀ := ∑ j,p j*(s j^2/B-1)^2
      have hC0 : Tendsto C atTop (𝓝 C₀) :=
        tendsto_finsetSum _ (fun j _ => ((ht0 j).sub tendsto_const_nhds).const_mul (p j*s j))
      have hD0 : Tendsto D atTop (𝓝 D₀) :=
        tendsto_finsetSum _ (fun j _ => (((ht0 j).sub tendsto_const_nhds).pow 2).const_mul (p j))
      let L := fun n => Q n*c n^2*(B*D n-C n^2)/(4*(1-e n)^2*B)
      have hL0 : Tendsto L atTop (𝓝 (B*(B*D₀-C₀^2)/4)) := by
        have hh := ((hQ0.mul hc0).mul ((hD0.const_mul B).sub (hC0.pow 2))).div
          ((((tendsto_const_nhds.sub he0).pow 2).const_mul 4).mul_const B)
          (show 4*(1-(0:ℝ))^2*B ≠ 0 by positivity)
        have hval : B*B*(B*D₀-C₀^2)/(4*(1-(0:ℝ))^2*B) = B*(B*D₀-C₀^2)/4 := by
          field_simp
          norm_num
        rw [hval] at hh
        exact hh
      have hCeq : C₀ = (∑ j,p j*s j^3)/B := by
        have hid (j : ι) : p j*s j*(s j^2/B-1)=(p j*s j^3)/B-p j*s j := by ring
        dsimp [C₀]; simp_rw [hid]; rw [sum_sub_distrib,← sum_div,hs,sub_zero]
      have hDeq : D₀ = (∑ j,p j*s j^4)/B^2-1 := by
        have hid (j : ι) : p j*(s j^2/B-1)^2=(p j*s j^4)/B^2-2*(p j*s j^2)/B+p j := by ring
        dsimp [D₀]; simp_rw [hid]
        simp only [sum_add_distrib,sum_sub_distrib,← sum_div,← mul_sum,hB,hp1]
        field_simp
        ring
      have hcoef : B*(B*D₀-C₀^2)/4 = ((∑ j,p j*s j^4)-B^2-(∑ j,p j*s j^3)^2/B)/4 := by
        rw [hCeq,hDeq]; field_simp
      have hle (n : ℕ) : L n ≤ (Q n-B)/R n^2 :=
        finite_matching_gap p s (t n) B (e n) (z n) (k n) (Q n) (c n) (R n) (C n) (D n)
          hp hs hp1 (ht1 n) hB hBp rfl rfl (he n).1 (he n).2 (hQp n) (hR n)
          (hF n) (hcost n) (hradius n)
      dsimp only
      intro d hd
      rw [hcoef] at hL0
      exact (hL0.eventually_const_lt hd).mono (fun n hn => hn.le.trans (hle n))
    classical
    let s := fun j => v j/p j
    let t := fun n j => q n j/p j
    let z := fun n => 1/(c n^2)
    let k := fun n => x n/c n
    obtain ⟨j₀,hvj⟩ := Function.ne_iff.mp hv
    change v j₀ ≠ 0 at hvj
    have hBp : 0 < B := by
      rw [hB]
      exact sum_pos' (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
        ⟨j₀,mem_univ _,mul_pos (hp _) (sq_pos_of_ne_zero (div_ne_zero hvj (ne_of_gt (hp _))))⟩
    have hsumS : (∑ j, p j*s j)=0 := by
      have hid (j : ι) : p j*s j=v j := by dsimp [s]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hvsum
    have htSum (n : ℕ) : (∑ j, p j*t n j)=1 := by
      have hid (j : ι) : p j*t n j=q n j := by dsimp [t]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hqsum n
    have hfn (n : ℕ) (j : ι) :
        e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0 := by
      exact coefficient_inequality (p j) (v j) (b n j) (A n j) (q n j) (e n) (c n) (x n)
        (hp j) (hc n) (lt_of_le_of_lt (he n).2 (by norm_num)) (hb n j) (hAf n j) (hpsd n j)

    have hCost (n : ℕ) : Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n) := by
      have hh := (eq_div_iff (ne_of_gt (sub_pos.mpr (hinside n)))).mp (hQf n)
      dsimp only [z,k]
      rw [div_pow, mul_one_div, ← sub_div, ← mul_div_assoc]
      exact (div_eq_iff (ne_of_gt (sq_pos_of_pos (hc n)))).mpr (by nlinarith only [hh])

    obtain ⟨he0,hc0,hq0⟩ := coefficient_degeneration p v B hp hpsum hv hvsum hB hthree
      e c x Q q A b he hc hq hA hqsum hb hAf hpsd hinside hQf hQ
    have ht0 (j : ι) : Tendsto (fun n => t n j) atTop (𝓝 (s j^2/B)) := by
      dsimp only [t]
      convert (hq0 j).div_const (p j) using 1
      dsimp [s]
      field_simp [ne_of_gt (hp j),ne_of_gt hBp]
    have hQp (n : ℕ) : 0 < Q n := by
      have ha : 0 < 1-e n := by have := (he n).2; linarith only [this]
      rw [hQf]
      exact div_pos (mul_pos (sq_pos_of_pos (hc n))
        (mul_pos (mul_pos (by norm_num) (he n).1) ha)) (sub_pos.mpr (hinside n))
    exact matching_lower_of_limits p s B (fun j => (hp j).le) hpsum hsumS hB.symm hBp
      e z k Q c R t (fun n => ⟨(he n).1,lt_of_le_of_lt (he n).2 (by norm_num)⟩)
      hQp hR htSum hfn hCost hRadius he0 hQ hc0 ht0

  have actual_rank_two_lower {m : ℕ}
      (p v : Fin m → ℝ) (B : ℝ)
      (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
      (hv : v ≠ 0) (hvsum : ∑ j, v j = 0)
      (hB : B = ∑ j, p j*(v j/p j)^2)
      (hthree : ∃ i j k, v i/p i ≠ v j/p j ∧ v i/p i ≠ v k/p k ∧ v j/p j ≠ v k/p k)
      (N : ℕ → Fin m → Matrix (Fin 2) (Fin 2) ℂ)
      (rho : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
      (I : ℕ → Set ℝ) (R : ℕ → ℝ)
      (hI : ∀ n, IsOpen (I n)) (hconn : ∀ n, IsPreconnected (I n))
      (h0 : ∀ n, 0 ∈ I n) (hR : ∀ n, 0 < R n)
      (hRI : ∀ n, Set.Icc (-R n) (R n) ⊆ I n)
      (hN : ∀ n j, (N n j).PosSemidef) (hnorm : ∀ n, ∑ j, N n j = 1)
      (hc : ∀ n, ContDiffOn ℝ 1 (rho n) (I n))
      (hrho : ∀ n u, u ∈ I n → (rho n u).PosSemidef ∧
        Matrix.trace (rho n u) = 1 ∧ rho n u * rho n u = rho n u)
      (hread : ∀ n u, u ∈ I n → ∀ j, (Matrix.trace (N n j * rho n u)).re = p j+u*v j)
      (hrank : ∀ n, Module.finrank ℝ (effectReadout (N n)).range = 2)
      (hQ : Tendsto (fun n => spectralQFI (rho n 0)
        (deriv (rho n) 0) (hrho n 0 (h0 n)).1) atTop (𝓝 B)) :
      let V := (∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B
      ∀ d : ℝ, d < V/4 → ∀ᶠ n in atTop,
        d ≤ (spectralQFI (rho n 0) (deriv (rho n) 0)
          (hrho n 0 (h0 n)).1-B)/R n^2 := by
    have htransfer : ∀
      (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : Set ℝ)
      (hI : IsOpen I) (h0 : 0 ∈ I) (hc : ContDiffOn ℝ 1 rho I)
      (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ Matrix.trace (rho u) = 1 ∧ rho u * rho u = rho u)
      (O : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3))) (x c ε s : ℝ) (hs : s=1 ∨ s= -1)
      (hinside : x^2 < 4*ε*(1-ε))
      (hcoord : ∀ u ∈ I, reframe O (rho u) = blochMatrix 1 (WithLp.toLp 2
        ![x+c*u,s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2),1-2*ε])),
      spectralQFI (rho 0) (deriv rho 0) (hrho 0 h0).1 =
        c^2*(4*ε*(1-ε))/(4*ε*(1-ε)-x^2) := by
      clear * - coefficient_matching_lower
      classical
      have matrix_bloch_geometry (M : Matrix (Fin 2) (Fin 2) ℂ)
          (hM : M.IsHermitian) :
          M = blochMatrix (Matrix.trace M).re (bloch M) := by
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
        ext i j
        fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
          simp only [Fin.zero_eta, Fin.isValue, blochMatrix, trace, diag_apply,
          Fin.sum_univ_two, Complex.add_re, bloch, neg_mul, Matrix.cons_val,
          add_add_sub_cancel, Complex.ofReal_add, add_self_div_two, cons_val_zero, Complex.ofReal_mul,
          Complex.ofReal_ofNat, cons_val_one, Complex.ofReal_neg, sub_neg_eq_add, add_sub_sub_cancel,
          of_apply, cons_val', cons_val_fin_one, Complex.ofReal_re, h00,
          Complex.ofReal_im, Fin.mk_one, Complex.div_ofNat_re, Complex.mul_re, Complex.re_ofNat,
          Complex.im_ofNat, mul_zero, sub_zero, Complex.I_re, Complex.mul_im,
          zero_mul, add_zero, Complex.I_im, mul_one, sub_self,
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, Complex.div_ofNat_im,
          Complex.add_im, zero_add, h10r, Complex.neg_re, neg_zero,
          h10i, Complex.neg_im, h11] <;> ring

      have trace_bloch_pairing (M N : Matrix (Fin 2) (Fin 2) ℂ)
          (hM : M.IsHermitian) (hN : N.IsHermitian) :
          (Matrix.trace (M * N)).re =
            ((Matrix.trace M).re * (Matrix.trace N).re + ⟪bloch M, bloch N⟫_ℝ) / 2 := by
        have hM' := matrix_bloch_geometry M hM
        have hN' := matrix_bloch_geometry N hN
        conv_lhs => rw [hM', hN']
        simp only [trace, blochMatrix, Fin.isValue, diag_apply, Fin.sum_univ_succ,
          Finset.univ_unique, Fin.default_eq_zero, sum_singleton, Fin.succ_zero_eq_one, Complex.add_re,
          Complex.ofReal_add, Complex.ofReal_sub, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
          vecMul_cons, head_cons, smul_cons, smul_eq_mul, Matrix.smul_empty,
          tail_cons, empty_vecMul, add_zero, add_cons, empty_add_empty,
          Matrix.empty_mul, Equiv.symm_apply_apply, of_apply, cons_val', cons_val_fin_one,
          cons_val_zero, cons_val_succ, sum_const, Finset.card_singleton, smul_add,
          one_smul, Complex.mul_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.div_ofNat_im,
          Complex.add_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero,
          Complex.sub_re, Complex.I_re, Complex.I_im, mul_one, sub_self,
          Complex.sub_im, Complex.mul_im, zero_sub, zero_add, PiLp.inner_apply,
          RCLike.inner_apply, Real.ringHom_apply, Fin.succ_one_eq_two]
        ring

      have blochMatrix_properties (a : ℝ) (r : EuclideanSpace ℝ (Fin 3)) :
          (blochMatrix a r).IsHermitian ∧ Matrix.trace (blochMatrix a r) = (a : ℂ) ∧
          bloch (blochMatrix a r) = r := by
        refine ⟨?_, ?_, ?_⟩
        · apply Matrix.IsHermitian.ext
          intro i j
          fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp only [blochMatrix, Fin.isValue, Complex.ofReal_add, Complex.ofReal_sub, Fin.zero_eta,
          of_apply, cons_val', cons_val_zero, cons_val_fin_one, star_div₀,
          star_add, RCLike.star_def, Complex.conj_ofReal, star_ofNat, Complex.div_ofNat_re,
          Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im,
          add_zero, zero_div, Fin.mk_one, cons_val_one, star_mul',
          Complex.conj_I, mul_neg, Complex.neg_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.I_im, mul_one, sub_self, neg_zero,
          Complex.sub_re, sub_zero, Complex.neg_im, Complex.mul_im, zero_add,
          Complex.sub_im, zero_sub, star_sub, sub_neg_eq_add]
        · apply Complex.ext <;> simp only [trace, blochMatrix, Fin.isValue, Complex.ofReal_add, Complex.ofReal_sub,
          diag_apply, of_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two,
          cons_val_zero, cons_val_one, Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re,
          Complex.sub_re, Complex.add_im, Complex.div_ofNat_im, Complex.ofReal_im, add_zero,
          zero_div, Complex.sub_im, sub_self] <;> ring
        · ext i
          fin_cases i <;> simp only [bloch, blochMatrix, Fin.isValue, Complex.ofReal_add, Complex.ofReal_sub,
          of_apply, cons_val', cons_val_one, cons_val_fin_one, cons_val_zero,
          Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          sub_zero, Complex.div_ofNat_im, Complex.sub_im, Complex.mul_im, add_zero,
          zero_sub, neg_mul, Complex.add_re, Fin.zero_eta, Fin.mk_one,
          Fin.reduceFinMk, Matrix.cons_val] <;> ring

      have reframe_pairing (O : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)))
          (M N : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
          (Matrix.trace (reframe O M * reframe O N)).re = (Matrix.trace (M * N)).re := by
        obtain ⟨hMr, htM, hbM⟩ := blochMatrix_properties (Matrix.trace M).re (O (bloch M))
        obtain ⟨hNr, htN, hbN⟩ := blochMatrix_properties (Matrix.trace N).re (O (bloch N))
        dsimp only [reframe]
        rw [trace_bloch_pairing _ _ hMr hNr, trace_bloch_pairing _ _ hM hN]
        change (((Matrix.trace (blochMatrix _ _)).re * (Matrix.trace (blochMatrix _ _)).re +
          ⟪bloch (blochMatrix _ _), bloch (blochMatrix _ _)⟫_ℝ) / 2) = _
        rw [htM, htN, hbM, hbN, O.inner_map_map]
        simp

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

      intro rho I hI h0 hc hrho O x c ε s hs hinside hcoord
      have energy (r d : Matrix (Fin 2) (Fin 2) ℂ) (h : d*r+r*d=d) :
          (Matrix.trace (((2:ℂ) • d)*r*((2:ℂ) • d))).re =
            2*(Matrix.trace (d*d)).re := by
        have ht := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (Matrix.trace (M*d)).re) h
        simp only [add_mul, Matrix.trace_add, Complex.add_re] at ht
        rw [← Matrix.trace_mul_cycle r d d] at ht
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
          Complex.mul_re]
        norm_num
        rw [← Matrix.trace_mul_cycle r d d]
        linarith
      let D := deriv rho 0
      have hd : HasDerivAt rho D 0 :=
        (hc.differentiableOn (by norm_num) 0 h0).differentiableAt (hI.mem_nhds h0) |>.hasDerivAt
      have he (i j : Fin 2) : HasDerivAt (fun u => rho u i j) (D i j) 0 :=
        hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
      have hD : D.IsHermitian := by
        apply Matrix.IsHermitian.ext
        intro i j
        apply (he j i).star.unique
        apply (he i j).congr_of_eventuallyEq
        filter_upwards [hI.mem_nhds h0] with u hu
        exact (hrho u hu).1.isHermitian.apply i j
      have hprod : HasDerivAt (fun u => rho u * rho u) (D*rho 0+rho 0*D) 0 := by
        apply hasDerivAt_pi.mpr
        intro i
        apply hasDerivAt_pi.mpr
        intro j
        simp only [Matrix.mul_apply, Matrix.add_apply]
        rw [← Finset.sum_add_distrib]
        exact HasDerivAt.fun_sum fun k _ => (he i k).mul (he k j)
      have htan : D*rho 0+rho 0*D=D := by
        apply hprod.unique
        apply hd.congr_of_eventuallyEq
        filter_upwards [hI.mem_nhds h0] with u hu
        exact (hrho u hu).2.2
      have hSLD : ((2:ℂ) • D)*rho 0+rho 0*((2:ℂ) • D)=(2:ℂ) • D := by
        rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, htan]
      have hQ := spectral_energy (rho 0) D ((2:ℂ) • D)
        (hrho 0 h0).1 (hD.smul (by norm_num)) hSLD
      have hpureQ : spectralQFI (rho 0) D (hrho 0 h0).1 =
          2*(Matrix.trace (D*D)).re := hQ.symm.trans (energy (rho 0) D htan)
      let y := Real.sqrt (4*ε*(1-ε)-x^2)
      have hy : 0 < y := Real.sqrt_pos.mpr (sub_pos.mpr hinside)
      have hy2 : y^2=4*ε*(1-ε)-x^2 := Real.sq_sqrt (sub_nonneg.mpr hinside.le)
      let r := blochMatrix 1 (WithLp.toLp 2 ![x,s*y,1-2*ε])
      let d := blochMatrix 0 (WithLp.toLp 2 ![c,-s*x*c/y,0])
      have hx : HasDerivAt (fun u : ℝ => x+c*u) c 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).const_mul c).const_add x
      have hys : HasDerivAt (fun u : ℝ => s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2))
          (-s*x*c/y) 0 := by
        have hh := (((hasDerivAt_const (0:ℝ) (4*ε*(1-ε))).sub (hx.pow 2)).sqrt
          (by simpa using ne_of_gt (sub_pos.mpr hinside))).const_mul s
        convert hh using 1 <;> first | rfl | (dsimp [y]; ring)
      have hxC : HasDerivAt (fun u : ℝ => ((x+c*u : ℝ):ℂ)) (c:ℂ) 0 :=
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hx
      have hyC : HasDerivAt (fun u : ℝ => ((s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2):ℝ):ℂ))
          ((-s*x*c/y:ℝ):ℂ) 0 := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hys
      have harc : HasDerivAt (fun u : ℝ => blochMatrix 1 (WithLp.toLp 2
          ![x+c*u,s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2),1-2*ε])) d 0 := by
        apply hasDerivAt_pi.mpr
        intro i
        apply hasDerivAt_pi.mpr
        intro j
        fin_cases i <;> fin_cases j
        · simpa [blochMatrix,d] using hasDerivAt_const (0:ℝ) (((1+(1-2*ε):ℝ):ℂ)/2)
        · exact (hxC.sub (hyC.mul_const Complex.I)).div_const 2
        · exact (hxC.add (hyC.mul_const Complex.I)).div_const 2
        · simpa [blochMatrix,d] using hasDerivAt_const (0:ℝ) (((1-(1-2*ε):ℝ):ℂ)/2)
      have hframe : HasDerivAt (fun u => reframe O (rho u)) (reframe O D) 0 :=
        (reframeLinear O).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hd
      have hDd : reframe O D=d := by
        apply hframe.unique
        apply harc.congr_of_eventuallyEq
        filter_upwards [hI.mem_nhds h0] with u hu
        exact hcoord u hu
      have hpair : (Matrix.trace (d*d)).re=(Matrix.trace (D*D)).re := by
        rw [← hDd]
        exact reframe_pairing O D D hD hD
      have hdinfo := blochMatrix_properties 0 (WithLp.toLp 2 ![c,-s*x*c/y,0])
      have hdd : 2*(Matrix.trace (d*d)).re = c^2+(s*x*c/y)^2 := by
        rw [trace_bloch_pairing d d hdinfo.1 hdinfo.1, hdinfo.2.1, hdinfo.2.2]
        simp [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, RCLike.inner_apply]
        ring
      have hs2 : s^2=1 := by rcases hs with rfl | rfl <;> norm_num
      change spectralQFI (rho 0) D (hrho 0 h0).1 = _
      rw [hpureQ, ← hpair, hdd]
      simp only [div_pow, mul_pow, hs2, one_mul, hy2]
      field_simp [ne_of_gt (sub_pos.mpr hinside)]
      <;> ring

    classical
    choose basis x c e s A q b hcpos hepos hele hs
      hcoeff hqsum hcoord hinside hend using fun n =>
        actual_rank_two_parameters (N n) (rho n) p v (I n) (hI n) (hconn n)
          (h0 n) hv (hN n) (hnorm n) (hc n) (hrho n) (hread n) (hrank n)
    let Q := fun n => spectralQFI (rho n 0) (deriv (rho n) 0)
      (hrho n 0 (h0 n)).1
    have hQf (n : ℕ) : Q n = c n^2*(4*e n*(1-e n))/(4*e n*(1-e n)-x n^2) := by
      exact htransfer (rho n) (I n) (hI n) (h0 n) (hc n) (hrho n)
        (basis n).repr (x n) (c n) (e n) (s n) (hs n)
        (by simpa only [mul_zero, add_zero] using hinside n 0 (h0 n)) (hcoord n)
    have hRadius (n : ℕ) : c n^2*R n^2 ≤ 4*e n*(1-e n) := by
      have he1 : 0 ≤ 1-e n := by linarith [hele n]
      have hk : 0 ≤ 4*e n*(1-e n) :=
        mul_nonneg (mul_nonneg (by norm_num) (hepos n).le) he1
      have hb := hend n (R n) (hR n).le (hRI n)
      have hcR : 0 ≤ c n*R n := mul_nonneg (hcpos n).le (hR n).le
      have hb' : c n*R n < Real.sqrt (4*e n*(1-e n)) := by
        linarith [abs_nonneg (x n)]
      have hsq := mul_self_le_mul_self hcR hb'.le
      rw [← pow_two, ← pow_two, Real.sq_sqrt hk] at hsq
      nlinarith only [hsq]
    exact coefficient_matching_lower p v B hp hpsum hv hvsum hB
      hthree e c x Q q A b (fun n => ⟨hepos n,hele n⟩) hcpos
      (fun n j => (hcoeff n j).1) (fun n j => (hcoeff n j).2.1) hqsum
      (fun n j => (hcoeff n j).2.2.2.1) (fun n j => (hcoeff n j).2.2.2.2)
      (fun n j => (hcoeff n j).2.2.1) (fun n => by simpa using hinside n 0 (h0 n))
      hQf hQ R hR hRadius

  have score_separation {ι : Type} [Fintype ι]
      (p s : ι → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1)
      (hs : ∑ j,p j*s j=0)
      (hthree : ∃ i j k, s i≠s j ∧ s i≠s k ∧ s j≠s k) :
      let B := ∑ j,p j*s j^2
      let V := (∑ j,p j*s j^4)-B^2-(∑ j,p j*s j^3)^2/B
      0<B ∧ 0<V ∧ ∃ lo hi, s lo<0 ∧ 0<s hi ∧ B < -s lo*s hi := by
    clear * - p s hp hp1 hs hthree
    classical
    dsimp only
    let B := ∑ j,p j*s j^2
    let C := ∑ j,p j*s j^3
    let D := ∑ j,p j*s j^4
    obtain ⟨i,j,k,hij,hik,hjk⟩ := hthree
    have hsne : ∃ a, s a≠0 := by by_contra! h; exact hij ((h i).trans (h j).symm)
    obtain ⟨a,ha⟩ := hsne
    have hB : 0<B := sum_pos' (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
      ⟨a,mem_univ _,mul_pos (hp a) (sq_pos_of_ne_zero ha)⟩
    have hrid : (∑ j,p j*(s j^2-B-C/B*s j)^2)=D-B^2-C^2/B := by
      have hid (j : ι) : p j*(s j^2-B-C/B*s j)^2 =
          p j*s j^4 - 2*(C/B)*(p j*s j^3) + ((C/B)^2-2*B)*(p j*s j^2) +
          (2*C)*(p j*s j) + B^2*p j := by
        field_simp
        <;> ring
      simp_rw [hid]
      simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,hp1,hs,mul_zero,add_zero,mul_one]
      change D-2*(C/B)*C+((C/B)^2-2*B)*B+B^2=D-B^2-C^2/B
      field_simp
      <;> ring
    have hV : 0<D-B^2-C^2/B := by
      rw [←hrid]
      apply sum_pos'
      · intro j _; exact mul_nonneg (hp j).le (sq_nonneg _)
      · by_contra! h
        have hz (a : ι) : s a^2-B-C/B*s a=0 := by
          have hh := h a (mem_univ a)
          have : (s a^2-B-C/B*s a)^2=0 := by nlinarith only [hh, hp a,sq_nonneg (s a^2-B-C/B*s a)]
          exact sq_eq_zero_iff.mp this
        have hf (a b : ι) : (s a-s b)*(s a+s b-C/B)=0 := by linear_combination hz a - hz b
        have h1 := (mul_eq_zero.mp (hf i j)).resolve_left (sub_ne_zero.mpr hij)
        have h2 := (mul_eq_zero.mp (hf i k)).resolve_left (sub_ne_zero.mpr hik)
        exact hjk (by linarith only [h1,h2])
    obtain ⟨lo,_,hlo⟩ := exists_min_image univ s ⟨i,mem_univ _⟩
    obtain ⟨hi,_,hhi⟩ := exists_max_image univ s ⟨i,mem_univ _⟩
    have hmin a := hlo a (mem_univ a)
    have hmax a := hhi a (mem_univ a)
    have hmid : ∃ a, s lo<s a ∧ s a<s hi := by
      by_contra! h
      have he (a : ι) : s a=s lo ∨ s a=s hi := by
        rcases eq_or_lt_of_le (hmin a) with hh|hh
        · exact Or.inl hh.symm
        · exact Or.inr (le_antisymm (hmax a) (h a hh))
      rcases he i with hi'|hi' <;> rcases he j with hj'|hj' <;>
        rcases he k with hk'|hk' <;> first | exact hij (hi'.trans hj'.symm) | exact hik (hi'.trans hk'.symm) | exact hjk (hj'.trans hk'.symm)
    obtain ⟨a,ha1,ha2⟩ := hmid
    have hlo0 : s lo<0 := by
      have hsum : 0<∑ b,p b*(s b-s lo) := sum_pos'
        (fun b _ => mul_nonneg (hp b).le (sub_nonneg.mpr (hmin b)))
        ⟨a,mem_univ _,mul_pos (hp a) (sub_pos.mpr ha1)⟩
      simp only [mul_sub,sum_sub_distrib,←sum_mul,hs,hp1,one_mul] at hsum
      linarith only [hsum]
    have hhi0 : 0<s hi := by
      have hsum : 0<∑ b,p b*(s hi-s b) := sum_pos'
        (fun b _ => mul_nonneg (hp b).le (sub_nonneg.mpr (hmax b)))
        ⟨a,mem_univ _,mul_pos (hp a) (sub_pos.mpr ha2)⟩
      simp only [mul_sub,sum_sub_distrib,←sum_mul,hs,hp1,one_mul] at hsum
      linarith only [hsum]
    have hgap : B < -s lo*s hi := by
      have hsum : 0<∑ b,p b*(s b-s lo)*(s hi-s b) := sum_pos'
        (fun b _ => mul_nonneg (mul_nonneg (hp b).le (sub_nonneg.mpr (hmin b)))
          (sub_nonneg.mpr (hmax b)))
        ⟨a,mem_univ _,mul_pos (mul_pos (hp a) (sub_pos.mpr ha1)) (sub_pos.mpr ha2)⟩
      have hid (b : ι) : p b*(s b-s lo)*(s hi-s b) =
        (s hi+s lo)*(p b*s b)-p b*s b^2-(s lo*s hi)*p b := by ring
      simp_rw [hid] at hsum
      simp only [sum_sub_distrib,←mul_sum,hs,hp1,mul_zero,mul_one] at hsum
      change 0<0-B-s lo*s hi at hsum
      linarith only [hsum]
    exact ⟨hB,hV,lo,hi,hlo0,hhi0,hgap⟩

  have infimum_limit (S : ℝ → Set ℝ) (B K : ℝ) (U : ℝ → ℝ)
      (hlower : ∀ R,0<R → ∀ q∈S R,B≤q)
      (hupper : ∀ᶠ R in 𝓝[>] 0,U R∈S R)
      (hU : Tendsto (fun R => (U R-B)/R^2) (𝓝[>] 0) (𝓝 K))
      (hseq : ∀ (R Q : ℕ → ℝ), (∀ n,0<R n) → (∀ n,Q n∈S (R n)) →
        Tendsto R atTop (𝓝[>] 0) → Tendsto Q atTop (𝓝 B) →
        ∀ d<K,∀ᶠ n in atTop,d≤(Q n-B)/R n^2) :
      Tendsto (fun R => (guardedInfimum (S R)-B)/R^2) (𝓝[>] 0) (𝓝 K) := by
    clear * - S B K U hlower hupper hU hseq
    classical
    apply tendsto_iff_seq_tendsto.mpr
    intro r hr
    have hev : ∀ᶠ n in atTop,0<r n ∧ U (r n)∈S (r n) :=
      (hr.eventually self_mem_nhdsWithin).and (hr.eventually hupper)
    obtain ⟨n0,hn0⟩ := eventually_atTop.mp hev
    let R := fun n : ℕ => r (n+n0)
    have hR (n : ℕ) : 0<R n := (hn0 (n+n0) (by omega)).1
    have hUm (n : ℕ) : U (R n)∈S (R n) := (hn0 (n+n0) (by omega)).2
    have hRt : Tendsto R atTop (𝓝[>] 0) := hr.comp (tendsto_add_atTop_nat n0)
    have hR0 : Tendsto R atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hRt
    have hne (n : ℕ) : (S (R n)).Nonempty := ⟨U (R n),hUm n⟩
    have hb (n : ℕ) : BddBelow (S (R n)) := ⟨B,fun q hq => hlower (R n) (hR n) q hq⟩
    let C := fun n => guardedInfimum (S (R n))
    have hC (n : ℕ) : C n=sInf (S (R n)) := by simp [C,guardedInfimum,hne n,hb n]
    have hCU (n : ℕ) : C n≤U (R n) := by rw [hC]; exact csInf_le (hb n) (hUm n)
    have hCB (n : ℕ) : B≤C n := by
      rw [hC]
      exact le_csInf (hne n) (fun q hq => hlower (R n) (hR n) q hq)
    have happrox (n : ℕ) : ∃ q∈S (R n),q<C n+R n^3 := by
      apply exists_lt_of_csInf_lt (hne n)
      rw [←hC]
      exact lt_add_of_pos_right _ (pow_pos (hR n) _)
    choose Q hQm hQa using happrox
    have hQlo (n : ℕ) : B≤Q n := hlower (R n) (hR n) (Q n) (hQm n)
    have hQhi (n : ℕ) : Q n≤U (R n)+R n^3 := (hQa n).le.trans (add_le_add (hCU n) le_rfl)
    have hUt : Tendsto (fun n => (U (R n)-B)/R n^2) atTop (𝓝 K) := hU.comp hRt
    have hU0 : Tendsto (fun n => U (R n)) atTop (𝓝 B) := by
      have ht := (hUt.mul (hR0.pow 2)).add_const B
      have heq : (fun n => (U (R n)-B)/R n^2*R n^2+B)=(fun n => U (R n)) := by
        funext n
        field_simp [(hR n).ne']
        <;> ring
      rw [heq] at ht
      simpa using ht
    have hQt : Tendsto Q atTop (𝓝 B) := tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa using hU0.add (hR0.pow 3)) hQlo hQhi
    have hClim : Tendsto (fun n => (C n-B)/R n^2) atTop (𝓝 K) := by
      apply tendsto_order.mpr
      constructor
      · intro d hd
        let d' := (d+K)/2
        have hdd : d<d' := by dsimp [d']; linarith
        have hdK : d'<K := by dsimp [d']; linarith
        filter_upwards [hseq R Q hR hQm hRt hQt d' hdK,
          hR0.eventually (gt_mem_nhds (sub_pos.mpr hdd))] with n hn hsmall
        have hsq : 0<R n^2 := sq_pos_of_pos (hR n)
        have hlow := (le_div_iff₀ hsq).mp hn
        have hdiff : d*R n^2 < Q n-B-R n^3 := by
          have hmul := mul_lt_mul_of_pos_right hsmall hsq
          nlinarith only [hmul,hlow]
        apply (lt_div_iff₀ hsq).mpr
        linarith only [hQa n, hdiff]
      · intro d hd
        filter_upwards [hUt.eventually (gt_mem_nhds hd)] with n hn
        exact lt_of_le_of_lt (div_le_div_of_nonneg_right (sub_le_sub_right (hCU n) B)
          (sq_nonneg _)) hn
    apply (tendsto_add_atTop_iff_nat n0).mp
    exact hClim

  have cost_set_bounds {m : ℕ} (p v : Fin m → ℝ)
      (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1) (hv0 : ∑ j,v j=0) (hv : v≠0) :
      (∀ R, 0≤R → ∀ Q ∈ costs p v R, (∑ j,v j^2/p j) ≤ Q) ∧
      (∀ᶠ R in 𝓝[>] 0, (costs p v R).Nonempty ∧ BddBelow (costs p v R)) := by
    clear * - p v hp hp1 hv0 hv upper_result
    have hlower (R : ℝ) (hR : 0≤R) (Q : ℝ) (hQ : Q ∈ costs p v R) :
        (∑ j,v j^2/p j) ≤ Q := by
      obtain ⟨N,rho,I,hI,hconn,hRI,hN,hNs,hc,hrho,hread,hcost⟩ := hQ
      have h0 : 0∈I := hRI ⟨by linarith,hR⟩
      have hpos : ∀ᶠ u in 𝓝 0, (rho u).PosSemidef :=
        (show ∀ᶠ u in 𝓝 (0:ℝ), u ∈ I from hI.mem_nhds h0).mono fun u hu => (hrho u hu).1
      have hh := actual_fisher (n := Fin 2) (ι := Fin m) N rho p v hN hNs hp
        ((hc.differentiableOn (by norm_num) 0 h0).differentiableAt (hI.mem_nhds h0)) hpos
        ((show ∀ᶠ u in 𝓝 (0:ℝ), u ∈ I from hI.mem_nhds h0).mono fun u hu j => by
          simpa using congrArg Complex.re (hread u hu j).1)
      rw [hcost] at hh
      exact hh
    refine ⟨hlower,?_⟩
    have hv' : ∃ j,v j≠0 := by contrapose! hv; ext j; exact hv j
    obtain ⟨N,rho,I,Q,hlim,hprog⟩ := upper_result p v hp hp1 hv0 hv'
    filter_upwards [hprog, self_mem_nhdsWithin] with R hR hRp
    have hmem : Q R ∈ costs p v R := by
      refine ⟨N R,rho R,I R,?_⟩
      rcases hR with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
      refine ⟨h1,h2,h3,h4,h5,h6,?_,h8,h9⟩
      intro u hu
      let r := densityBridge (rho R u) (h7 u hu).1 (h7 u hu).2.1
      exact ⟨(h7 u hu).1,(h7 u hu).2.1,(h7 u hu).2.2.1,r.1,r.2⟩
    exact ⟨⟨Q R,hmem⟩,⟨∑ j,v j^2/p j,fun q hq => hlower R (le_of_lt hRp) q hq⟩⟩

  have all_program_lower {m : ℕ} (p v : Fin m → ℝ)
      (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1) (hv0 : ∑ j,v j=0) (hv : v≠0)
      (hthree : ∃ i j k, v i/p i≠v j/p j ∧ v i/p i≠v k/p k ∧ v j/p j≠v k/p k)
      (R Q : ℕ → ℝ) (hR : ∀ n,0<R n) (hmem : ∀ n,Q n ∈ costs p v (R n))
      (hQ : Tendsto Q atTop (𝓝 (∑ j,v j^2/p j))) :
      ∀ d : ℝ, d<((∑ j,p j*(v j/p j)^4)-(∑ j,v j^2/p j)^2-
        (∑ j,p j*(v j/p j)^3)^2/(∑ j,v j^2/p j))/4 →
        ∀ᶠ n in atTop, d≤(Q n-(∑ j,v j^2/p j))/R n^2 := by
    clear * - p v hp hp1 hv0 hv hthree R Q hR hmem hQ score_separation actual_rank_two_lower
    classical
    let B := ∑ j,v j^2/p j
    have hB : B=∑ j,p j*(v j/p j)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    have hs : ∑ j,p j*(v j/p j)=0 := by
      simpa [mul_div_cancel₀ _ (hp _).ne'] using hv0
    obtain ⟨hBp,hVp,lo,hi,hlo,hhi,hgap⟩ := score_separation p (fun j => v j/p j) hp hp1 hs hthree
    rw [←hB] at hgap
    choose N rho I hprog using hmem
    have h0 (n : ℕ) : 0∈I n := (hprog n).2.2.1 ⟨by linarith [hR n],(hR n).le⟩
    have hpure (n : ℕ) (u : ℝ) (hu : u∈I n) :
        (rho n u).PosSemidef ∧ trace (rho n u)=1 ∧ rho n u*rho n u=rho n u :=
      ⟨((hprog n).2.2.2.2.2.2.1 u hu).1,
        ((hprog n).2.2.2.2.2.2.1 u hu).2.1,
        ((hprog n).2.2.2.2.2.2.1 u hu).2.2.1⟩
    have hread (n : ℕ) (u : ℝ) (hu : u∈I n) (j : Fin m) :
        (trace (N n j*rho n u)).re=p j+u*v j := by
      simpa using congrArg Complex.re (((hprog n).2.2.2.2.2.2.2.1 u hu j).1)
    have hrank : ∀ᶠ n in atTop,Module.finrank ℝ (effectReadout (N n)).range=2 := by
      filter_upwards [hQ.eventually (gt_mem_nhds hgap)] with n hn
      rcases actual_rank_alternative (N n) (rho n) p v (I n) (hprog n).1 (h0 n) hv hp
        (hprog n).2.2.2.1 (hprog n).2.2.2.2.2.1 (hpure n) (hread n) lo hi hlo hhi with hh | hl
      · exact hh
      · rw [(hprog n).2.2.2.2.2.2.2.2] at hl
        exact False.elim (not_le_of_gt hn hl)
    obtain ⟨n0,hn0⟩ := eventually_atTop.mp hrank
    have hcost : ∀ n,spectralQFI (rho n 0) (deriv (rho n) 0)
        (hpure n 0 (h0 n)).1=Q n := fun n => (hprog n).2.2.2.2.2.2.2.2 _
    have hQt : Tendsto (fun n => spectralQFI (rho (n+n0) 0)
        (deriv (rho (n+n0)) 0) (hpure (n+n0) 0 (h0 (n+n0))).1) atTop (𝓝 B) := by
      simp only [hcost]
      exact hQ.comp (tendsto_add_atTop_nat n0)
    have ht := actual_rank_two_lower p v B hp hp1 hv hv0 hB hthree
      (fun n => N (n+n0)) (fun n => rho (n+n0)) (fun n => I (n+n0)) (fun n => R (n+n0))
      (fun n => (hprog (n+n0)).1) (fun n => (hprog (n+n0)).2.1)
      (fun n => h0 (n+n0)) (fun n => hR (n+n0)) (fun n => (hprog (n+n0)).2.2.1)
      (fun n => (hprog (n+n0)).2.2.2.1) (fun n => (hprog (n+n0)).2.2.2.2.1)
      (fun n => (hprog (n+n0)).2.2.2.2.2.1) (fun n => hpure (n+n0))
      (fun n => hread (n+n0)) (fun n => hn0 (n+n0) (by omega)) hQt
    intro d hd
    have hh := ht d hd
    simp only [hcost] at hh
    obtain ⟨k,hk⟩ := eventually_atTop.mp hh
    apply eventually_atTop.mpr
    refine ⟨k+n0,fun n hn => ?_⟩
    have hn' : n-n0≥k := by omega
    simpa [Nat.sub_add_cancel (show n0≤n by omega)] using hk (n-n0) hn'
  intro m p v hp hp1 hv0 hv hthree
  dsimp only
  let B := ∑ j,v j^2/p j
  have hB : (∑ j,p j*(v j/p j)^2)=B := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have h3 : (∑ j,p j*(v j/p j)^3)=(∑ j,v j^3/(p j)^2) := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have h4 : (∑ j,p j*(v j/p j)^4)=(∑ j,v j^4/(p j)^3) := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hs : ∑ j,p j*(v j/p j)=0 := by
    simpa [mul_div_cancel₀ _ (hp _).ne'] using hv0
  have hV := (score_separation p (fun j => v j/p j) hp hp1 hs hthree).2.1
  refine ⟨hV,?_,?_⟩
  · filter_upwards [(cost_set_bounds p v hp hp1 hv0 hv).2] with R hR
    refine ⟨hR.1,hR.2,?_⟩
    have heq : C2 p v R=sInf (costs p v R) := by
      simp [C2,guardedInfimum,hR.1,hR.2]
    rw [heq]
    exact isGLB_csInf hR.1 hR.2
  · rw [hB]
    have hv' : ∃ j,v j≠0 := by contrapose! hv; ext j; exact hv j
    obtain ⟨N,rho,I,Q,hlim,hprog⟩ := upper_result p v hp hp1 hv0 hv'
    refine infimum_limit (costs p v) B
      (((∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B)/4) Q ?_ ?_ ?_ ?_
    · intro R hR q hq
      exact (cost_set_bounds p v hp hp1 hv0 hv).1 R hR.le q hq
    · filter_upwards [hprog] with R hR
      refine ⟨N R,rho R,I R,?_⟩
      rcases hR with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
      refine ⟨h1,h2,h3,h4,h5,h6,?_,h8,h9⟩
      intro u hu
      let r := densityBridge (rho R u) (h7 u hu).1 (h7 u hu).2.1
      exact ⟨(h7 u hu).1,(h7 u hu).2.1,(h7 u hu).2.2.1,r.1,r.2⟩
    · simpa only [h3,h4] using hlim
    · intro R Q hR hmem _hRt hQt
      exact all_program_lower p v hp hp1 hv0 hv hthree R Q hR hmem hQt

end D5.S3.Quantum.Information.ActualPureQubitCostInfimum
