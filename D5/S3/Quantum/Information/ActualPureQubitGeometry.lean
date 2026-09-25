/- GID: D5/S3/Quantum/Information/ActualPureQubitGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualPureQubitGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Rank-two affine readouts of pure qubit curves admit strict arc coordinates. -/

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
end D5.S3.Quantum.Information.ActualPureQubitCostInfimum
