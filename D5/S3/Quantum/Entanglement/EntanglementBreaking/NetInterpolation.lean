/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bilinear and quadratic interpolation of finite net estimates. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.RankNet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix
open scoped InnerProductSpace
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)

private theorem bounded_unit_pair_of_net {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (H : E →L[ℂ] E) (P : E → Prop)
    (hsmul : ∀ (c : ℂ) (x : E), P x → P (c • x))
    (N : Finset E) (hN : ∀ x ∈ N, P x ∧ ‖x‖ = 1)
    {δ t : ℝ} (hδ₀ : 0 ≤ δ) (hδ : 2 * δ < 1) (ht : 0 ≤ t)
    (hcover : ∀ x : E, P x → ‖x‖ = 1 →
      ∃ x₀ ∈ N, ∃ e₁ e₂ : E, x = x₀ + e₁ + e₂ ∧ P e₁ ∧ P e₂ ∧ ‖e₁‖ + ‖e₂‖ ≤ δ)
    (hnet : ∀ x ∈ N, ∀ y ∈ N, ‖⟪x, H y⟫_ℂ‖ ≤ t) :
    ∀ x y : E, P x → P y → ‖x‖ = 1 → ‖y‖ = 1 →
      ‖⟪x, H y⟫_ℂ‖ ≤ t / (1 - 2 * δ) := by
  let b (x y : E) : ℂ := ⟪x, H y⟫_ℂ
  let S : Set ℝ := insert 0 {s | ∃ x y : E, P x ∧ P y ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    s = ‖b x y‖}
  have hS : BddAbove S := by
    refine ⟨‖H‖, ?_⟩
    rintro s (rfl | ⟨x, y, -, -, hx, hy, rfl⟩)
    · exact norm_nonneg _
    · calc
        ‖b x y‖ ≤ ‖x‖ * ‖H y‖ := norm_inner_le_norm _ _
        _ ≤ ‖H‖ := by simpa only [hx, hy, one_mul, mul_one] using H.le_opNorm y
  let M := sSup S
  have hM : 0 ≤ M := le_csSup hS (by simp [S])
  have hunit (x y : E) (hx : P x) (hy : P y) (hxn : ‖x‖ = 1) (hyn : ‖y‖ = 1) :
      ‖b x y‖ ≤ M := le_csSup hS (Or.inr ⟨x, y, hx, hy, hxn, hyn, rfl⟩)
  have hbound (x y : E) (hx : P x) (hy : P y) : ‖b x y‖ ≤ ‖x‖ * ‖y‖ * M := by
    by_cases hx₀ : x = 0
    · simp [hx₀, b]
    by_cases hy₀ : y = 0
    · simp [hy₀, b]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx₀
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy₀
    let x' := (↑‖x‖ : ℂ)⁻¹ • x
    let y' := (↑‖y‖ : ℂ)⁻¹ • y
    have hxn : ‖x'‖ = 1 := by
      simp [x', norm_smul, Complex.norm_real, hxpos.ne']
    have hyn : ‖y'‖ = 1 := by
      simp [y', norm_smul, Complex.norm_real, hypos.ne']
    have hxx : (↑‖x‖ : ℂ) • x' = x :=
      smul_inv_smul₀ (by exact_mod_cast hxpos.ne') _
    have hyy : (↑‖y‖ : ℂ) • y' = y :=
      smul_inv_smul₀ (by exact_mod_cast hypos.ne') _
    calc
      ‖b x y‖ = ‖x‖ * ‖y‖ * ‖b x' y'‖ := by
        conv_lhs => rw [← hxx, ← hyy]
        simp [b, mul_assoc]
      _ ≤ ‖x‖ * ‖y‖ * M :=
        mul_le_mul_of_nonneg_left (hunit _ _ (hsmul _ _ hx) (hsmul _ _ hy) hxn hyn) (by positivity)
  have happrox (x y : E) (hx : P x) (hy : P y) (hxn : ‖x‖ = 1) (hyn : ‖y‖ = 1) :
      ‖b x y‖ ≤ t + 2 * δ * M := by
    obtain ⟨x₀, hx₀, e₁, e₂, heq, he₁, he₂, he⟩ := hcover x hx hxn
    obtain ⟨y₀, hy₀, f₁, f₂, hfq, hf₁, hf₂, hf⟩ := hcover y hy hyn
    have heq' : b x y = (b x₀ y₀ + (b e₁ y + b e₂ y)) + (b x₀ f₁ + b x₀ f₂) := by
      have hleft : b x y = b x₀ y + b e₁ y + b e₂ y := by
        conv_lhs => rw [heq]
        simp only [b, inner_add_left]
      have hright : b x₀ y = b x₀ y₀ + b x₀ f₁ + b x₀ f₂ := by
        conv_lhs => rw [hfq]
        simp only [b, map_add, inner_add_right]
      rw [hleft, hright]
      abel
    have h₁ := hbound e₁ y he₁ hy
    have h₂ := hbound e₂ y he₂ hy
    have h₃ := hbound x₀ f₁ (hN x₀ hx₀).1 hf₁
    have h₄ := hbound x₀ f₂ (hN x₀ hx₀).1 hf₂
    rw [hyn, mul_one] at h₁ h₂
    rw [(hN x₀ hx₀).2, one_mul] at h₃ h₄
    rw [heq']
    apply (norm_add_le _ _).trans
    have hleft := (norm_add_le (b x₀ y₀) (b e₁ y + b e₂ y)).trans
      (add_le_add (hnet x₀ hx₀ y₀ hy₀) ((norm_add_le _ _).trans (add_le_add h₁ h₂)))
    have hright := (norm_add_le _ _).trans (add_le_add h₃ h₄)
    refine (add_le_add hleft hright).trans ?_
    linarith only [mul_le_mul_of_nonneg_right he hM, mul_le_mul_of_nonneg_right hf hM]
  have htop : M ≤ t + 2 * δ * M := by
    apply csSup_le (show S.Nonempty from ⟨0, by simp [S]⟩)
    rintro s (rfl | ⟨x, y, hx, hy, hxn, hyn, rfl⟩)
    · exact ht.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hM))
    · exact happrox x y hx hy hxn hyn
  intro x y hx hy hxn hyn
  refine (hunit x y hx hy hxn hyn).trans ((le_div_iff₀ (by linarith)).mpr ?_)
  linarith

open scoped _root_.Matrix.Norms.Frobenius

private abbrev BipartiteSpace (d : ℕ) := EuclideanSpace ℂ (Fin d × Fin d)

/-- Read a coefficient matrix in the order used by the sign-cube lemmas. -/
def coeffVector {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Fin d × Fin d → ℂ :=
  fun ij => A ij.1 ij.2

private theorem coeffVector_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖WithLp.toLp 2 (coeffVector A)‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2),
    EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, coeffVector]

private theorem coeffVector_rank {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    schmidtRank (coeffVector A) = A.rank := by
  rfl

private theorem schmidtRank_smul_le {d k : ℕ} (c : ℂ) (x : BipartiteSpace d)
    (hx : schmidtRank x.ofLp ≤ k) : schmidtRank (c • x).ofLp ≤ k := by
  let A : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => x.ofLp (i, j)
  change (c • A).rank ≤ k
  by_cases hc : c = 0
  · simp [hc]
  · rwa [Matrix.rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero hc)]

private theorem inner_toEuclideanCLM_eq_dot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) H y⟫_ℂ = star x.ofLp ⬝ᵥ (H *ᵥ y.ofLp) := by
  rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y, Matrix.toEuclideanCLM_toLp,
    EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

/-- A finite net of Schmidt-rank-at-most-k vectors controls all such unit-vector pairs. -/
theorem exists_schmidt_bilinear_net (d k : ℕ) (hkd : k ≤ d) :
    ∃ N : Finset (Fin d × Fin d → ℂ),
      N.card ≤ 17 ^ (4 * d * k) ∧
      (∀ x ∈ N, ‖WithLp.toLp 2 x‖ = 1 ∧ schmidtRank x ≤ k) ∧
      ∀ (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (t : ℝ), 0 ≤ t →
        (∀ x ∈ N, ∀ y ∈ N, ‖star x ⬝ᵥ (H *ᵥ y)‖ ≤ t) →
        ∀ x y : Fin d × Fin d → ℂ, ‖WithLp.toLp 2 x‖ = 1 → ‖WithLp.toLp 2 y‖ = 1 →
          schmidtRank x ≤ k → schmidtRank y ≤ k → ‖star x ⬝ᵥ (H *ᵥ y)‖ ≤ 2 * t := by
  classical
  obtain ⟨N, hcard, hN, hcover⟩ := exists_rank_sphere_net d k hkd
  let S := N.image coeffVector
  have hS (x : Fin d × Fin d → ℂ) (hx : x ∈ S) :
      ‖WithLp.toLp 2 x‖ = 1 ∧ schmidtRank x ≤ k := by
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
    simpa only [coeffVector_norm, coeffVector_rank] using hN A hA
  refine ⟨S, Finset.card_image_le.trans hcard, hS, ?_⟩
  intro H t ht hnet x y hx hy hxr hyr
  let T : Finset (BipartiteSpace d) := S.image (WithLp.toLp 2)
  have hT (u : BipartiteSpace d) (hu : u ∈ T) : u.ofLp ∈ S := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    exact hz
  have happ := bounded_unit_pair_of_net (Matrix.toEuclideanCLM (𝕜 := ℂ) H)
    (fun u : BipartiteSpace d => schmidtRank u.ofLp ≤ k) (schmidtRank_smul_le (k := k))
    T (fun u hu => ⟨(hS _ (hT u hu)).2, (hS _ (hT u hu)).1⟩)
    (δ := 1 / 4) (by norm_num) (by norm_num) ht ?_ ?_
  · have h := happ (WithLp.toLp 2 x) (WithLp.toLp 2 y) hxr hyr hx hy
    rw [inner_toEuclideanCLM_eq_dot] at h
    change ‖star x ⬝ᵥ H *ᵥ y‖ ≤ t / (1 - 2 * (1 / 4)) at h
    convert h using 1
    ring
  · intro u hur hun
    let A : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => u.ofLp (i, j)
    have hAu : coeffVector A = u.ofLp := by ext z; cases z; rfl
    have hAn : ‖A‖ = 1 := by rw [← coeffVector_norm, hAu, WithLp.toLp_ofLp, hun]
    obtain ⟨A₀, hA₀, E₁, E₂, heq, h₁r, h₂r, h₁n, h₂n⟩ := hcover A hAn hur
    refine ⟨WithLp.toLp 2 (coeffVector A₀), Finset.mem_image.mpr
      ⟨_, Finset.mem_image.mpr ⟨A₀, hA₀, rfl⟩, rfl⟩,
      WithLp.toLp 2 (coeffVector E₁), WithLp.toLp 2 (coeffVector E₂), ?_, h₁r, h₂r, ?_⟩
    · rw [← WithLp.toLp_ofLp 2 u, ← hAu, heq]
      rfl
    · rw [coeffVector_norm, coeffVector_norm]
      linarith
  · intro u hu v hv
    rw [inner_toEuclideanCLM_eq_dot]
    exact hnet _ (hT u hu) _ (hT v hv)


/-- A full sphere net, used with quadratic tests on Hermitian matrices. -/
theorem exists_full_sphere_quadratic_net (d : ℕ) :
    ∃ N : Finset (Fin d × Fin d → ℂ),
      N.card ≤ 17 ^ (2 * d ^ 2) ∧
      (∀ x ∈ N, ‖WithLp.toLp 2 x‖ = 1) ∧
      (∀ x : Fin d × Fin d → ℂ, ‖WithLp.toLp 2 x‖ = 1 →
        ∃ y ∈ N, ‖WithLp.toLp 2 x - WithLp.toLp 2 y‖ ≤ 1 / 8) ∧
      ∀ (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ), H.IsHermitian →
        ∀ t : ℝ, 0 ≤ t → (∀ x ∈ N, ‖star x ⬝ᵥ (H *ᵥ x)‖ ≤ t) →
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) H‖ ≤ (4 / 3) * t := by
  classical
  let S : Set (BipartiteSpace d) := {x | ‖x‖ = 1}
  obtain ⟨P, hP, hcover, hcard⟩ :=
    exists_finset_net_unitBall (S := S)
      (fun _ hx => mem_closedBall_zero_iff.mpr (le_of_eq hx)) (ε := 1 / 8) (by norm_num)
  have hdim : Module.finrank ℝ (BipartiteSpace d) = 2 * d ^ 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace]
    simp [pow_two]
  rw [hdim] at hcard
  norm_num at hcard
  let N := P.image WithLp.ofLp
  have hP' (x : BipartiteSpace d) (hx : x ∈ P) : ‖x‖ = 1 := hP hx
  refine ⟨N, Finset.card_image_le.trans (by exact_mod_cast hcard), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [WithLp.toLp_ofLp] using hP' y hy
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover (WithLp.toLp 2 x) hx
    refine ⟨y.ofLp, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    simpa only [dist_eq_norm, WithLp.toLp_ofLp] using hxy
  · intro H hH t ht hnet
    let T := Matrix.toEuclideanCLM (𝕜 := ℂ) H
    have hT : IsSelfAdjoint T := hH.isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℂ))
    have hinner (x y : BipartiteSpace d) :
        ‖⟪x, T y⟫_ℂ‖ ≤ ‖x‖ * (‖T‖ * ‖y‖) :=
      (norm_inner_le_norm x (T y)).trans
        (mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg x))
    have hunit (x : BipartiteSpace d) (hx : ‖x‖ = 1) :
        ‖⟪x, T x⟫_ℂ‖ ≤ t + ‖T‖ / 4 := by
      obtain ⟨y, hy, hxy⟩ := hcover x hx
      rw [dist_eq_norm] at hxy
      have hyn := hP' y hy
      have hyq : ‖⟪y, T y⟫_ℂ‖ ≤ t := by
        rw [inner_toEuclideanCLM_eq_dot]
        exact hnet _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      have hdiff : ⟪x, T x⟫_ℂ = (⟪y, T y⟫_ℂ + ⟪x - y, T x⟫_ℂ) + ⟪y, T (x - y)⟫_ℂ := by
        simp only [inner_sub_left, map_sub, inner_sub_right]
        abel
      have h₁ := hinner (x - y) x
      have h₂ := hinner y (x - y)
      rw [hx, mul_one] at h₁
      rw [hyn, one_mul] at h₂
      rw [hdiff]
      refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
        (add_le_add hyq h₁)) h₂).trans ?_)
      linarith only [mul_le_mul_of_nonneg_right hxy (norm_nonneg T)]
    have hop : ‖T‖ ≤ t + ‖T‖ / 4 := by
      conv_lhs => rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
      apply ciSup_le
      intro x
      by_cases hx : x = 0
      · simpa [hx] using add_nonneg ht (show 0 ≤ ‖T‖ / 4 by positivity)
      · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let c := (↑‖x‖ : ℂ)⁻¹
        have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hpos.ne')
        have hcx : ‖c • x‖ = 1 := by simp [c, norm_smul, Complex.norm_real, hpos.ne']
        rw [← T.rayleigh_smul x hc, ContinuousLinearMap.rayleighQuotient, hcx,
          one_pow, div_one, ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
        exact (Complex.abs_re_le_norm _).trans (hunit _ hcx)
    change ‖T‖ ≤ _
    linarith only [hop]

end D5.S3.Quantum.Entanglement.EntanglementBreaking
