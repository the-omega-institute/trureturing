/- GID: D5/S3/Quantum/Algebra/PBMinimalEnvironment
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBMinimalEnvironment
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Three actor moments determine a minimal environment. -/

import D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Algebra.Polynomial.Roots

/-! The zero kernel-coupling branch of the finite three-moment realization problem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace Matrix MatrixOrder Polynomial
open Module (finrank)

namespace D5.S3.Quantum.Algebra.PBMinimalEnvironment

private theorem exists_real_det_ne_zero_of_complex {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (H Q : E →ₗ[ℂ] E) (h : LinearMap.det (H + Complex.I • Q) ≠ 0) :
    ∃ t : ℝ, LinearMap.det (H + (t : ℂ) • Q) ≠ 0 := by
  classical
  let b := Module.finBasis ℂ E
  let hM := LinearMap.toMatrix b b H
  let qM := LinearMap.toMatrix b b Q
  let p := (hM.map (Polynomial.C : ℂ →+* ℂ[X]) +
    (Polynomial.X : ℂ[X]) • qM.map (Polynomial.C : ℂ →+* ℂ[X])).det
  have hp (z : ℂ) : p.eval z = LinearMap.det (H + z • Q) := by
    rw [← LinearMap.det_toMatrix b]
    change Polynomial.evalRingHom z _ = _
    dsimp only [p]
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, hM, qM, mul_comm]
  have hn : p ≠ 0 := by
    intro he
    exact h (by simpa [he] using (hp Complex.I).symm)
  by_contra! ht
  have hInf : Set.Infinite ((fun x : ℝ => (x : ℂ)) '' Set.univ) :=
    Set.infinite_univ.image (Complex.ofReal_injective.injOn)
  exact hn (Polynomial.eq_zero_of_infinite_isRoot p (hInf.mono (by
    rintro _ ⟨t, -, rfl⟩
    exact (hp _).trans (ht t))))

/-- An injective symmetric map on a subspace extends to an invertible symmetric
operator on the same finite space. Its image need not lie in the subspace. -/
private theorem exists_symmetric_bijective_extension {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (M : Submodule ℂ E) (A : M →ₗ[ℂ] E) (hi : Function.Injective A)
    (hs : ∀ x y : M, ⟪A x, (y : E)⟫_ℂ = ⟪(x : E), A y⟫_ℂ) :
    ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧ Function.Bijective T ∧
      ∀ x : M, T x = A x := by
  let P : E →ₗ[ℂ] E := M.starProjection.toLinearMap
  let Q : E →ₗ[ℂ] E := Mᗮ.starProjection.toLinearMap
  let L : E →ₗ[ℂ] E := A.comp M.orthogonalProjectionOnto.toLinearMap
  have hP : P.IsSymmetric := M.starProjection_isSymmetric
  have hQ : Q.IsSymmetric := Mᗮ.starProjection_isSymmetric
  have hPL : (P.comp L).IsSymmetric := by
    intro x y
    change ⟪P (L x), y⟫_ℂ = ⟪x, P (L y)⟫_ℂ
    rw [hP, ← hP x (L y)]
    exact hs (M.orthogonalProjectionOnto x) (M.orthogonalProjectionOnto y)
  let H : E →ₗ[ℂ] E := L + L.adjoint - P.comp L
  have hH : H.IsSymmetric := by
    have hsum : (L + L.adjoint).IsSymmetric := by
      intro x y
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right,
        LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
      exact add_comm _ _
    exact hsum.sub hPL
  have hExt (x : M) : H x = A x := by
    have hL : L x = A x := by
      simp [L, M.orthogonalProjectionOnto_mem_subspace_eq_self x]
    have he : L.adjoint x = P (L x) := by
      apply ext_inner_left ℂ
      intro y
      rw [LinearMap.adjoint_inner_right, ← hP y (L x), hL]
      exact hs (M.orthogonalProjectionOnto y) x
    simp [H, he, hL]
  have hImag : Function.Injective (H + Complex.I • Q : E →ₗ[ℂ] E) := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply] at hx
    have hQQ : Q (Q x) = Q x :=
      Submodule.starProjection_eq_self_iff.mpr (Mᗮ.starProjection_apply_mem x)
    have hInner : ⟪x, Q x⟫_ℂ = ⟪Q x, Q x⟫_ℂ := by rw [hQ x (Q x), hQQ]
    have hx' : (⟪x, H x⟫_ℂ + Complex.I * ⟪Q x, Q x⟫_ℂ).im = 0 := by
      simpa [inner_add_right, inner_smul_right, hInner] using
        congrArg (fun y : E => (⟪x, y⟫_ℂ).im) hx
    have hnorm : ‖Q x‖ ^ 2 = 0 := by
      have hh : (⟪x, H x⟫_ℂ).im = 0 := hH.im_inner_self_apply x
      have hsq : ⟪Q x, Q x⟫_ℂ = ((‖Q x‖ ^ 2 : ℝ) : ℂ) := by
        exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _).trans (Complex.ofReal_pow _ _).symm
      rw [hsq, Complex.add_im, hh, Complex.I_mul_im, Complex.ofReal_re, zero_add] at hx'
      exact hx' 
    have hqx : Q x = 0 := norm_eq_zero.mp (by nlinarith)
    have hxm : x ∈ M := by
      have hz : Mᗮ.starProjection x = 0 := hqx
      rw [Submodule.starProjection_orthogonal_val, sub_eq_zero] at hz
      exact Submodule.starProjection_eq_self_iff.mp hz.symm
    have hz : A ⟨x, hxm⟩ = 0 := by simpa [hqx, hExt ⟨x, hxm⟩] using hx
    change x = 0
    exact congrArg Subtype.val (hi (hz.trans A.map_zero.symm))
  have hdet : LinearMap.det (H + Complex.I • Q) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff]
    exact LinearMap.ker_eq_bot.mpr hImag
  obtain ⟨t, ht⟩ := exists_real_det_ne_zero_of_complex H Q hdet
  have hti : Function.Injective (H + (t : ℂ) • Q : E →ₗ[ℂ] E) := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff] at ht
    exact LinearMap.ker_eq_bot.mp ht
  refine ⟨H + (t : ℂ) • Q, hH.add (hQ.smul (by simp)),
    ⟨hti, LinearMap.injective_iff_surjective.mp hti⟩, ?_⟩
  intro x
  have hqx : Q x = 0 := by
    change Mᗮ.starProjection (x : E) = 0
    rw [Submodule.starProjection_orthogonal_val, M.starProjection_mem_subspace_eq_self x, sub_self]
  simp [hqx, hExt]


open Matrix
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open D5.S3.Observer.Hilbert.FiniteSynthesisGramDistance (moore_penrose_eq_inverse)

/-- The ambient actor has two fixed, labelled complex coordinates. -/
abbrev Actor := Fin 2

/-- The order of the two labelled copies is the order of the two moment blocks. -/
def momentGram (M₀ M₁ M₂ : Matrix Actor Actor ℂ) : Matrix (Actor ⊕ Actor) (Actor ⊕ Actor) ℂ :=
  fromBlocks M₀ M₁ M₁ M₂

/-- The actual Moore–Penrose inverse, in the original environment coordinates. -/
noncomputable def envDagger {m : ℕ} (D : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.toEuclideanLin.symm (moorePenroseInverse D.toEuclideanLin)

/-- An actual finite environment for the three prescribed actor moments. -/
structure Realizes {m : ℕ} (D : Matrix (Fin m) (Fin m) ℂ)
    (V : Matrix Actor (Fin m) ℂ) (M₀ M₁ M₂ : Matrix Actor Actor ℂ) : Prop where
  hermitian : D.IsHermitian
  zero_mode : D.toEuclideanLin.ker ≤ V.toEuclideanLin.ker
  zeroth : V * Vᴴ = M₀
  first : V * envDagger D * Vᴴ = M₁
  second : V * (envDagger D * envDagger D) * Vᴴ = M₂

private theorem dagger_symm_comm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (D : E →ₗ[ℂ] E) (hD : D.IsSymmetric) :
    (moorePenroseInverse D).adjoint = moorePenroseInverse D ∧
      D.comp (moorePenroseInverse D) = (moorePenroseInverse D).comp D := by
  let T := moorePenroseInverse D
  have h := isMoorePenroseInverse_moorePenroseInverse D
  have hd : D.adjoint = D := (LinearMap.eq_adjoint_iff _ _).mpr hD |>.symm
  have hdt : (D.comp T).adjoint = D.comp T :=
    ((LinearMap.eq_adjoint_iff _ _).mpr h.isSymmetric_comp).symm
  have htd : (T.comp D).adjoint = T.comp D :=
    ((LinearMap.eq_adjoint_iff _ _).mpr h.isSymmetric_comp').symm
  have h₁ : T.adjoint.comp D = D.comp T := by
    simpa [LinearMap.adjoint_comp, hd] using hdt
  have h₂ : D.comp T.adjoint = T.comp D := by
    simpa [LinearMap.adjoint_comp, hd] using htd
  have ht : T.adjoint = T := by
    apply eq_moorePenroseInverse_of_isMoorePenroseInverse
    constructor
    · simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc, hd] using
        congrArg LinearMap.adjoint h.comp_comp_self
    · simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc, hd] using
        congrArg LinearMap.adjoint h.comp_comp_self'
    · rw [h₂]
      exact h.isSymmetric_comp'
    · rw [h₁]
      exact h.isSymmetric_comp
  exact ⟨ht, by rw [← h₁, ht]⟩

private theorem gram_blocks {n : Type*} [Fintype n]
    (F G : Matrix n Actor ℂ) :
    (fromCols F G)ᴴ * fromCols F G =
      fromBlocks (Fᴴ * F) (Fᴴ * G) (Gᴴ * F) (Gᴴ * G) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]

private theorem rank_euclidean {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    (A : Matrix m n ℂ) : A.rank = finrank ℂ A.toEuclideanLin.range := by
  exact A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun n ℂ).toBasis
    (EuclideanSpace.basisFun m ℂ).toBasis

private theorem fromCols_action {n : Type*} [Fintype n]
    (F G : Matrix n Actor ℂ) (x : EuclideanSpace ℂ (Actor ⊕ Actor)) :
    (fromCols F G).toEuclideanLin x =
      F.toEuclideanLin (WithLp.toLp 2 (fun i => x (Sum.inl i))) +
      G.toEuclideanLin (WithLp.toLp 2 (fun i => x (Sum.inr i))) := by
  apply WithLp.ofLp_injective 2
  funext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private theorem fromCols_range {n : Type*} [Fintype n] (F G : Matrix n Actor ℂ) :
    (fromCols F G).toEuclideanLin.range = F.toEuclideanLin.range ⊔ G.toEuclideanLin.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [fromCols_action]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · intro hy
    obtain ⟨f, ⟨a, rfl⟩, g, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨WithLp.toLp 2 (Sum.elim (fun i => a i) (fun i => b i)), by
      rw [fromCols_action]
      rfl⟩

private theorem gram_ker_euclidean {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (F : Matrix n m ℂ) :
    (Fᴴ * F).toEuclideanLin.ker = F.toEuclideanLin.ker := by
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.ker_adjoint_comp_self]

private theorem actual_factor {m : ℕ} {D : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix Actor (Fin m) ℂ} {M₀ M₁ M₂ : Matrix Actor Actor ℂ}
    (h : Realizes D V M₀ M₁ M₂) :
    let F := Vᴴ
    let G := envDagger D * F
    momentGram M₀ M₁ M₂ = (fromCols F G)ᴴ * fromCols F G ∧
      F.toEuclideanLin.ker = G.toEuclideanLin.ker ∧
      (fromCols F G).toEuclideanLin.range ≤ D.toEuclideanLin.range ∧
      M₀ = Fᴴ * F ∧ M₂ = Gᴴ * G := by
  dsimp only
  let F := Vᴴ
  let G := envDagger D * F
  let d := D.toEuclideanLin
  let T := moorePenroseInverse d
  have hD : d.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr h.hermitian
  obtain ⟨ht, hcomm⟩ := dagger_symm_comm d hD
  have hT : (envDagger D).toEuclideanLin = T := by simp [envDagger, T, d]
  have hTH : (envDagger D)ᴴ = envDagger D := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hT, ht]
  have hf : F.toEuclideanLin.range ≤ d.range := by
    have hd : d.adjoint = d := ((LinearMap.eq_adjoint_iff _ _).mpr hD).symm
    rw [show F.toEuclideanLin = V.toEuclideanLin.adjoint from
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint V, ← LinearMap.orthogonal_ker, ← hd,
      ← LinearMap.orthogonal_ker]
    exact Submodule.orthogonal_le h.zero_mode
  have hDT (y : _) (hy : y ∈ d.range) : d (T y) = y := by
    obtain ⟨z, rfl⟩ := hy
    exact LinearMap.congr_fun (comp_moorePenroseInverse_comp d) z
  have hg : G.toEuclideanLin = T.comp F.toEuclideanLin := by
    rw [show G = envDagger D * F from rfl, Matrix.toLpLin_mul_same, hT]
  have hk : F.toEuclideanLin.ker = G.toEuclideanLin.ker := by
    ext x
    simp only [LinearMap.mem_ker, hg, LinearMap.comp_apply]
    exact ⟨fun hx => by simp [hx], fun hx => by
      simpa [hx] using (hDT _ (hf ⟨x, rfl⟩)).symm⟩
  have hgr : G.toEuclideanLin.range ≤ d.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hf (show F.toEuclideanLin x ∈ F.toEuclideanLin.range from ⟨x, rfl⟩)
    refine ⟨T y, ?_⟩
    rw [hg, LinearMap.comp_apply, ← hy]
    exact LinearMap.congr_fun hcomm y
  have h₀ : Fᴴ * F = M₀ := by simpa [F] using h.zeroth
  have h₁ : Fᴴ * G = M₁ := by simpa [F, G, Matrix.mul_assoc] using h.first
  have h₁' : Gᴴ * F = M₁ := by
    simpa [G, Matrix.conjTranspose_mul, hTH, Matrix.mul_assoc] using h₁
  have h₂ : Gᴴ * G = M₂ := by
    simpa [F, G, Matrix.conjTranspose_mul, hTH, Matrix.mul_assoc] using h.second
  exact ⟨by rw [gram_blocks, h₀, h₁, h₁', h₂]; rfl, hk,
    by rw [fromCols_range]; exact sup_le hf hgr, h₀.symm, h₂.symm⟩


private theorem dagger_of_inverse {n : ℕ} (D T : Matrix (Fin n) (Fin n) ℂ)
    (h₁ : D * T = 1) (h₂ : T * D = 1) :
    envDagger D = T ∧ Function.Injective D.toEuclideanLin := by
  let d := D.toEuclideanLin
  let t := T.toEuclideanLin
  have hd : d.comp t = LinearMap.id := by
    simpa [d, t] using congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A.toEuclideanLin) h₁
  have ht : t.comp d = LinearMap.id := by
    simpa [d, t] using congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A.toEuclideanLin) h₂
  let e : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { d with invFun := t
             left_inv := fun x => LinearMap.congr_fun ht x
             right_inv := fun x => LinearMap.congr_fun hd x }
  exact ⟨Matrix.toEuclideanLin.injective (by
    change Matrix.toEuclideanLin (envDagger D) = t
    rw [envDagger, LinearEquiv.apply_symm_apply]
    exact moore_penrose_eq_inverse e), e.injective⟩

private theorem exists_minimal_matrices (M₀ M₁ M₂ : Matrix Actor Actor ℂ)
    (h₁ : M₁.IsHermitian) (hp : (momentGram M₀ M₁ M₂).PosSemidef)
    (hk : M₀.toEuclideanLin.ker = M₂.toEuclideanLin.ker) :
    let k := (momentGram M₀ M₁ M₂).rank
    ∃ D : Matrix (Fin k) (Fin k) ℂ, ∃ V : Matrix Actor (Fin k) ℂ,
      IsUnit D ∧ Realizes D V M₀ M₁ M₂ := by
  classical
  let Γ := momentGram M₀ M₁ M₂
  obtain ⟨R : Matrix (Actor ⊕ Actor) (Actor ⊕ Actor) ℂ, hR⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.nonneg
  change Γ = Rᴴ * R at hR
  let F := R.toCols₁
  let G := R.toCols₂
  have hcat : fromCols F G = R := fromCols_toCols R
  have hblocks := gram_blocks F G
  rw [hcat, ← hR] at hblocks
  have hFF : Fᴴ * F = M₀ := (congrArg Matrix.toBlocks₁₁ hblocks).symm
  have hFG : Fᴴ * G = M₁ := (congrArg Matrix.toBlocks₁₂ hblocks).symm
  have hGG : Gᴴ * G = M₂ := (congrArg Matrix.toBlocks₂₂ hblocks).symm
  let K := R.toEuclideanLin.range
  have hK : K = F.toEuclideanLin.range ⊔ G.toEuclideanLin.range := by
    rw [← fromCols_range, hcat]
  let f : EuclideanSpace ℂ Actor →ₗ[ℂ] K :=
    F.toEuclideanLin.codRestrict K fun x => hK.symm ▸ le_sup_left (show F.toEuclideanLin x ∈ F.toEuclideanLin.range from ⟨x, rfl⟩)
  let g : EuclideanSpace ℂ Actor →ₗ[ℂ] K :=
    G.toEuclideanLin.codRestrict K fun x => hK.symm ▸ le_sup_right (show G.toEuclideanLin x ∈ G.toEuclideanLin.range from ⟨x, rfl⟩)
  have hfgker : f.ker = g.ker := by
    rw [LinearMap.ker_codRestrict, LinearMap.ker_codRestrict,
      ← gram_ker_euclidean F, ← gram_ker_euclidean G, hFF, hGG, hk]
  let A : f.range →ₗ[ℂ] K :=
    (f.ker.liftQ g hfgker.le).comp f.quotKerEquivRange.symm.toLinearMap
  have hA (x : EuclideanSpace ℂ Actor) : A (f.rangeRestrict x) = g x := by
    simp [A, LinearMap.quotKerEquivRange_symm_apply_image]
  have hAi : Function.Injective A := by
    apply (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ _ hfgker)).comp
    exact f.quotKerEquivRange.symm.injective
  have hgram : f.adjoint.comp g = M₁.toEuclideanLin := by
    rw [← hFG, Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    ext x
    apply ext_inner_left ℂ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    rfl
  have hAs : ∀ x y : f.range, ⟪A x, (y : K)⟫_ℂ = ⟪(x : K), A y⟫_ℂ := by
    rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩
    change ⟪A (f.rangeRestrict a), f b⟫_ℂ = ⟪f a, A (f.rangeRestrict b)⟫_ℂ
    rw [hA, hA]
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr h₁
    calc
      _ = ⟪(f.adjoint.comp g) a, b⟫_ℂ := (f.adjoint_inner_left _ _).symm
      _ = ⟪a, (f.adjoint.comp g) b⟫_ℂ := by rw [hgram]; exact hs a b
      _ = _ := f.adjoint_inner_right _ _
  obtain ⟨T, hT, hTi, hTf⟩ := exists_symmetric_bijective_extension f.range A hAi hAs
  have hTfg : T.comp f = g := by
    ext x
    exact (hTf (f.rangeRestrict x)).trans (hA x)
  let e := LinearEquiv.ofBijective T hTi
  have hk' : finrank ℂ K = Γ.rank := by rw [hR, rank_conjTranspose_mul_self, rank_euclidean]
  let b := (stdOrthonormalBasis ℂ K).reindex (finCongr hk')
  let a := EuclideanSpace.basisFun Actor ℂ
  let D := LinearMap.toMatrix b.toBasis b.toBasis e.symm.toLinearMap
  let J := LinearMap.toMatrix b.toBasis b.toBasis T
  let V := LinearMap.toMatrix b.toBasis a.toBasis f.adjoint
  have hDH : D.IsHermitian := by
    change Dᴴ = D
    rw [← LinearMap.toMatrix_adjoint, hT.toLinearMap_symm.adjoint_eq]
  have hdj : D * J = 1 := by
    rw [← LinearMap.toMatrix_comp, show e.symm.toLinearMap.comp T = LinearMap.id from
      LinearMap.ext e.symm_apply_apply, LinearMap.toMatrix_id]
  have hjd : J * D = 1 := by
    rw [← LinearMap.toMatrix_comp, show T.comp e.symm.toLinearMap = LinearMap.id from
      LinearMap.ext e.apply_symm_apply, LinearMap.toMatrix_id]
  obtain ⟨hdag, hdi⟩ := dagger_of_inverse D J hdj hjd
  have hV : Vᴴ = LinearMap.toMatrix a.toBasis b.toBasis f := by
    rw [← LinearMap.toMatrix_adjoint, LinearMap.adjoint_adjoint]
  have hgram₀ : f.adjoint.comp f = M₀.toEuclideanLin := by
    rw [← hFF, Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    ext x
    apply ext_inner_left ℂ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    rfl
  have hgram₂ : g.adjoint.comp g = M₂.toEuclideanLin := by
    rw [← hGG, Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    ext x
    apply ext_inner_left ℂ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    rfl
  have hm (M : Matrix Actor Actor ℂ) :
      LinearMap.toMatrix a.toBasis a.toBasis M.toEuclideanLin = M := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact LinearEquiv.apply_symm_apply _ _
  refine ⟨D, V, isUnit_iff_exists_inv.mpr ⟨J, hdj, hjd⟩, hDH, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.ker_eq_bot.mpr hdi]
    exact bot_le
  · rw [hV, ← LinearMap.toMatrix_comp, hgram₀, hm]
  · rw [hdag, hV, Matrix.mul_assoc, ← LinearMap.toMatrix_comp, hTfg,
      ← LinearMap.toMatrix_comp, hgram, hm]
  · have he : g.adjoint = f.adjoint.comp T := by
      rw [← hTfg, LinearMap.adjoint_comp, hT.adjoint_eq]
    rw [hdag, hV, Matrix.mul_assoc, Matrix.mul_assoc J, ← LinearMap.toMatrix_comp, hTfg,
      ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, ← LinearMap.comp_assoc,
      ← he, hgram₂, hm]

end D5.S3.Quantum.Algebra.PBMinimalEnvironment
