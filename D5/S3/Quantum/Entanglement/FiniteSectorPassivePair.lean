/- GID: D5/S3/Quantum/Entanglement/FiniteSectorPassivePair
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteSectorPassivePair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Passive sector-pair prefix majorization under actual local isometries. -/

import D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open SectorSchmidtEncoding
open Matrix RHLinalg
open _root_.LinearMap
open Module (finrank)
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

set_option maxHeartbeats 40000000 in
/-- The common spectral kernel bounds every passive sector pair from actual isometries. -/
theorem sector_pair {Sector : Type u} {EX : Type u} {EY : Type u} [Fintype Sector] [DecidableEq Sector]
    [Fintype EX] [DecidableEq EX] [Fintype EY] [DecidableEq EY]
    {J : ℕ} (M : Model Sector J)
    (VX : Matrix (EX × TargetLocal M.d) (SourceLocal (Coord := Fin J) M.d) ℂ)
    (VY : Matrix (EY × TargetLocal M.d) (SourceLocal (Coord := Fin J) M.d) ℂ)
    (hVX : VXᴴ * VX = 1) (hVY : VYᴴ * VY = 1) :
    let C : Sector → Matrix (SourceLocal (Coord := Fin J) M.d)
        (SourceLocal (Coord := Fin J) M.d) ℂ := fun s => Matrix.diagonal fun u =>
      if u.1 = s then (Real.sqrt (M.spectrum s u.2.2 / (M.d s : ℝ)) : ℂ) else 0
    let Q := fun s => VX * C s * VY.transpose
    let Z : Sector → Matrix EX EY ℂ := fun s ex ey =>
      (((Real.sqrt (M.d s : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ a : Fin (M.d s), Q s (ex, ⟨s, a⟩) (ey, ⟨s, a⟩)
    ∀ s t, (∑ ex, ∑ ey, star (Z s ex ey) * Z t ex ey).re ≤ kernel M s t := by
  classical
  intro C Q Z
  have hAttain {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
      (A : E →ₗ[𝕜] F) {k : ℕ} (hkE : k ≤ finrank 𝕜 E) (hkF : k ≤ finrank 𝕜 F) :
      ∃ (u : Fin k → F) (v : Fin k → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
        RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) = kyFanSum k A := by
    classical
    set hS := A.isSymmetric_adjoint_comp_self with hSdef
    set b := hS.eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) with hbdef
    set v : Fin k → E := fun i => b (Fin.castLE hkE i) with hvdef
    have hv : Orthonormal 𝕜 v := b.orthonormal.comp _ (Fin.castLE_injective hkE)
    -- the Gram relation of the singular directions
    have hgram : ∀ i j : Fin k, ⟪A (v i), A (v j)⟫_𝕜
        = ((A.singularValues (i : ℕ) ^ 2 : ℝ) : 𝕜) * (if i = j then (1 : 𝕜) else 0) := by
      intro i j
      have h1 : ⟪A (v i), A (v j)⟫_𝕜 = ⟪(A.adjoint ∘ₗ A) (v i), v j⟫_𝕜 := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
      have h2 : (A.adjoint ∘ₗ A) (v i)
          = ((hS.eigenvalues rfl (Fin.castLE hkE i) : ℝ) : 𝕜) • v i :=
        hS.apply_eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
      have h3 : (A.singularValues (i : ℕ) ^ 2 : ℝ)
          = hS.eigenvalues rfl (Fin.castLE hkE i) :=
        A.sq_singularValues_fin (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
      rw [h1, h2, inner_smul_left, RCLike.conj_ofReal, h3]
      rw [orthonormal_iff_ite.mp hv i j]
    -- norms of the images
    have hnorm : ∀ i : Fin k, ‖A (v i)‖ = A.singularValues (i : ℕ) := by
      intro i
      have h := hgram i i
      rw [if_pos rfl, mul_one] at h
      have h2 : ‖A (v i)‖ ^ 2 = A.singularValues (i : ℕ) ^ 2 := by
        have := congrArg (RCLike.re (K := 𝕜)) h
        rw [inner_self_eq_norm_sq_to_K] at this
        simpa using this
      have := A.singularValues_nonneg (i : ℕ)
      nlinarith [norm_nonneg (A (v i))]
    -- the codomain family, defined on the indices with a nonzero singular value
    set w : Fin (finrank 𝕜 F) → F := fun j =>
      if h : (j : ℕ) < k then ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, h⟩) else 0
      with hwdef
    set s : Set (Fin (finrank 𝕜 F)) :=
      {j | (j : ℕ) < k ∧ A.singularValues (j : ℕ) ≠ 0} with hsdef
    have hws : Orthonormal 𝕜 (s.domRestrict w) := by
      rw [orthonormal_iff_ite]
      rintro ⟨j, hj⟩ ⟨j', hj'⟩
      obtain ⟨hjk, hjne⟩ := hj
      obtain ⟨hj'k, hj'ne⟩ := hj'
      have hwj : w j = ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, hjk⟩) := by
        simp [hwdef, hjk]
      have hwj' : w j' = ((A.singularValues (j' : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j', hj'k⟩) := by
        simp [hwdef, hj'k]
      change ⟪w j, w j'⟫_𝕜 = _
      rw [hwj, hwj', inner_smul_left, inner_smul_right, hgram ⟨j, hjk⟩ ⟨j', hj'k⟩]
      have hj0 : ((A.singularValues (j : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hjne
      rcases eq_or_ne j j' with hjj | hjj
      · subst hjj
        simp only [map_inv₀, RCLike.conj_ofReal]
        push_cast
        field_simp
      · have h1 : (⟨(j : ℕ), hjk⟩ : Fin k) ≠ ⟨(j' : ℕ), hj'k⟩ := by
          simp only [ne_eq, Fin.mk.injEq]
          exact fun hh => hjj (Fin.ext hh)
        simp [h1, hjj, Subtype.ext_iff]
    obtain ⟨c, hc⟩ := hws.exists_orthonormalBasis_extension_of_card_eq
      (Fintype.card_fin _).symm
    set u : Fin k → F := fun i => c (Fin.castLE hkF i) with hudef
    have hu : Orthonormal 𝕜 u := c.orthonormal.comp _ (Fin.castLE_injective hkF)
    refine ⟨u, v, hu, hv, ?_⟩
    have hterm : ∀ i : Fin k, ⟪u i, A (v i)⟫_𝕜 = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) := by
      intro i
      by_cases hz : A.singularValues (i : ℕ) = 0
      · have hA0 : A (v i) = 0 := by
          have h := hnorm i
          rw [hz] at h
          exact norm_eq_zero.mp h
        rw [hA0, inner_zero_right, hz, RCLike.ofReal_zero]
      · have hlt : ((Fin.castLE hkF i : Fin (finrank 𝕜 F)) : ℕ) < k := i.isLt
        have hmem : (Fin.castLE hkF i) ∈ s := ⟨hlt, hz⟩
        have hwv : w (Fin.castLE hkF i) = ((A.singularValues (i : ℕ) : ℝ) : 𝕜)⁻¹ • A (v i) := by
          simp only [hwdef, dif_pos hlt]
          rfl
        have h0 : ((A.singularValues (i : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hz
        change ⟪c (Fin.castLE hkF i), A (v i)⟫_𝕜 = _
        rw [hc _ hmem, hwv, inner_smul_left, hgram i i]
        simp only [map_inv₀, RCLike.conj_ofReal]
        push_cast
        field_simp
    rw [Finset.sum_congr rfl fun (i : Fin k) (_ : i ∈ Finset.univ) => hterm i]
    rw [show (∑ i : Fin k, ((A.singularValues (i : ℕ) : ℝ) : 𝕜))
        = ((∑ i : Fin k, A.singularValues (i : ℕ) : ℝ) : 𝕜) by push_cast; rfl,
      RCLike.ofReal_re]
    rfl
  have hSourcePrefix {Sector : Type u} {EX : Type u} {EY : Type u}
      [Fintype Sector] [DecidableEq Sector]
      [Fintype EX] [DecidableEq EX] [Fintype EY] [DecidableEq EY]
      {J : ℕ} (d : Sector → ℕ) (s : Sector) (hd : 0 < d s)
      (lam : Fin J → ℝ) (hnonneg : ∀ j, 0 ≤ lam j) (hanti : Antitone lam) :
      let S := Sigma (fun t : Sector => Fin (d t) × Fin J)
      let O := Sigma (fun t : Sector => Fin (d t))
      ∀ (VX : Matrix (EX × O) S ℂ) (VY : Matrix (EY × O) S ℂ),
      VXᴴ * VX = 1 → VYᴴ * VY = 1 →
      let C : Matrix S S ℂ := Matrix.diagonal fun u =>
        if u.1 = s then (Real.sqrt (lam u.2.2 / (d s : ℝ)) : ℂ) else 0
      let Q := VX * C * VY.transpose
      let Z : Matrix EX EY ℂ := fun ex ey =>
        (((Real.sqrt (d s : ℝ))⁻¹ : ℝ) : ℂ) *
          ∑ a : Fin (d s), Q (ex, ⟨s, a⟩) (ey, ⟨s, a⟩)
      ∀ k : ℕ, kyFanSum k (Matrix.toEuclideanLin Z) ≤
        ∑ j : Fin (min k J), Real.sqrt (lam (Fin.castLE (Nat.min_le_right k J) j)) := by
    classical
    intro S O VX VY hVX hVY C Q Z k
    have hspectrum : ∀ i : ℕ, (Matrix.toEuclideanLin Q).singularValues i =
        if hi : i < J * d s then
          Real.sqrt (lam (⟨i, hi⟩ : Fin (J * d s)).divNat / (d s : ℝ)) else 0 := by
      let I := Fin J × Fin (d s)
      let B : Matrix I I ℂ :=
        Matrix.diagonal fun ja => (Real.sqrt (lam ja.1 / (d s : ℝ)) : ℂ)
      have hfiber : ∃ W : Matrix S I ℂ, Wᴴ * W = 1 ∧ C = W * B * Wᴴ := by
        let f : Fin J × Fin (d s) → S := fun ja => ⟨s, (ja.2, ja.1)⟩
        have hf : Function.Injective f := by
          rintro ⟨j, a⟩ ⟨j', a'⟩ h
          change (⟨s, (a, j)⟩ : Sigma (fun t : Sector => Fin (d t) × Fin J)) =
            ⟨s, (a', j')⟩ at h
          have hp : (a, j) = (a', j') :=
            (@sigma_mk_injective Sector (fun t => Fin (d t) × Fin J) s) h
          exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)
        have hfeq (j : Fin J) (a : Fin (d s)) (ja : Fin J × Fin (d s)) :
            (⟨s, (a, j)⟩ : S) = f ja ↔ ja = (j, a) := by
          change f (j, a) = f ja ↔ ja = (j, a)
          rw [hf.eq_iff, eq_comm]
        let W : Matrix S (Fin J × Fin (d s)) ℂ :=
          fun u ja => if u = f ja then 1 else 0
        refine ⟨W, ?_, ?_⟩
        · ext ja jb
          change (∑ u : S, star (if u = f ja then (1 : ℂ) else 0) *
            (if u = f jb then (1 : ℂ) else 0)) = if ja = jb then 1 else 0
          have hs (u : S) : star (if u = f ja then (1 : ℂ) else 0) =
              if u = f ja then (1 : ℂ) else 0 := by split_ifs <;> simp
          simp_rw [hs, ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq']
          simp only [Finset.mem_univ, if_true]
          by_cases h : ja = jb
          · subst jb
            simp
          · have h' : f ja ≠ f jb := fun e => h (hf e)
            simp [h, h']
        · ext u v
          have heval : (W * B * Wᴴ) u v =
              ∑ ja : Fin J × Fin (d s),
                (if u = f ja then (1 : ℂ) else 0) *
                (Real.sqrt (lam ja.1 / (d s : ℝ)) : ℂ) *
                (if v = f ja then (1 : ℂ) else 0) := by
            rw [Matrix.mul_apply]
            change (∑ ja, (W * Matrix.diagonal
              (fun ja : Fin J × Fin (d s) => (Real.sqrt (lam ja.1 / (d s : ℝ)) : ℂ))) u ja *
              star (W v ja)) = _
            simp only [Matrix.mul_diagonal]
            simp only [W, apply_ite, star_one, star_zero]
          change (if u = v then
            (if u.1 = s then (Real.sqrt (lam u.2.2 / (d s : ℝ)) : ℂ) else 0)
            else 0) = (W * B * Wᴴ) u v
          rw [heval]
          by_cases huv : u = v
          · subst v
            rw [if_pos rfl]
            by_cases hus : u.1 = s
            · obtain ⟨t, a, j⟩ := u
              dsimp only at hus
              subst t
              simp [hfeq]
            · rw [if_neg hus]
              symm
              refine Finset.sum_eq_zero fun ja _ => ?_
              have huf : u ≠ f ja := fun h => hus (congrArg Sigma.fst h)
              simp [huf]
          · rw [if_neg huv]
            symm
            refine Finset.sum_eq_zero fun ja _ => ?_
            by_cases huf : u = f ja
            · have hvf : v ≠ f ja := fun h => huv (huf.trans h.symm)
              simp [huf, hvf]
            · simp [huf]

      obtain ⟨W, hW, hC⟩ := hfiber
      have hxi : ∃ (ix : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (EX × O))
          (iy : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (EY × O)),
          Matrix.toEuclideanLin (VX * C * VY.transpose) =
            ix.toLinearMap ∘ₗ (Matrix.toEuclideanLin B ∘ₗ iy.toLinearMap.adjoint) := by
        let conjVY : Matrix (EY × O) S ℂ := VY.map star
        have hconj : conjVYᴴ * conjVY = 1 := by
          ext i j
          have h := congrArg star (congrFun (congrFun hVY i) j)
          simpa [conjVY, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.one_apply, mul_comm] using h
        have hconjT : conjVYᴴ = VY.transpose := by
          ext i j
          simp [conjVY, Matrix.conjTranspose_apply]
        have hX : (VX * W)ᴴ * (VX * W) = 1 := by
          calc
            (VX * W)ᴴ * (VX * W) = Wᴴ * (VXᴴ * VX) * W := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
            _ = 1 := by rw [hVX, Matrix.mul_one, hW]
        have hY : (conjVY * W)ᴴ * (conjVY * W) = 1 := by
          calc
            (conjVY * W)ᴴ * (conjVY * W) = Wᴴ * (conjVYᴴ * conjVY) * W := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
            _ = 1 := by rw [hconj, Matrix.mul_one, hW]
        let LX := Matrix.toEuclideanLin (VX * W)
        let LY := Matrix.toEuclideanLin (conjVY * W)
        have hgramX : LX.adjoint ∘ₗ LX = LinearMap.id := by
          change (Matrix.toEuclideanLin (VX * W)).adjoint ∘ₗ
            Matrix.toEuclideanLin (VX * W) = _
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
            ← Matrix.toLpLin_mul_same, hX, Matrix.toLpLin_one]
        have hgramY : LY.adjoint ∘ₗ LY = LinearMap.id := by
          change (Matrix.toEuclideanLin (conjVY * W)).adjoint ∘ₗ
            Matrix.toEuclideanLin (conjVY * W) = _
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
            ← Matrix.toLpLin_mul_same, hY, Matrix.toLpLin_one]
        have hinnerX (x y : EuclideanSpace ℂ I) : ⟪LX x, LX y⟫_ℂ = ⟪x, y⟫_ℂ := by
          rw [← LinearMap.adjoint_inner_left]
          change ⟪(LX.adjoint ∘ₗ LX) x, y⟫_ℂ = _
          rw [hgramX]
          rfl
        have hinnerY (x y : EuclideanSpace ℂ I) : ⟪LY x, LY y⟫_ℂ = ⟪x, y⟫_ℂ := by
          rw [← LinearMap.adjoint_inner_left]
          change ⟪(LY.adjoint ∘ₗ LY) x, y⟫_ℂ = _
          rw [hgramY]
          rfl
        let ix := LX.isometryOfInner hinnerX
        let iy := LY.isometryOfInner hinnerY
        have hix : ix.toLinearMap = Matrix.toEuclideanLin (VX * W) :=
          LinearMap.isometryOfInner_toLinearMap _ _
        have hiy : iy.toLinearMap = Matrix.toEuclideanLin (conjVY * W) :=
          LinearMap.isometryOfInner_toLinearMap _ _
        refine ⟨ix, iy, ?_⟩
        rw [hix, hiy, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
          ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
        congr 1
        rw [hC, Matrix.conjTranspose_mul, hconjT]
        simp only [Matrix.mul_assoc]

      obtain ⟨ix, iy, hxi⟩ := hxi
      let E0 := EuclideanSpace ℂ I
      let F0 := EuclideanSpace ℂ I
      let H0 := EuclideanSpace ℂ (EY × O)
      let K0 := EuclideanSpace ℂ (EX × O)
      have hiso : (ix.toLinearMap ∘ₗ (Matrix.toEuclideanLin B ∘ₗ
          iy.toLinearMap.adjoint)).singularValues = (Matrix.toEuclideanLin B).singularValues := by
        have sortedSpectrum {S : H0 →ₗ[ℂ] H0} {n : ℕ}
            (hS : S.IsSymmetric) (hn : finrank ℂ H0 = n)
            (w : OrthonormalBasis (Fin n) ℂ H0) {μ : Fin n → ℝ}
            (hμ : Antitone μ) (hw : ∀ i, S (w i) = (μ i : ℂ) • w i) :
            hS.eigenvalues hn = μ := by
          have hmatrix : S.toMatrix w.toBasis w.toBasis =
              Matrix.diagonal (RCLike.ofReal ∘ μ) := by
            ext i j
            rw [LinearMap.toMatrix_apply]
            change (w.repr (S (w j))) i = _
            rw [hw, map_smul, w.repr_self]
            by_cases hij : i = j
            · subst j
              simp
            · simp [hij]
          have hchar : S.charpoly = ∏ i, (Polynomial.X - Polynomial.C (μ i : ℂ)) := by
            rw [← S.charpoly_toMatrix w.toBasis, hmatrix, Matrix.charpoly_diagonal]
            rfl
          have hroots : S.charpoly.roots =
              Multiset.map (RCLike.ofReal ∘ μ) Finset.univ.val := by
            rw [hchar, Polynomial.roots_prod _ _ (by
              simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
            simp
          rw [← List.ofFn_inj, ← hS.sort_roots_charpoly_eq_eigenvalues hn]
          simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
            Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
          convert! List.mergeSort_of_pairwise ?_
          simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
          exact hμ.sortedGE_ofFn

        have adjointApply (ι : E0 →ₗᵢ[ℂ] H0) (x : E0) :
            LinearMap.adjoint ι.toLinearMap (ι x) = x :=
          ext_inner_right ℂ fun y => by
            rw [LinearMap.adjoint_inner_left]
            exact ι.inner_map_map x y

        have adjointZero (ι : E0 →ₗᵢ[ℂ] H0) {y : H0}
            (hy : y ∈ (LinearMap.range ι.toLinearMap)ᗮ) :
            LinearMap.adjoint ι.toLinearMap y = 0 :=
          ext_inner_right ℂ fun z => by
            rw [LinearMap.adjoint_inner_left, inner_zero_left]
            exact Submodule.inner_left_of_mem_orthogonal
              (LinearMap.mem_range.mpr ⟨z, rfl⟩) hy
        have finrank_le_of_linearIsometry (ι : E0 →ₗᵢ[ℂ] H0) :
            finrank ℂ E0 ≤ finrank ℂ H0 := by
          have hdimU : finrank ℂ (LinearMap.range ι.toLinearMap) = finrank ℂ E0 :=
            LinearMap.finrank_range_of_inj ι.injective
          have hsum := Submodule.finrank_add_finrank_orthogonal (LinearMap.range ι.toLinearMap)
          omega

        have finrank_orthogonal_range_linearIsometry (ι : E0 →ₗᵢ[ℂ] H0) :
            finrank ℂ ((LinearMap.range ι.toLinearMap)ᗮ : Submodule ℂ H0)
              = finrank ℂ H0 - finrank ℂ E0 := by
          have hdimU : finrank ℂ (LinearMap.range ι.toLinearMap) = finrank ℂ E0 :=
            LinearMap.finrank_range_of_inj ι.injective
          have hsum := Submodule.finrank_add_finrank_orthogonal (LinearMap.range ι.toLinearMap)
          omega

        let isometryPad (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) : Fin (finrank ℂ H0) → H0 := fun i =>
          if h : (i : ℕ) < finrank ℂ E0 then ι (v ⟨(i : ℕ), h⟩)
          else
            (stdOrthonormalBasis ℂ ((LinearMap.range ι.toLinearMap)ᗮ : Submodule ℂ H0)
              (Fin.cast (finrank_orthogonal_range_linearIsometry ι).symm
                ⟨(i : ℕ) - finrank ℂ E0, by have := i.isLt; omega⟩) : H0)

        have isometryPad_of_lt (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) {i : Fin (finrank ℂ H0)}
            (h : (i : ℕ) < finrank ℂ E0) : isometryPad ι v i = ι (v ⟨(i : ℕ), h⟩) :=
          dif_pos h

        have isometryPad_of_ge (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) {i : Fin (finrank ℂ H0)}
            (h : ¬ (i : ℕ) < finrank ℂ E0) :
            isometryPad ι v i
              = (stdOrthonormalBasis ℂ ((LinearMap.range ι.toLinearMap)ᗮ : Submodule ℂ H0)
                  (Fin.cast (finrank_orthogonal_range_linearIsometry ι).symm
                    ⟨(i : ℕ) - finrank ℂ E0, by have := i.isLt; omega⟩) : H0) :=
          dif_neg h

        have isometryPad_mem_range (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) {i : Fin (finrank ℂ H0)}
            (h : (i : ℕ) < finrank ℂ E0) : isometryPad ι v i ∈ LinearMap.range ι.toLinearMap := by
          rw [isometryPad_of_lt ι v h]; exact ⟨_, rfl⟩

        have isometryPad_mem_orthogonal (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) {i : Fin (finrank ℂ H0)}
            (h : ¬ (i : ℕ) < finrank ℂ E0) :
            isometryPad ι v i ∈ (LinearMap.range ι.toLinearMap)ᗮ := by
          rw [isometryPad_of_ge ι v h]; exact SetLike.coe_mem _

        have orthonormal_isometryPad (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) : Orthonormal ℂ (isometryPad ι v) := by
          classical
          rw [orthonormal_iff_ite]
          intro i j
          by_cases hi : (i : ℕ) < finrank ℂ E0
          · by_cases hj : (j : ℕ) < finrank ℂ E0
            · rw [isometryPad_of_lt ι v hi, isometryPad_of_lt ι v hj, ι.inner_map_map,
                orthonormal_iff_ite.mp v.orthonormal]
              by_cases hij : i = j
              · subst hij; rw [if_pos rfl, if_pos rfl]
              · rw [if_neg (fun hc => hij (Fin.ext (by simpa using congrArg Fin.val hc))),
                  if_neg hij]
            · rw [if_neg (fun hc : i = j => hj (hc ▸ hi))]
              exact Submodule.inner_right_of_mem_orthogonal (isometryPad_mem_range ι v hi)
                (isometryPad_mem_orthogonal ι v hj)
          · by_cases hj : (j : ℕ) < finrank ℂ E0
            · rw [if_neg (fun hc : i = j => hi (hc ▸ hj))]
              exact Submodule.inner_left_of_mem_orthogonal (isometryPad_mem_range ι v hj)
                (isometryPad_mem_orthogonal ι v hi)
            · rw [isometryPad_of_ge ι v hi, isometryPad_of_ge ι v hj, ← Submodule.coe_inner,
                orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ
                  ((LinearMap.range ι.toLinearMap)ᗮ : Submodule ℂ H0)).orthonormal]
              by_cases hij : i = j
              · subst hij; rw [if_pos rfl, if_pos rfl]
              · rw [if_neg (fun hc => ?_), if_neg hij]
                rw [Fin.cast_inj] at hc
                have hval : (i : ℕ) - finrank ℂ E0 = (j : ℕ) - finrank ℂ E0 := by
                  simpa using congrArg Fin.val hc
                have hi' := i.isLt
                have hj' := j.isLt
                exact hij (Fin.ext (by omega))

        let isometryPadBasis (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) :
            OrthonormalBasis (Fin (finrank ℂ H0)) ℂ H0 :=
          OrthonormalBasis.mk (orthonormal_isometryPad ι v) (by
            refine (Submodule.eq_top_of_finrank_eq ?_).ge
            rw [finrank_span_eq_card (orthonormal_isometryPad ι v).linearIndependent,
              Fintype.card_fin])

        have isometryPadBasis_apply (ι : E0 →ₗᵢ[ℂ] H0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) (i : Fin (finrank ℂ H0)) :
            isometryPadBasis ι v i = isometryPad ι v i :=
          congrFun (OrthonormalBasis.coe_mk _ _) i

        have antitone_padZero {n m : ℕ} {μ : Fin n → ℝ} (hanti : Antitone μ)
            (hnonneg : ∀ i, 0 ≤ μ i) :
            Antitone (fun i : Fin m => if h : (i : ℕ) < n then μ ⟨(i : ℕ), h⟩ else 0) := by
          intro i j hij
          have hvij : (i : ℕ) ≤ (j : ℕ) := hij
          dsimp only
          by_cases hj : (j : ℕ) < n
          · have hi : (i : ℕ) < n := lt_of_le_of_lt hvij hj
            rw [dif_pos hi, dif_pos hj]
            exact hanti (Fin.mk_le_mk.mpr hvij)
          · rw [dif_neg hj]
            by_cases hi : (i : ℕ) < n
            · rw [dif_pos hi]; exact hnonneg _
            · rw [dif_neg hi]

        have isometryPadBasis_conj_apply (ι : E0 →ₗᵢ[ℂ] H0)
            (G : E0 →ₗ[ℂ] E0)
            (v : OrthonormalBasis (Fin (finrank ℂ E0)) ℂ E0) (μ : Fin (finrank ℂ E0) → ℝ)
            (hv : ∀ j, G (v j) = ((μ j : ℝ) : ℂ) • v j) (i : Fin (finrank ℂ H0)) :
            (ι.toLinearMap ∘ₗ (G ∘ₗ LinearMap.adjoint ι.toLinearMap)) (isometryPadBasis ι v i)
              = (((if h : (i : ℕ) < finrank ℂ E0 then μ ⟨(i : ℕ), h⟩ else 0 : ℝ)) : ℂ)
                  • isometryPadBasis ι v i := by
          classical
          rw [isometryPadBasis_apply]
          by_cases h : (i : ℕ) < finrank ℂ E0
          · simp only [dif_pos h, isometryPad_of_lt ι v h, LinearMap.comp_apply,
              adjointApply, hv, map_smul, LinearIsometry.coe_toLinearMap]
          · simp only [dif_neg h, isometryPad_of_ge ι v h, LinearMap.comp_apply,
              adjointZero ι (SetLike.coe_mem _),
              map_zero, Complex.ofReal_zero, zero_smul]

        have singularPad
            (ι : E0 →ₗᵢ[ℂ] H0) (X : E0 →ₗ[ℂ] F0) :
            (X ∘ₗ LinearMap.adjoint ι.toLinearMap).singularValues = X.singularValues := by
          classical
          set Y : H0 →ₗ[ℂ] F0 := X ∘ₗ LinearMap.adjoint ι.toLinearMap with hYdef
          -- the gram operator of `Y` is that of `X`, conjugated onto the range of `ι`
          have hgram : LinearMap.adjoint Y ∘ₗ Y =
              ι.toLinearMap ∘ₗ ((LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
            rw [hYdef, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
            ext x
            simp only [LinearMap.comp_apply]
          have hGX : (LinearMap.adjoint X ∘ₗ X).IsSymmetric := X.isSymmetric_adjoint_comp_self
          -- push its eigenbasis into `H0` along `ι`, padding the complement with zeros
          have heq := sortedSpectrum
            Y.isSymmetric_adjoint_comp_self rfl (isometryPadBasis ι (hGX.eigenvectorBasis rfl))
            (antitone_padZero (hGX.eigenvalues_antitone rfl)
              (fun i => X.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i))
            (fun i => by
              rw [hgram]
              exact isometryPadBasis_conj_apply ι _ _ (hGX.eigenvalues rfl)
                (fun j => hGX.apply_eigenvectorBasis rfl j) i)
          -- three ranges of the index: inside `E0`, the padding, and past `H0`
          refine Finsupp.ext fun i => ?_
          rcases lt_or_ge i (finrank ℂ E0) with hid | hid
          · have hin : i < finrank ℂ H0 := lt_of_lt_of_le hid (finrank_le_of_linearIsometry ι)
            rw [Y.singularValues_of_lt rfl hin, X.singularValues_of_lt rfl hid, heq]
            simp only [dif_pos hid]
          · rcases lt_or_ge i (finrank ℂ H0) with hin | hin
            · rw [Y.singularValues_of_lt rfl hin, X.singularValues_of_finrank_le hid, heq]
              simp only [dif_neg (not_lt.mpr hid)]
              exact Real.sqrt_zero
            · rw [Y.singularValues_of_finrank_le hin, X.singularValues_of_finrank_le hid]

        have singularLeft (ι : F0 →ₗᵢ[ℂ] K0) (X : H0 →ₗ[ℂ] F0) :
            (ι.toLinearMap ∘ₗ X).singularValues = X.singularValues := by
          have hgram : (ι.toLinearMap ∘ₗ X).adjoint ∘ₗ (ι.toLinearMap ∘ₗ X) =
              X.adjoint ∘ₗ X := by
            apply LinearMap.ext
            intro x
            apply ext_inner_right ℂ
            intro y
            simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
            exact ι.inner_map_map (X x) (X y)
          have heigen :
              (ι.toLinearMap ∘ₗ X).isSymmetric_adjoint_comp_self.eigenvalues rfl =
                X.isSymmetric_adjoint_comp_self.eigenvalues rfl := by
            congr 1
          refine Finsupp.ext fun i => ?_
          rcases lt_or_ge i (finrank ℂ H0) with hi | hi
          · rw [(ι.toLinearMap ∘ₗ X).singularValues_of_lt rfl hi,
              X.singularValues_of_lt rfl hi, heigen]
          · rw [(ι.toLinearMap ∘ₗ X).singularValues_of_finrank_le hi,
              X.singularValues_of_finrank_le hi]

        rw [singularLeft ix, singularPad iy (Matrix.toEuclideanLin B)]

      let ds := d s
      have hrepeated : ∀ i : Fin (J * ds), (Matrix.toEuclideanLin B).singularValues i =
          Real.sqrt (lam i.divNat / (ds : ℝ)) := by
        let H := EuclideanSpace ℂ (Fin J × Fin ds)
        let A : H →ₗ[ℂ] H := Matrix.toEuclideanLin B
        let mu : Fin (J * ds) → ℝ := fun i => lam i.divNat / (ds : ℝ)
        have hmu : Antitone mu := by
          intro i j hij
          exact div_le_div_of_nonneg_right
            (hanti (Fin.mk_le_mk.mpr (Nat.div_le_div_right hij))) (Nat.cast_nonneg ds)
        have hpos (i : Fin (J * ds)) : 0 ≤ mu i :=
          div_nonneg (hnonneg _) (Nat.cast_nonneg ds)
        have hgram : A.adjoint ∘ₗ A =
            Matrix.toEuclideanLin (Matrix.diagonal fun ja => ((lam ja.1 / (ds : ℝ) : ℝ) : ℂ)) := by
          change (Matrix.toEuclideanLin B).adjoint ∘ₗ Matrix.toEuclideanLin B = _
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
            ← Matrix.toLpLin_mul_same]
          congr 1
          ext i j
          simp only [B, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
          by_cases hij : i = j
          · subst j
            simp only [Matrix.diagonal_apply_eq]
            simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg (hnonneg _) (Nat.cast_nonneg ds))]
          · simp [Matrix.diagonal_apply_ne _ hij]
        let w := (EuclideanSpace.basisFun (Fin J × Fin ds) ℂ).reindex finProdFinEquiv
        have hw (i : Fin (J * ds)) :
            (A.adjoint ∘ₗ A) (w i) = (mu i : ℂ) • w i := by
          rw [hgram]
          ext j
          change (Matrix.diagonal (fun ja => ((lam ja.1 / (ds : ℝ) : ℝ) : ℂ)) *ᵥ (w i).ofLp) j =
            (mu i : ℂ) * w i j
          rw [Matrix.mulVec_diagonal]
          by_cases hij : j = finProdFinEquiv.symm i
          · subst j
            simp [mu, finProdFinEquiv]
          · have hij' : j ≠ (i.divNat, i.modNat) := hij
            simp [w, OrthonormalBasis.reindex_apply, EuclideanSpace.basisFun_apply, hij']
        have sortedSpectrum {S : H →ₗ[ℂ] H}
            (hS : S.IsSymmetric) (hn : finrank ℂ H = J * ds)
            (v : OrthonormalBasis (Fin (J * ds)) ℂ H) {nu : Fin (J * ds) → ℝ}
            (hnu : Antitone nu) (hv : ∀ i, S (v i) = (nu i : ℂ) • v i) :
            hS.eigenvalues hn = nu := by
          have hmatrix : S.toMatrix v.toBasis v.toBasis =
              Matrix.diagonal (RCLike.ofReal ∘ nu) := by
            ext i j
            rw [LinearMap.toMatrix_apply]
            change (v.repr (S (v j))) i = _
            rw [hv, map_smul, v.repr_self]
            by_cases hij : i = j
            · subst j
              simp
            · simp [hij]
          have hchar : S.charpoly =
              ∏ i, (Polynomial.X - Polynomial.C (nu i : ℂ)) := by
            rw [← S.charpoly_toMatrix v.toBasis, hmatrix, Matrix.charpoly_diagonal]
            rfl
          have hroots : S.charpoly.roots =
              Multiset.map (RCLike.ofReal ∘ nu) Finset.univ.val := by
            rw [hchar, Polynomial.roots_prod _ _ (by
              simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
            simp
          rw [← List.ofFn_inj, ← hS.sort_roots_charpoly_eq_eigenvalues hn]
          simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
            Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
          convert! List.mergeSort_of_pairwise ?_
          simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
          exact hnu.sortedGE_ofFn
        have heigen := sortedSpectrum A.isSymmetric_adjoint_comp_self (by simp [H]) w hmu hw
        intro i
        rw [A.singularValues_fin (by simp [H]), heigen]

      intro i
      rw [hxi, hiso]
      by_cases hi : i < J * d s
      · rw [dif_pos hi]
        exact hrepeated ⟨i, hi⟩
      · rw [dif_neg hi]
        exact (Matrix.toEuclideanLin B).singularValues_of_finrank_le
          (by simpa [I] using Nat.le_of_not_lt hi)

    let ds := d s
    let sig := (Matrix.toEuclideanLin Q).singularValues
    have hsig : ∀ i : ℕ, sig i = if hi : i < J * ds then
        Real.sqrt (lam (⟨i, hi⟩ : Fin (J * ds)).divNat / (ds : ℝ)) else 0 := hspectrum
    have hprefix (k : ℕ) : (∑ i : Fin (k * ds), sig i) =
        Real.sqrt (ds : ℝ) * ∑ j : Fin (min k J),
          Real.sqrt (lam (Fin.castLE (Nat.min_le_right k J) j)) := by
      let q := min k J
      have hqk : q ≤ k := Nat.min_le_left _ _
      have hqJ : q ≤ J := Nat.min_le_right _ _
      have hcut : (∑ i : Fin (k * ds), sig i) = ∑ i : Fin (q * ds), sig i := by
        rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
        symm
        refine Finset.sum_subset (Finset.range_mono (Nat.mul_le_mul_right ds hqk))
          fun i hik hiq => ?_
        simp only [Finset.mem_range, not_lt] at hik hiq
        rw [hsig, dif_neg]
        have hJd : J * ds ≤ i := by
          by_cases hkJ : k ≤ J
          · have hqeq : q = k := Nat.min_eq_left hkJ
            rw [hqeq] at hiq
            omega
          · have hqeq : q = J := Nat.min_eq_right (by omega)
            simpa [hqeq] using hiq
        omega
      rw [hcut, ← finProdFinEquiv.sum_comp]
      rw [Fintype.sum_prod_type]
      have hterm (j : Fin q) (a : Fin ds) :
          sig (finProdFinEquiv (j, a)).val =
            Real.sqrt (lam (Fin.castLE hqJ j) / (ds : ℝ)) := by
        have hi : (finProdFinEquiv (j, a)).val < J * ds :=
          lt_of_lt_of_le (finProdFinEquiv (j, a)).isLt (Nat.mul_le_mul_right ds hqJ)
        rw [hsig, dif_pos hi]
        congr 2
        apply congrArg lam
        apply Fin.ext
        change (a.val + ds * j.val) / ds = j.val
        rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt a.isLt, zero_add]
      simp_rw [hterm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.sqrt_div (hnonneg _) (ds : ℝ)]
      have hdpos : 0 < (ds : ℝ) := Nat.cast_pos.mpr hd
      have hsqrt : Real.sqrt (ds : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdpos)
      rw [← mul_div_assoc]
      apply (div_eq_iff hsqrt).2
      calc
        (ds : ℝ) * Real.sqrt (lam (Fin.castLE hqJ j)) =
            (Real.sqrt (ds : ℝ) * Real.sqrt (ds : ℝ)) *
              Real.sqrt (lam (Fin.castLE hqJ j)) := by
                rw [Real.mul_self_sqrt (le_of_lt hdpos)]
        _ = _ := by ring

    let c := (Real.sqrt (ds : ℝ))⁻¹
    have hc : 0 ≤ c := inv_nonneg.mpr (Real.sqrt_nonneg _)
    let fx : Fin ds → O := fun a => ⟨s, a⟩
    let fy := fx
    have hfx : Function.Injective fx := by
      intro a b h
      exact (@sigma_mk_injective Sector (fun t => Fin (d t)) s) h
    have hfy : Function.Injective fy := hfx
    have hprojectGeneric {OX OY : Type u}
        [Fintype OX] [DecidableEq OX] [Fintype OY] [DecidableEq OY]
        {d k : ℕ} (fx : Fin d → OX) (fy : Fin d → OY)
        (hfx : Function.Injective fx) (hfy : Function.Injective fy)
        (Q : Matrix (EX × OX) (EY × OY) ℂ) (c : ℝ) (hc : 0 ≤ c) :
        let Z : Matrix EX EY ℂ := fun ex ey =>
          (c : ℂ) * ∑ a : Fin d, Q (ex, fx a) (ey, fy a)
        kyFanSum k (Matrix.toEuclideanLin Z) ≤
          c * kyFanSum (d * k) (Matrix.toEuclideanLin Q) := by
      classical
      intro Z
      have hbounded (k : ℕ) (hkX : k ≤ Fintype.card EX) (hkY : k ≤ Fintype.card EY) :
          kyFanSum k (Matrix.toEuclideanLin Z) ≤
            c * kyFanSum (d * k) (Matrix.toEuclideanLin Q) := by
        obtain ⟨u, v, hu, hv, hattain⟩ :=
          hAttain (Matrix.toEuclideanLin Z)
            (by simpa using hkY) (by simpa using hkX)
        let liftX : Fin d × Fin k → EuclideanSpace ℂ (EX × OX) := fun ai =>
          WithLp.toLp 2 fun exox => if exox.2 = fx ai.1 then u ai.2 exox.1 else 0
        let liftY : Fin d × Fin k → EuclideanSpace ℂ (EY × OY) := fun ai =>
          WithLp.toLp 2 fun eyoy => if eyoy.2 = fy ai.1 then v ai.2 eyoy.1 else 0
        have huLift : Orthonormal ℂ liftX := by
          rw [orthonormal_iff_ite]
          rintro ⟨a, i⟩ ⟨b, j⟩
          by_cases hab : a = b
          · subst b
            simpa [liftX, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply]
              using orthonormal_iff_ite.mp hu i j
          · have hf : fx a ≠ fx b := fun h => hab (hfx h)
            have hp : (a, i) ≠ (b, j) := fun h => hab (congrArg Prod.fst h)
            simp [liftX, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
              Ne.symm hf, hp]
        have hvLift : Orthonormal ℂ liftY := by
          rw [orthonormal_iff_ite]
          rintro ⟨a, i⟩ ⟨b, j⟩
          by_cases hab : a = b
          · subst b
            simpa [liftY, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply]
              using orthonormal_iff_ite.mp hv i j
          · have hf : fy a ≠ fy b := fun h => hab (hfy h)
            have hp : (a, i) ≠ (b, j) := fun h => hab (congrArg Prod.fst h)
            simp [liftY, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
              Ne.symm hf, hp]
        let e : Fin (d * k) ≃ (Fin d × Fin k) := Fintype.equivOfCardEq (by simp)
        have hkQ : d * k ≤ finrank ℂ (EuclideanSpace ℂ (EY × OY)) := by
          have hd : d ≤ Fintype.card OY := by
            simpa using Fintype.card_le_of_injective fy hfy
          simpa [Nat.mul_comm] using Nat.mul_le_mul hd hkY
        have hupper := re_sum_inner_map_le_ky_fan_sum (A := Matrix.toEuclideanLin Q)
          hkQ (huLift.comp e e.injective) (hvLift.comp e e.injective)
        have hsum : (∑ i : Fin k, ⟪u i, Matrix.toEuclideanLin Z (v i)⟫_ℂ) =
            (c : ℂ) * ∑ ai : Fin d × Fin k,
              ⟪liftX ai, Matrix.toEuclideanLin Q (liftY ai)⟫_ℂ := by
          have hevalZ (i : Fin k) (ex : EX) :
              Matrix.toEuclideanLin Z (v i) ex =
                ∑ ey, (c : ℂ) * (∑ a : Fin d, Q (ex, fx a) (ey, fy a)) * v i ey := rfl
          have hevalQ (ai : Fin d × Fin k) (exox : EX × OX) :
              Matrix.toEuclideanLin Q (liftY ai) exox =
                ∑ eyoy : EY × OY, Q exox eyoy *
                  (if eyoy.2 = fy ai.1 then v ai.2 eyoy.1 else 0) := rfl
          simp only [PiLp.inner_apply, RCLike.inner_apply, hevalZ, hevalQ]
          simp only [liftX, Fintype.sum_prod_type, mul_zero,
            apply_ite, map_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_pos,
            Finset.mul_sum, Finset.sum_mul]
          simp only [mul_assoc]
          conv_lhs =>
            arg 2
            ext i
            arg 2
            ext ex
            rw [Finset.sum_comm]
          conv_lhs =>
            arg 2
            ext i
            rw [Finset.sum_comm]
          rw [Finset.sum_comm]
        rw [← e.sum_comp] at hsum
        rw [← hattain, hsum]
        change ((c : ℂ) * ∑ i : Fin (d * k),
          ⟪liftX (e i), Matrix.toEuclideanLin Q (liftY (e i))⟫_ℂ).re ≤ _
        rw [Complex.re_ofReal_mul]
        exact mul_le_mul_of_nonneg_left hupper hc

      let n := min k (min (Fintype.card EX) (Fintype.card EY))
      have hn : n ≤ k := Nat.min_le_left _ _
      have hnX : n ≤ Fintype.card EX := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
      have hnY : n ≤ Fintype.card EY := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
      have hrank : finrank ℂ (Matrix.toEuclideanLin Z).range ≤
          min (Fintype.card EX) (Fintype.card EY) := by
        exact le_min (by simpa using (Matrix.toEuclideanLin Z).range.finrank_le)
          (by simpa using (Matrix.toEuclideanLin Z).finrank_range_le)
      have hzero (i : ℕ) (hi : min (Fintype.card EX) (Fintype.card EY) ≤ i) :
          (Matrix.toEuclideanLin Z).singularValues i = 0 := by
        have hnot : i ∉ (Matrix.toEuclideanLin Z).singularValues.support := by
          rw [LinearMap.support_singularValues, Finset.mem_range]
          exact not_lt_of_ge (hrank.trans hi)
        simpa only [Finsupp.mem_support_iff, not_not] using hnot
      have heq : kyFanSum k (Matrix.toEuclideanLin Z) =
          kyFanSum n (Matrix.toEuclideanLin Z) := by
        unfold kyFanSum
        rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
        symm
        refine Finset.sum_subset (Finset.range_mono hn) fun i hik hin => ?_
        simp only [Finset.mem_range, not_lt] at hik hin
        exact hzero i (by dsimp [n] at hin; omega)
      have hmono : kyFanSum (d * n) (Matrix.toEuclideanLin Q) ≤
          kyFanSum (d * k) (Matrix.toEuclideanLin Q) := by
        unfold kyFanSum
        rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.mul_le_mul_left d hn))
          (fun i _ _ => (Matrix.toEuclideanLin Q).singularValues_nonneg i)
      rw [heq]
      exact (hbounded n hnX hnY).trans (mul_le_mul_of_nonneg_left hmono hc)
    have hproject : kyFanSum k (Matrix.toEuclideanLin Z) ≤
        c * kyFanSum (ds * k) (Matrix.toEuclideanLin Q) :=
      hprojectGeneric fx fy hfx hfy Q c hc

    have hsourcePrefix : kyFanSum (ds * k) (Matrix.toEuclideanLin Q) =
        Real.sqrt (ds : ℝ) * ∑ j : Fin (min k J),
          Real.sqrt (lam (Fin.castLE (Nat.min_le_right k J) j)) := by
      unfold kyFanSum
      rw [Nat.mul_comm ds k]
      exact hprefix k
    have hnonzero : Real.sqrt (ds : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr hd))
    refine hproject.trans_eq ?_
    rw [hsourcePrefix]
    dsimp only [c]
    rw [← mul_assoc, inv_mul_cancel₀ hnonzero, one_mul]
  have hTraceMajor (A B : (EuclideanSpace ℂ EY) →ₗ[ℂ] (EuclideanSpace ℂ EX)) :
      (Complex.re (LinearMap.trace ℂ (EuclideanSpace ℂ EY) (A.adjoint ∘ₗ B)) ≤
        ∑ i ∈ Finset.range (finrank ℂ A.range), A.singularValues i * B.singularValues i) ∧
      ∀ (α β : ℕ → ℝ) (n : ℕ), finrank ℂ A.range ≤ n →
        Antitone α → Antitone β → (∀ i, 0 ≤ α i) → (∀ i, 0 ≤ β i) →
        (∀ k ≤ n, (∑ i ∈ Finset.range k, A.singularValues i) ≤
          ∑ i ∈ Finset.range k, α i) →
        (∀ k ≤ n, (∑ i ∈ Finset.range k, B.singularValues i) ≤
          ∑ i ∈ Finset.range k, β i) →
        Complex.re (LinearMap.trace ℂ (EuclideanSpace ℂ EY) (A.adjoint ∘ₗ B)) ≤
          ∑ i ∈ Finset.range n, α i * β i := by
    classical
    let r := finrank ℂ A.range
    let d := finrank ℂ (EuclideanSpace ℂ EY)
    have hr : r ≤ d := LinearMap.finrank_range_le A
    let b := rightSingularBasis A
    let v : Fin r → (EuclideanSpace ℂ EY) := fun i => b (Fin.castLE hr i)
    let u : Fin r → (EuclideanSpace ℂ EX) := fun i => ((A.singularValues i : ℂ)⁻¹) • A (v i)
    have hpos (i : Fin r) : 0 < A.singularValues i :=
      A.singularValues_pos_iff_lt_finrank_range.mpr i.isLt
    have hnz (i : Fin r) : (A.singularValues i : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos i))
    have hv : Orthonormal ℂ v :=
      b.orthonormal.comp (Fin.castLE hr) (Fin.castLE_injective hr)
    have hu : Orthonormal ℂ u := by
      rw [orthonormal_iff_ite]
      intro i j
      have hg := inner_apply_rightSingularBasis A (Fin.castLE hr i) (Fin.castLE hr j)
      change inner ℂ (A (v i)) (A (v j)) =
        ((A.singularValues j ^ 2 : ℝ) : ℂ) * inner ℂ (v i) (v j) at hg
      simp only [u, inner_smul_left, inner_smul_right, hg]
      rw [orthonormal_iff_ite.mp hv i j]
      by_cases hij : i = j
      · subst j
        simp only [map_inv₀, Complex.conj_ofReal]
        push_cast
        field_simp [hnz i]
      · simp [hij]
    have htrace : LinearMap.trace ℂ (EuclideanSpace ℂ EY) (A.adjoint ∘ₗ B) =
        ∑ i : Fin d, inner ℂ (A (b i)) (B (b i)) := by
      rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, LinearMap.comp_apply,
        LinearMap.adjoint_inner_right]
      rfl
    have hzero (i : Fin d) (hi : r ≤ i.val) :
        inner ℂ (A (b i)) (B (b i)) = 0 := by
      have hs := A.singularValues_eq_zero_iff_le_finrank_range.mpr hi
      rw [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hs, inner_zero_left]
    have htrunc : (∑ i : Fin d, inner ℂ (A (b i)) (B (b i))) =
        ∑ i : Fin r, inner ℂ (A (v i)) (B (v i)) := by
      let s : Finset (Fin d) := Finset.univ.image (Fin.castLE hr)
      have hs : s ⊆ Finset.univ := Finset.subset_univ _
      have hsum := Finset.sum_subset hs (fun i _ hi => hzero i (by
        by_contra h
        have hi' : i.val < r := by omega
        apply hi
        apply Finset.mem_image.mpr
        exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, by ext; rfl⟩))
      rw [← hsum]
      simp only [s, Finset.sum_image (Fin.castLE_injective hr).injOn]
      rfl
    have hscale (i : Fin r) :
        A (v i) = (A.singularValues i : ℂ) • u i := by
      simp only [u, smul_smul, mul_inv_cancel₀ (hnz i), one_smul]
    have hRe : Complex.re (LinearMap.trace ℂ (EuclideanSpace ℂ EY) (A.adjoint ∘ₗ B)) =
        ∑ i : Fin r, A.singularValues i * Complex.re ⟪u i, B (v i)⟫_ℂ := by
      rw [htrace, htrunc, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hscale, inner_smul_left]
      simp
    have hprefix (k : ℕ) (hk : k ≤ r) :
        (∑ i : Fin k, Complex.re ⟪u (Fin.castLE hk i),
          B (v (Fin.castLE hk i))⟫_ℂ) ≤ kyFanSum k B := by
      have huk : Orthonormal ℂ (fun i : Fin k => u (Fin.castLE hk i)) :=
        hu.comp (Fin.castLE hk) (Fin.castLE_injective hk)
      have hvk : Orthonormal ℂ (fun i : Fin k => v (Fin.castLE hk i)) :=
        hv.comp (Fin.castLE hk) (Fin.castLE_injective hk)
      simpa using re_sum_inner_map_le_ky_fan_sum (A := B) (hk.trans hr) huk hvk
    let t : ℕ → ℝ := fun i => if hi : i < r then
      Complex.re ⟪u ⟨i, hi⟩, B (v ⟨i, hi⟩)⟫_ℂ else 0
    have ht (k : ℕ) (hk : k ≤ r) (i : Fin k) :
        t i = Complex.re ⟪u (Fin.castLE hk i), B (v (Fin.castLE hk i))⟫_ℂ := by
      simp only [t, dif_pos (lt_of_lt_of_le i.isLt hk)]
      rfl
    have htPrefix (k : ℕ) (hk : k ≤ r) :
        (∑ i ∈ Finset.range k, t i) ≤ ∑ i ∈ Finset.range k, B.singularValues i := by
      have h := hprefix k hk
      change (∑ i : Fin k, _) ≤ ∑ i : Fin k, B.singularValues i at h
      simp_rw [← ht k hk] at h
      simpa only [Fin.sum_univ_eq_sum_range] using h
    have htRe : Complex.re (LinearMap.trace ℂ (EuclideanSpace ℂ EY) (A.adjoint ∘ₗ B)) =
        ∑ i ∈ Finset.range r, A.singularValues i * t i := by
      rw [← Fin.sum_univ_eq_sum_range, hRe]
      apply Finset.sum_congr rfl
      intro i _
      rw [ht r le_rfl i]
      rfl
    have hWeighted (a b w : ℕ → ℝ) (n : ℕ)
        (hw : Antitone w) (hw0 : ∀ i, 0 ≤ w i)
        (hab : ∀ k ≤ n, (∑ i ∈ Finset.range k, a i) ≤ ∑ i ∈ Finset.range k, b i) :
        (∑ i ∈ Finset.range n, a i * w i) ≤ ∑ i ∈ Finset.range n, b i * w i := by
      have hA := Finset.sum_range_by_parts w a n
      have hB := Finset.sum_range_by_parts w b n
      simp only [smul_eq_mul] at hA hB
      simp_rw [mul_comm (a _) (w _), mul_comm (b _) (w _)]
      rw [hA, hB]
      apply sub_le_sub
      · exact mul_le_mul_of_nonneg_left (hab n le_rfl) (hw0 (n - 1))
      · apply Finset.sum_le_sum
        intro i hi
        have hin : i + 1 ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        exact mul_le_mul_of_nonpos_left (hab (i + 1) hin)
          (sub_nonpos.mpr (hw (Nat.le_succ i)))
    have hpair : Complex.re (LinearMap.trace ℂ (EuclideanSpace ℂ EY) (A.adjoint ∘ₗ B)) ≤
        ∑ i ∈ Finset.range r, A.singularValues i * B.singularValues i := by
      rw [htRe]
      simpa only [mul_comm] using hWeighted t B.singularValues A.singularValues r
        A.singularValues_antitone A.singularValues_nonneg htPrefix
    refine ⟨hpair, ?_⟩
    intro α β n hn hα hβ hα0 hβ0 hA hB
    calc
      Complex.re (LinearMap.trace ℂ (EuclideanSpace ℂ EY) (A.adjoint ∘ₗ B)) ≤
          ∑ i ∈ Finset.range r, A.singularValues i * B.singularValues i := hpair
      _ ≤ ∑ i ∈ Finset.range n, A.singularValues i * B.singularValues i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
          (fun i _ _ => mul_nonneg (A.singularValues_nonneg i) (B.singularValues_nonneg i))
      _ ≤ ∑ i ∈ Finset.range n, A.singularValues i * β i := by
        simpa only [mul_comm] using hWeighted B.singularValues β A.singularValues n
          A.singularValues_antitone A.singularValues_nonneg hB
      _ ≤ ∑ i ∈ Finset.range n, α i * β i := hWeighted A.singularValues α β n hβ hβ0 hA
  let alpha : Sector → ℕ → ℝ := fun s i =>
    if hi : i < J then Real.sqrt (M.spectrum s ⟨i, hi⟩) else 0
  have hAlpha0 (s : Sector) (i : ℕ) : 0 ≤ alpha s i := by
    dsimp [alpha]
    split_ifs <;> first | exact Real.sqrt_nonneg _ | exact le_rfl
  have hAnti (s : Sector) : Antitone (alpha s) := by
    intro i j hij
    by_cases hj : j < J
    · have hi : i < J := lt_of_le_of_lt hij hj
      simp only [alpha, dif_pos hi, dif_pos hj]
      exact Real.sqrt_le_sqrt (M.spectrumAntitone s hij)
    · simp only [alpha, dif_neg hj]
      exact hAlpha0 s i
  have hAlphaPrefix (s : Sector) (k : ℕ) :
      (∑ i ∈ Finset.range k, alpha s i) =
      ∑ j : Fin (min k J), Real.sqrt (M.spectrum s (Fin.castLE (Nat.min_le_right k J) j)) := by
    have hcut : (∑ i ∈ Finset.range k, alpha s i) =
        ∑ i ∈ Finset.range (min k J), alpha s i := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left k J))
      intro i hi hin
      have hiJ : J ≤ i := by
        simp only [Finset.mem_range, not_lt] at hi hin
        omega
      simp only [alpha, dif_neg (not_lt_of_ge hiJ)]
    rw [hcut, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [alpha, dif_pos (lt_of_lt_of_le j.isLt (Nat.min_le_right k J))]
    rfl
  have hDom (s : Sector) (k : ℕ) :
      (∑ i ∈ Finset.range k, (Matrix.toEuclideanLin (Z s)).singularValues i) ≤
        ∑ i ∈ Finset.range k, alpha s i := by
    have h := hSourcePrefix (EX := EX) (EY := EY) M.d s (M.positiveRank s)
      (M.spectrum s) (M.spectrumNonneg s) (M.spectrumAntitone s) VX VY hVX hVY k
    change kyFanSum k (Matrix.toEuclideanLin (Z s)) ≤ _ at h
    rw [hAlphaPrefix]
    simpa only [kyFanSum, Fin.sum_univ_eq_sum_range] using h
  have hFrobenius (Z W : Matrix EX EY ℂ) :
      LinearMap.trace ℂ (EuclideanSpace ℂ EY)
          ((Matrix.toEuclideanLin Z).adjoint ∘ₗ Matrix.toEuclideanLin W) =
        ∑ ex, ∑ ey, star (Z ex ey) * W ex ey := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toLpLin_mul_same, Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
  intro s t
  let n := max (finrank ℂ (Matrix.toEuclideanLin (Z s)).range) J
  have hBound := (hTraceMajor (Matrix.toEuclideanLin (Z s)) (Matrix.toEuclideanLin (Z t))).2
    (alpha s) (alpha t) n (Nat.le_max_left _ _) (hAnti s) (hAnti t)
    (hAlpha0 s) (hAlpha0 t) (fun k _ => hDom s k) (fun k _ => hDom t k)
  have hProduct : (∑ i ∈ Finset.range n, alpha s i * alpha t i) = kernel M s t := by
    have hcut : (∑ i ∈ Finset.range J, alpha s i * alpha t i) =
        ∑ i ∈ Finset.range n, alpha s i * alpha t i := by
      apply Finset.sum_subset (Finset.range_mono (Nat.le_max_right
        (finrank ℂ (Matrix.toEuclideanLin (Z s)).range) J))
      intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      simp only [alpha, dif_neg (not_lt_of_ge hi), zero_mul]
    rw [← hcut, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [alpha, dif_pos i.isLt]
  rw [hFrobenius, hProduct] at hBound
  exact hBound

end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
