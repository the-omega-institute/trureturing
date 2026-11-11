/- GID: D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed orthogonal coordinate baths select five modes on open real and complex Hamiltonian sets in every dimension at least five. -/

import D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation

/- The open sets concern the particular two-coordinate-bath cubic five-mode
construction. Exponent persistence is local at its strict cubic certificates. -/

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation
open D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open Matrix Set
open scoped BigOperators NNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The real eigenvalues of a Hermitian matrix in increasing order. -/
def increasingSpectrum {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian) (i : Fin n) : ℝ :=
  hH.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i.rev)

private theorem increasingSpectrum_of_charpoly {H : Matrix (Fin n) (Fin n) 𝕜}
    (hH : H.IsHermitian) (e : Fin n → ℝ) (he : Monotone e)
    (hc : H.charpoly = ∏ i, (Polynomial.X - Polynomial.C (RCLike.ofReal (e i) : 𝕜))) :
    increasingSpectrum hH = e := by
  let d : Fin n → ℝ := e ∘ Fin.rev
  have hd : Antitone d := fun i j hij => he (Fin.rev_le_rev.mpr hij)
  have hp : H.charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (RCLike.ofReal (d i) : 𝕜)) := by
    rw [hc]
    exact (Equiv.prod_comp Fin.revPerm (fun i => Polynomial.X -
      Polynomial.C (RCLike.ofReal (e i) : 𝕜))).symm
  have hr : H.charpoly.roots = Finset.univ.val.map (RCLike.ofReal ∘ d) := by
    rw [hp, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Function.comp_apply]
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort := hH.sort_roots_charpoly_eq_eigenvalues₀
  rw [hr] at hsort
  simp only [Function.comp_def, RCLike.ofReal_re, Fin.univ_val_map,
    Multiset.map_coe, List.map_ofFn, Multiset.coe_sort] at hsort
  change (List.ofFn d).mergeSort (fun x y => decide (x ≥ y)) = _ at hsort
  have hdlist : List.Pairwise (fun x y : ℝ => decide (x ≥ y) = true) (List.ofFn d) := by
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hd.sortedGE_ofFn
  rw [List.mergeSort_of_pairwise hdlist] at hsort
  have hcast : List.ofFn d = List.ofFn (fun i => d (Fin.cast (Fintype.card_fin n) i)) := by
    simp
  rw [hcast, List.ofFn_inj] at hsort
  funext i
  rw [increasingSpectrum, ← hsort]
  simp [d]

private theorem increasingSpectrum_monotone {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian) :
    Monotone (increasingSpectrum hH) := by
  intro i j hij
  exact hH.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)

/-- The spectral theorem with its columns reindexed by increasing energy. -/
private theorem exists_increasing_diagonalization {H : Matrix (Fin n) (Fin n) 𝕜}
    (hH : H.IsHermitian) :
    ∃ U : Matrix.unitaryGroup (Fin n) 𝕜, H = spectralMatrix U (increasingSpectrum hH) := by
  let σ : Fin n ≃ Fin n :=
    (Fin.revPerm.trans (finCongr (Fintype.card_fin n).symm)).trans
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))
  let q := hH.eigenvectorBasis.reindex σ.symm
  let U : Matrix.unitaryGroup (Fin n) 𝕜 :=
    ⟨(EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix q.toBasis,
      (EuclideanSpace.basisFun (Fin n) 𝕜).toMatrix_orthonormalBasis_mem_unitary q⟩
  let V := (U : Matrix (Fin n) (Fin n) 𝕜)
  have hcol (r i) : V r i = hH.eigenvectorBasis (σ i) r := by
    change q i r = _
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  have hval (i) : hH.eigenvalues (σ i) = increasingSpectrum hH i := by
    simp [σ, increasingSpectrum, IsHermitian.eigenvalues]
  have hmul : H * V = V * diagonal (fun i => RCLike.ofReal (increasingSpectrum hH i)) := by
    ext r i
    rw [mul_diagonal, hcol]
    have hv := congrFun (hH.mulVec_eigenvectorBasis (σ i)) r
    rw [hval] at hv
    change (∑ j, H r j * hH.eigenvectorBasis (σ i) j) =
      increasingSpectrum hH i • hH.eigenvectorBasis (σ i) r at hv
    rw [mul_apply]
    simp only [hcol, ← mul_comm (RCLike.ofReal (increasingSpectrum hH i) : 𝕜),
      ← smul_eq_mul, ← RCLike.real_smul_eq_coe_smul]
    exact hv
  refine ⟨U, ?_⟩
  unfold spectralMatrix
  change H = V * _ * Vᴴ
  rw [← hmul, mul_assoc, show V * Vᴴ = 1 from Unitary.coe_mul_star_self U, mul_one]

private def lagrangeFactor (H : Matrix (Fin n) (Fin n) 𝕜) (e : Fin n → ℝ)
    (i j : Fin n) : Matrix (Fin n) (Fin n) 𝕜 :=
  if j = i then 1 else
    (RCLike.ofReal (e i - e j)⁻¹ : 𝕜) • (H - (RCLike.ofReal (e j) : 𝕜) • 1)

/-- The spectral projection onto level `i` when the spectrum is simple. The product
is evaluated in the fixed order of the labels. -/
def lagrangeProjector (H : Matrix (Fin n) (Fin n) 𝕜) (e : Fin n → ℝ) (i : Fin n) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  (List.ofFn (lagrangeFactor H e i)).prod

theorem lagrangeProjector_spectralMatrix (U : Matrix.unitaryGroup (Fin n) 𝕜)
    (e : Fin n → ℝ) (he : Function.Injective e) (i : Fin n) :
    lagrangeProjector (spectralMatrix U e) e i =
      (U : Matrix (Fin n) (Fin n) 𝕜) * coordinateProjector i *
        (U : Matrix (Fin n) (Fin n) 𝕜)ᴴ := by
  let J := (Unitary.conjStarAlgAut 𝕜 _ U).toAlgEquiv
  let D := diagonal (fun i => (RCLike.ofReal (e i) : 𝕜))
  let K := Matrix.diagonalRingHom (Fin n) 𝕜
  let d (j k : Fin n) : 𝕜 := if j = i then 1 else
    (RCLike.ofReal (e i - e j)⁻¹ : 𝕜) * (RCLike.ofReal (e k) - RCLike.ofReal (e j))
  have hf (j : Fin n) : lagrangeFactor (spectralMatrix U e) e i j = J (K (d j)) := by
    by_cases h : j = i
    · have hconst : d j = 1 := by ext k; simp [d, h]
      rw [lagrangeFactor, ite_eq_left h, hconst, map_one, map_one]
    · have hdiag : K (d j) = (RCLike.ofReal (e i - e j)⁻¹ : 𝕜) •
          (D - (RCLike.ofReal (e j) : 𝕜) • 1) := by
        ext k l
        change diagonal (d j) k l = (RCLike.ofReal (e i - e j)⁻¹ : 𝕜) *
          (D k l - (RCLike.ofReal (e j) : 𝕜) * (1 : Matrix (Fin n) (Fin n) 𝕜) k l)
        by_cases hkl : k = l <;>
          simp [D, d, h, hkl, Matrix.one_apply]
      rw [lagrangeFactor, ite_eq_right h, hdiag, map_smul, map_sub, map_smul, map_one]
      rfl
  have hprod : (∏ j, d j) = Pi.single i (1 : 𝕜) := by
    ext k
    rw [Finset.prod_apply]
    by_cases hk : k = i
    · subst k
      rw [Pi.single_eq_same]
      apply Finset.prod_eq_one
      intro j _
      by_cases h : j = i
      · simp [d, h]
      · have hne : e i - e j ≠ 0 := sub_ne_zero.mpr (fun hj => h (he hj).symm)
        simp only [d, ite_eq_right h, ← RCLike.ofReal_sub, ← RCLike.ofReal_mul,
          inv_mul_cancel₀ hne, RCLike.ofReal_one]
    · rw [Pi.single_eq_of_ne hk]
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp [d, hk]
  unfold lagrangeProjector
  rw [show lagrangeFactor (spectralMatrix U e) e i = fun j => J (K (d j)) from funext hf]
  change (List.ofFn (J ∘ K ∘ d)).prod = _
  rw [← List.map_ofFn, ← map_list_prod, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn, hprod]
  rfl

/-- The diagonal of the rank-one spectral projection gives the same weight as
the expectation of the coordinate bath in the unit eigenvector. -/
private theorem lagrangeProjector_weight (U : Matrix.unitaryGroup (Fin n) 𝕜)
    (e : Fin n → ℝ) (he : Function.Injective e) (i r : Fin n) :
    RCLike.re (lagrangeProjector (spectralMatrix U e) e i r r) =
      coordinateWeight r (fun j => U j i) := by
  rw [lagrangeProjector_spectralMatrix U e he, coordinateWeight_eq, mul_apply]
  simp only [coordinateProjector, mul_diagonal, Pi.single_apply, mul_ite, mul_zero, mul_one,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Hermitian matrices with their ordinary matrix topology. -/
abbrev HermitianSpace (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :=
  {H : Matrix (Fin n) (Fin n) 𝕜 // H.IsHermitian}

open scoped Matrix.Norms.Elementwise in
theorem continuous_increasingSpectrum_complex (i : Fin n) :
    Continuous (fun H : HermitianSpace ℂ n => increasingSpectrum H.property i) := by
  apply LipschitzWith.continuous (K := (n : ℝ≥0))
  rw [lipschitzWith_iff_dist_le_mul]
  intro H K
  rw [Real.dist_eq, Subtype.dist_eq, dist_eq_norm]
  change |increasingSpectrum H.property i - increasingSpectrum K.property i| ≤
    (n : ℝ) * ‖H.val - K.val‖
  apply D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le
    K.property H.property _ (Fin.cast (Fintype.card_fin n).symm i.rev)
  intro r s
  exact Matrix.norm_entry_le_entrywise_sup_norm (H.val - K.val)

private def complexify (H : HermitianSpace ℝ n) : HermitianSpace ℂ n :=
  ⟨H.val.map Complex.ofRealHom, by
    apply IsHermitian.ext
    intro i j
    simp only [Matrix.map_apply, Complex.ofRealHom_eq_coe, RCLike.star_def, Complex.conj_ofReal]
    exact_mod_cast (IsSymm.ext_iff.mp H.property.isSymm i j)⟩

theorem continuous_increasingSpectrum_real (i : Fin n) :
    Continuous (fun H : HermitianSpace ℝ n => increasingSpectrum H.property i) := by
  have hc : Continuous (complexify (n := n)) := by
    apply Continuous.subtype_mk
    exact continuous_matrix fun r s =>
      Complex.continuous_ofReal.comp (continuous_subtype_val.matrix_elem r s)
  have he (H : HermitianSpace ℝ n) :
      increasingSpectrum (complexify H).property = increasingSpectrum H.property := by
    let e := increasingSpectrum H.property
    obtain ⟨U, hU⟩ := exists_increasing_diagonalization H.property
    have hchar : H.val.charpoly = ∏ j, (Polynomial.X - Polynomial.C (e j)) := by
      rw [hU]
      exact spectralMatrix_charpoly U e
    apply increasingSpectrum_of_charpoly _ e (increasingSpectrum_monotone H.property)
    change (H.val.map Complex.ofRealHom).charpoly = _
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp
  have h := (continuous_increasingSpectrum_complex i).comp hc
  change Continuous (fun H => increasingSpectrum (complexify H).property i) at h
  simpa only [he] using h

private theorem continuous_increasingSpectrum_of_equiv
    {𝕜' : Type*} [RCLike 𝕜'] (f : 𝕜 ≃+* 𝕜') (hf : Continuous f)
    (hstar : ∀ z, f (star z) = star (f z))
    (hreal : ∀ r : ℝ, f (RCLike.ofReal r) = RCLike.ofReal r)
    (hc : ∀ i, Continuous (fun H : HermitianSpace 𝕜' n => increasingSpectrum H.property i))
    (i : Fin n) :
    Continuous (fun H : HermitianSpace 𝕜 n => increasingSpectrum H.property i) := by
  let φ : HermitianSpace 𝕜 n → HermitianSpace 𝕜' n := fun H =>
    ⟨H.val.map f.toRingHom, by
      apply IsHermitian.ext
      intro r s
      change star (f (H.val s r)) = f (H.val r s)
      rw [← hstar, IsHermitian.ext_iff.mp H.property r s]⟩
  have hφ : Continuous φ := by
    apply Continuous.subtype_mk
    exact continuous_matrix fun r s => hf.comp (continuous_subtype_val.matrix_elem r s)
  have he (H : HermitianSpace 𝕜 n) :
      increasingSpectrum (φ H).property = increasingSpectrum H.property := by
    let e := increasingSpectrum H.property
    obtain ⟨U, hU⟩ := exists_increasing_diagonalization H.property
    have hchar : H.val.charpoly = ∏ j, (Polynomial.X - Polynomial.C (RCLike.ofReal (e j) : 𝕜)) := by
      rw [hU]
      exact spectralMatrix_charpoly U e
    apply increasingSpectrum_of_charpoly _ e (increasingSpectrum_monotone H.property)
    change (H.val.map f.toRingHom).charpoly = _
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Finset.prod_congr rfl (fun j _ =>
      congrArg (fun z : 𝕜' => Polynomial.X - Polynomial.C z) (hreal (e j)))
  have h := (hc i).comp hφ
  change Continuous (fun H => increasingSpectrum (φ H).property i) at h
  simpa only [he] using h

private theorem continuous_lagrangeProjector {X : Type*} [TopologicalSpace X]
    {H : X → Matrix (Fin n) (Fin n) 𝕜} {e : X → Fin n → ℝ}
    (hH : Continuous H) (he : ∀ i, Continuous (fun x => e x i))
    (hs : ∀ x, Function.Injective (e x)) (i : Fin n) :
    Continuous (fun x => lagrangeProjector (H x) (e x) i) := by
  unfold lagrangeProjector
  simp only [List.ofFn_eq_map]
  apply continuous_list_prod
  intro j _
  by_cases hj : j = i
  · simp only [lagrangeFactor, ite_eq_left hj]
    exact continuous_const
  · simp only [lagrangeFactor, ite_eq_right hj]
    have hinv : Continuous (fun x : X => (e x i - e x j)⁻¹) :=
      ((he i).sub (he j)).inv₀ (fun x => sub_ne_zero.mpr (fun h => hj ((hs x) h).symm))
    have hc : Continuous (fun x : X => (RCLike.ofReal (e x j) : 𝕜) •
        (1 : Matrix (Fin n) (Fin n) 𝕜)) := by
      have ht : Continuous (fun x : X => (RCLike.ofReal (e x j) : 𝕜)) :=
        RCLike.continuous_ofReal.comp (he j)
      exact ht.smul (continuous_const (y := (1 : Matrix (Fin n) (Fin n) 𝕜)))
    have ht : Continuous (fun x : X => (RCLike.ofReal ((e x i - e x j)⁻¹) : 𝕜)) :=
      RCLike.continuous_ofReal.comp hinv
    exact ht.smul (hH.sub hc)

end

end D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths

namespace D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths

open D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation
open D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open Matrix Set
open scoped BigOperators

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The physical bath weight, computed from the spectral projector of the actual matrix. -/
def matrixWeight (H : HermitianSpace 𝕜 n) (r i : Fin n) : ℝ :=
  RCLike.re (lagrangeProjector H.val (increasingSpectrum H.property) i r r)

def matrixRates (hn : 5 ≤ n) (d : ℝ) (H : HermitianSpace 𝕜 n) :
    Matrix (Fin n) (Fin n) ℝ :=
  asym d (increasingSpectrum H.property) (matrixWeight H ⟨0, by omega⟩)
    (matrixWeight H ⟨1, by omega⟩)

private theorem matrixWeight_eq {H : HermitianSpace 𝕜 n}
    (U : Matrix.unitaryGroup (Fin n) 𝕜) (e : Fin n → ℝ) (he : StrictMono e)
    (hH : H.val = spectralMatrix U e) (r i : Fin n) :
    matrixWeight H r i = coordinateWeight r (fun j => U j i) := by
  have hspec : increasingSpectrum H.property = e :=
    increasingSpectrum_of_charpoly H.property e he.monotone
      (hH ▸ spectralMatrix_charpoly U e)
  rw [matrixWeight, hspec, hH]
  exact lagrangeProjector_weight U e he.injective i r

theorem matrixRates_eq (hn : 5 ≤ n) (d : ℝ) {H : HermitianSpace 𝕜 n}
    (U : Matrix.unitaryGroup (Fin n) 𝕜) (e : Fin n → ℝ) (he : StrictMono e)
    (hH : H.val = spectralMatrix U e) :
    matrixRates hn d H = fixedBathRates hn d e U := by
  have hspec : increasingSpectrum H.property = e :=
    increasingSpectrum_of_charpoly H.property e he.monotone
      (hH ▸ spectralMatrix_charpoly U e)
  unfold matrixRates
  rw [hspec, funext (matrixWeight_eq U e he hH ⟨0, by omega⟩),
    funext (matrixWeight_eq U e he hH ⟨1, by omega⟩)]
  rfl

private theorem sum_coordinateWeight (U : Matrix.unitaryGroup (Fin n) 𝕜) (r : Fin n) :
    ∑ i, coordinateWeight r (fun j => U j i) = 1 := by
  have hu := Unitary.coe_mul_star_self U
  have h := congrArg RCLike.re (congrFun (congrFun hu r) r)
  change RCLike.re (((U : Matrix (Fin n) (Fin n) 𝕜) *
    (U : Matrix (Fin n) (Fin n) 𝕜)ᴴ) r r) = RCLike.re ((1 : Matrix (Fin n) (Fin n) 𝕜) r r) at h
  simpa only [mul_apply, conjTranspose_apply, RCLike.star_def, RCLike.mul_conj,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_sum, RCLike.ofReal_re, one_apply_eq, RCLike.one_re,
    coordinateWeight_eq] using h

private theorem sum_matrixWeight {H : HermitianSpace 𝕜 n}
    (hs : StrictMono (increasingSpectrum H.property)) (r : Fin n) :
    ∑ i, matrixWeight H r i = 1 := by
  obtain ⟨U, hU⟩ := exists_increasing_diagonalization H.property
  simp_rw [matrixWeight_eq U _ hs hU]
  exact sum_coordinateWeight U r

private def simpleDomain (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) : Set (HermitianSpace 𝕜 n) :=
  {H | StrictMono (increasingSpectrum H.property)}

private theorem isOpen_simpleDomain
    (hc : ∀ i, Continuous (fun H : HermitianSpace 𝕜 n => increasingSpectrum H.property i)) :
    IsOpen (simpleDomain 𝕜 n) := by
  have heq : simpleDomain 𝕜 n =
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _h : i < j,
        {H : HermitianSpace 𝕜 n | increasingSpectrum H.property i <
          increasingSpectrum H.property j} := by
    ext H
    simp only [simpleDomain, mem_ofPred_eq, mem_iInter, StrictMono]
  rw [heq]
  refine isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
    isOpen_iInter_of_finite (fun _ => isOpen_lt (hc i) (hc j))))

private theorem continuous_cubicRates_on_simple (hn : 5 ≤ n)
    (hc : ∀ i, Continuous (fun H : HermitianSpace 𝕜 n => increasingSpectrum H.property i)) :
    Continuous (fun H : simpleDomain 𝕜 n => matrixRates hn 3 H.val) := by
  have he (i : Fin n) : Continuous (fun H : simpleDomain 𝕜 n =>
      increasingSpectrum H.val.property i) := (hc i).comp continuous_subtype_val
  have hw (r i : Fin n) : Continuous (fun H : simpleDomain 𝕜 n => matrixWeight H.val r i) := by
    apply RCLike.continuous_re.comp
    exact (continuous_lagrangeProjector (continuous_subtype_val.comp continuous_subtype_val)
      he (fun H => H.property.injective) i).matrix_elem r r
  apply continuous_matrix
  intro i j
  have hentry (H : simpleDomain 𝕜 n) : matrixRates hn 3 H.val i j =
      (increasingSpectrum H.val.property j - increasingSpectrum H.val.property i)^3 *
        (matrixWeight H.val ⟨0, by omega⟩ i * matrixWeight H.val ⟨0, by omega⟩ j -
          matrixWeight H.val ⟨1, by omega⟩ i * matrixWeight H.val ⟨1, by omega⟩ j) := by
    simp only [matrixRates, asym, spectral_three,
      D5.S3.Geometry.FiniteCoordinateTruncation.normalize, sum_matrixWeight H.property, div_one]
  simp_rw [hentry]
  exact (((he j).sub (he i)).pow 3).mul (((hw _ i).mul (hw _ j)).sub ((hw _ i).mul (hw _ j)))

private theorem strictFiveCertificate_open {X : Type*} [TopologicalSpace X]
    {A : X → Matrix (Fin n) (Fin n) ℝ} (hc : Continuous A) (f : Fin 5 ↪ Fin n) :
    IsOpen {x | StrictFiveCertificate (A x) f} := by
  let p (x : X) := pfaffianVector ((A x).submatrix f f)
  have hp (i : Fin 5) : Continuous (fun x => p x i) := by
    have he (j k : Fin 5) := hc.matrix_elem (f j) (f k)
    fin_cases i <;> dsimp [p, pfaffianVector, Matrix.submatrix] <;> fun_prop
  have hl (i : Fin n) : Continuous (fun x => liftFive f (p x) i) := by
    by_cases hi : ∃ j, f j = i
    · simp only [liftFive, dite_eq_left hi]
      exact hp _
    · simp only [liftFive, dite_eq_right hi]
      exact continuous_const
  have hd (i : Fin n) : Continuous (fun x => (A x *ᵥ liftFive f (p x)) i) := by
    change Continuous (fun x => ∑ j : Fin n, A x i j * liftFive f (p x) j)
    exact continuous_finsetSum Finset.univ (fun j _ => (hc.matrix_elem i j).mul (hl j))
  have hset : {x | StrictFiveCertificate (A x) f} =
      (⋂ i : Fin 5, {x | 0 < p x i}) ∩
        ⋂ i : Fin n, ⋂ _h : i ∉ Finset.univ.map f, {x | (A x *ᵥ liftFive f (p x)) i < 0} := by
    ext x
    simp only [StrictFiveCertificate, mem_ofPred_eq, mem_inter_iff, mem_iInter, p]
  rw [hset]
  exact (isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hp i))).inter
    (isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite
      (fun _ => isOpen_lt (hd i) continuous_const)))

/-- Open persistence in the actual Hermitian matrix space at the cubic exponent. On the
whole open set the two fixed coordinate baths select the first five ordered levels,
and the normalized occupation is unique and its selected block has rank four. -/
theorem exists_open_fixedBathHamiltonians (hn : 5 ≤ n) :
    ∃ O : Set (HermitianSpace 𝕜 n), IsOpen O ∧ O.Nonempty ∧
      ∀ H ∈ O, StrictMono (increasingSpectrum H.property) ∧
        ∃ w : Fin n → ℝ, (∑ i, w i) = 1 ∧
          IsSelected (matrixRates hn 3 H) (firstFive hn) w ∧
          ((matrixRates hn 3 H).submatrix (fiveEmbedding hn) (fiveEmbedding hn)).rank = 4 ∧
          ∀ s v, IsSelected (matrixRates hn 3 H) s v → (∑ i, v i) = 1 →
            s = firstFive hn ∧ v = w := by
  have hc : ∀ i, Continuous (fun H : HermitianSpace 𝕜 n => increasingSpectrum H.property i) := by
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
    · exact continuous_increasingSpectrum_of_equiv (RCLike.realRingEquiv h)
        (RCLike.realLinearIsometryEquiv h).continuous
        (by intro z; simp [RCLike.realRingEquiv, RCLike.star_def])
        (by intro r; simp [RCLike.realRingEquiv]) continuous_increasingSpectrum_real
    · exact continuous_increasingSpectrum_of_equiv (RCLike.complexRingEquiv h)
        (RCLike.complexLinearIsometryEquiv h).continuous
        (by intro z; simp [RCLike.complexRingEquiv, RCLike.star_def])
        (by intro r; simp [RCLike.complexRingEquiv]) continuous_increasingSpectrum_complex
  let V : Set (simpleDomain 𝕜 n) :=
    {H | StrictFiveCertificate (matrixRates hn 3 H.val) (fiveEmbedding hn)}
  have hV : IsOpen V := strictFiveCertificate_open
    (continuous_cubicRates_on_simple hn hc) (fiveEmbedding hn)
  have ho := (isOpen_simpleDomain hc).isOpenMap_subtype_val V hV
  refine ⟨Subtype.val '' V, ho, ?_, ?_⟩
  · obtain ⟨H, hH, _, U, e, w, hdiag, _, he, _, hchar, _, _, hsel, hp, _, _⟩ :=
      exists_fixedBathHamiltonian 𝕜 hn
    let H₀ : HermitianSpace 𝕜 n := ⟨H, hH⟩
    have hs : H₀ ∈ simpleDomain 𝕜 n := by
      change StrictMono (increasingSpectrum hH)
      rw [increasingSpectrum_of_charpoly hH e he.monotone hchar]
      exact he
    refine ⟨H₀, ⟨H₀, hs⟩, ?_, rfl⟩
    change StrictFiveCertificate (matrixRates hn 3 H₀) (fiveEmbedding hn)
    rw [matrixRates_eq hn 3 U e he hdiag]
    exact strictFiveCertificate_of_selected (fixedBathRates_transpose hn e U) _ hsel hp
  · rintro _ ⟨H, hV', rfl⟩
    refine ⟨H.property, ?_⟩
    exact StrictFiveCertificate.selected (asym_cubic_transpose _ _ _) hV'

open D5.S3.Analytic.SeriesInequalities.StampachWaclawekExpansionRefutation (spow)

private theorem asym_transpose (d : ℝ) (e F G : Fin n → ℝ) :
    (asym d e F G)ᵀ = -asym d e F G := by
  have hodd (x : ℝ) : spow d (-x) = -spow d x := by
    by_cases h : x = 0
    · simp [h, spow]
    · simp [spow, h, neg_ne_zero.mpr h]
  ext i j
  simp only [transpose_apply, Matrix.neg_apply, asym]
  rw [show e i - e j = -(e j - e i) by ring, hodd]
  ring

private theorem continuous_matrixRates_exponent (hn : 5 ≤ n) (H : HermitianSpace 𝕜 n) :
    Continuous (fun d : ℝ => matrixRates hn d H) := by
  apply continuous_matrix
  intro i j
  unfold matrixRates asym
  let x := increasingSpectrum H.property j - increasingSpectrum H.property i
  suffices h : Continuous (fun d : ℝ => spow d x) by exact h.mul continuous_const
  by_cases hz : x = 0
  · simpa only [hz, spow, ite_true] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · simp only [spow, ite_eq_right hz]
    have h := Real.continuous_const_rpow (abs_ne_zero.mpr hz)
    have hg : Continuous (fun d : ℝ => d - 1) := continuous_id.sub continuous_const
    exact continuous_const.mul (h.comp hg)

/-- At a matrix with a strict cubic certificate, the same two fixed baths retain
unique normalized five-mode selection for an open interval of exponents around three.
This is qualitative and the interval may depend on the matrix. -/
theorem fixedBath_local_exponent (hn : 5 ≤ n) (H : HermitianSpace 𝕜 n)
    (h₀ : StrictFiveCertificate (matrixRates hn 3 H) (fiveEmbedding hn)) :
    ∃ I : Set ℝ, IsOpen I ∧ (3 : ℝ) ∈ I ∧ ∀ d ∈ I,
      ∃ w : Fin n → ℝ, (∑ i, w i) = 1 ∧
        IsSelected (matrixRates hn d H) (firstFive hn) w ∧
        ((matrixRates hn d H).submatrix (fiveEmbedding hn) (fiveEmbedding hn)).rank = 4 ∧
        ∀ s v, IsSelected (matrixRates hn d H) s v → (∑ i, v i) = 1 →
          s = firstFive hn ∧ v = w := by
  let I : Set ℝ := {d | StrictFiveCertificate (matrixRates hn d H) (fiveEmbedding hn)}
  refine ⟨I, strictFiveCertificate_open (continuous_matrixRates_exponent hn H) _, h₀, ?_⟩
  intro d hd
  exact StrictFiveCertificate.selected (asym_transpose d _ _ _) hd

end

end D5.S3.StatisticalMechanics.BoseSelectionFixedOrthogonalBaths
