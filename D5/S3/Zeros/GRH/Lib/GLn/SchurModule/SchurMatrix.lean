/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurMatrix
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.SchurMatrix. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/SchurMatrix.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.MinorBasis
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Universal basis, Schur matrices with functoriality and base change, Weyl character
formula. -/
seal Finset.univ Finset.sum Finset.prod


open MvPolynomial Finset Matrix PolyRep Submodule Equiv Classical Fintype Function Sigma
variable {Φ R S : Type} {F : Type _} [CommRing R] [CommRing S] [Fintype Φ] {n : Φ → Type}
  {n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] {κ : Φ → ℕ → ℕ}
  (h : FitsRanks n n' κ) (A : AddSubgroup R) (t : Φ → R) {ι : Type} {M} [Fintype ι]
  (z : ∀ τ, Matrix (n' τ) (n τ) R) (e : Φ → ℕ) (i : WeylIndexFam n' κ) {f} [FunLike F R S]
  [RingHomClass F R S] (φ : F) (g : ∀ τ, Matrix (n τ) (n τ) R) (x : ∀ τ, n τ → R)
attribute [local simp] AlgHom.map_det Matrix.map Matrix.mul_apply minor tableauPoly prod_smul
  prod_univ_sum RingHom.map_det detPow sum_smul sum_mul Fintype.prod_sigma minorProduct
  diagramWeight_apply smul_sum permArray bind₁_bind₁
attribute [local simp ←] rowSubst_rowSubst det_mul det_mul_column pow_mul
  diagramWeight_eq_columnWeight zsmul_eq_mul' C_mul'
  QuotientAddGroup.eq_zero_iff diagonal.eq_1 prod_pow_eq_pow_sum Fin.ext_iff mul_smul

omit [∀ τ, Fintype (n' τ)] in
lemma prod_tableauPoly_mem_nabla {M : Φ → ℕ} {T : ∀ τ, Tableau (n' τ) (M τ) (κ τ)} : ∏ τ,
  tableauPoly R (.mk τ) (T τ) ∈ nabla R fst (diagramWeight M κ) := diagramWeight_eq_columnWeight M
  κ ▸ Eq.subst (by simp) (minorProduct_mem_nabla (⟨⟨_, T _ _ ·.2.2 ·⟩, rfl⟩))

lemma isStdTableauSet_epsilon {k} : IsStdTableauSet (epsilon (@IsStdTableauSet ι M k)) :=
  epsilon_spec (by
  choose _ _ I h W using
    @exists_minorProduct_basis Unit (Σ _, Σ h : Fin M, Fin (k h)) ι _ _ 0 fst (·.2.1)
  use univ.map ⟨_, .of_comp (f := tableauPoly ℤ id) (by simpa using! (h ℤ).1.injective)⟩,
    fun R ↦ ⟨coe_map .. ▸ .image_of_comp _ _ (by simpa using! (h _).1), fun T ↦ by
    simpa [← Set.range_comp] using!
      (h R).2 (minorProduct_mem_nabla (⟨T _ ·.2.2 ·, rfl⟩))⟩, by simpa using W ())

/-- Over any commutative ring R, the minor products b_i indexed by families of chosen standard
fillings are linearly independent.

Known result: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character. -/
lemma linearIndependent_nablaBasis : LinearIndependent R (nablaBasis R n κ) := by
  induction' hk : card Φ with _ ih generalizing Φ R
  exacts [have := card_eq_zero_iff.1 hk; .of_subsingleton' default (by simp [nablaBasis,
      univ_eq_empty]), (card_eq_succ.1 hk).elim fun τ _ ↦ .of_comp (aeval fun (⟨σ, a⟩, j) ↦
    dite (σ = τ) (C <| X ⟨· ▸ a, j⟩) (X ⟨⟨⟨_, ·⟩, a⟩, j⟩)).toLinearMap ((linearIndependent_equiv'
    (piSplitAt ..) (by simp [funext_iff, nablaBasis, prod_eq_mul_prod_subtype_ne _ τ, @Subtype.prop
    _ (· ≠ τ)])).2 (linearIndependent_smul (isStdTableauSet_epsilon.1 R).1 (ih (by simp [*]))))]

lemma isRegular_detPow {e} : IsRegular (detPow R n e) := isRegular_iff_mem_nonZeroDivisors.2
  (mem_nonZeroDivisors_of_injective (f := (coeToMvPowerSeries.algHom _).comp (bind₁
  (permArray (rowPos n) - X))) ((coe_injective _ R).comp (Involutive.injective (by aesop_cat)))
  (MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff (by simp [map_pow, map_sub])))

omit [Fintype Φ] [∀ τ, Fintype (n' τ)] in
lemma PolyRep.rowSubst_minor τ I : rowSubst z (minor R (⟨τ, I ·⟩)) =
  det ((z τ).submatrix I (rowPos n τ).symm) •
  minor R (⟨τ, (rowPos n τ).symm ·⟩) := by simp [rowSubst, reindex_equiv (rowPos n τ).symm]; rfl

@[simp] lemma rowSubst_detPow : rowSubst g (detPow R n e) = (∏ τ,
  (g τ).det ^ e τ) • detPow R n e := by simp [-minor, rowSubst_minor, mul_pow]

/-- Every Borel semi-invariant polynomial whose weight is that of κ increased by e_τ on the
first |n_τ| columns at each place τ is an R-linear combination of the products b_i · ∏_τ
det(y_τ)^{e_τ}, b_i the basis minor products for κ. -/
lemma nabla_le_span_nablaBasis_mul_detPow : nabla R fst (diagramWeight (rankAt n) κ + ∑ τ,
  e τ • (range (rankAt n τ)).sum (.single ⟨τ, ·⟩ 1)) ≤
  (Fintype.linearCombination R (nablaBasis R n κ · * detPow R n e)).range := by
  simp_rw [← Fin.sum_const, ← Fintype.sum_sigma', diagramWeight_eq_columnWeight]
  refine (exists_minorProduct_basis _ (_ ⊕ᵥ _) (_ ⊕ᵥ _)).elim fun _ ⟨_, I, H, _⟩ ↦
    (congrArg _ (sum_sum_type _)).ge.trans ((H R).2.trans (span_le.2 fun _ ⟨i, h⟩ ↦ h ▸ ?_))
  choose T h using ((sigmaSubtype _).symm.surjective <| I i · ·)
  exact ⟨_, by simpa [← funext₂ h, -C_mul', -univ_eq_attach] using! congr((∏ τ, rename (·.map (mk τ)
    id) $(((mem_span_image_finset_iff_exists_fun _).1 ((isStdTableauSet_epsilon.1 R).2 (T <|
    .inl ⟨τ, ·, ·⟩))).choose_spec)) * ∏ τ, ∏ j, $((rowSubst_minor (R :=
    R) (fun _ ↦ 1) τ (T (.inr ⟨τ, j⟩))).symm))⟩

lemma PolyRep.nablaCombination_injective : Injective (nablaCombination (R := R) (n := n) κ) :=
  linearIndependent_nablaBasis.fintypeLinearCombination_injective

/-- Over any commutative ring R, the minor products b_i indexed by families of chosen standard
fillings span exactly the module of Borel semi-invariant polynomials whose weight is built
from κ using heights below |n_τ|. -/
lemma span_nablaBasis : (nablaCombination κ).range = nablaFam R n κ := le_antisymm
  (by simp [span_le, nablaBasis, prod_tableauPoly_mem_nabla, -tableauPoly])
  (by simpa using nabla_le_span_nablaBasis_mul_detPow 0)

lemma sum_coords_nablaBasis (h : f ∈ nablaFam R n κ) : ∑ i,
  invFun (nablaCombination κ) f i • nablaBasis R n κ i = f := invFun_eq (span_nablaBasis.ge h)

/-- Over any commutative ring R and for any exponents e_τ, the polynomials b_i · ∏_τ
det(y_τ)^{e_τ}, with b_i the basis minor products for κ, are linearly independent over R. -/
lemma PolyRep.linearIndependent_nablaBasis_mul_detPow : LinearIndependent R (nablaBasis R n κ · *
  detPow R n e) := linearIndependent_nablaBasis.map_injOn (.mulRight ..) isRegular_detPow.2.injOn

/-- If f = Σ_j x_j b_j · ∏_τ det_τ^{e_τ}, with b_j the basis minor products, and all
coefficients of f lie in an additive subgroup A of R, then every x_i lies in A. -/
lemma PolyRep.coord_mem_of_coeff_mem {x : _ → R} (H : ∑ j,
  x j • (nablaBasis R n κ j * detPow R n e) = f) (h : ∀ d, f.coeff d ∈ A) i : x i ∈ A := by
  have E (S : Type) [CommRing S] j := (nablaBasis ℤ n κ j * detPow ℤ n e).coeff_map (algebraMap ℤ S)
  subst H; simp at E h
  let φ := TrivSqZeroExt.inrHom ℤᵐᵒᵖ _ ∘ TensorProduct.mk ℤ ℤᵐᵒᵖ (R ⧸ A) 1
  simpa [φ] using congr($(linearIndependent_iff.1 (linearIndependent_nablaBasis_mul_detPow e) (φ <|
    x ·) (by ext1; simpa [φ, coeff_sum, E R, E (TrivSqZeroExt ..)] using congr(φ $(h _))) i).snd)

omit [Fintype Φ] in
@[simp] lemma FitsRanks.refl : FitsRanks n n κ := by grind

omit [Fintype Φ] in
@[simp] lemma schurDetExp_self : schurDetExp n n κ = 0 := funext (by simp [schurDetExp])

lemma PolyRep.schur_eq_of_expansion {z} (h : ∀ i, ∑ j, M i j • (nablaBasis R n κ j * detPow R n
  (schurDetExp n n' κ)) = rowSubst z (nablaBasis R n' κ i)) : schur κ z = M := funext fun i ↦
  (linearIndependent_nablaBasis_mul_detPow _).fintypeLinearCombination_injective
  (.trans (invFun_eq ⟨_, h i⟩) (h i).symm)

@[local simp] lemma schur_diagonal_eq_prod : schur κ (diagonal <| x ·) = diagonal fun i ↦ ∏ τ, ∏ h,
  ∏ j, ∏ s, x τ ((i τ).1 h j s) :=
  schur_eq_of_expansion (by simp [diagonal, nablaBasis, rowSubst, ← prod_mul_distrib])

/-- Weyl's character formula over ℂ: for diagonal matrices with entries x_τ, the trace of
S_κ(diag x) times ∏_τ of the Vandermonde determinants of x_τ equals ∏_τ
det(x_{τ,i}^{λ_τ(|n_τ|−1−j)+j}), with λ the partition `diagramWeight` of κ, indexed from 0. -/
lemma weyl_character {a : Φ → ℕ} (e : ∀ τ, Fin (a τ) ≃ n τ) (x : ∀ _, _ → ℂ) : (schur κ (diagonal <|
    x ·)).trace * ∏ τ, (vandermonde (x τ ∘ e τ)).det = ∏ τ, det (of fun i j ↦ x τ (e τ i) ^
    (diagramWeight (rankAt n) κ (τ, j.rev) +
  j)) := by simpa [← card_congr (e _), ← sum_coe_sort (epsilon _), alternant, -univ_eq_attach]
  using! congr(∏ τ, $(isStdTableauSet_epsilon (M := rankAt n τ).2 _ (e τ) _))

@[simp] lemma schur_one (h : ∀ τ, g τ = 1) : schur κ g = 1 :=
  schur_eq_of_expansion (by simp [h, rowSubst])

/-- The Schur matrix of a tuple of diagonal matrices diag(x_τ) is diagonal, with i-th entry ∏_τ
∏_a x_τ(a)^{w}, where w is the number of entries equal to a in the filling i_τ. -/
lemma schur_diagonal : schur κ (diagonal <| x ·) = diagonal (∏ τ, ∏ a, x τ a ^ tableauWeight · τ
  a) := by simp [tableauWeight, @prod_comm _ _ (n _), card_filter, -sum_boole]

include h

lemma PolyRep.diagramWeight_eq_of_fitsRanks : diagramWeight (rankAt n') κ =
  diagramWeight (rankAt n) κ + ∑ τ, schurDetExp n n' κ τ • (range (rankAt n τ)).sum
  (.single ⟨τ, ·⟩ 1) := .trans (sum_congr _ _ fun τ ↦ by grind [zero_smul, schurDetExp,
  sum_eq_ite (rankAt n τ), sum_range_add_sum_Ico _ (h τ).1]) sum_add_distrib

/-- Under the condition `FitsRanks` on n, n', κ, row i of the Schur matrix expands the
substituted basis polynomial: b'_i(zy) = Σ_j S_κ(z)_{ij} b_j(y) ∏_τ det(y_τ)^{d_τ}, with d
given by `schurDetExp`. -/
@[simp ← low] lemma sum_schur_smul_nablaBasis : ∑ j,
  schur κ z i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
  rowSubst z (nablaBasis R _ κ i) := invFun_eq (nabla_le_span_nablaBasis_mul_detPow _
  (diagramWeight_eq_of_fitsRanks h ▸ rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla))

/-- Base change: if the sizes fit κ (`FitsRanks`), then for a ring homomorphism φ the Schur
matrix of φ(z), φ applied entrywise, is φ applied entrywise to the Schur matrix S_κ(z). -/
@[simp ←] lemma schur_map : schur κ (z · |>.map φ) = (schur κ z).map φ := schur_eq_of_expansion (by
  simpa [rowSubst, map_bind₁] using congr(map (φ : R →+* S) $(sum_schur_smul_nablaBasis h z ·)))

lemma map_schur i j : φ (schur κ z i j) = schur κ (fun τ ↦ of (φ <| z τ · ·)) i j :=
  schur_map h z φ ▸ rfl

/-- If the sizes fit κ (`FitsRanks`), then S_κ(gz) = S_κ(g) S_κ(z) for square matrices g_τ of
size n'_τ and matrices z_τ of size n'_τ×n_τ over R. -/
@[simp ←] lemma schur_mul_left (g : ∀ τ, Matrix (n' τ) (n' τ) R) : (schur κ fun τ ↦ g τ * z τ) =
    schur κ g * schur κ z := schur_eq_of_expansion fun _ ↦ by simpa [h, -C_mul'] using sum_comm

/-- If the sizes fit κ (`FitsRanks`), then S_κ(zg) = ∏_τ det(g_τ)^{d_τ} · S_κ(z) S_κ(g) for z_τ
of size n'_τ×n_τ and g_τ square of size n_τ, with exponents d_τ given by `schurDetExp`. -/
lemma schur_mul_right : schur κ (fun τ ↦ z τ * g τ) =
  (∏ τ, (g τ).det ^ schurDetExp n n' κ τ) • (schur κ z * schur κ g) := schur_eq_of_expansion
  fun _ ↦ by simpa [h, -detPow, -C_mul', mul_sum, mul_left_comm] using sum_comm

/-- If the sizes fit κ (`FitsRanks`), the (i,j) entry of S_κ(z) is the product over places τ of
the (i_τ, j_τ) entries of the one-place Schur matrices S_{κ_τ}(z_τ). -/
lemma schur_apply_eq_prod j : schur κ z i j = ∏ τ, schur (fun () ↦ κ τ) (fun _ ↦ z τ) (fun _ ↦ i τ)
    fun _ ↦ j τ := congrFun₂ (schur_eq_of_expansion fun i ↦ by simpa [nablaBasis, rowSubst, -C_mul']
  using! (congr(∏ τ, rename (·.map (mk τ ·.2) id) $(((piUnique _).symm.sum_comp _).trans
                 (sum_schur_smul_nablaBasis (const Unit (h τ)) (fun _ ↦ z τ) fun _ ↦ i τ))))) ..

lemma schur_smul : (schur κ fun τ ↦ t τ • z τ) = (∏ τ, t τ ^ ∑ i ∈ range (rankAt n' τ), i * κ τ i) •
    schur κ z := by simp [smul_eq_diagonal_mul, schur_mul_left h, sum_range]
