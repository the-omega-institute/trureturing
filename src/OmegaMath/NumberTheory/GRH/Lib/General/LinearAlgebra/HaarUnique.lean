import OmegaMath.NumberTheory.GRH.Lib.General.Analysis.OstrowskiTaussky
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

General lemmas of real and complex analysis (textbook or folklore).

This file: Complex Gaussian integral for matrices of positive real part; linear change of variables.
Determinant is monotone in the semidefinite order; matrix Bessel inequality for contractions.
Reindexing, currying and flipping product measures preserve measure. Haar measures giving one
function integral one are equal. -/

open CStarAlgebra Complex ComplexOrder Finset Matrix MatrixOrder MeasureTheory PiLp

variable {ι} [Fintype ι] (x : ι → ℂ) {A P Q : Matrix ι ι ℂ} {Y α} {n : ι → _} [Fintype Y]
  [∀ i, Fintype (n i)] [MeasureSpace α] [SigmaFinite (@volume α _)]

/-- The complex matrix A is accretive: its hermitian part is positive definite, A + A* > 0. -/
def Matrix.IsAccretive (A : Matrix ι ι ℂ) := (A + Aᴴ).PosDef

omit [Fintype ι] in
lemma Matrix.PosDef.isAccretive (h : A.PosDef) : A.IsAccretive := h.add h.conjTranspose

lemma Matrix.IsAccretive.det_ne_zero (h : A.IsAccretive) : A.det ≠ 0 := fun e ↦ by
  simpa [e, h.det_pos.ne'] using ostrowski_taussky h.posSemidef (le_iff.1 le_rfl)

/-- Lebesgue measure on ℂ^ι divided by π to the power of the number of coordinates. -/
noncomputable def realMeasure ι [Fintype ι] : Measure (ι → ℂ) :=
  NNReal.pi⁻¹ ^ Fintype.card ι • volume

instance : (realMeasure ι).IsAddHaarMeasure := .nnreal_smul _ (by simp [NNReal.pi_ne_zero])

lemma map_mulVec_haar {μ : Measure (ι → ℂ)} [μ.IsAddHaarMeasure] {u} (h : det u ≠ 0) : μ.map (u *ᵥ
  ·) = (ENNReal.ofReal (‖u.det‖ ^ 2))⁻¹ • μ := by erw [μ.map_linearMap_addHaar_eq_smul_addHaar (f :=
  u.toLin')] <;> simp [LinearMap.det_restrictScalars, Algebra.norm_complex_eq, normSq_eq_norm_sq, h]

/-- Linear change of variables on ℂ^ι: for a complex square matrix u with det u ≠ 0 and any g :
ℂ^ι → [0, ∞], ∫ g(y) dy = |det u|² ∫ g(uy) dy (lower Lebesgue integrals). -/
lemma lintegral_eq_det_mul u (h : u.det ≠ 0) (g : (ι → ℂ) → _) : ∫⁻ y, g y = .ofReal (‖u.det‖ ^ 2)
    * ∫⁻ y, g (u *ᵥ y) := by simp [← (Continuous.measurableEmbedding (by fun_prop)
  (mulVec_injective_of_det_ne_zero h)).lintegral_map, map_mulVec_haar, ENNReal.mul_inv_cancel_left,
  h]

lemma star_dot_self_eq_sum : star x ⬝ᵥ x = ∑ i, ‖x i‖ ^ 2 := by simp [dotProduct, conj_mul']

lemma star_dot_self_eq_norm_sq :
    star x ⬝ᵥ x = ‖WithLp.toLp 2 x‖ ^ 2 := mod_cast by simp [star_dot_self_eq_sum, norm_sq_eq_of_L2]

lemma norm_sq_le_re_star_dot : ‖x‖ ^ 2 ≤ (star x ⬝ᵥ x).re := by
  grw [(antilipschitzWith_toLp 2 _).le_mul_norm] <;> simp [star_dot_self_eq_norm_sq, sq]

/-- Complex Gaussian integral: if A + A* is positive definite, then for every vector a the
integral of exp(−x*A(x − a)) over x in ℂ^ι, for Lebesgue measure divided by π^|ι|, equals
(det A)⁻¹. -/
lemma integral_gauss (hA : A.IsAccretive) a : ∫ x, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) ∂realMeasure ι =
  A.det⁻¹ := by
  have ⟨_, ⟨B, rfl⟩, hB⟩ := isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  have k := ((imaginaryPart A).2.conjugate' B⁻¹).isHermitian
  obtain ⟨p, d, rfl, h⟩ : ∃ p d, A = (p : GL ι ℂ)ᴴ * diagonal d * p.1 ∧ ∀ i, 0 < (d i).re :=
    ⟨Unitary.toUnits k.eigenvectorUnitary⁻¹ * B, I • _ + ofReal 2⁻¹ • 1, by
    erw [← diagonal_add, diagonal_smul, ← k.conjStarAlgAut_star_eigenvectorUnitary]
    simp [mul_assoc, ← star_eq_conjTranspose, mul_add, add_mul, ← hB, smul_smul, imaginaryPart,
      ← mul_assoc _ (star _), ← star_mul]; module⟩
  simp [← mulVec_mulVec, ← star_mulVec_dotProduct]
  convert (congr(∏ i, $(GaussianFourier.integral_cexp_neg_mul_sum_add _ (d i • (p *ᵥ a) i •
   ![1, -I]) ▸ volume_preserving_equiv_pi.integral_comp' _)) ▸ integral_fintype_prod_volume_eq_prod
   _) ▸ ((map_mulVec_haar (μ := realMeasure ι) p.det_ne_zero).trans (smul_smul ..) ▸ integral_map
    (by fun_prop) (by fun_prop)).symm.trans (integral_smul_measure ..)
    using 1 <;> simp [-sum_add_distrib, ← exp_sum, field, dotProduct, mulVec_sub, mul_pow,
    re_eq_add_conj, im_eq_sub_conj, ← sum_neg_distrib] <;> grind [I_sq, mul_conj']

lemma norm_det_le_norm_det_of_posSemidef (hP : P.PosSemidef) (h : (Q - P).PosSemidef) :
    ‖P.det‖ ≤ ‖Q.det‖ := by simpa [← two_smul ℂ] using (ostrowski_taussky (hP.add
  hP) (le_iff.1 (add_le_add h (hP.1 ▸ star_le_star_iff.2 h))))

/-- Cauchy–Schwarz inequality for determinants: if the complex block matrix with rows (P, A) and
(B, Q), all blocks square of the same size, is positive semidefinite, then |det A|² ≤ |det
P|·|det Q|. -/
lemma norm_det_sq_le_of_posSemidef {B} (h : (fromBlocks P A B Q).PosSemidef) :
    ‖A.det‖ ^ 2 ≤ ‖P.det‖ * ‖Q.det‖ := by
  by_cases e : Q.det = 0
  simp [*, ← exists_mulVec_eq_zero_iff] at *
  peel e with v _
  simpa [fromBlocks_mulVec, *, dotProduct, funext_iff] using h.dotProduct_mulVec_zero_iff (x :=
    0 ⊕ᵥ v)
  have q : Q.PosDef := (h.submatrix .inr).posDef_iff_det_ne_zero.2 e
  let := q.isUnit.invertible
  simpa [field, mul_comm] using norm_det_le_norm_det_of_posSemidef (.mul_mul_conjTranspose_same
    q.inv.posSemidef A) ((q.fromBlocks₂₂ P A).1 ((isHermitian_fromBlocks_iff.1 h.1).2.1 ▸ h))

open Norms.L2Operator in
/-- Bessel's inequality for complex matrices: if E has operator norm at most 1, then X(1 −
EEᴴ)Xᴴ is positive semidefinite for every X. -/
lemma posSemidef_bessel {m n} [Fintype m] [Fintype n] {E : Matrix ι n ℂ} (h : ‖E‖ ≤ 1)
    (X : Matrix m ι ℂ) : (X * (1 - E * Eᴴ) * Xᴴ).PosSemidef := .mul_mul_conjTranspose_same
    ((norm_le_one_iff_of_nonneg _ E.posSemidef_self_mul_conjTranspose.nonneg).1 (by
  grw [l2_opNorm_mul, l2_opNorm_conjTranspose]; bound)) X

/-- For a bijection e from the disjoint union of finite sets n_i onto Y, the regrouping map α^Y
→ ∏_i α^(n_i), x ↦ (x(e(i,j)))_{i,j}, preserves the product volume measures. -/
lemma measurePreserving_sigma (e : Sigma n ≃ Y) : MeasurePreserving fun (x : _ → α) i j ↦ x
    (e ⟨i, j⟩) := .comp (.symm (.symm (.piCurry fun _ _ ↦ α)) ⟨by fun_prop, .symm
    (Measure.pi_eq (by simp [MeasurableEquiv.map_apply, ↓Fintype.prod_sigma, ← volume_pi_pi,
  Set.pi, Sigma.forall, Sigma.uncurry]))⟩) (volume_preserving_arrowCongr' e.symm (.refl _) (.id _))

lemma measurePreserving_curry :
    MeasurePreserving (MeasurableEquiv.curry ι Y α) := measurePreserving_sigma (.sigmaEquivProd ..)

lemma measurePreserving_flip : MeasurePreserving (@flip ι Y α) := (measurePreserving_sigma
    (.trans (.sigmaEquivProd ..) (.prodComm ..))).comp measurePreserving_curry.symm

/-- Two Haar measures μ, ν on a second countable locally compact additive group are equal if
some real function f has integral 1 for both. -/
lemma addHaar_eq_of_integral_eq_one {G} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {μ ν : Measure G} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {f : G → ℝ} : integral ν f = 1 →
    integral μ f = 1 → μ = ν := μ.isAddLeftInvariant_eq_smul ν ▸ by simp_intro .. [NNReal.smul_def]
