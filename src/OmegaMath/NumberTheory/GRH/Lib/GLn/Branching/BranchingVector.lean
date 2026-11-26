import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.SubmersionZero
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Witt.FrameAction
import OmegaMath.NumberTheory.GRH.Lib.GLn.SchurModule.Gram
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Branching from GL(n+1) to GL(n) with multiplicity one (known result; see
Lib.GLn.Branching.Branching).

Part of: Contravariant form on Weyl's lattice, Fischer product, irreducibility under U(n) (known
result; see Lib.Adelic.CuspForms.DeltaForms).

This file: Norm on Weyl's lattice, Zariski density of U(n), hook number clears denominators. Cartan
multiplication: integral, isometric, equivariant, split; submultiplicativity of norms. Denominator
of the branching vector bounded by the columns of height at least q. -/

open MvPolynomial Matrix Complex ComplexOrder Norms.L2Operator NormedSpace ComplexStarModule Finset

section

variable {Φ R} [CommRing R] [Fintype Φ] {n} [∀ τ : Φ, Fintype (n τ)] {κ} (ξ : WeylIndexFam n κ → ℂ)

/-- For a complex coordinate vector ξ, the real part of ξ* G ξ, where G is the integer Gram
matrix. -/
noncomputable def weylNormSq := (star ξ ⬝ᵥ (weylGram n κ).map (↑) *ᵥ ξ).re

@[simp] lemma weylNormSq_nonneg : 0 ≤ weylNormSq ξ :=
  weylGram_posDef.posSemidef.re_dotProduct_nonneg ξ

lemma weylNormSq_smul (t : ℂ) :
  weylNormSq (t • ξ) = ‖t‖ ^ 2 * weylNormSq ξ := by simp [weylNormSq, ← mul_assoc, mul_conj', sq]

@[simp] lemma weylNormSq_comp_smul {F} [FunLike F ℂ ℂ] [MulHomClass F ℂ ℂ] (σ : F) t :
  weylNormSq (σ ∘ (t • ξ)) = ‖σ t‖ ^ 2 * weylNormSq (σ ∘ ξ) := by convert weylNormSq_smul ..; aesop

namespace PolyRep

lemma analyticOnNhd_evalMat {P} : AnalyticOnNhd ℂ (@evalMat Φ ℂ _ n · P) ⊤ :=
  .eval_linearMap ⟨⟨_, by tauto⟩, by tauto⟩ P

/-- Zariski density of ∏_τ U(n_τ): a complex polynomial P in the entries of a tuple of square
matrices that vanishes at all tuples of unitary matrices vanishes at every tuple x. -/
lemma zariski_dense_unitary x P (h : ∀ g, (∀ τ, (g τ)ᴴ * g τ = 1) → @evalMat Φ ℂ _ n g P = 0) :
  evalMat x P = 0 := eq_zero_of_submersion analyticOnNhd_evalMat hasStrictFDerivAt_exp_zero
  (by bound) (.of_forall fun x ↦ by simpa [smul_smul,
  realPart_add_I_smul_imaginaryPart] using congrFun ((analyticOnNhd_evalMat.comp (fun _ _ ↦ .comp
  (exp_analytic _) (f := I • (· • (-ℜ x).1 + ℑ x)) (by fun_prop)) (by simp)).eq_of_frequently_eq
  analyticOnNhd_const (((hasDerivAt_id 0).ofReal_comp.tendsto_nhdsNE one_ne_zero).frequently
  (.of_forall fun t ↦ h _ (congrFun (selfAdjoint.expUnitary (t • -ℜ x + ℑ x)).2.1)))) I) x

lemma posDef_cauchy_schwarz {ι} [Fintype ι] {M} (h : PosDef M) (x :
  ι → ℂ) y : ‖star x ⬝ᵥ M *ᵥ y‖ ^ 2 ≤
  (star y ⬝ᵥ M *ᵥ y).re * (star x ⬝ᵥ M *ᵥ x).re := by simpa only [dotProduct_comm, norm_inner_symm,
  sq] using! (@inner_mul_inner_self_le _ _ _ (_) (M.toInnerProductSpace h.posSemidef) y x)

lemma coe_weylNormSq : weylNormSq ξ = star ξ ⬝ᵥ weylGramOver *ᵥ ξ :=
  Complex.ext rfl (weylGram_posDef.posSemidef.dotProduct_mulVec_nonneg ξ).2

lemma star_weylEval y : star (weylEval n κ y) =
  weylEval n κ (star y : _ → ℂ) := by ext; simp [weylEval, map_eval]; rfl

/-- For bijections e_τ from the rows n_τ onto {0, …, |n_τ| − 1}, the evaluation vector at the
permutation array `permArray` of e has squared norm 1 for the Gram form `weylNormSq`. -/
lemma weylNormSq_weylEval_permArray (e : ∀ τ, n τ ≃ Fin (rankAt n τ)) : weylNormSq (weylEval n κ
  (permArray e)) = 1 := by simpa [weylNormSq, ↓star_weylEval, Pi.star_def,
  permArray] using! congr(re $(eval_weylKernel_permArray e))

/-- The hook number clears denominators: over any commutative ring, for every semi-invariant f
in `nablaFam`, the multiple of f by the hook number `hookNumber` lies in the image of
`toPoly`. -/
lemma exists_toPoly_eq_hookNumber_smul {f} (hf : f ∈ nablaFam R n κ) : ∃ ζ, toPoly n κ ζ =
  hookNumber κ (rankAt n) • f := (span_nablaBasis.ge hf).imp' _ fun c
  _ ↦ by rw [← nablaCombination_weylGramOver_mulVec, mulVec_mulVec c, ← map_mul_intCast,
  weylGram_mul_fockPairing]; simp [*, Matrix.map_intCast, ← C_mul']

open Kronecker SetLike
variable {Φ R : Type} [CommRing R] [Fintype Φ] {n : Φ → _} [∀ τ, Fintype (n τ)] {κ : _} {κ'}

attribute [scoped simp] vecMulVec_apply kronecker_mulVec_vec mul_vecMulVec vecMulVec_mul
  vecMul_transpose vec_dotProduct_vec star_vec vecMulVec_mulVec

attribute [local simp] weylKernel highestPoly tableauPoly mulVec_transpose

variable (R n κ κ') in noncomputable def comulMatrix := of fun (p, q) k ↦ (↑(Function.invFun
  (nablaCombination (κ + κ')) (nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q) k) : R)

/-- Over any commutative ring, the matrix of coordinates of the products of basis minor products
for κ and κ' sends the evaluation vector ev_y for κ + κ' to the tensor product ev_y ⊗ ev_y
of those for κ and κ'. -/
lemma cm_mulVec_weylEval y : comulMatrix R n κ κ' *ᵥ weylEval n _ y =
  (vecMulVec (weylEval n _ y) (weylEval n _ y)).vec := _root_.funext fun _ ↦ .trans (by
  simpa using! congr(($(sum_coords_nablaBasis (f := nablaBasis .. * nablaBasis ..) (congr(nabla _
    _ $diagramWeight_add).ge (mul_mem_graded prod_tableauPoly_mem_nabla
    prod_tableauPoly_mem_nabla))).map (algebraMap ℤ R)).eval y)) (mul_comm ..)

variable [IsDomain R] [Infinite R]

/-- Over an infinite domain, the row vector a ⊗ b times the multiplication matrix equals x
exactly when the product of the polynomials with coordinates a (basis for κ) and b (basis
for κ') has coordinates x (basis for κ + κ'). -/
lemma vecMul_comulMatrix_eq_iff {a b x} : (vecMulVec b a).vec ᵥ* comulMatrix R n κ _ = x ↔
    nablaCombination κ a * nablaCombination κ' b = nablaCombination _
  x := by simp [← nablaCombination_injective.eq_iff, MvPolynomial.funext_iff, cm_mulVec_weylEval, ←
  weylEval.eq_1, Fintype.linearCombination, ← dotProduct.eq_1, ← dotProduct_mulVec]; grind

/-- Over an infinite domain, let C express products of basis elements of weights κ, κ' in the
basis of weight κ+κ'. Then Cᵀ(G_κ⊗G_κ')C = G_{κ+κ'} for the Gram matrices, and
(S_κ(g)⊗S_κ'(g))C = C·S_{κ+κ'}(g) for all tuples g of square matrices.

Known result: Dual of a Weyl module by Jacobi's complementary minors; Cartan component. -/
lemma comulMatrix_isometry_and_equivariant (g : ∀ τ,
  Matrix (n τ) (n τ) R) : let C := comulMatrix R n κ κ'
  Cᵀ * ((weylGram n κ).map (↑) ⊗ₖ (weylGram n κ').map (@Int.cast R _) * C) = weylGramOver ∧
    schur κ g ⊗ₖ schur κ' g * C =
    C * schur (κ + κ') g := by constructor <;> exact toLin'.injective (ext_weylEval 0
  (by simp [cm_mulVec_weylEval, vecMul_comulMatrix_eq_iff, nablaCombination_weylGramOver_mulVec,
  pow_add, schur_mulVec_weylEval_of_detExp_zero]))

/-- The integer matrix whose row (p, q) lists the coordinates of the product of the basis minor
products b_p for κ and b_q for κ', in the basis for κ + κ', has an integer left inverse. -/
lemma hasLeftInv_comulMatrix : HasLeftInv (comulMatrix ℤ n κ κ') :=
  ⟨_, ext_row fun _ ↦ vecMul_comulMatrix_eq_iff.2
  (by simp [← single_one_vecMul, nablaBasis,
  Fin.prod_univ_add]; congr <;> exact sum_coords_nablaBasis prod_tableauPoly_mem_nabla)⟩

/-- If the polynomial attached by the Gram matrix to the complex vector ζ of weight κ+κ' is the
product of those attached to ξ (weight κ) and η (weight κ'), then ‖ζ‖² ≤ ‖ξ‖²‖η‖² for the
Gram norms. -/
lemma _root_.weylNormSq_le_mul_of_toPoly_eq {ξ η ζ} (h : toPoly n (κ + κ') ζ = toPoly n κ ξ * toPoly
  n κ' η) : weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η := let C := comulMatrix ℂ n κ κ'; by
    nlinarith [mul_nonneg (weylNormSq_nonneg ξ) (weylNormSq_nonneg η), by
      simpa [star_mulVec, ← dotProduct_mulVec, by simpa [toPoly, ← vecMul_comulMatrix_eq_iff] using
        h.symm, comulMatrix_isometry_and_equivariant 1, ← coe_weylNormSq,
        (Matrix.ext (by simp [comulMatrix]) : Cᴴ = Cᵀ), C, ↓map_vecMulVec_star, -vecMul_transpose,
        vecMul_transpose _ ξ] using posDef_cauchy_schwarz
        (weylGram_posDef.kronecker weylGram_posDef) (C *ᵥ ζ) (vecMulVec η ξ).vec]

end PolyRep

end

namespace PolyRep

attribute [-simp] zsmul_eq_mul

variable {Φ : Type} (R : Type) [CommRing R] [Fintype Φ] {n N : Φ → _} [∀ τ, Fintype (n τ)]
  [∀ τ, Fintype (N τ)] (ι : ∀ τ, n τ ⊕ Unit ≃ N τ) {γ κ' : Φ → ℕ → ℕ}

/-- The numbering of the rows N_τ by 0, …, |N_τ|−1 that gives the added row the number i_τ and
keeps the rows of n_τ in their fixed order. -/
noncomputable def newRowOrder (i : ∀ _, _) τ :=
  (((((finCongr (rankAt_eq_succ ι τ)).trans (finSuccEquiv'
  (i τ))).trans (rowPos ..).symm.optionCongr).trans (.optionEquivSumPUnit _)).trans (ι τ)).symm

/-- The product over τ and h < |N_τ| of the leading h×h minors to the power γ_τ(h) with the added
row first, and to the power κ_τ(h) with it last. -/
noncomputable def branchVector γ κ := weylKernel N γ (permArray (newRowOrder ι 0)) * weylKernel
  (R := R) N κ (permArray (newRowOrder ι ⊤))

lemma rowSubst_branchVector s : rowSubst (blockScalar ι 1 s) (branchVector R ι γ κ') =
  (∏ τ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) • branchVector R ι γ κ' := by rw [branchVector,
  map_mul, rowSubst_weylKernel_permArray, rowSubst_weylKernel_permArray] <;> simp [newRowOrder,
  blockScalar, rankAt_eq_succ ι, reindex_equiv (ι _),
  diagramWeight_apply, Nat.Ioo_eq_range', BlockTriangular] <;> grind

/-- Let κ₀(h) = κ'(h)+γ(h) for 0<h<|n_τ|, κ'(i) = 0 for i<q, and f number the rows with `rowPos` ≤
f+1. Some integer c>0, at most L^{3L} whenever L ≥ ∑_τ∑_{q≤h<|n_τ|} hκ₀(h), and integer
vector η satisfy c·K_γ·K_{κ'} = `toPoly` η, kernels `weylKernel` at the permutation arrays of f and
`rowPos`. -/
lemma exists_smul_weylKernel_mul_eq_toPoly {κ₀ q} (f : ∀ τ, _ ≃ Fin (rankAt n τ)) (p : ∀ τ a,
  (rowPos n τ a).1 ≤ f τ a + 1) (hq : ∀ τ, ∀ i < q, κ' τ i = 0) (h₀ : ∀ τ, ∀ h ∈ Ioo 0 (rankAt n τ),
  κ₀ τ h = (κ' + γ) τ h) : ∃ c : ℤ, 0 < c ∧
  (∀ L, ∑ τ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧ ∃ η, c • (weylKernel n γ
  (permArray f) * weylKernel n κ' (permArray (rowPos n)) : MatrixPoly _ ℤ) = toPoly n κ₀ η := by
  let β τ i := ite (i ∈ Ioo 0 (q ⊓ rankAt n τ)) (γ τ i) 0
  obtain ⟨α, rfl⟩ := exists_add_of_le (by aesop_cat : β ≤ κ₀)
  use hookNumber α (rankAt n), hookNumber_pos, fun _ ↦ hookNumber_le ∘
    (sum_le_sum (by simp_all; grind [sum_congr_of_eq_on_inter])).trans
  obtain ⟨⟨F, hF⟩, ζ, T⟩ := (by simp [weylKernel, rowSubst_highestPoly, prod_sigma']; grind
    [prod_dvd_prod_of_dvd, pow_dvd_pow] : weylKernel (R := ℤ) n β (permArray f) ∣ weylKernel n γ
    (permArray f)), exists_toPoly_eq_hookNumber_smul (congr(nabla ℤ _
    $((by grind [=_ diagramWeight_add, diagramWeight_apply, sum_congr, add_comm] : diagramWeight
    (rankAt n) (β + α) = diagramWeight _ γ + diagramWeight _ κ'))).ge (SetLike.mul_mem_graded
    (weylKernel_mem_nablaFam (permArray f)) (weylKernel_mem_nablaFam (permArray (rowPos n)))))
  obtain ⟨a, Q⟩ : ∃ a, comulMatrix ℤ n β α *ᵥ ζ = (vecMulVec a _).vec := ⟨_, _root_.funext fun ⟨i,
    i'⟩ ↦ by simpa [← toPoly_weylEval, mul_assoc] using map_nablaBasis_eq_mul_weylEval f i
               (fockPairing ℤ (toPoly n β ((comulMatrix ℤ n β α *ᵥ ζ) ⟨·, _⟩))) fun h τ a ↦ by
               by_contra! o; obtain ⟨E, B⟩ := congr(($((comulMatrix_isometry_and_equivariant fun _ ↦
                 diagonal (2 ^ Finsupp.single (Sigma.mk τ a) 1 ⟨_, ·⟩)).2) *ᵥ ζ) ⟨i, i'⟩),
                 add_lt_add_of_lt_of_le o (sum_tableauWeight_le i' τ {a}).1
               rw [← mulVec_mulVec, ← mulVec_mulVec, (toPoly_injective (by
                 simp [T, rowSubst_weylKernel_permArray, smul_smul]
                 rw [mul_comm]) : _ *ᵥ ζ = (_ : ℤ) • ζ)] at E
               simp_all [schur_diagonal, ← pow_add, diagramWeight, ite_and,
                 diagonal_kronecker_diagonal, Finsupp.single_apply, ← sum_add_distrib]
               grind [exists_lt_of_sum_lt B, sum_eq_zero.mt o.ne_bot]⟩
  have D := by simpa [vecMul_comulMatrix_eq_iff, nablaCombination_weylGramOver_mulVec, *, mul_assoc,
    mulVec_transpose, ← mulVec_mulVec, ← Algebra.mul_smul_comm, ne_zero_of_map (ne_zero_of_eq_one
    (eval_weylKernel_permArray f))] using congr($((comulMatrix_isometry_and_equivariant 1).1) *ᵥ ζ)
  exact hasLeftInv_comulMatrix.elim fun L l ↦
    ⟨_, by simpa [← Q, smul_comm (hookNumber α _), ← Int.zsmul_eq_mul, T, l, -smul_eq_mul,
    ← Pi.smul_def] using congr(toPoly _ _ (L *ᵥ (vecMulVec (fockPairing ℤ $D <|
    nablaBasis ℤ n α ·) (weylEval n β (permArray f))).vec))⟩
