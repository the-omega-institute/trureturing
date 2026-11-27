/- GID: D5/S3/Zeros/GRH/Lib/GLn/Branching/Branching
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/Branching/Branching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.Branching.Branching. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/Branching/Branching.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.Branching.BranchingVector
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.ExpSurjective
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Branching from GL(n+1) to GL(n) with multiplicity one. For one interlacing pair,
this file gives an integer matrix with an explicit norm bound, equivariant over every field of
characteristic 0, of which every unitarily equivariant map is a multiple. The matrix is shown to be
non-zero only inside the proof. Source: Goodman, Wallach 2009, Theorem 8.1.1; Zhelobenko, Compact
Lie Groups and their Representations, 1973, ch. X; Molev, Gelfand-Tsetlin bases for classical Lie
algebras, arXiv math/0211289.

Known result: Dual of a Weyl module by Jacobi's complementary minors, and the Cartan component. The
groups here are products of GL_n, and the duality and the Cartan map are integer matrices, isometric
and equivariant over fields of characteristic 0. The duality has an integral inverse, and the Cartan
map has an integral left inverse. Source: Fulton, Harris, Representation Theory, 1991, section 15.5;
Jantzen 2003; for Jacobi's identity, Grinberg, An Introduction to Algebraic Combinatorics, Thm
6.4.48.

This file: Extremal vector is cyclic; Schur's lemma for U(n) on Weyl modules. Dual of a Weyl module
by Jacobi complementary minors, as unimodular integral isometry. Multiplicity-one branching GL(n+1)
to GL(n) as an integral map with explicit norm bound. -/

open Finset ComplexOrder Equiv PolyRep Matrix MvPolynomial RingHom SetLike

variable {Φ} {K : Type} [Field K] [CharZero K] [Fintype Φ] {n} [∀ τ : Φ, Fintype (n τ)] {κ}
  (e : ∀ τ, n τ ≃ Fin (rankAt n τ))

/-- Over a field K of characteristic zero, two linear maps on coordinate vectors of weight κ
that agree on all S_κ(g)ev, g in ∏_τ GL(n_τ,K), with ev the evaluation vector at the
permutation array of the enumerations e, are equal. -/
lemma PolyRep.ext_schur_weylEval {M} [AddCommGroup M] [Module K M] {L L' : _ →ₗ[K] M} (h :
  ∀ (g : ∀ _, GL _ K) v, v = schur κ (g · |>.1) *ᵥ weylEval n κ (permArray e) → L v = L' v) : L =
  L' := ext_weylEval 1 fun y _ _ ↦ h
  (fun τ ↦ ((isUnit_submatrix_equiv (rowPos n τ).symm (e τ).symm).1 (by simp_all [detPow, minor,
  det_apply, isUnit_iff_isUnit_det, prod_eq_zero_iff])).unit) _ (schur_squarePart_mulVec ..).symm

/-- Schur's lemma: a complex matrix commuting with the Schur matrix S_κ(g) for every tuple g of
unitary matrices g_τ is scalar.

Known result: Contravariant form on Weyl's lattice, Fischer product, irreducibility under U(n). -/
lemma scalar_of_commute_schur {T} (h : ∀ g : ∀ τ, Matrix (n τ) _ ℂ, (∀ τ, (g τ)ᴴ * g τ = 1) →
  Commute T (schur κ g)) : T ∈ Set.range (scalar _) := by
  let v : _ → ℂ := weylEval n κ (permArray (rowPos n)); have H g i := by
    simpa +contextual [Ring.lie_def, ↓map_mulVec, Matrix.map_sub, (h ..).eq, Function.comp_def,
      ← mulVec_mulVec] using
      zariski_dense_unitary (n := n) g ((⁅schur κ (genericMatrixAt ℂ n), T.map C⁆ *ᵥ C ∘ v) i)
  have p i :=
    map_nablaBasis_eq_mul_weylEval (rowPos n) i (fockPairing ℂ (toPoly n κ (T *ᵥ v))) fun k τ a ↦ by
    have := (toPoly_injective (by simp [v, rowSubst_weylKernel_permArray]; rfl) : schur κ (fun σ ↦
      diagonal (if σ = τ ∧ · ≍ a then 2 else 1)) *ᵥ v = (_ : ℂ) • v) ▸ congr(‖$(H _ i)‖)
    simp_all [schur_diagonal, ite_and]
  use ?_, toLin'.injective (ext_schur_weylEval (rowPos n) (by
    simp_all [← funext (H _), -mulVec_mulVec, ← mulVec_smul, v, ← toPoly_weylEval, mul_assoc]
    rw [funext p]; tauto))

section

attribute [local simp] Fin.val_inj filter_eq' prod_eq_zero_iff squarePart schur_squarePart_mulVec
  transpose_map transpose_nonsing_inv eq_inv_smul_iff ite_and minor mul_pow weylRep smul_smul

variable {Φ : Type} {n : Φ → Type} [Fintype Φ] [∀ τ : Φ, Fintype (n τ)] {κ κ' : Φ → ℕ → ℕ}
  (e e' : ∀ τ, n τ ≃ Fin (rankAt n τ)) (he : e' = (e · |>.trans Fin.revPerm))
  (hκ : ∀ τ, ∀ h ∈ Ico 1 (rankAt n τ), κ' τ h = κ τ (rankAt n τ - h))

include he hκ

/-- Let e' be the reversal of the enumerations e, and κ'_τ(h) = κ_τ(|n_τ|−h) for 1 ≤ h < |n_τ|.
Some integer matrix J satisfies J·S_κ(g)·ev_{e'} = ∏_τ det(g_τ)^{Σ_{1≤h<|n_τ|}
κ'_τ(h)}·S_κ'(g^{−T})·ev_e over every commutative ring, for all invertible g; ev_e is
evaluation at the permutation array of e. -/
lemma PolyRep.exists_int_duality_matrix : ∃ J, ∀ R [CommRing R] g, (∀ τ, @IsUnit R _ (g τ).det) →
  map J Int.cast *ᵥ schur κ g *ᵥ weylEval n _ (permArray e') = (∏ τ, (g τ).det ^ diagramWeight
  (rankAt n) κ' (τ, 0)) • (schur κ' fun τ ↦ (g⁻¹ τ)ᵀ) *ᵥ weylEval n _ (permArray e) := by
  let ρ {τ} {h : Fin _} := (Perm.sumCongr 1 Fin.revPerm).trans (finSumFinEquiv.trans
    ((finCongr (Nat.add_sub_of_le h.is_le')).trans (e τ).symm))
  choose π q using fun {τ h} ↦ Perm.exists_smul_eq_embedding (.trans .inl (@ρ τ h).toEmbedding)
  let D {τ h} I := (π I).sign • minor ℤ (Sigma.mk τ ∘ @π τ h I ∘ @ρ τ h ∘ .inr)
  constructor; intro R _ g _; ext i
  have p p : (@squarePart _ R n _ p).Surjective :=
    (⟨fun (a, k) ↦ ∑ b with p _ b = k, · _ a.2 b, by bound⟩)
  obtain ⟨⟨y, w⟩, ⟨z, hz⟩, M⟩ := p e' g, p e fun τ ↦ (g⁻¹ τ)ᵀ, (flip cast (by repeat apply_rules
    [prod_mem_graded, pow_mem_graded, zsmul_mem, minor_mem_nabla] <;> intros) congr(_ ∈ nabla _ _ (∑
    _, $((sum_equiv (.neg _) (by simp) (by rintro ⟨⟨⟩⟩ <;> simp [*, Fin.neg_def])).trans (sum_range
    _).symm))) : ∏ τ, ∏ h, ∏ j, D ⟨_, tableau_col_injective i τ h j⟩ ^ min 1 ↑h ∈ nablaFam ℤ n κ)
  have H τ h I : aeval y (@D τ h I) = (g τ).det * aeval z (minor R (⟨τ, I ·⟩)) := by
    convert congr((π I).sign * $((((squarePart e z τ).submatrix I ρ).fromRows
      (fromCols 0 1)).det_mul_comm (((g τ)ᵀ.submatrix _root_.id (π I)).submatrix ρ ρ))) using 1
    rw [(?_ : _ * _ = fromBlocks 1 0 _ _ᵀ)]
    any_goals rw [det_mul, det_submatrix_equiv_self, ← (submatrix _ I _).fromCols_toCols]
    any_goals simp [D, -squarePart, det_permute', ← zsmul_eq_mul, AlgHom.map_det, -fromCols_toCols]
    any_goals ext ⟨⟩ ⟨⟩ <;> simp [*, -squarePart, -q, ← DFunLike.congr_fun (q I)] <;> rfl
    all_goals congr 2 with; simp [ρ, mul_apply, ← w, *] <;> grind
  convert congr(aeval y $(sum_coords_nablaBasis M)); simp [← w, aeval_def, ← eval_map]; rfl
  simp [↓← hz, nablaBasis, tableauPoly, H, weylEval, ↓prod_pow_eq_pow_sum, diagramWeight,
    Finsupp.single_apply, sum_range]
  congr with <;> congr with ⟨⟨⟩⟩ <;> simp

/-- Duality: for e' reversing the enumerations e and κ'_τ(h) = κ_τ(|n_τ|−h), 1≤h<|n_τ|, some
unimodular integer matrix J has JᵀG_κJ = G_κ' and, over characteristic zero fields, J ev_e =
ev_e' and S_κ(g^{−T})J = ∏det(g_τ)^{−Σ_{1≤i<|n_τ|}κ_τ(i)}·J·S_κ'(g) for invertible g.

Known result: Dual of a Weyl module by Jacobi's complementary minors; Cartan component. -/
lemma exists_dual_isometry : ∃ (J : Matrix ..) (J' :
  Matrix (WeylIndexFam n κ') (WeylIndexFam n κ) ℤ), J * J' = 1 ∧ J' * J = 1 ∧
  Jᵀ * weylGram n κ * J = weylGram n κ' ∧ ∀ R [Field R] [CharZero R], let j := J.map (@Int.cast R _)
  j *ᵥ weylEval n _ (permArray e) = weylEval n κ (permArray e') ∧ ∀ g : ∀ τ, GL (n τ) R, schur κ
    (fun τ ↦ (g τ)⁻¹.1ᵀ) * j = j * weylRep κ' (fun τ ↦ -(Ico 1 (rankAt n τ)).sum (κ τ ·)) g := by
  simp [← (map_injective (algebraMap _ ℂ).injective_int).eq_iff, -algebraMap_int_eq, -Nat.cast_sum]
  refine (exists_int_duality_matrix _ _ he hκ).elim fun K _ ↦ (exists_int_duality_matrix e' e
    (by bound) (by grind)).imp fun J H ↦ ⟨K, toLin'.injective (ext_schur_weylEval e' ?_),
    toLin'.injective (ext_schur_weylEval e ?_), (fun A ↦ ⟨?_, A⟩) fun R ↦ ⟨by simpa using H R 1,
    fun _ ↦ toLin'.injective (ext_schur_weylEval e ?_)⟩⟩ <;> simp +contextual [*, -he,
    sum_Ico_reflect, diagramWeight_apply, ← Ico_add_one_left_eq_Ioo, Units.smul_def]
  refine weylGram_posDef.isUnit.dvd.elim fun T q ↦ q.trans ?_
  obtain ⟨_, rfl⟩ := scalar_of_commute_schur (T := T) fun g h ↦
    weylGram_posDef.isUnit.mul_left_cancel (by simp [← q, weylGram_mul_schur,
    det_ne_zero_of_left_inverse (h _), ← transpose_mul, ← fun (g h : ∀ _, _) ↦ by
                     simpa using (A ℂ).2 fun τ ↦ .mk'' (g τ) (h τ), Units.smul_def,
                     Matrix.mul_assoc _ _ (schur _ _), ← Matrix.mul_assoc, mul_assoc])
  simp [← by simpa [← mulVec_mulVec, ← toBilin'_comp, toBilin'_apply', A, eval_weylKernel_permArray]
    using congr((toBilin' $q).toQuadraticMap (weylEval _ _ (permArray e)))]

end

attribute [local simp ←] Equiv.eq_symm_apply mul_sum coe_weylNormSq rowSubst_branchVector
  diagonal.eq_1 mulVec_mulVec
  submatrix_map vecMul_vecMul coe_eval₂Hom coeff_map eval₂_comp monomial_sum_one weylEval.eq_1

attribute [local simp] Fin.top_eq_last prod_eq_zero_iff Function.comp_def blockScalar.eq_unfold
  squarePart eval_toPoly nablaCombination_weylGramOver_mulVec weylNormSq_weylEval_permArray
  BlockTriangular fromBlocks_transpose mulVec_transpose Matrix.mul_assoc smul_vecMul vecMul_smul
  vecMul_sub aeval_def map_det map_dotProduct map_matrix_mul map_mulVec Units.smul_def permArray
  weylGram_mul_schur diagramWeight_add minor mul_assoc weylRep _root_.zpow_add

variable {n N : Φ → _} [∀ τ, Fintype (n τ)] [∀ τ, Fintype (N τ)] (ι : ∀ τ, n τ ⊕ Unit ≃ N τ) {κ κ₀ :
  Φ → ℕ → ℕ} (e₀ e : Φ → ℤ) (A : Matrix (WeylIndexFam n κ₀) (WeylIndexFam N κ) ℂ) {γ κ' : Φ → ℕ → ℕ}

/-- The property of A that every complex matrix T with Tρ_{κ,e}(diag(g,1)) = ρ_{κ₀,e₀}(g)T for
all tuples g of unitary matrices (ρ = `weylRep`) is a scalar multiple of A. -/
def SpansBranchingMaps := ∀ T, (∀ g : ∀ _, GL _ ℂ, (∀ τ, (g τ).1ᴴ * (g τ).1 = 1) → ∃ x,
    (∀ τ, (x τ).1 = blockScalar ι (g · |>.1) 1 τ) ∧ T * weylRep κ e x = weylRep κ₀ e₀ g * T) →
  ∃ a : ℂ, T = a • A

open Norms.L2Operator

/-- There is a complex vector v whose images S_κ(diag(g,1))v, for g ranging over tuples of lower
triangular matrices on the rows n_τ, span the whole space: a row vector r killing all of
them is zero. -/
lemma PolyRep.exists_cyclic_lower_triangular κ : ∃ v, ∀ r, (∀ g, (∀ τ, (g τ)ᵀ.BlockTriangular
  (rowPos n τ)) → r ⬝ᵥ schur κ (blockScalar ι g 1) *ᵥ v = (0 : ℂ)) → r = 0 := by
  let E := newRowOrder ι ⊤; let u τ := of fun a c ↦ ite (a = ι τ (.inr ()) ∨ a = c) (1 : ℂ) 0
  let U := ((by constructor <;> simp [funext_iff] <;> grind : IsLinearMap ℂ fun (M : type_of% u) τ ↦
    of fun a c ↦ ite (E τ a < E τ c) (M τ a c) 0 + ite (a = c) (M τ (ι τ (.inr ())) c -
    ∑ d with E τ d < E τ c, M τ d c) 0).mk' _).toContinuousLinearMap
  let v := weylEval (R := ℂ) N κ (permArray E); use schur κ u *ᵥ v, fun r h ↦
    (dotProductEquiv ..).injective (ext_schur_weylEval E fun g ↦ ?_)
  simpa using eq_zero_of_submersion (analyticOnNhd_evalMat (P :=
    C ∘ r ⬝ᵥ schur κ (genericMatrixAt ℂ _) *ᵥ C ∘ v)) (((1 - u •
    U).hasStrictFDerivAt.const_add u).fun_mul' (U.hasStrictFDerivAt.const_add 1)) (a := 0)
    (by bound) (.of_forall fun M ↦ let g τ := ((1 + M - U M) τ).submatrix (ι τ ∘ .inl) (ι τ ∘ .inl)
    have ⟨l, k⟩ : _ ∧ u + (1 - u • U) M = blockScalar ι g 1 * u := .imp_left (h g) (by
      simp [funext_iff, entrywise, reindex_equiv (ι _), u, U, E, newRowOrder, sum_filter,
        g]; grind-order)
    by simp [↓k, -Pi.smul_apply, l, -blockScalar.eq_unfold, schur_mul_left, (toPoly_injective
      (by simpa [v] using (rowSubst_weylKernel_permArray _ _ (by simp [U]; grind))) :
      schur κ (1 + U M ·) *ᵥ v = (_ : ℂ) • v)]) _

attribute [-simp] finRotate_symm_apply in
/-- If c·K_{γ(·+1)}·K_{κ'} = `toPoly` η, η integral of type κ₀ (kernels `weylKernel` at the
cyclic shift and at 1), some integer matrix B has BᵀG·ev₁ = coordinates of c·`PolyRep.branchVector`
over ℂ, and B·S_{γ+κ'}(diag(g,s)) = ∏_τ s_τ^{∑_{0<h≤|n_τ|} γ_τ(h)}
det(g_τ)^{κ'_τ(|n_τ|)}·S_{κ₀}(g)·B over fields of characteristic 0. -/
lemma PolyRep.exists_int_branching_of_weylKernel {c : ℤ} {η : _ → ℤ} (hη :
  c • (weylKernel n (γ · <| · + 1) (permArray fun τ a ↦
  (finRotate _).symm (rowPos n τ a)) * weylKernel n κ' (permArray (rowPos n))) = toPoly n κ₀ η) :
  ∃ B : Matrix _ _ ℤ, nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀ (permArray
  (rowPos n))) ᵥ* B.map (↑)) = (c : ℂ) • branchVector ℂ ι γ κ' ∧ ∀ R [Field R] [CharZero R] g (s :
  _ → R), let b := B.map (@Int.cast R _); b * schur (γ + κ') (blockScalar ι g s) = (∏ τ, s τ ^
    diagramWeight (rankAt N) γ (τ, 0) * (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * b) := by
  let K {S} [CommRing S] x y := eval y
    (rowSubst (blockScalar ι (fun τ ↦ (squarePart (rowPos n) x τ)ᵀ) 1) (branchVector S ι γ κ'))
  let L S [CommRing S] := .mulRight S (detPow S n fun τ ↦ κ' τ (rankAt n τ)) ∘ₗ toPoly n κ₀
  have A S T [CommRing S] [CommRing T] (φ : S →+* T) x y : φ (K x y) = K (φ <| x ·) (φ <| y ·) := by
    simp [K, branchVector, weylKernel, eval_rowSubst, reindex_equiv (ι _), map_eval, apply_ite]
  have Z S [CommRing S] b x y : K x _ = _ * K x y := mem_nabla.1 (rowSubst_mem_nabla _
    (by apply_rules [mul_mem_graded, weylKernel_mem_nablaFam])) S b y
  have G {S} [CommRing S] [IsDomain S] [CharZero S] g θ : L S ((∏ τ, (g τ).det ^ κ' τ
    (rankAt n τ)) • schur _ g *ᵥ θ) = rowSubst (fun τ ↦ (g τ)ᵀ) (L _ θ) := by simp [L]
  have R y (Y : ∀ τ j, y (⟨τ, ι τ (.inr ())⟩, j + 1) = 0) : ∃ θ, ∀ x,
    eval x (L (MatrixPoly (Sigma N) ℤ) θ) = c * K x y :=
    ⟨(∏ τ, ∏ h ∈ range (rankAt n τ), y (⟨τ, ι τ (.inr ())⟩, 0) ^ γ τ (h + 1)) • _, fun x ↦ by
    rw [map_smul, G (fun τ ↦ of (y ⟨⟨τ, ι τ <| .inl ·⟩, rowPos n τ ·⟩)) (C ∘ η),
      LinearMap.comp_apply]
    simp [↓← map_toPoly, ← hη, K, branchVector, weylKernel, rowSubst_highestPoly, rankAt_eq_succ ι,
      detPow, eval_rowSubst, mul_comm _ (x _),
      prod_range_succ' (_ ^ γ _ ·), prod_range_succ, Matrix.map, -permArray]
    simp [det_succ_row_zero', Fin.sum_univ_succ, reindex_equiv (ι _), newRowOrder, mul_pow,
      submatrix, Y]
    rw [mul_left_comm]; clear * -; conv_rhs => simp +singlePass [← det_transpose]
    congr! <;> simp +instances (disch := grind) [ite_eq_right, ← Fin.eq_mk_iff_val_eq,
      Nat.mod_eq_of_lt, Fin.add_def] <;> rfl⟩
  obtain ⟨⟨θ, H⟩, _, s⟩ := R (borelMul (·.1) (fun (τ, i, j) ↦ ite (i = j) 1 (ite (i = 0) (-1) 0) *
    X (⟨τ, ι τ (.inr ())⟩, j - i)) X) (by simp [borelMul, sum_range_succ', mul_comm]),
    nabla_le_span_nablaBasis_mul_detPow
    (κ := γ + κ') 0 (x := c • K (C ∘ @X ℤ _ _) X) (by simp [mem_nabla, *, mul_left_comm])
  simp [Z, Int.cast_comm, X_pow_eq_monomial, Finsupp.prod] at H
  choose B l using coord_mem_of_coeff_mem (L ℤ).range.toAddSubgroup _ s fun δ ↦
    ⟨_, funext fun x ↦ by
    simpa [← map_nablaBasis C, ← map_detPow C, L, weylEval, entrywise, -map_nablaBasis, -map_detPow,
      A, coeff_sum, mul_comm (eval x _), ← Int.cast_comm, ← zsmul_eq_mul, -Function.comp_def] using!
      (congrArg (AddMonoidAlgebra.coeff · (_ + δ)) (H (C ∘ x))).trans (coeff_monomial_mul ..)⟩
  have k {T} [CommRing T] y x : eval x (L T ((of B)ᵀ.map (↑) *ᵥ weylEval N _ y)) = c * K x y := by
    simpa [← eval_map, dotProduct, L, ← l, A, weylEval, mulVec_eq_sum, smul_eq_C_mul,
      mul_comm (eval y _), Fintype.linearCombination_apply] using congr(eval₂ (aeval x).1 y $s)
  use (of B)ᵀ, funext fun y ↦ ?_, fun S _ _ g s ↦ toLin'.injective (ext_weylEval 0 fun y _ _ ↦
    toPoly_injective (isRegular_detPow.2 (funext (by
    simp [schur_mulVec_weylEval_of_detExp_zero, *, mul_smul, eval_rowSubst (n' := n), K,
      ← eval_rowSubst, -blockScalar.eq_unfold, mul_left_comm]
    simp [← smul_eval, ← map_smul, rowSubst_rowSubst, mul_comm (g ..)]
    tauto) : L _ _ = L _ _)))
  simpa [Fintype.linearCombination_apply, K, L, detPow, ← dotProduct.eq_1, dotProduct_mulVec,
    Fin.val_inj, Matrix.map.eq_1 (of _), vecMul_mulVec, ← transpose_map, weylGram_isSymm.eq] using
    k y (permArray (rowPos n))

/-- Branching from rank n+1 to n = |n_τ|: let κ = γ+κ', κ₀(h) = κ'(h)+γ(h+1) for 0<h<n, e₀ =
e+κ'(n), κ'(i) = 0 for i<q. Some integer matrix br satisfies `SpansBranchingMaps`,
br·ρ_{κ,e}(diag(g,s)) = ∏_τ s_τ^{e_τ+∑_{1≤h≤n}γ_τ(h)}·ρ_{κ₀,e₀}(g)·br over fields of
characteristic 0, and ‖br‖ ≤ L^{3L} in Gram norms whenever L ≥ ∑_τ∑_{q≤h<n} hκ₀(h).

Known result: Branching from GL(n+1) to GL(n) with multiplicity one. -/
lemma exists_branching_matrix κ₀ q (e e₀ : Φ → ℤ) (k : γ + κ' = κ) (h₀ : ∀ τ,
  ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = κ' τ h + γ τ (h + 1)) (hq : ∀ τ, ∀ i < q, κ' τ i = 0) (h₁ :
  ∀ τ, e₀ τ = e τ + κ' τ (rankAt n τ)) : ∃ br : Matrix (WeylIndexFam n κ₀) (WeylIndexFam N κ) ℤ,
  (∀ R [Field R] [CharZero R] g (s : Φ → Rˣ) x, (∀ τ, (x τ).1 = blockScalar ι
  (g · |>.1) (s · |>.1) τ) → br.map (@Int.cast R _) * weylRep κ e x = (∏ τ,
  s τ ^ (diagramWeight (rankAt N) γ (τ, 0) + e τ)) • (weylRep κ₀ e₀ g * br.map (@Int.cast R _))) ∧
  (∀ L, ∑ τ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → ∀ ξ, weylNormSq (br.map (↑) *ᵥ ξ) ≤
  ((L ^ L) ^ 3) ^ 2 * weylNormSq ξ) ∧ SpansBranchingMaps ι e₀ e (br.map (↑)) := by
  obtain ⟨⟨v, hv⟩, I, rfl, c, hc, hA, η, hη⟩ := exists_cyclic_lower_triangular ι κ,
    (@weylGram_posDef _ _ N _ κ).isUnit.invertible, k, exists_smul_weylKernel_mul_eq_toPoly
    (rowPos n · |>.trans (finRotate _).symm) (by simp; grind [Fin.val_sub_one_of_ne_zero]) hq h₀
  obtain ⟨B, ha, he⟩ := exists_int_branching_of_weylKernel ι hη; set G₀ :=
    weylGramOver (R := ℂ) (n := n); set x := G₀ *ᵥ _
  have E := by simpa using (he ℂ · 1)
  use B, by simp_all [mul_zpow, smul_smul, mul_left_comm], fun A H ξ ↦ ?_, fun T l ↦ ?_
  set T := map B _; have hC := weylGramOver.mul_invOf_cancel_left (Tᵀ * G₀); set C :=
    I.1 * (Tᵀ * G₀)
  let w := C *ᵥ weylEval n _ (permArray (rowPos n)); trans weylNormSq w * weylNormSq ξ
  obtain ⟨⟨m, hm⟩, p, q⟩ := scalar_of_commute_schur (T := T * C) fun g u ↦ by
    simpa [commute_iff_eq, det_ne_zero_of_left_inverse (u _),
      (weylGramOver.mul_right_injective_of_invertible
      (by simpa [hC, G₀, ← weylGramOver.mul_assoc] using congr($(E _)ᵀ * G₀)) : schur (γ + κ')
      (blockScalar ι g 1) * C = (_ : ℂ) • C * schur κ₀ g), -blockScalar.eq_unfold]
      using congr($(he ℂ g 1) * C), mul_nonneg (weylNormSq_nonneg ξ) (weylNormSq_nonneg w),
    posDef_cauchy_schwarz weylGram_posDef (C *ᵥ T *ᵥ ξ) ξ
  simp [w, weylNormSq.eq_1 (C *ᵥ _), star_mulVec_dotProduct C, T, mulVec_mulVec _ T, ← hm, by
    simpa [weylGram_posDef.1.eq, transpose_conjTranspose, G₀] using
      (congr($hCᴴ *ᵥ ·))] at *; nlinarith
  grw [weylNormSq_le_mul_of_toPoly_eq (by
    rw [map_smul, toPoly_weylEval, toPoly_weylEval, ← nablaCombination_weylGramOver_mulVec,
      mulVec_mulVec, hC]
    simpa), weylNormSq_smul, Complex.norm_intCast, hA _ H] <;> simp
  let D {R} [CommRing R] g := mulRightLinearMap _ R (schur (γ + κ') (blockScalar (R := R) ι g 1)) -
    (∏ τ, (g τ).det ^ κ' τ (rankAt n τ)) • mulLeftLinearMap _ R (schur κ₀ g)
  have top T (hT : ∀ g, D g T = 0) (h : x ᵥ* T ⬝ᵥ v = 0) : T = 0 :=
    have hT := by simpa [D] using (congr(x ᵥ* $(hT ·)))
    transpose_injective (mul_left_injective_of_inv _ _ weylGram_posDef.isUnit.mul_val_inv
    (toLin'.injective (ext_schur_weylEval _ fun g ↦ by simpa [mulVec_mulVec _ weylGramOver,
      (hv (x ᵥ* T) fun g l ↦ by simp [hT, h, dotProduct_mulVec,
      (by simpa [vecMul_schur_eq_iff, x, G₀] using rowSubst_weylKernel_permArray _ _ l :
      x ᵥ* schur _ g = (_ : ℂ) • x)])] using (hT (g · |>.1.transpose)).symm)))
  exact ⟨_, sub_eq_zero.1 (top _ (fun g ↦ by ext; simpa [map_sub, D, E] using
    (zariski_dense_unitary g (D (genericMatrixAt ℂ _) (T.map C) _ _) fun g u ↦
    (l (⟨_, _, mul_eq_one_symm <| u ·, u _⟩) u).elim fun x ⟨y,
    h⟩ ↦ by simpa [D, h₁, y, det_ne_zero_of_left_inverse (u _)] using congr($h _ _))) (by
    simp [← div_eq_iff (mt (top _ (sub_eq_zero.2 <| E ·)) (by simpa [·, branchVector, hc.ne',
      (ne_zero_of_map (ne_zero_of_eq_one (eval_weylKernel_permArray _)))] using ha.symm))]; rfl))⟩
