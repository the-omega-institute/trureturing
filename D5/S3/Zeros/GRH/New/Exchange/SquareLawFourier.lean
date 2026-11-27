/- GID: D5/S3/Zeros/GRH/New/Exchange/SquareLawFourier
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/SquareLawFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.SquareLawFourier. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/SquareLawFourier.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.BlockPartners
import D5.S3.Zeros.GRH.New.Exchange.DeterminantVectors
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Lift then descent is proportional to descent then lift (see New.Exchange.OneSquare).

Part of: Injectivity and norm of a chain of theta lifts (see New.Exchange.TriangleArrows).

This file: Theta integrals under change to an isometric or opposite hermitian space. Finite-ring
algebra of partner functions: shear identity and kernel with root-of-unity coefficients. Square
identity for Fourier-transformed data over a finite ring, via matrix Gauss sums. -/

noncomputable section

open Matrix MeasureTheory Space G MatMul Finset BigOperators Equiv Fintype Function MulChar
  IsPartner

section

variable {E} [Field E] [CMType E] {n a} [Fintype n] [Fintype a] {s t}
  (W W₁ : Space E n s) (V V₁ : Space E a t)

attribute [mk_iff] IsForm Space.IsAutomorphic

/-- Let W, S have opposite signs and the same rational points under `G.neg`. Then F is a
form of type typeKernel l on S iff its pull-back is one on W, and integrals over the two quotients
agree under pull-back. -/
-- Full names are used in the default tactic, since it runs in the scope of the caller.

lemma isForm_neg_iff_and_integral_neg (S : Space E _ (-s)) (Γ : ∀ g, G.neg g ∈ S.Γ ↔ g ∈ W.Γ := by
  simp [Space.neg, flipSpace, Space.mem_Γ_iff_range, ← map_inv, ← smul_one_eq_diagonal, ← mul_assoc,
    ← star_mul]) : (∀ l F, W.IsForm (typeKernel l s) (F <| G.neg ·) ↔ S.IsForm (typeKernel l (-s))
  F) ∧ ∀ F : _ → ℂ, integral S.quotMeasure F = ∫ g, F g.neg ∂W.quotMeasure := by
  have m h :=
    measurePreserving_haarU 1 1 (-1) (.subtypeEquivRight h : USign s ≃ USign (-s)) (by simp)
  simp_rw [isForm_iff, isAutomorphic_iff, quotMeasure]; generalize W.Γ = Γ' at *
  delta HasLevel realConv typeKernel dsKernel formalDegree dsCoeff blockDiagPart flenstedJensen
    kTypeNormSq lowestKType haarK maxCompactU G.neg USign G GInf measureSpaceU at *
  simp_rw [Pi.neg_apply, neg_inj]; generalize_proofs at *
  generalize U (signMatrix s) = H, haarU (signMatrix s) = quotMeasure at *
  subst_vars; cases Subgroup.ext Γ; cases Measure.map_id ▸ (m (by simp)).2; bound

/-- If the points of W and W₁ differ by a rational matrix and k in G, and V, V₁ have the same
signs, the theta integral for (W, V) at g is that for (W₁, V₁) at kg times a constant of
modulus 1. -/
lemma thetaLarge_move [WeilData E] (c : GL n E) (k : G E s) (hk : W.x =
  (c.map toAdele)⁻¹ * W₁.x * k.toUnitary) {μ} (𝔠 : SplitTameChar E μ) : ∃ u : Circle, ∀ v Φ g,
  thetaLarge W V 𝔠 v Φ g = u * thetaLarge W₁ V₁ 𝔠 v Φ (k * g) := by
  obtain ⟨⟨c', k', w, _⟩, a, q⟩ := V₁.exists_eq_move V, (W.hom V).exists_mapsTo_ratVectors
  use (rankTwist 𝔠.ν⁻¹ n).1 (k.det / k'.det), fun f Φ g ↦
    .symm ?_; delta thetaLarge thetaIntegral localDatum name
  rw [← (identDistrib_orbitMeasure_comp (H := V.Γ) (measurePreserving_count
    ((MulAut.conj k').subtypeEquiv (by simp [Γ, reindex_equiv (U.conj _ w), *])))
    (measurePreserving_mul_left _ k') (by simp [Subgroup.smul_def, mul_assoc])
    ((pairThetaKer ..).swap.theta_rat_mul _ ·.2)).integral_eq, ← integral_const_mul]
  congr!; simp [← Prod.mk_mul_mk, pairTheta, pairWeil, -θ_apply]
  rw [← ext_of_vacElem _ a (T := (W₁.hom V₁).θ ∘L ω _ (onHom (k, k'))) fun z ↦
    (congrArg _ (rep_apply_apply ..)).trans ((theta_vacElem_eq_prod_lineTheta (fun y h ↦ ?_)
    z).trans (theta_vacElem_eq_prod_lineTheta q z).symm)]
  simp [field]; rfl
  rw [mul_smul, smul_eq_mat_mulVec, onHom_mulVec, mem_ratVectors_hom]
  exact (mem_ratVectors_hom.1 (q y h)).imp' (c'.1 * · * c⁻¹.1) (by simp_all [mat,
               ← (c'.map _).1.mul_assoc, ← GeneralLinearGroup.val_map_apply, -coe_units_inv])

variable {R : Type} [CommRing R] [Fintype R] {a b N n : Type} [Fintype a] [Fintype b] [Fintype N]
  [Fintype n] (χ : MulChar R ℂ) (e : b ⊕ a ≃ n)

/-- L and L′ transform by χ∘det under left, respectively right, multiplication by invertible
matrices, and ΣΨL′ = c·ΣΦL for all partners Φ, Ψ (`IsPartner`). -/
structure SquareLaw σ c (L : Matrix a n R → ℂ) (L' : Matrix n b R → ℂ) where
  left_mul (k : GL a R) x : L (k.1 * x) = χ k.1.det * L x
  right_mul (k : GL b R) y : L' (y * k.1) = χ k.1.det * L' y
  partners Φ Ψ : IsPartner ⊤ σ χ Φ Ψ → ∑ y, Ψ y * L' y = c * ∑ x, Φ x * L x

/-- The point datum: the indicator function of the block matrix (1; 0) among (a⊕b)×a matrices over
R. -/
abbrev inclusionDatum (R : Type) [CommRing R] {a b : Type} : Matrix (a ⊕ b) a R → ℂ :=
  Pi.single (inclMatrix R .inl) 1

/-- From p on n×a matrices, the function on (n⊕b)×(a⊕b) matrices sending [[y,*],[0,1]] to p(−y)
divided by the number of n×b matrices, and other matrices to 0. -/
def nextDatum (p : _ → ℂ) (y : Matrix (n ⊕ b) (a ⊕ b) R) := if y.toBlocks₂₂ = 1 ∧
  y.toBlocks₂₁ = 0 then p (-y.toBlocks₁₁) / card (Matrix n b R) else 0

/-- The bijection a⊕(n⊕b) → n⊕(a⊕b) that exchanges the first two summands. -/
def swapFirstTwo : a ⊕ n ⊕ b ≃ n ⊕ a ⊕ b := (sumAssoc ..).symm.trans
    (((sumComm ..).sumCongr (.refl _)).trans (sumAssoc ..))

omit [CommRing R] in
lemma sum_eq_sum_fromRows (f : Matrix (N ⊕ n) a R → ℂ) :
    ∑ w, f w = ∑ y, ∑ z, f (fromRows y z) := (sumPiEquivProdPi _).symm.sum_comp f ▸ sum_prod_type _

omit [CommRing R] in
lemma sum_eq_sum_fromCols (f : Matrix a (N ⊕ n) R → ℂ) : ∑ w, f w = ∑ z, ∑ y, f (fromCols y z) :=
  Bijective.sum_comp ⟨fromCols_inj.uncurry, (⟨(_, _), ·.fromCols_toCols⟩)⟩ f ▸ sum_prod_type_right _

omit [Fintype R] in
lemma injective_gl_inv_mul_mul (f : GL a R) (g : GL b R) : Injective (f⁻¹.1 * · * g.1 : Matrix a b
  R → _) := (mul_left_injective_of_invertible _).comp (mul_right_injective_of_invertible _)

attribute [local simp] inv_mul_eq_iff_eq_mul_of_invertible Matrix.mul_apply
  mul_inv_eq_iff_eq_mul_of_invertible apply_eq_zero_iff inv_apply_eq_inv' NNRat.smul_def
  Units.val_inj div_eq_inv_mul dotProduct inclMatrix mem_intGL mul_assoc neg_eq_iff_eq_neg nextDatum
  sum_eq_sum_fromCols

omit [Fintype R] [Fintype a] [Fintype b] in
lemma inclMatrix_inl : inclMatrix R .inl = fromRows 1 (0 : Matrix b a R) := by aesop

/-- If c, L, L′ satisfy `SquareLaw`, then |GL_a(R)|·Σ_y p(y)L′(y; 1₀) = c·|GL_{n⊕b}(R)|·Σ_x
p⁺(x)L(1₀, x) for all p, where 1₀ is the standard inclusion matrix in the other block and
p⁺ = `nextDatum` p. -/
lemma SquareLaw.sum_eq_nextDatum {χ c L L'} (h : SquareLaw χ (@swapFirstTwo a b n) c L L') p :
  card (GL a R) * ∑ y, p y * L' (fromRows y (inclMatrix R .inl)) = c * card (GL (n ⊕ b) R) * ∑ x,
  nextDatum p x * L (fromCols (inclMatrix R .inl) x) := by
  rw [← neg_bijective.sum_comp, ← Fintype.expect_const (ι := Matrix n b R) (_ * _), expect]
  simp [sum_eq_sum_fromRows, ite_and, mul_sum, -sum_const]
  congr! 2 with s _ x
  set w := x.fromRows 0
  set σ := swapFirstTwo
  obtain ⟨t, l, r⟩ := h.partners _ _ (partner_block σ χ (Pi.single w 1)),
    (submatrix_mul_equiv _ (w.fromCols 1) id (.refl _) σ.symm ▸ h.left_mul · _),
    ((fromRows 1 (-w)).submatrix_mul_equiv _ σ.symm (.refl _) id ▸ h.right_mul · _)
  simp_all [reindex_equiv (Matrix.reindex σ (.refl _)),
    sum_eq_sum_fromRows (N := a), ↓reindex_equiv (Matrix.reindex (.refl _) σ),
    ← fun m [Fintype m] (f : Matrix m m R → ℂ) ↦ sum_of_injective _ Units.val_injective _ (fun u ↦
    (χ u.det)⁻¹ * f u) (by simp [mt ·.isUnit_iff_isUnit_det.2 ·]) (by tauto), ← mul_sum, -mul_ite]
  erw [congr(L $(?_)).trans (l (.mk'' (fromBlocks 1 s 0 1) _)), congr(L' $(?_)).trans (r 1)] <;>
    simp_all [← ext_iff, w, σ, swapFirstTwo]; grind

/-- The homomorphism g ↦ diag(g, 1) from GL_b(R) to GL_n(R), the indices matched by e. -/
abbrev blockInlGL := (reindexGL e).toMonoidHom.comp (blockGL (R := R).comp (.inl ..))

/-- The kernel with δ(x_k, y_k) = χ(det k)/|GL_b(R)| for k in GL_n(R), x_k = `invLastRows`, y_k =
`firstCols`, and δ = 0 on all other pairs of matrices. -/
def graphKernel x y :=
  Function.extend (Function.prod (invLastRows e) (firstCols e)) (χ ·.1.det / card (GL b R)) 0 (x, y)

@[local simp] lemma graphKernel_invLastRows_firstCols k : graphKernel χ e (invLastRows e k)
  (firstCols e k) = χ k.1.det / card (GL b R) := FactorsThrough.extend_apply (fun k ↦ by grind
  [congr(Matrix.det $(invFirstRows_mul_firstCols e k))]) ..

omit [Fintype a] in
lemma exists_eq_of_graphKernel_ne_zero x y : graphKernel χ e x y ≠ 0 → ∃ k,
  (invLastRows e k, firstCols e k) = (x, y) := by simp [graphKernel, Function.extend]

/-- Equivariance of the kernel δ = `graphKernel`: δ(x, y) = χ(det g · (det f)⁻¹ · (det q)⁻¹)
δ(f⁻¹xg, g⁻¹yq) for g in GL_n(R), f in GL_a(R), q in GL_b(R). -/
lemma graphKernel_equivariant (g : GL n R) (f : GL a R) (q : GL b R) x y : graphKernel χ e x y =
  χ g.1.det / χ f.1.det / χ q.1.det * graphKernel χ e (f⁻¹.1 * x * g.1) (g⁻¹.1 * y * q.1) := by
  wlog! n : graphKernel χ e x y ≠ 0
  · simpa [n] using this χ e g⁻¹ f⁻¹ q⁻¹ (f⁻¹.1 * x * g.1) (g⁻¹.1 * y * q.1)
  obtain ⟨k, ⟨⟩⟩ := exists_eq_of_graphKernel_ne_zero χ e _ _ n
  nth_rw 2 [(congrArg₂ _ ?_ ?_).trans (graphKernel_invLastRows_firstCols χ e (g⁻¹ * k * reindexGL e
    (blockGL (q, f))))] <;> simp [← ext_iff, reindex_equiv e, ← χ.inv_apply, field, ← map_inv]

@[local simp] lemma graphKernel_mul_right x y (g : GL b R) : graphKernel χ e x (y * g.1) =
  χ g.1.det * graphKernel χ e x y := by simp [graphKernel_equivariant χ e 1 1 g x y]

/-- If Ψ(yg) = χ⁻¹(det g)Ψ(y) for all y and all g in GL_b(R), then ∑_y δ(x_k, y)Ψ(y) = χ(det
k)Ψ(y_k) for every k in GL_n(R), with δ = `graphKernel`. -/
lemma sum_graphKernel_mul (Ψ : _ → ℂ) (h : ∀ y (g : GL b R), Ψ (y * g.1) = χ⁻¹ g.1.det * Ψ y) k :
    ∑ y, graphKernel χ e (invLastRows e k) y * Ψ y = χ k.1.det * Ψ (firstCols e k) := by
  refine (sum_of_injective _ ((mul_right_injective_of_inv _ _ (invFirstRows_mul_firstCols e k)).comp
    Units.val_injective) _ _ (fun y ↦
    Not.imp_symm ((fun ⟨l, _⟩ ↦ ⟨⟨invFirstRows e k * y, invFirstRows e l *
    firstCols e k, ?_, ?_⟩, ?_⟩) ∘ exists_eq_of_graphKernel_ne_zero χ e _ y ∘ left_ne_zero_of_mul))
    (by tauto)).symm.trans (by simp [h, mul_left_comm _ (χ _)⁻¹]) <;> grind [Matrix.mul_assoc]

/-- For finite R with `IsValuationPair`, δ = `graphKernel`: for some d, nonzero d(y)δ(x,y) are
roots of unity passing left inverses from blocks of y to opposite blocks of x; d(yk)δ(x,y)
averages to δ; `SquareLaw` gives L'(y) = c∑δ(x,y)L(x) when y has a left invertible block. -/
lemma exists_partner_kernel (e : b ⊕ a ≃ N ⊕ n) (val : @IsValuationPair R _ ⊤) : ∃ d : _ → ℂ,
  (∀ x y, (d y * graphKernel χ e x y ≠ 0 → IsOfFinOrder (d y * graphKernel χ e x y) ∧ (HasLeftInv
  y.toRows₁ → HasLeftInv x.toCols₂) ∧ (HasLeftInv y.toRows₂ → HasLeftInv x.toCols₁)) ∧ 𝔼 k : GL b R,
  d (y * k.1) * graphKernel χ e x y = graphKernel χ e x y) ∧ ∀ c L L', SquareLaw χ e c L L' → ∀ y,
  HasLeftInv y.toRows₁ ∨ HasLeftInv y.toRows₂ → L' y = c * ∑ x, graphKernel χ e x y * L x := by
  use fun y ↦ ite (y = (@Set.range_nonempty _ (GL b R) _ (y * ·.1)).some) (card (GL b R)) 0,
    fun x y ↦ ?_, fun c L L' h y i ↦ ?_
  · generalize_proofs o
    have F (k : GL b R) := by simpa [comp_def] using (mul_left_surjective k).range_comp (y * ·.1)
    obtain ⟨⟨l, p⟩, h | ⟨k, ⟨⟩⟩⟩ := o.some_mem,
      or_not.imp_right (exists_eq_of_graphKernel_ne_zero χ e x y)
    · simp [h]
    have Y s h : HasLeftInv _ := ⟨_, (submatrix_id_mul_right ..).trans (nonsing_inv_mul _
      (.of_mul_eq_one _ (det_fromRows_invLastRows e k s ▸ congr(Matrix.det $h).trans det_one)))⟩
    refine ⟨fun _ ↦ ⟨cast ?_ (χ.1.isOfFinOrder k.det.isUnit.isOfFinOrder),
      fun ⟨L, h⟩ ↦ (Y (L.fromCols 0) ?_).imp' toBlocks₂₂ ?_, fun ⟨L, h⟩ ↦ (Y
      (fromCols 0 L) ?_).imp' toBlocks₁₂ ?_⟩, by simp [← p, F, (mul_right_injective_of_inv _ _
      (invFirstRows_mul_firstCols ..)).eq_iff]⟩ <;> simp_all [← ext_iff, toBlocks₁₂, toBlocks₂₂]
  obtain ⟨j, -, rfl⟩ := (val.exists_firstCols_iff (y := y) e).2 (by refine ⟨?_, i.elim (.imp'
                 (·.fromCols 0) ?_) (.imp' (fromCols 0) ?_)⟩ <;> simp [IsIntMatrix, ← ext_iff])
  have := (fun Ψ ↦ h.partners (graphKernel χ e · ⬝ᵥ Ψ) Ψ) (graphKernel χ⁻¹ e (invLastRows e j))
    ⟨?_, ?_, ?_⟩ <;> simp_all [↓sum_graphKernel_mul, h.right_mul, mul_left_comm c, ← mul_sum,
    mul_comm (graphKernel χ ..)] <;> grind [exists_eq_of_graphKernel_ne_zero]

end

attribute [local simp] nextDatum trace ite_and mul_assoc pow_add pow_mul

/-- For ψ, χ primitive, some γ with |γ|²|R|^{t(t+2n)} = 1 (n = #N, t = #T) has Σ_y 𝓕(p̄)(y)L′(y;
1₀) = γc·Σ_x 𝓕(conj p⁺)(x)L(1₀, x) for all p and c, L, L′ satisfying `SquareLaw`; 1₀ is
the standard inclusion, p⁺ = `nextDatum` p. -/
lemma SquareLaw.sum_fourier_eq_nextDatum {R} [CommRing R] [Fintype R] N T [Fintype N] [Fintype T]
  {χ ψ} (hψ : AddChar.IsPrimitive ψ) (hχ : IsPrimitiveMulChar χ) : ∃ γ, ‖γ‖ ^ 2 * card R ^ (card T *
  (card T + card N * 2)) = 1 ∧ ∀ {c L L'} p, SquareLaw χ (@swapFirstTwo (N ⊕ T) T N) c L L' → ∑ y,
  matrixFourier ψ (star p) y * L' (fromRows y (inclMatrix R .inl)) = γ * c * ∑ x, matrixFourier ψ
  (star (nextDatum p)) x * L (fromCols (inclMatrix R .inl) x) := ⟨star _ / card (Matrix (T ⊕ N) T
  R), by simpa [card_congr of.symm, field] using
  congr(‖$((matrix_gauss_sum (a := T) hψ hχ _ (by simp)).2)‖), @fun c L _ p h ↦ by
  rcases h.sum_eq_nextDatum (matrixFourier ψ (star p)), fun x y ↦
    (matrix_gauss_sum hψ hχ (L ∘ fromCols (inclMatrix R .inl) ∘ fromBlocks x
    y 0) fun g d ↦ by convert! h.left_mul (blockGL (1, g)) _ <;> simp [inclMatrix_inl]).2.symm
  conv_rhs =>
    enter [2, 2, x]
    rw [← x.fromBlocks_toBlocks, matrixFourier, sum_eq_sum_fromRows]
    simp [apply_ite, sum_eq_sum_fromCols, ← mul_assoc, ψ.map_add_eq_mul, ← sum_mul, ← mul_sum]
    erw [sum_addChar_trace_mul hψ, mul_right_comm, ← neg_bijective.sum_comp]
  simp_all [matrixFourier, mul_left_comm c, sum_eq_sum_fromRows (a := _ ⊕ _),
    sum_eq_sum_fromCols (N := _ ⊕ _), div_eq_inv_mul,
   ← mul_sum, ← eq_div_iff, card_congr of.symm, mul_comm (∑ _, starRingEnd _ (p _) * _)]
  simp [sum_mul]⟩
