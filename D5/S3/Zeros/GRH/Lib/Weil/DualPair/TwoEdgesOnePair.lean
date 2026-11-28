/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/TwoEdgesOnePair
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/TwoEdgesOnePair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.TwoEdgesOnePair. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/TwoEdgesOnePair.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.Flip
import D5.S3.Zeros.GRH.Lib.Weil.Periods.BesselIntegral
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Heisenberg group law and its normalisation by the dual pair, in rational coordinates.
Parabolic elements act on the zero term along an isotropic subspace; determinant bookkeeping. Tensor
of two Weil representations as one pair via adjoint; theta kernels multiply. -/
seal Finset.univ Finset.sum Finset.prod

lemma x_inv_mulVec_matToVec {E ι ι'} [Field E] [CMType E] [Fintype ι] [Fintype ι'] {ε ε'} {V :
  Space E ι ε} {V' : Space E ι' ε'} w : (V.hom V').x⁻¹.1.mulVec (matToVec w) = V.homAtPoint V' w :=
  kronecker_mulVec_eq_matToVec ..

section

open Matrix Kronecker Space Splitting Subtype WeilData MatMul
variable {E n n₀ : Type} [Field E] [CMType E] [Fintype n] [Fintype n₀]
  {t t₀ m g g₀ u N s} {U : Space E n t} {V₀ : Space E n₀ t₀} {wt : n → ℤ}
  (D : U.Splitting V₀ {i // 0 < wt i}) (hD : D.k = inclMatrix E val)

attribute [local simp] ratCoordMatrix_eq map_inclMatrix kAdelic iAdelic HasDegreeGe
  toSquareBlockProp_def

@[simp] lemma ratCoordMatrix_onHom : (U.hom V₀).ratCoordMatrix (.onHom (g, g₀)) =
  V₀.ratCoordMatrix g₀ ⊗ₖ (U.ratCoordMatrix g⁻¹)ᵀ := by simp [hom]

lemma pairWeil_homHeisOp [WeilData E] a b w f : pairWeil U _ a b (g, g₀) (homHeisOp w f) =
  homHeisOp (V₀.ratCoordMatrix g₀ * w * U.ratCoordMatrix g⁻¹) (pairWeil U V₀ a b
  (g, g₀) f) := by simp [pairWeil, homHeisOp, ω_ϱ, homAtPoint, ↓G.onHom_mulVec]

lemma det_ratCoordMatrix g : (U.ratCoordMatrix g).det = g.det := det_units_conj ..

lemma det_eq_one_of_hasDegreeGe_one (h : HasDegreeGe wt wt 1 (U.ratCoordMatrix g - 1)) :
  g.det = 1 :=
  Subtype.ext (det_ratCoordMatrix g ▸ det_eq_one_of_unitriangular (lev := -wt) (by simpa using h))

lemma det_inclX (Y : Grading U N n₀ s) : (Y.inclX g).det =
  g.det := by ext1; rw [← det_ratCoordMatrix, Y.ratCoordMatrix_inclX]; simp

include hD

lemma kAdelic_mul_submatrix (B : Matrix n m (𝔸 E)) (h : HasDegreeGe wt 0 1 B) : D.kAdelic *
  B.submatrix val id = U.x⁻¹.1 * B := by erw [Matrix.mul_assoc, hD, map_inclMatrix,
  ← (eq_inclMatrix_mul_iff (.subtype _)).2]; simp_all; bound

lemma kAdelic_mulVec {y} (h : ∀ i, ¬0 < wt i → y i = 0) : D.kAdelic *ᵥ y ∘ val = ↑U.x⁻¹ *ᵥ y :=
  congr(($(kAdelic_mul_submatrix D hD (replicateCol _ y) (by simp; bound)) · ()))

lemma actsOnFrame_submatrix_ratCoordMatrix (h : ∀ i l, wt i < 1 → 0 < wt l → U.ratCoordMatrix g i
  l = 0) : D.ActsOnFrame g (submatrix (U.ratCoordMatrix g) val val) := by erw [ActsOnFrame,
  kAdelic_mul_submatrix D hD ((U.ratCoordMatrix g).submatrix id _)] <;> simp_all [← mul_inclMatrix]

lemma zeroTerm_omega_of_inclMatrix [WeilData E]
    {C} (h : HasDegreeGe 0 wt 0 (U.ratCoordMatrix g - C)) (h' :
  HasDegreeGe wt (0 ⊓ wt) 1 (C - 1)) (hu : C.det = u.1) (e : HasDegreeGe wt 0 1
  (U.ratCoordMatrix g * D.i.map toAdele - D.i.map toAdele * V₀.ratCoordMatrix g₀)) f :
  D.zeroTerm (U.ω g f) = (upsilonU1.1 u).1⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  rw [twoBlockTriangular_det₀ _ (0 < wt ·), mul_comm,
    det_eq_one_of_unitriangular (lev := (-wt ·.1))] at hu
  rcases kAdelic_mul_submatrix D hD _ e ▸ D.coord_mul_frame_mul.1 _, D.coord_mul_frame_mul (m := n₀)
  rw [D.zeroTerm_omega g₀ (V₀.x⁻¹.mul_left_inj.1 _) (actsOnFrame_submatrix_ratCoordMatrix D hD _)
    (Unitary.toUnits u)]
  all_goals simp_all [Space.ratMap, submatrix] <;> grind

end

open Fintype LinearMap MatMul Matrix Space Submodule TensorProduct Weil WeilData

attribute [local simp ←] smul_eq_diagonal_mul smul_eq_mul_diagonal mul_smul Std.map_ϱ map_inv

variable {E ι ι' ι'' : Type} [Field E] [CMType E] [WeilData E] [Fintype ι] [Fintype ι'] [Fintype
  ι''] {ε ε' ε''} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''} (f : 𝒮 (V.hom V'))
  (f' : 𝒮 (V'.hom V'')) (a b : AutChar E) (g) (t :
  (V.hom V').finitePart ⊗[ℂ] (V'.hom V'').finitePart)

/-- For hermitian spaces V and V'', the orthogonal sum V⁻ ⊕ V'' of V with its form negated and
V''. -/
noncomputable abbrev flipSum (V : Space E ι ε) (V'' : Space E _ ε'') := (flipSpace V).sum V''

/-- The bounded bilinear map combining data on Hom(V,V') and Hom(V',V'') into one datum on
Hom(V', V⁻ ⊕ V''), the first being carried to Hom(V', V⁻) by a scaled adjoint. -/
noncomputable def arrowProduct := (V'.hom (flipSum V V'')).boxProd homSigns_sum_target (V₂ := V'.hom
  V'') ∘L (flipCoords star_normNegOne_mul_self rfl).map (V₁ := V.hom V') (V := V'.hom (flipSpace V))

/-- The Weil operator of (g₂, g₁ ⊕ g₃) on Hom(V', V⁻ ⊕ V''), times a_V(det g₂) a_{V'}(det g₁)⁻¹
b_{V'}(det g₃) b_{V''}(det g₂)⁻¹ υ(det g₁)^{rk V'} υ(det g₂)^{−rk V}, where a_V = aυ^⌊rk
V/2⌋. -/
noncomputable def tripleWeil := (pairChar (rankTwist a ι) (rankTwist a ι') (.fst g, g.2.1) *
  pairChar (rankTwist b ι') (rankTwist b ι'') g.2 * pairChar (upsilonU1 ^ card ι') (upsilonU1 ^ card
  ι) (g.2.1, g.1)) • (V'.hom (flipSum V V'')).ω (.onHom (g.2.1, .sum (g.1.neg, g.2.2)))

/-- The linear map induced by `arrowProduct` from the tensor product of the finite parts 𝒲_f of
Hom(V,V') and Hom(V',V'') to the data on Hom(V', V⁻ ⊕ V''). -/
noncomputable def arrowTensor :=
  lift arrowProduct.toLinearMap₁₂ ∘ₗ mapIncl (V.hom V').finitePart (V'.hom V'').finitePart

/-- The Weil representation of the finite adelic U(V) × U(V') ∋ (g, h) on the finite part 𝒲_f of
Hom(V,V'), twisted by (aυ^⌊rk V/2⌋)(det h) (aυ^⌊rk V'/2⌋)(det g)⁻¹. -/
noncomputable abbrev liftWeilFin := pairWeilFinite V V' (rankTwist a ι) (rankTwist a ι')

attribute [local simp] rho_boxProd flipSpace_x arrowTensor arrowProduct tripleWeil

@[simp] lemma ratCoordMatrix_flipSpace g : (flipSpace V).ratCoordMatrix g.neg =
  V.ratCoordMatrix g := by simp [ratCoordMatrix_eq, ← star_mul]

variable (V V' V'') in
lemma theta_arrowProduct : ∃ z ≠ 0, ∀ f f', θ _ (arrowProduct f f') =
  z * ((V.hom V').θ f * (V'.hom V'').θ f') := (exists_pairTheta_flip star_normNegOne_mul_self rfl V
  V' (flipSpace V) 1 (by simp) 1).imp fun _ ↦ .imp (by aesop) fun H f
  _ ↦ by erw [theta_boxProd_target rfl _ rfl]; specialize H 1 f 1 1 1; simp_all [pairTheta, field]

lemma homHeisOp_arrowProduct w w' : homHeisOp (fromRows (V.formAdjoint V' w) w')
  (arrowProduct f f') = arrowProduct (homHeisOp w f) (homHeisOp w' f') := by
  simp [homHeisOp, homAtPoint, sum]
  congr; erw [flipCoords_apply (x := matToVec (toRows₁ _)), vecToMat_matToVec, toRows₁_fromRows]
  simp [formAdjoint, map_J_inv, V'.map_J]

lemma finHeisOp_arrowProduct y : finHeisOp _ y (arrowProduct f f') =
  stdLattice.semichar (fun q ↦ y (.inl q.2, Prod.fst q)) ^ 2 • arrowProduct (finHeisOp _ (fun q ↦
  normNegOne.1.1 * star (y (.inl q.2, q.1))) f) (finHeisOp _ (fun q ↦ y (.inr q.1, q.2)) f') := by
  simp [finHeisOp]; erw [Std.apply_finVec]; congr
  simp [stdLattice.semichar, dotProduct, sum_prod_type, sq, ← AddChar.map_add_eq_mul,
    mul_mul_mul_comm _ (y _), Finset.sum_comm (γ := ι)]; grind [-stdLattice.two_mul_half]

@[simp] lemma arrowProduct_vacElem : arrowProduct (V.hom V').vacElem (V'.hom V'').vacElem =
  vacElem _ := by simp

lemma arrowProduct_twistedPairWeil g g' g'' : arrowProduct (twistedPairWeil (rankTwist a) (g, g') f)
  (twistedPairWeil (rankTwist b) (g', g'') f') = tripleWeil a b (g, g', g'')
  (arrowProduct f f') := by simp [pairWeil, flipCoords_map_omega]; rw [omega_boxProd]; module; aesop

lemma leftInverse_arrowTensor : arrowTensor.leftInverse (arrowTensor t) = t :=
  leftInverse_apply_of_inj (ker_eq_bot'.2 fun t
  ht ↦ tensor_eq_zero_of_separating (f := (θ _ ∘L ϱ _ · |>.1.domRestrict _)) (by aesop) t fun x ↦ by
  obtain ⟨⟨x, ⟨⟩⟩, ⟨⟩⟩ := flipCoords star_normNegOne_mul_self rfl (t := ε) (s := ε').φ.surjective x,
    theta_arrowProduct V V' V''
  ext y; apply_fun (· ((x ⊕ᵥ y) ∘ Equiv.sumProdDistrib ..)) at ht
  rw [← θ_ϱ, t.exists_finset.choose_spec] at *; simp_all [Function.comp_def, ← Finset.mul_sum]) t

lemma range_arrowTensor : arrowTensor.range = (V'.hom (flipSum V V'')).finitePart := by
  simp [← map₂_eq_range_lift_comp_mapIncl, finitePart, map₂_span_span, ← arrowProduct_vacElem,
    finHeisOp_arrowProduct, -arrowProduct, le_antisymm_iff, span_le, smul_mem, mem_span_of_mem]
  exact (starMulAut.1.trans (normNegOne.map (Ô E).subtype.1).mulLeft).surjective.comp_left.forall.2
    ((smul_mem_iff _ (by simp)).1 <| subset_span ⟨matToVec <| flip ·.curry ⊕ᵥ vecToMat ·, rfl⟩)

lemma arrowTensor_map_liftWeilFin p q r : arrowTensor
  (.map (liftWeilFin a (p, q)) (liftWeilFin b (q, r)) t) = tripleWeil a b ((1, p), (1, q), 1, r)
  (arrowTensor t) := by induction t with simp_all [arrowProduct_twistedPairWeil, -arrowProduct]

lemma theta_tripleWeil_rat_mul f : let F x := (V'.hom (flipSum V V'')).θ (tripleWeil a b x f); ∀ γ ∈
    V.Γ, ∀ δ ∈ V'.Γ, ∀ g g' k, F (γ * g, δ * g', k) = F (g, g', k) := fun γ h@⟨_, e⟩ δ k@⟨_, d⟩ g g'
  l ↦ by simpa [pairWeil, ← e, ← d, ← G.sum.map_mul] using (pairThetaKer _ _ 1 1).4 (γ' := .sum
  (γ.neg, 1)) k (by simpa [↓sum_mem_Γ, mem_Gamma_iff_ratCoordMatrix] using h) g' (.sum (g.neg, l)) f
