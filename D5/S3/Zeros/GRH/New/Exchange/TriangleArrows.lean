/- GID: D5/S3/Zeros/GRH/New/Exchange/TriangleArrows
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/TriangleArrows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.TriangleArrows. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/TriangleArrows.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.OneSquare
import D5.S3.Zeros.GRH.New.Exchange.CostOfSquares
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Injectivity and norm of a chain of theta lifts. The chain of m theta lifts from U(Y_0) to the
definite U(Y_m), mostly outside the range of Rallis's formula, is injective at level g, and on rows
its Gram determinant is the product of the determinants of m Hecke-type operators times a power of
one scalar that costs little height at the chosen twists. Norm and injectivity of one cuspidal theta
lift, also below Weil's range, are known. Related work: Gan–Qiu–Takeda, Regularized Siegel–Weil
formula and Rallis inner product formula (Thm 1.3), 2014; Bruinier–Funke, Injectivity of the
Kudla–Millson lift, 2010; He, Compositions of theta correspondences, 2005.

Set-up for this proof: general results applied to the objects of this proof.

This file: The lifts and descents of the data form a triangle with two laws. -/

noncomputable section

open MeasureTheory Matrix Complex ComplexConjugate Fintype LinearMap


open WeilData Space Modulus ComplexInnerProductSpace
variable {E N N'} [Field E] [CMType E] [WeilData E] [Fintype N] [Fintype N'] {s s'}
  (S : Space E N s) (T : Space E N' s') {I} {a : I → _} {P} (D : Data P) (z ϑ i n)

/-- The linear isometry from forms of parameter l on S to forms of parameter l on the opposite
space, by the identification of the two unitary groups. -/
def formNegEquiv l : S.Form (typeKernel l s) ≃ₗᵢ[ℂ] S.neg.Form (typeKernel l _) := .symm
  (LinearEquiv.isometryOfInner
  (.ofEq _ _ (.symm (SetLike.ext ((isForm_neg_iff_and_integral_neg S _).1 _))) ≪≫ₗ .ofSubmodule'
  (.funCongrLeft ℂ ℂ G.neg.1) _) fun _ _ ↦ .symm ((isForm_neg_iff_and_integral_neg S _).2 _))

/-- Given an edge from S to T and an edge from the opposite space of S with characters a⁻¹υ^{rk S},
a⁻¹υ^{rk T} (that is, b = a⁻¹υ^{card n} at S and at T), the lift along the first with datum Ψ is the
adjoint of the descent along the second with some datum Ψ′, via `formNegEquiv`. -/
lemma IsEdgeFamily.exists_adjoint_first_arrow {l k' Φ Φ'} (h : IsEdgeFamily a (kernelPair l s) k'
  false Φ) i {𝔪} Ψ : let b i n [Fintype n] := (a i n)⁻¹ * upsilonU1 ^ card n
  IsEdgeFamily b (kernelPair l (-s)) k' true Φ' → ∃ Ψ', ∀ y x, ⟪x, modLift S T (a i) (𝔪 := 𝔪) Φ Ψ _
    _ y⟫ = ⟪modDescent _ T (b i) (𝔪 := 𝔪) Φ' Ψ' (k' false) _ x, formNegEquiv S l y⟫ := fun h' ↦ by
  obtain ⟨⟨c, _⟩, κ, K⟩ := exists_modKernel_neg_left S T, h'.petersson_descent_eq _
  exact ⟨c • conj κ • _, (reindex_equiv (formNegEquiv ..).symm).1.2 fun y x ↦ by
  simp [modDescent, modDatum, Pi.smul_comp]
  erw [← star_inj, mul_comm, mul_comm _ κ, ← K, inner_eq_petersson,
    h.isArrow_modDatum.1.coe_formLift]; simp_all [modKernel, pairTheta, Space.lift, Space.petersson,
    ← integral_conj, mul_assoc, isForm_neg_iff_and_integral_neg S S.neg, mul_left_comm _ c]; tauto⟩

namespace Data

seal U w Int.add instInv

/-- The space of forms on the hermitian space at position (i, n) of the triangle whose type has
the doubled parameter `Data.gridParam` z i 0 n. -/
abbrev TriForm := (D.gridSpace i ..).Form (typeKernel (D.gridParam z i 0 n) _)

/-- The theta lift from forms at node (0, n) to node (0, n+1) of grid z, offset i, with
characters `Data.gridChar` of index n+i, harmonic `Data.gridHarmonic`, and indicator of the standard
inclusion modulo `Data.triangleModulus`. -/
def triLift : D.TriForm z i n →ₗ[ℂ] D.TriForm z i (n + 1) := modLift _ _ (gridChar ϑ (!z) (n + i))
  (D.gridHarmonic i false (!z) (n + i) z 0 n 0 (n + 1))
  (inclusionDatum (triangleModulus z ϑ).ResRing) ..

/-- For each i, the linear isometric isomorphism from forms at (0,0) to forms at (i,0), composed
of i passages to the opposite hermitian space. -/
def triNegEquiv : ∀ i, D.TriForm z 0 0 ≃ₗᵢ[ℂ] D.TriForm z i 0 := Nat.rec (.refl ..) fun _ ↦
  (·.trans (formNegEquiv ..))

/-- The space of forms at the base corner of the triangle: forms of level g on Y₀ if z is false,
forms fixed by principal level `Data.gridLevelGen` if true. -/
def triBase : Submodule ℂ (D.TriForm z 0 0) :=
  levelSpace (formRep ..) (z.rec D.chosenLevel (principalLevel _ D.gridLevelGen))

lemma triNegEquiv_formRep k y : ∀ i, D.triNegEquiv z i (formRep _ _ k y) =
  formRep _ _ k (D.triNegEquiv z i y) := Nat.rec rfl fun _ ↦ congrArg (formNegEquiv ..)

/-- Inner product formula for the first lift a in row i < m: a is injective on `Data.triBase`, and
for y there N₀⟨ax, ay⟩ (N₀ = `triangleOrder` z ϑ 0) is the sum over γ of C·`cosetTerm` x y γ divided
by the number of matrices over the residue ring, with one constant C. -/
lemma hasSum_inner_triLift (h : i < D.m) : ∃ C,
  ∀ ϑ (y : D.triBase z), let a y := D.triLift z ϑ i 0 (D.triNegEquiv z i y)
  (∀ v, (∀ x, ⟪v, x⟫ = ⟪a y, a x⟫) → v ∈ D.triBase z ∧ (v = 0 → y = 0)) ∧ ∀ x, HasSum (fun γ ↦ C *
    (cosetTerm (card (D.GridIndex z 0 1)) (gridChar ϑ (!z) i (D.GridIndex z 0 1))
    (triangleModulus z ϑ).places.conjClosureᶜ x y γ / card (D.GridIndex z 0 1 × D.GridIndex z 0 0 →
    (triangleModulus z ϑ).ResRing))) (triangleOrder z ϑ 0 * ⟪a x, a y⟫) := by
  have e := D.paramsCorrespond_grid false z i 0 0 rfl
  obtain ⟨C, -, H⟩ := rallis_inner_product_euler (T :=
    gridSpace ..) e.isEdge_jointHarmonic (by simp [card_gridIndex]; grind [Bool])
  use C, fun ϑ y ↦ ?_
  have r u := by simpa [triNegEquiv_formRep] using congr(D.triNegEquiv z i $(y.2 u))
  specialize H (gridChar ϑ ..) (gridChar ϑ ..) (isSharp_modDatum (F := Pi.single
    (inclMatrix (triangleModulus z ϑ).ResRing .inl) 1) _ _ (.inr nonempty_modulus_places) _ (by
    simp; exact inclMatrix_transpose_mul_self .inl) (by cases z <;> exact ((auxPair ..).tame_eq_one
    · <| places_levelModulus.ge.mt ·)) (by simp)) _ fun k ⟨u, a, e⟩ g ↦ congr($(r ⟨k, e ▸ by
    cases z; exacts [D.levelY_le_chosenLevel ϑ 0 ⟨u, (LevelPlaces.ker_reductionK₀_eq _).le a, rfl⟩,
      (mem_principalLevel_iff gridModulus_one_ideal _).2 a]⟩).1 g)
  refine ⟨fun v p ↦ ⟨fun u ↦ ext_inner_right ℂ (((formRep ..).apply_bijective u).2.forall.2
    fun x ↦ ?_), fun o ↦ by simpa using H.1 (inner_self_eq_zero.1 (by erw [← p]; simp [o]))⟩,
    fun x ↦ ((H.2 _).mul_left _).congr_fun (by simp [cosetTerm, ← triNegEquiv_formRep, field,
      Bool.cond_false, -Bool.cond_eq_ite])⟩
  let o : Kf .. := ⟨u.1, by cases z; exacts [levelOf_le_Kf u.2, u.2.1]⟩
  choose k f using reductionK₀_surjective (blockGL ((triangleModulus z ϑ).reductionK₀ o,
    (1 : GL (Fin (D.t - z.toNat)) _)))
  erw [inner_formRep, one_smul, p, p, ← (gridSpace ..).inner_formRep k.1]
  repeat erw [(isEdgeFamily_of_paramsCorrespond (D.gridChar · _ _) _
    e).isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_single (y :=
    inclMatrix _ .inl) o k (by erw [f, ← map_inv]; simp [inclMatrix_inl]; rfl))]
  erw [inner_smul_left, inner_smul_right, ← mul_assoc, conj_mul', r, ← triNegEquiv_formRep,
    Circle.norm_coe, one_pow, one_mul]; rfl

attribute [local implicit_reducible] Data.GridIndex BlockIndex kernelPair

/-- For some descents d, the lifts `Data.triLift`, the orders `Data.triangleOrder`, the cost
`Data.CostsSquares` and the embeddings of `Data.triBase` in the forms at (i, 0) form a triangle
`IsTriangle` of size m; the cost bound and second law are asserted for z false only. -/
theorem exists_isTriangle : ∃ d, IsTriangle D.m (D.triangleOrder z) D.CostsSquares (D.triLift z) d
    (fun i ↦ (D.triNegEquiv z i).toLinearIsometry.comp (D.triBase z).subtypeₗᵢ) (z = false) := by
  let b i ϑ n [Fintype n] := (D.gridChar ϑ (!z) (0 + i) n)⁻¹ * upsilonU1 ^ card n
  have L {i n} (h : i + n < D.m) := isEdgeFamily_of_paramsCorrespond (D.gridChar · _ _) false
    (D.paramsCorrespond_grid _ z i 0 n rfl)
  choose! Φ F using fun i n h ↦ Exists.intro _
    (isEdgeFamily_of_paramsCorrespond (b i) true (@paramsCorrespond_first_arrow n _ D i z h).1)
  have R {n i} h := Exists.intro _
    (isEdgeFamily_of_paramsCorrespond (b i) true (@paramsCorrespond_first_arrow n _ D i z h).2)
  choose! p H using fun i h ϑ ↦ (L h).exists_adjoint_first_arrow (gridSpace ..) (gridSpace ..) ϑ
    (inclusionDatum (triangleModulus z ϑ).ResRing) (F i 0 h)
  let e ϑ i : ∀ n, Matrix (D.GridIndex z 0 (n + 1)) _ _ → ℂ := Nat.rec (p i ϑ) fun _ ↦ nextDatum
  use fun ϑ i n ↦ modDescent _ _ (b i ϑ) (Φ i n) (e ϑ i n) .., .one, .mul, fun i n h ↦ ?_,
    fun i h ϑ y ↦ ⟨H i h ϑ _, (((D.hasSum_inner_triLift z i h).choose_spec ϑ y).1 _ fun _ ↦
    ((D.triNegEquiv z i.succ).symm.inner_map_eq_flip ..).trans (H i h ..).symm).elim (⟨⟨_, ·⟩,
    (D.triNegEquiv z i.succ).right_inv _, · ∘ Subtype.ext_iff.1⟩)⟩
  obtain ⟨⟨H, g⟩, h₀, h₁, h₀', h₁', ⟨P, h₂⟩, _, h₂'⟩ := exists_isTameFor_costsSquares_one ⟨_,
    fun _ ↦ (n + 1) * D.h, _, _, by simpa using!
    (hasWeight_upsilonU1_pow (n.succ * D.h)).inv.mul (D.chi_hasWeight.zpow n.succ), by simp_all,
    ⟨D.nat_le_of_hasLogBound, le_rfl⟩, by clear * -; grind, fun _ ↦ by
    grw [le_of_add_le_right h.le]; use D.le_of_hasLogBound⟩ (D.omega_zpow_ne_one _) (cond z D.b₁ 1)
    ⟨_, n.succ_pos, by omega⟩, @L (i + 1) n (by lia), L h, F _ _ h.le, F _ _ h, R h, R h.le
  simp only [triLift, n.succ_add] at h₁ ⊢
  obtain ⟨Q, rfl⟩ := (fun s t ↦ (⟨flipPoly t s (P.map conj), by
    apply P.induction_on <;> simp +contextual [flipPoly, Int.cast_smul_eq_zsmul, pairSign,
    -zsmul_eq_mul, smul_smul, ← Units.val_mul, mul_comm (t _)]⟩ : ∃ Q, flipPoly s t (Q.map conj) =
    P)) (D.gridSigns z (i + 1) 0 _) (D.gridSigns z i 0 _)
  have ht ϑ := H (cond z 1 ϑ)
  have S := one_square (gridSpace ..) (gridSpace ..) (gridSpace ..) (gridSpace ..) h₁' h₁ h₀ h₀'
    swapFirstTwo ?s (D.t - z.toNat) ?e ?t ?u ht ?v
  have T := one_square (gridSpace ..) (gridSpace ..) (gridSpace ..) (gridSpace ..) h₂ h₀ h₁ h₂'
    swapFirstTwo ?s' 0 rfl ?t' ?u' ht ?v'
  case s | s' =>
    clear * -; simp_rw [negCount_sumElim, card_neg_gridSigns_eq_sum, ← Finset.sum_add_distrib,
      entrySign_eq]
    grind
  case t | t' | e => clear * -; simp [card_neg_gridSigns_eq_sum, card_gridIndex]; grind [Bool]
  case u | u' => cases z <;> simp [card_gridIndex, Data.h, D.t_odd.pos] <;>
    nlinarith [D.k_add_t_add_one_le_h₂, D.r_add_six_le_t]
  case v | v' =>
    clear * -; intros; apply_fun Additive.ofMul
    cases z <;> simp [b, rankTwist, gridChar, liftChar, μ₀, TameChar.pow, twist_one_spec,
      card_gridIndex] at * <;> match_scalars <;> grind
  choose C κ c _ _ S using S; choose _ _ _ _ _ T using T
  use (conj <| c · / κ), fun ϑ y z ↦ by simpa [modDescent, modDatum_eq_sum _ _ (e _ _ _)] using!
    (S _ _ (innerₛₗ ℂ z)).sum_eq_nextDatum _
  rintro rfl
  choose c₁ n₁ e₁ using @exists_conj_modKernel_eq_swap
  choose _ _ hG using (SquareLaw.sum_fourier_eq_nextDatum (D.Y n) (Fin D.t)
    (isPrimitive_primAddChar _) <| isPrimitiveMulChar_of_isTameFor <| ht ·)
  obtain ⟨⟨_, M⟩, _, M₀⟩ := h₁'.petersson_descent_eq Q, h₂'.petersson_descent_eq _
  refine ⟨g (C := C / ‖κ‖ ^ 2) (by simp [*, field]), _, ?_, fun ϑ z ↦
    have A :=
      h₁.isArrow_modDatum.1.inner_formLift_adjoint h₁.isArrow_modDatum.2 (h₂.1 _).2 (h₁.1 true).2 z
    ⟨_, A, fun y ↦ by
    let u j := (triangleModulus false ϑ).flipScalar (D.GridIndex false 0 j)
    have K := by simpa using hG ϑ (e ϑ i n) (T ϑ (formRep _ _ (u n)⁻¹ y) (innerₛₗ ℂ z))
    simp_rw [← inner_smul_right, ← inner_sum, ← (modLift ..).map_smul, ← map_sum, ← map_smul₂] at K
    repeat erw [← map_sum₂, ← modDatum_eq_sum] at K
    have K := congr(conj $(M₀ ..)).trans (by erw [map_mul, ← A, inner_conj_symm, K, ((formRep
      ..).inv_self_apply (u _) _).symm.trans
      (congrArg _ (h₀.isArrow_modDatum.1.formRep_formLift_of_eq_smul (k := u _) (by
      erw [pairWeil_apply, G.onHom_scalarFin]) _)), (formRep ..).self_inv_apply, inner_eq_petersson,
      h₂.isArrow_modDatum.2.coe_formLift, funext (formRep_apply _ _),
      ← ThetaKernel.lift_omega_left _ (h₁'.1.form_mem_rapidFunctions _).1 (1, u _)])
    erw [← inner_formRep (u n)⁻¹, inner_eq_petersson, funext (formRep_apply _ _),
      h₀'.isArrow_modDatum.2.coe_formLift]
    simp [petersson, ↓conj_petersson] at K
    simp [Space.lift, ← integral_conj, u, rep_apply_apply, e₁, petersson, -θ_apply,
      ← pairTheta.eq_1, ← modKernel.eq_1, mul_assoc, mul_left_comm _ (c₁ ..)] at K M ⊢
    erw [K, (eq_inv_mul_iff_mul_eq₀ (by simpa using left_ne_zero_of_mul_eq_one (n₁ ..))).2 (M ..)]
    simp [← mul_assoc]; rfl⟩⟩
  apply_rules (transparency := .instances) [CostsSquares.mul _ _ (zero_add 0).le] <;> first
    | exact .of_norm_sq_eq_mul_card_zpow 1 _ 0 (by simp [*, lValueProd, div_pow]; rfl)
    | exact .of_norm_sq_eq_mul_card_zpow 1 1 (-.ofNat _) (by simp [field]; tauto)
    | exact .of_norm_sq_eq_mul_card_zpow 1 1 (.ofNat _) (by simp [inv_eq_iff_eq_inv, field]; tauto)
