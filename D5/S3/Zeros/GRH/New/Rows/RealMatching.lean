/- GID: D5/S3/Zeros/GRH/New/Rows/RealMatching
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/RealMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.RealMatching. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/RealMatching.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.StackedDeterminants
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange of theta kernels with explicit determinant polynomials (see New.Rows.Carrier).

This file: Real-place matching of determinant polynomials via invariant functionals on Fock
space. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section


open NumberField Finset Matrix MvPolynomial Sum Fintype Function Prod Real ComplexOrder
variable {E n m a b p l : Type} [Field E] [NumberField E] [Fintype n] [Fintype m] [Fintype a]
  [Fintype b] [Fintype p] [Fintype l] (f : p ⊕ l ≃ b) (j : m ⊕ l ≃ n) (e : p ⊕ a ≃ m)
  {ι : InfinitePlace E → Type} [∀ τ, Fintype (ι τ)] {γ} (hγ : γ = fun τ ↦ (card l - card (ι τ) : ℤ))
  (τ : InfinitePlace E) (η : ∀ τ, ι τ → _)

/-- For a bijection f : p ⊕ l ≃ b, the sign function on b equal to +1 on the image of p and −1
on the image of l. -/
abbrev blockSigns : b → ℤˣ := (1 ⊕ᵥ -1) ∘ f.symm

/-- The homomorphism, place by place, from the archimedean definite unitary group on m to that
of signs `blockSigns` j, acting on the positive block and trivially on the negative block. -/
@[simps!] def posBlockEmb : GInf E (1 : m → _) →* GInf E (blockSigns j) :=
  ((U.reindex j (by simp [signMatrix])).toMonoidHom.comp (U.inl 1 (-1))).compLeft _

omit [NumberField E] in
lemma posBlockEmb_spec k : (posBlockEmb j k τ)⁻¹.1.1 = posBlockEmb j k⁻¹ τ ∧ ↑(posBlockEmb j k τ) ∈
  blockDiagAlg (blockSigns j) ∧ principalMinor (posBlockEmb j k τ) (blockSigns j · = 1) =
  (k τ).1.1.det ∧ principalMinor (posBlockEmb j k τ) (blockSigns j · = -1) = 1 := by
  simp [mem_blockDiagAlg, reindex_equiv j, ← principalMinor_submatrix j, principalMinor_fromBlocks]

@[simp↓] lemma card_neg_blockSigns : card {i // blockSigns f i = -1} = card l := by
  simp [Fintype.card_subtype, card_filter, reindex_equiv f, -sum_boole]

/-- The polynomial ∏_τ (determinant of the negative-negative variable block)^{d_τ+|n|−2|l|} ·
∏_{τ,k} det(η_{τk} y_τ), with d_τ = |ι_τ| and y_τ the positive-positive variable block. -/
def matchedPoly := (∏ τ, letterMinor τ (j ∘ inr) (f ∘ inr) ^
  (card (ι τ) + card n - 2 * card l)) * pairedDetProd (X ⟨·, j <| inl ·, f <| inl ·⟩) η

/-- The linear map renaming a polynomial's m-indexed variables into the positive block of n via
j, then taking its Fock vector for signs `blockSigns` j against a definite space a. -/
abbrev posFockVector := polyVector (realSigns E (homSigns (n' := a) (blockSigns j) 1)) ∘ₗ
  (renameRowsCols id (j ∘ inl)).toLinearMap

include hγ
attribute [local simp↓] mul_pow prod_ne_zero_iff posBlockEmb_spec diagTorus matchedPoly
  pairedDetProd stackedDetProd fst_prod snd_prod fst_sum C_mul' snd_sum smul_smul diagonal_apply
  AlgHom.map_det realPairWeil_polyVector Nat.card_eq_fintype_card val_posBlockEmb_apply_coe
  letterMinor injective_id inl_injective bind₁_bind₁ smul_pow prod_smul prod_pair _root_.funext_iff

lemma realPairWeil_stackedDetProd k u : realPairWeil γ 0 (posBlockEmb j k,
  u) (posFockVector j (stackedDetProd e fun τ ↦ (η τ · * (k τ).1.1⁻¹ᵀ))) = (∏ τ,
  (k τ).1.1.det ^ card (ι τ))⁻¹ • posFockVector j (stackedDetProd e
  η) := have := congr(posFockVector j $(twoSidedSubst_stackedDetProd e η (u ·) (k⁻¹ ·)))
  by simp_all [rename_eq_aeval, reindex_equiv j]

/-- Archimedean step of explicit matching, weights γ_τ = |l| − |ι_τ|. For some polynomial Q₀, each v
has κ such that, if ℓ_g(Ω(x)w) = ℓ_{gx₁}(w) and ℓ_x(v) = ℓ′(Q) whenever Ω(1, x)v_{Q₀} = v_Q, then
κ·ℓ₁(`posFockVector` j (`stackedDetProd` e η)) = ℓ′(`matchedPoly` f j η) for all η. -/
lemma real_matching : ∃ Q₀, ∀ v, ∃ κ, ∀ (ℓ : _ → _ →L[ℂ] ℂ) (ℓ' : _ →ₗ[ℂ] ℂ), (∀ g x w,
  ℓ g (realPairWeil γ 0 x w) = ℓ (g * x.1) w) → (∀ x Q, realPairWeil (s := blockSigns f) γ 0 (1,
  x) (polyVector _ Q₀) = polyVector _ Q → ℓ x v = ℓ' Q) → ∀ η,
  κ * ℓ 1 (posFockVector j (stackedDetProd e η)) = ℓ' (matchedPoly (ι := ι) f j η) := by
  let η τ (_ : ι τ) := (1 : Matrix m m ℂ).submatrix (e ∘ inl) id
  let t z : GInf E 1 := fun _ ↦ diagTorus _ fun i ↦ z⁻¹ ^ ite (e.symm i).isLeft 2 1
  let r := j ∘ inl ∘ e ∘ inr
  let Ω y z := let o := diagTorus 1 (const a z⁻¹)
    (∏ τ, o.1.1.det ^ card (ι τ)) • realPairWeil γ 0 (posBlockEmb j (t z), fun _ ↦ o) y
  have : Continuous (posBlockEmb (E :=
    E) j) := by simp [continuous_pi_iff, continuous_U_iff_matrix]; fun_prop
  use matchedPoly f j η, (.imp (fun κ hκ ℓ ℓ' m hx ↦ ?_) <| isClosed_property denseRange_polyVector
    ((isClosedMap_smul_left fun ℓ : {ℓ : _ →L[ℂ] ℂ // ∀ u w, ℓ (realPairWeil γ 0 (1, u) w) = ℓ w} ↦
    ℓ.1 (posFockVector j (stackedDetProd e η))).isClosed_range.preimage_of_continuous (f :=
    fun y ℓ ↦ (2 * π)⁻¹ • ∫ θ in 0..2 * π, ℓ.1 (Ω y (.exp θ)))) (fun P ↦ ⟨_, funext fun ⟨ℓ, m⟩ ↦
    (mul_right_comm ..).trans (div_eq_of_eq_mul (fockPairing_star_self_pos (p := ∏ τ,
    letterMinor τ id id ^ card (ι τ)) (by simp [-letterMinor])).ne' (by
    let T (s : ℂ) := ℓ (P.bind₁ fun x ↦ s ^ extend r 0 1 x.2.2 • X x)
    have h z : ℓ (Ω P z) = T z := by
      simp [-diagTorus, Ω, *]; congr
      simp [r, t, extend, reindex_equiv j, reindex_equiv e, inv_diagonal, Ring.inverse,
        Pi.isUnit_iff, sq]
    have D τ k : stackedDet τ (η τ k) e = _ * det (of _) := (congrArg det (by
      ext ⟨⟩ ⟨⟩ <;> simp [η] <;> rfl)).trans (det_fromBlocks_zero₁₂' 1 ..)
    simpa [map_one, circleAverage, circleMap, *, det_apply, ↓det_one, ← (by
      simp [T, ← aeval_eq_bind₁, aeval_def, eval₂_eq]
      fun_prop : Differentiable ℂ T).diffContOnCl.circleAverage (c := 0) (R := 1)] using!
      fockPairing_polarisation (X ⟨·, ·, r ·⟩) 1 (ℓ.1 ∘ₗ polyVector _) (P.bind₁ fun (τ, i, k) ↦
      extend r (X ⟨τ, i, ·⟩) 0 k) (T 0 • ∏ τ, letterMinor τ id id ^ card (ι τ)) fun u ↦ by
     unfold T; rw [← m u]
     simp [*, field, RingHom.map_det, Matrix.map]; congr; simp [reindex_equiv j, reindex_equiv e, r,
       extend]))⟩) ·)
  choose Z c hc _ using fun (τ : InfinitePlace E) z ↦ exists_det_fromCols e.symm
    (of (curry (curry z τ)))ᵀ
  have hc τ z η : (stackedDet τ η e).eval z = _ := .trans (by
   rw [stackedDet, ← det_transpose]; simp [← det_reindex_self e.symm, det_apply]) (hc τ z ηᵀ)
  let' M := (κ • (ℓ 1).1 ∘ₗ posFockVector j ∘ₗ .leftInverse _ ∘ₗ .fst .. - ℓ' ∘ₗ .snd ..) ∘ₗ
    .mulLeft ℂ ((∏ τ, c τ · ^ card (ι τ)), _); with_unfolding_all
    refine have H y : M (pairedDetProd (fun τ i k ↦ ((Z τ · k i),
        X (τ, j (inl i), f (inl k)))) y) = 0 ↔ _ := ?_
      (H · |>.1 ((mul_eq_zero_iff_left (fockPairing_star_self_pos (by simp [-letterMinor])).ne').1
        (fockPairing_polarisation (r := e ∘ inl) _ _ M _ 0 fun k ↦ .trans ?_ ((H _).2
        (.trans (by simpa [m] using congr(κ * (ℓ (posBlockEmb j k) $(realPairWeil_stackedDetProd j e
        hγ η k⁻¹ 1)))) (congr($hκ ⟨(_ : ℂ) • _, by simp [m]⟩).trans ?_))))))
    rw [← (evalₗ ℂ _).leftInverse_apply_of_inj (bot_unique fun _ ↦
      funext ∘ congrFun) (stackedDetProd ..)]
    simp [M]; congr!
    iterate 3 simp [η, hc, det_apply', mul_apply, ← Algebra.smul_def]
    have {z} := hx (posBlockEmb j (k * t z)) ((_ : ℂ) • matchedPoly f j fun τ i ↦
      z⁻¹.1 ^ 2 • η τ i * (k τ).1.1ᵀ) (by
      simp [Matrix.map, reindex_equiv j]; congr!; simp [η, entrywise, t, mul_comm])
    simp [Ω, m, t, reindex_equiv e, Matrix.map_smul] at *
    simp [*]; field_simp; simp [field]
