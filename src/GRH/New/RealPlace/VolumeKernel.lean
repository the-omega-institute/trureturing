import GRH.New.Filling.LinkPairing
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Frames with equal Gram block and congruent middle parts are lattice translates. Volume
weight for the Schur test, dominated by a kernel with Hua-type integral bound. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

open Fin ENNReal Finset MatMul Matrix Pointwise Submodule

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} {γ j c}

/-- Let c ∈ Ô be an idele, K ⊇ cÔ^σ, Y(a) integral, m primitive π×τ, |π| = |τ| + s, |τ| ≤ l, and
[M_a : K ∩ M_a] | n(a), M_a = Y(a)mÔ^τ. If every nonempty subset of B on which the columns
of Y agree modulo K has at most x elements, then ∑_B n(a)^(−l) ≤ [Ô : cÔ]^(|σ|(|σ|+s))·x. -/
lemma tsum_inv_index_pow_le_of_congr [StablyUnram E]
    {α π σ τ : Type} {x : ℝ≥0∞} [Fintype σ] [Fintype τ] [Fintype π]
  {c : (𝔸f E)ˣ} (hc : ↑c ∈ Ô E) {B : Set α} (Y : α → Matrix σ π _) (hY : ∀ a ∈ B,
  IsIntMatrix (Ô E) (Y a)) {m : Matrix π τ _} (hm : IsPrimitiveMatrix (Ô E) m) {s} (e :
  τ ⊕ Fin s ≃ π) {K} (hK : c • intVectors .. ≤ K) (n : α → ℕ) (hn : ∀ a ∈ B,
  submoduleIndex K (colLattice (Ô E) (Y a * m)) ∣ n a) l (hl : Fintype.card τ ≤ l) (H : ∀ᵉ (D ⊆ B)
  (_ ∈ D), (∀ᵉ (a ∈ D) (b ∈ D), colLattice _ (Y a - Y b) ≤ K) → ∑' _ : D, 1 ≤ x) : ∑' a : B,
  .ofReal (n a ^ l)⁻¹ ≤ .ofReal ((genIndex c.1 ^ Fintype.card σ) ^ (Fintype.card σ + s)) * x := by
  choose V o u _ q r using fun a ↦ isValuationPair_Ohat.hermite .inr ((Y a * m)ᵀ.fromRows 0)
  have p a j : u a j ∈ colLattice _ (Y a * m) := ⟨_, ((o a).isIntMatrix_inv (.inr j) <| .inl ·), by
    simp [← r, funext_iff, mul_apply, mulVec_eq_sum]⟩
  have i a h j := colLattice_le (L := intVectors ..) ((hY a h).mul hm.1).isInt_transpose (p a j)
  obtain ⟨U, hU, rfl⟩ := (isValuationPair_Ohat.exists_firstCols_iff e).2 hm
  grw [tsum_le_of_colouring (fun _ ↦ _ ⊕ᵥ _) (submoduleIndex_smul_ne_zero hc) (fun a h ↦
    Sum.rec (i a h) (((hY a h).mul hU.isIntMatrix).isInt_transpose <| e <| .inr ·)) (fun a ↦
    .ofReal (n a ^ l)⁻¹) x fun D s _ _ f ↦ ?_]
  simp [submoduleIndex_smul_intVectors hc]
  have z := (ne_zero_and_le_of_dvd (submoduleIndex_smul_ne_zero hc)
    (submoduleIndex_dvd_of_le .id hK ((iSup₂_le (colLattice_le <| i · <| s ·)).trans (by simp)))).1
  choose k y using fun a h ↦
    (submoduleIndex_dvd_of_le 1 le_rfl (iSup₂_le (colLattice_le fun j ↦ mem_sup.2
    ⟨_, ⟨_, p .., rfl⟩, _, hK <| f · · _ h (.inl j), add_sub_cancel ..⟩))).trans (hn a (s h))
  simp [y, ← inv_pow]
  grw [Nat.cast_inv_le_one, tsum_set_const, ← tsum_set_one, tsum_le_of_colouring _ z (fun a k j ↦
    mem_iSup_of_mem a (mem_iSup_of_mem k ⟨_, ((o a).isIntMatrix (.inl j) <| .inr ·),
    (mulVec_transpose ..).trans congr($(q a) _).symm⟩)) (fun _ ↦ 1) _ fun _ t ↦ (H _ (by tauto)
    · · ∘ fun g a k b h ↦ map_le_iff_le_comap.2 fun _ ↦ (colLattice_le (by simpa [reindex_equiv e]
    using ⟨g a k b h, (hK <| f a (t k) b (t h) <| .inr ·)⟩) ⟨_, hU.isIntMatrix_inv.mulVec ·,
    inv_mulVec_eq_vec rfl⟩)), hl, mul_right_comm, ← ofReal_mul] <;> simp [z, ← Nat.not_lt]

attribute [-simp] MulMemClass.coe_mul Nat.cast_mul Subgroup.coe_mul

attribute [local simp] gIdele_val mulVec Matrix.mul_apply splitGram frameGram middleGram
  Units.smul_def dotProduct funext_iff mul_pow

lemma HasLevel.middle_shared_vector_le (h : S.HasLevel j γ) (b : Fin _) (hb : b.1 < j → b = 𝔰.top) :
    let y := frameImage γ.1.1 *ᵥ col (paddedLeading j (S.frameProducts γ))⁻¹ b
    (∀ a, y (eStar a) = 0) ∧ ∀ v, 5 * ∑ i, ‖Φ v (y (𝔰.indexX₀ i))‖ ^ 2 ≤ 1 :=
  (le_or_gt ..).rec (h.exists_shared_frame_vector · |>.rec fun _ e ↦
  e ▸ by simp [↓frameImage_one_mulVec]) fun h₀ ↦ (norm_sq_middle_part_eq
  (by simpa [paddedLeading, h₀.trans_le', is_le, hb h₀] using congr(col $h.paddedLeading_mul_inv b))
  rfl).imp (·.1) (by grw [S.le_N]; simp [↓·, mul_nonneg])

lemma col_eq_zero_of_norm_lt_one {n} {l : Matrix 𝔰.κ n E} (h : IsIntMatrix (Ô E)
  (S.classCoordX₀ c * finAdeleMat l)) {i} a (H : ∀ v, ∑ a, ‖Φ v (l a i)‖ ^ 2 < 1) :
  l a i = 0 := congr($(S.eq_zero_of_ratMiddle_form_eq_zero (lᵀ i ⊕ᵥ 0) rfl
  (eq_zero_of_norm_Φ (by simpa [↓gram_mul, ↓gram_classCoordX₀, ← algebraMap_mem_Ô] using
  (h.isInt_conjTranspose.mul S.isUnimodular_latMiddle.isIntMatrix).mul h i i)
  (by simp; grw [norm_sum_le]; simpa [← sq]))) (.inl a))

lemma IsLabelledTerm.eq_of_frameImage_eq [S.IsAdmissible]
    {j t p p' u u'} (hu : u ∈ S.classUnip₀ c) (hu' :
  u' ∈ S.classUnip₀ c) : S.IsLabelledTerm j c t p → S.IsLabelledTerm j c t p' →
  frameImage (u * p.2).1.1 = frameImage (u' * p'.2).1.1 → p = p' := by
  rintro ⟨o, s, h, rfl⟩ ⟨o', r, g, e⟩ f
  obtain ⟨⟨k, rfl, a⟩, k', rfl, a'⟩ := one_mul s ▸ termsOver.mul hu.1.2 h,
    one_mul r ▸ termsOver.mul hu'.1.2 g
  refine (termsOver.eq_and_mem_classUnip₀ ⟨k, rfl, a⟩ ⟨_, Equiv.injective _
    (Prod.ext (QuotientGroup.eq.2 ?_) e), a'⟩ f).rec fun e x ↦ Prod.ext e (by rw [← o.1.2,
    (DoubleCoset.eq (b := p'.2)).2 ⟨_, mul_mem (inv_mem hu') hu, _, x, by group⟩, e, o'.1.2])
  use k'⁻¹ * k, mem_besselS_iff_frameImage.2 (by erw [frameImage_inv_mul_eq_iff.2] <;> simp [*,
    frameImage_termPosition]), by simp

/-- Let γ, γ' have level j and equal Z, ξ rows of Z including all below min(j,ϱ). If the middle
rows of h_c⁻¹γ'h_c''f − h_c⁻¹γh_c'f lie in the Ô-row span of gξ and g·`Filling.paddedLeading` j Z,
then γ'f − γf below the e-rows is g·l·ξ on X₀, `Filling.classCoordX₀` c·l integral.
Here f is the frame, Z = `frameProducts`, h_c⁻¹γh_c' = `termPosition`, g the number `S.g`. -/
lemma HasLevel.exists_frameImage_toRows₂_eq_add [StablyUnram E]
    {c' c'' γ γ' j ι} [Fintype ι] (q : ι ↪ _) (h :
  S.HasLevel j γ) (H : ∀ a ∉ Set.range q, ↑j ≤ a.1) (h' : S.HasLevel j γ') (e : S.frameProducts γ' =
  S.frameProducts γ) : let ξ := (xRows (S.frameProducts γ)).submatrix q id
  let t := (S.g : E)⁻¹ • (paddedLeading j (S.frameProducts γ))⁻¹
  (∀ r, (frameMiddle (S.termPosition c c'' γ') - frameMiddle (S.termPosition c c' γ))ᴴ.col r ∈
    S.gIdele • colLattice (Ô E) (finAdeleMat ξ)ᴴ ⊔ preimageLattice _
  (finAdeleMat tᴴ)) → ∃ l : Matrix _ ι E, IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMat l) ∧
    (frameImage γ').toRows₂ = (frameImage γ).toRows₂ + fromRows
    (fromRows (S.g • (l * ξ)) 0) 0 := let x := (frameMiddle γ'.1.1 - frameMiddle γ).toRows₁; by
    intro ξ t e'
    have ⟨a, _, ia, Q, iq, w⟩ := exists_preimageLattice_eq_colLattice ⟨_, gram_classCoordX₀ c⟩
    have := by simpa using forall_fin_succ'.1 (congrFun e)
    choose Λ iΛ f using (by simpa [Submodule.mem_sup, colLattice, frameMiddle,
      frameImage_termPosition, classCoord_eq_fromBlocks, -funext_iff,
      ← eq_sub_iff_add_eq', pointwise_smul_def] using e' ·)
    have ⟨μ, k, k'⟩ := DenseRange.exists_mem_open (f := finAdeleMat) (.piMap (.piMap ∘ fun _ _ ↦
      denseRange_algebraMap_finAdele)) ((isOpen_Ô.matrix.prod isOpen_Ô.matrix).preimage (f :=
      fun M ↦ (S.classCoordX₀ c * M, S.classCoordX₀ c * ((finAdeleMat x -
      S.gIdele • M * finAdeleMat ξ) * finAdeleMat t))) (by fun_prop)) ⟨a.1 * Q * Λᴴᵀ, by
      simpa [by simpa using congr(a.1 * $w * a.1⁻¹ * finAdeleMat (x * t))] using!
        And.intro (ia.mul (iq.mul (.isInt_conjTranspose (.isInt_transpose iΛ)))) (ia.mul (iq.mul
        (N := (S.classCoordX₀ c * finAdeleMat x - S.gIdele • Λᴴᵀ * finAdeleMat ξ) * finAdeleMat t)
      (by simpa [x, *, mul_sub, ← Algebra.commutes] using! star_mem_Ô <| f · ·)))⟩
    let L := (x - S.g • μ * ξ) * t
    have v b hb r : L r b = 0 := col_eq_zero_of_norm_lt_one (by simpa [L] using k' · ·) r (by
      simp_intro v [L, x, t, ξ, sub_mul, ← mul_sum, -map_sum, by simpa using
        (h.middle_shared_vector_le b hb).1]
      grw [norm_sub_le, add_sq_le, ← mul_sum, sum_add_distrib,
        ← (by simp : S.g ≠ 0).pos.nat_succ_le]
      linarith! [(h.middle_shared_vector_le b hb).2 v, (e ▸ h'.middle_shared_vector_le b hb).2 v])
    use L.submatrix id (castSucc ∘ q) + μ, (by simpa [mul_add, L] using add_mem (k' _ _) <| k · ·)
    rw [Matrix.add_mul, (Matrix.ext fun k b ↦ Fintype.sum_of_injective _ (q.trans castSuccEmb).2 _ _
      (by simp_all [forall_fin_succ']) (by simp [paddedLeading, ξ]; grind) : _ * _ =
      L * paddedLeading j (S.frameProducts γ))]
    simp [L, x, t, h.2, ← ext_iff, *, -frameGram]

end Filling

open Fintype MeasureTheory Real ComplexOrder Norms.L2Operator IsHermInvolution
variable {𝔰 : Shape} (γ : 𝔰.G₁)

/-- The volume Δ(γ) = |det ⟨v_a, γ⁻¹f_b⟩|, Euclidean products, for the basis v = (e₁ − e*₁, …,
e_ϱ − e*_ϱ, 2z) of a maximal negative subspace. -/
def frameVolume := ‖(((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ * γ⁻¹.1.1 * 𝔰.frameCols).det‖

/-- For γ in G₁, the κ × (ϱ+1) complex matrix whose columns are the X₀-components of the images
γe₁, …, γe_ϱ, γz of the frame vectors. -/
def frameX₀Part := 𝔰.definiteColsᴴ * γ.1.1 * 𝔰.frameCols

/-- The volume weight Δ(y) is strictly positive for every y ∈ G₁. -/
lemma frameVolume_pos : 0 < frameVolume γ := by
  simp_rw [frameVolume, norm_pos_iff, ← exists_mulVec_eq_zero_iff.not, ← mulVec_mulVec]; rintro ⟨⟩
  set w := γ⁻¹.1.1 *ᵥ _ with ← e
  simpa [inclMatrix_gram_eq_one besselFrame_injective, *] using congr(𝔰.frameColsᴴ *ᵥ γ *ᵥ $(e.trans
    (dotProduct_star_self_pos_iff.not_left.1 (have := e ▸ U.form_mulVec_mulVec ..
    by simp_all [-sub_mulVec, inclMatrix, entrywise, sum_univ_castSucc, funext_iff,
      forall_fin_succ', add_neg_eq_zero, J₁_eq, RCLike.conj_mul, not_lt_of_ge]))))

attribute [local simp] Matrix.mul_apply inclMatrix_gram_mul_eq_zero frameVolume castLE_injective
  ne_of_gt abs_of_pos frameGram
  inclMatrix_gram_mul_eq_self inclMatrix_gram_eq_zero forall_fin_succ' frameX₀Part

attribute [local simp ←] conjTranspose_submatrix

/-- The volume Δ on G₁ is left invariant under 𝖴⁰: for u in the subgroup 𝖴⁰ of the Bessel
unipotent group fixing every frame vector, and any y in G₁, Δ(uy) = Δ(y). -/
lemma frameVolume_mul_left (hu : γ ∈ besselU0) y : frameVolume (γ * y) = frameVolume y := by
  cases mem_besselU0_iff_unipotentOf.1 (inv_mem hu)
  simp [val_unipotentOf_coe, *]

@[fun_prop] lemma continuous_frameVolume : Continuous (@frameVolume 𝔰) := by fun_prop [frameVolume]

/-- Fix `besselSize` y ≤ θ, e: σ ↪ j, V; R, z = Z_j (leading block) invertible. Some measurable
K has ∫K ≤
((2θ²)^j/|det z|)^(k+n)(π^|σ|/(|σ|!θ^{2|σ|}|det R|²))^k, and (Δ(y)/Δ(γ⁻¹y))^(k+n) ≤ K(A)
whenever Z(γ) = Z, `IsNormalForm` j γ, and γf₁, …, γf_j have X₀-components V + (AR,0)z. -/
lemma exists_kernel_frameVolume_le {y θ} (hθ : besselSize y ≤ θ) {σ j} [Fintype.{0} σ] (e :
  σ ↪ Fin j) (R : Matrix σ σ ℂ) (hR : R.det ≠ 0) {Z : 𝔰.FrameMat} {l : j ≤ 𝔰.n} : let i := castLE l
  let z := Z.submatrix i i
  z.det ≠ 0 → ∀ V, ∃ K, Measurable K ∧ ∫⁻ a : Matrix 𝔰.κ σ ℂ, K a ≤ .ofReal (((2 * θ ^ 2) ^ j /
  ‖z.det‖) ^ (𝔰.k + 𝔰.n) * (π ^ Fintype.card σ / (Fintype.card σ).factorial /
    (θ ^ Fintype.card σ * ‖R.det‖) ^ 2) ^ 𝔰.k) ∧ ∀ γ A, realFrameGram γ = Z → IsNormalForm j γ →
    frameX₀Part γ * inclMatrix ℂ i = V + A * R * (inclMatrix ℂ e)ᴴ * z →
    .ofReal ((frameVolume y / frameVolume (γ⁻¹ * y)) ^ (𝔰.k + 𝔰.n)) ≤ K A := by
  have ⟨ω, ι, g⟩ := _root_.exists_norm_le_of_besselSize_le hθ
  intro i z hD V
  have := (Units.norm_pos _).trans_le g
  let T := (θ • frameMatrix ω).submatrix i i
  have : T.det = θ ^ j ∧ (T.submatrix e e).det = θ ^ Fintype.card σ := by constructor
    <;> erw [det_smul_of_tower θ, det_eq_one_of_unitriangular fun _ _ ↦
    (frameMatrix_unitriangular ι _ _ ·|>.trans _)] <;> simp [i]
  have hB := (mul_mul_eq_of_mul_eq rfl).symm.trans (nonsing_inv_mul _
    (norm_pos_iff.1 (frameVolume_pos y)).isUnit)
  set B := (_ : 𝔰.FrameMat) * (_ : type_of% 𝔰.frameColsᴴ)
  let I := inclMatrix ℂ (𝔰.besselFrame ∘ i)
  let p := Z.submatrix id i * z⁻¹
  have o : p.submatrix i id = 1 := mul_nonsing_inv _ hD.isUnit
  let C := T * pᴴ * B
  let c := (V * z⁻¹ * Tᴴ - 𝔰.definiteColsᴴ * Cᴴ) * inclMatrix ℂ e
  let S := R * ((T * inclMatrix ℂ e)ᴴ * inclMatrix ℂ e)
  refine ⟨_, by fun_prop, (lintegral_eq_lmarginal_univ 0).trans_le ((hua_integral_le S ?_ c
    .one (by bound) _ (card_le_of_embedding (e.trans (castLEEmb l))) _).trans_eq
    (congrArg _ (congrArg _ ?_))), fun γ A s ⟨_, u, h⟩ v ↦ ENNReal.ofReal_mono ?_⟩
  iterate 2 simp [S, mul_inclMatrix, *, mul_comm]
  let t := γ.1.1 * I * z⁻¹
  have f : 𝔰.frameColsᴴ * 𝔰.J₁ * t = p :=
    mul_mul_eq_of_mul_eq (by simp [← s, I, inclMatrix, ← ext_iff])
  let M := B * t * z - inclMatrix ℂ i
  choose X _ w x using fun b ↦ show ∃ X Y, (B * γ.1.1 * 𝔰.frameCols) *ᵥ Y = (1 + M * pᴴ) *ᵥ X ∧
      ‖X b‖ = 1 ∧ Y b = 1 ∧ ∀ a > b, X a = 0 ∧ Y a = 0 by
    by_cases! b < j; use Pi.single b 1, Pi.single b 1
    simp_all [M, t, I, i, funext_iff, (congr($o ⟨b, ‹_›⟩) : p b = _), inclMatrix]
    obtain ⟨X, Y, e, rfl, _⟩ := h b ‹_›
    use X, Y, ?_, by simpa using congr(√‖$u‖)
    convert congr((B + M * tᴴ * 𝔰.J₁) *ᵥ $e).symm <;> simp [← mul_inclMatrix, ← f, t,
      isHermitian.eq, ← U.form_mul_inv_eq, *]
    simp [I, J₁_eq, (funext fun a ↦ besselFrame_castSucc ⟨a, by lia⟩ : 𝔰.besselFrame ∘ i = _)]
  have k : I = _ := (mul_inclMatrix 𝔰.frameCols i).symm
  let Y := 𝔰.J₁ * t * Tᴴ - Cᴴ
  let W := 𝔰.definiteColsᴴ * Y
  let G := A * S + c
  have P := PosDef.one.add_posSemidef G.posSemidef_self_mul_conjTranspose
  have n := congr(‖det $((ext_col w : _ * (of _)ᵀ = _ * (of X)ᵀ))‖)
  simp +contextual [*, M, mul_inclMatrix pᴴ, ↓det_mul, ← Matrix.mul_assoc, ↓M.det_one_add_mul_comm,
    det_of_isLowerTriangular (of _), BlockTriangular] at n
  grw [show ∑ i, _ = Gᴴ * G by ext; apply Matrix.sum_apply, det_one_add_mul_comm, show _ / _ = _ by
    simp [B, field, -conjTranspose_sub].trans congr($n⁻¹), (det_one_add_mul_comm W _ ▸
    ostrowski_taussky (Θ := -C * t * Tᴴ) (.add .one W.posSemidef_conjTranspose_mul_self)
    ?_ :).trans' (norm_det_le_norm_det_of_posSemidef P.posSemidef ?_)]
  iterate 2 simp [C, *, det_neg, pow_two, mul_pow, field, ↓det_mul, div_pow, P.det_pos.ne']
  let D := C * y.1.1
  let Q := θ⁻¹ • (ω * y)⁻¹.1.1 * I
  convert (posSemidef_bessel (E := Q) (by grw [l2_opNorm_mul, norm_smul, U.norm_inv, g,
    norm_inclMatrix_le_one] <;> simp [*, i, besselFrame_injective]) D).add
    (𝔰.zColᴴ * I * z⁻¹ * Tᴴ).posSemidef_conjTranspose_mul_self
  simp [(by simp +contextual [W, ← ext_iff, inclMatrix, J₁_eq] : 𝔰.frameColsᴴ * Y = 0 → Wᴴ * W =
    Yᴴ * (𝔰.J₁ * Y)) (by simp [Y, *, C, ← Matrix.mul_assoc, ← B.conjTranspose_mul]), Y, t,
    isHermitian.eq, mul_mul_eq_of_mul_eq mul_self, mul_mul_eq_of_mul_eq (U.form_mul_inv_eq γ).symm,
    ← D.conjTranspose_mul, show D * Dᴴ = -(C * (𝔰.J₁ * Cᴴ)) by
    simpa [D, C, B, mul_mul_eq_of_mul_eq mul_self] using congr(C * $(U.coe_inv mul_self y⁻¹) *
      Dᴴ), show D * Q = 1 by simp [D, C, mul_mul_eq_of_mul_eq hB, mul_inclMatrix pᴴ, *,
    mul_eq_one_comm (a := T), ← show y⁻¹.1.1 * I = Q * T by
    ext a b; simp_rw +zetaDelta [mul_inclMatrix]; apply congr($(frameVector_eq_sum (i b) ι) a).trans
    rw [mul_apply, sum_of_injective i] <;> simp [frameVector, field,
      i]; grind [frameMatrix_unitriangular, one_apply_ne]]]
  simp [k, J₁_eq]; abel
  convert posSemidef_bessel (norm_inclMatrix_le_one e.2) W
  simp [W, Y, G, S, c, t, k, ← sub_eq_of_eq_add v, hD, J₁_eq]; abel

lemma frameX₀Part_unipotentOf_inv_mul q : frameX₀Part ((unipotentOf q)⁻¹ * γ) =
  frameX₀Part γ + q.1ᴴ * Filling.xRows (realFrameGram γ) := by simp [← ext_iff, inclMatrix,
  splitGram, middleGram, val_unipotentOf_coe, ↓by simpa using U.coe_inv mul_self (unipotentOf q)]
