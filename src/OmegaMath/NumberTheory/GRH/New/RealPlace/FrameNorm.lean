import OmegaMath.NumberTheory.GRH.New.Filling.BesselSystem
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Basic properties of frame vectors and the size function modulo the Bessel subgroup. Norm
bounds for unitary elements from bounded frames and bounded dual frames. -/

open CStarRing Finset InnerProductSpace MatMul Matrix Subgroup WithLp Norms.L2Operator

variable {𝔰 : Shape} (a) {y s : 𝔰.G₁} (x y' : 𝔰.G₁) {M} (a' b)

@[fun_prop] lemma continuous_frameVector :
  Continuous (@frameVector 𝔰 · a) := by fun_prop [frameVector]

lemma frameVector_mul (hs : s ∈ besselU0 ⊔ besselH) : frameVector (s * y) = frameVector y := by
  ext; simp [frameVector, mul_apply, fun i a ↦ by simpa using
    (sup_le inf_le_right (comap_mono (by intro _ h i; grind [h i])) (inv_mem hs) i _ ⟨a, rfl⟩)]

lemma frameVector_eq_sum (hs : s ∈ besselU) : frameVector y a = ∑ b,
  frameMatrix s b a • frameVector (s * y) b := by
  ext i
  simpa [mul_comm (frameMatrix ..), frameVector, mul_apply] using!
    congrFun₂ (submatrix_mul_besselFrame hs (y⁻¹ * s⁻¹) id) i a

lemma norm_frameVector_le : ‖frameVector y a‖ ≤ ‖y.1.1‖ := by
  simpa [↓U.norm_inv, frameVector] using! y⁻¹.1.1.l2_opNorm_mulVec (.single _ 1)

lemma norm_sum_le_mul_norm_sum_frameVector {ι} [Fintype ι] (e c : ι → _) i :
  ‖∑ a, c a * s.1 i (𝔰.besselFrame (e a))‖ ≤ ‖(s * y).1.1‖ * ‖∑ a, c a • frameVector y (e a)‖ := by
  grw [← l2_opNorm_mulVec, ← PiLp.norm_apply_le _ i]
  simp [frameVector, mulVec_sum, ← mul_apply, mulVec_apply_eq_sum]

lemma besselSize_le (hs : s ∈ besselS) : besselSize y ≤ ‖(s * y).1.1‖ + 1 :=
  csInf_le ⟨1, fun _ ↦ by aesop⟩ (by tauto)

/-- If `besselSize` y ≤ T, then some u in the Bessel unipotent group 𝖴 has operator norm ‖uy‖ ≤
T. -/
lemma exists_norm_le_of_besselSize_le {T} (h : besselSize y ≤ T) : ∃ u ∈ besselU, ‖(u * y).1.1‖ ≤
  T := by
  choose s _ using exists_lt_of_ciInf_lt (h.trans_lt (lt_add_one T))
  choose _ _ w _ using exists_besselU_mul_toBesselH s⁻¹.2
  use embedH w * s, by simp_all [inv_eq_iff_eq_inv], by grind [norm_embedH_mul, mul_assoc]

lemma besselSize_besselS_mul (hs : s ∈ besselS) :
    besselSize (s * y) = besselSize y := (Equiv.mulRight ⟨s, hs⟩).iInf_congr (by simp [mul_assoc])

lemma besselSize_le_norm_mul : besselSize y' ≤ ‖(x⁻¹ * y').1.1‖ * besselSize x :=
  (le_ciInf fun s ↦ by
    grw [besselSize_le s.2, mul_comm, add_mul, ← norm_mul_le, ← U.one_le_norm]
    simp [mul_assoc]).trans (Real.mul_iInf_of_nonneg (by simp) _).ge

@[fun_prop] lemma continuous_besselSize : Continuous (@besselSize 𝔰) := .of_at fun y ↦ by
    refine .squeeze ?_ ?_ ((div_le_iff₀' (Units.norm_pos _)).2 <|
      besselSize_le_norm_mul · y) (besselSize_le_norm_mul y) <;>
  apply (ContinuousAt.tendsto (by fun_prop (disch := simp))).trans <;> simp

lemma norm_inclMatrix_le_one {m n : Type} [Fintype m] [Fintype n] {e : n → m} (h : e.Injective) :
    ‖inclMatrix ℂ e‖ ≤ 1 := le_of_sq_le_sq (by simp [sq,
  ← l2_opNorm_conjTranspose_mul_self, inclMatrix_gram_eq_one h, IsStarProjection.norm_le]) (by simp)

@[local simp] lemma norm_J₁ : ‖𝔰.J₁‖ = 1 := norm_of_mem_unitary IsHermInvolution.mem_unitary

/-- Let x in G₁ have all |x⁻¹f_i| ≤ M and all |x⁻¹e*_a| ≤ M, with 1 ≤ M. Then ‖x‖ + 1 ≤ 8(ϱ+1)M. -/
lemma norm_le_of_mem_frameBox (h : x ∈ frameBox M) (h1 : 1 ≤ M) (h' :
  ∀ a, ‖toLp 2 (x⁻¹.1 · (eStar a))‖ ≤ M) : ‖x.1.1‖ + 1 ≤ 8 * (𝔰.ϱ + 1) * M := by
  obtain ⟨e, o⟩ := congr(x⁻¹ * $(U.coe_inv IsHermInvolution.mul_self x⁻¹) * 𝔰.J₁), U.one_le_norm x
  simp_all [frameBox, Fin.forall_fin_succ', frameVector, IsHermInvolution.mul_self, ← U.norm_inv,
    ← star_eq_conjTranspose]
  have s (Z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) : ‖∑ j, rankOne ℂ (toLp 2 (Z · j))
    (PiLp.single 2 j (1 : ℂ))‖ = ‖Z‖ := congrArg _ (by ext; simp [mulVec_eq_sum, inner])
  grw [← mul_le_mul_iff_left₀ (one_pos.trans_le o), add_mul, ← norm_self_mul_star,
    norm_le_insert', norm_J₁, e, ← mul_assoc, ← sub_mul, norm_mul_le, ← s, norm_sum_le]
  simp [↓norm_rankOne, splitGram, middleGram, mul_apply, ← Pi.sub_def, ← Pi.neg_def]
  grw [norm_sub_le, norm_sub_le, norm_add_le, h.1, h.1, h', h']
  simp; nlinarith [one_le_mul_of_one_le_of_one_le h1 o]

lemma norm_inner_J₁_le {v w} : ‖⟪v, toEuclideanLin 𝔰.J₁ w⟫_ℂ‖ ≤ ‖v‖ * ‖w‖ := by
  grw [norm_inner_le_norm, ← one_mul ‖w‖, ← norm_J₁, ← l2_opNorm_mulVec]; rfl

lemma realFrameGram_eq_inner : realFrameGram x a' b = ⟪frameVector y' a',
  toEuclideanLin 𝔰.J₁ (frameVector (x⁻¹ * y') b)⟫_ℂ :=
  congr(($(y'⁻¹.2.symm) * x) _ _).trans (by simp_rw [mul_assoc]; apply dotProduct_comm)

lemma realFrameGram_mul_invariant {s} (t : s ∈ besselU0 ⊔ besselH) : realFrameGram (s * x) =
  realFrameGram x ∧ realFrameGram (x * s) = realFrameGram x := by simp [← Matrix.ext_iff,
  realFrameGram_eq_inner (_ * x) (s * s), realFrameGram_eq_inner _ s, frameVector_mul, mul_assoc, *]

lemma realFrameGram_eq_frameMatrix_mul {s} (h : s ∈ besselU) : realFrameGram x =
  (frameMatrix s)ᴴ * realFrameGram (s * x) := by
  simpa [↓mem_besselU0_iff.1] using! frameGram_inv_mul_mul (γ := s * x) h (one_mem _)

lemma norm_realFrameGram_le_mul : ‖realFrameGram x a' b‖ ≤ ‖frameVector y' a'‖ * ‖frameVector
  (x⁻¹ * y') b‖ := by grw [realFrameGram_eq_inner, norm_inner_J₁_le]

/-- Let V_0, …, V_{2ϱ} have lengths at most M ≥ 1, with V_a = x⁻¹f_{a+1} for a ≤ ϱ, and h(V_a,
V_b) = −1 if a+b = 2ϱ, 0 if a+b < 2ϱ. Then `besselSize` x ≤ 8(ϱ+1)M. -/
lemma besselSize_le_of_dual (hM : 1 ≤ M) (V : ℕ → _) (h : ∀ a, frameVector x a = V a) (n :
  ∀ a ≤ 2 * 𝔰.ϱ, ‖V a‖ ≤ M) (k : ∀ a b, a + b ≤ 2 * 𝔰.ϱ → ⟪V a, toEuclideanLin 𝔰.J₁ (V b)⟫_ℂ =
  ite (a + b = 2 * 𝔰.ϱ) (-1) 0) : besselSize x ≤ 8 * (𝔰.ϱ + 1) * M := by
  have d := gramSchmidt_def'' ℂ (frameVector x)
  set f := gramSchmidt ℂ (frameVector x)
  have hu := liftUnitri_mem_besselU fun ⟨(a, b), _⟩ ↦ ⟪f a, frameVector x b⟫_ℂ / ‖f a‖ ^ 2
  set u := liftUnitri _
  have e : frameVector (u * x) = f :=
    funext (WellFoundedLT.fix fun b i ↦ by simpa +contextual [u, i, unitriMatrix,
    (add_comm (f b)), sum_ite, filter_gt_eq_Iio] using (frameVector_eq_sum b hu).symm.trans (d b))
  have l a : 1 ≤ ‖f a‖ * M := by grw [← n (2 * 𝔰.ϱ - a), ← norm_inner_J₁_le, ← e,
    frameVector_eq_sum a (inv_mem
    hu), sum_inner, sum_eq_single a (lt_or_ge · a |>.rec ?_ ?_)] <;> simp +contextual (disch := lia)
    [↓frameMatrix_unitriangular (inv_mem hu), inner_smul_left, *]
  have z a : 0 < ‖f a‖ := by nlinarith [l a]
  replace d a : ‖f a‖ ≤ M := le_of_mul_le_mul_left (by
    grw [← n a (by lia), ← h, ← @norm_inner_le_norm ℂ, d]; simp +contextual [f, ← mem_Iio,
    ne_of_gt, gramSchmidt_orthogonal, sq, inner_add_right, inner_sum, inner_smul_right]) (z a)
  let v a := ‖f a‖⁻¹ ^ 2 • f a
  have ⟨q, k⟩ := (by simpa only [Matrix.mul_assoc, mul_mul_eq_of_mul_eq IsHermInvolution.mul_self,
    mul_inclMatrix, Matrix.one_mul] using
    (@exists_mul_unipotentOf_dualCols_eq _ (u * x)⁻¹ (𝔰.J₁ * (of (v ·.castSucc ·))ᵀ)) :) ?_ ?_
  exact besselSize_besselS_mul (mem_unitriGroup_of_mem_besselU hu) ▸
    (besselSize_le (mem_unitriGroup_of_mem_besselU (inv_mem (unipotentOf_mem_besselU0 q).1))).trans
    (norm_le_of_mem_frameBox _ (by simp_all [frameBox, frameVector_mul, mem_sup_left,
    unipotentOf_mem_besselU0]) hM fun j ↦ .trans (congr(‖toLp 2
    ($kᵀ j)‖).trans_le (l2_opNorm_mulVec _ (v _))) (by simp [*, v, norm_smul, field]))
  all_goals ext; apply (dotProduct_comm ..).trans
  show ⟪frameVector (u * x) _, v _⟫_ℂ = ite ..; aesop (add simp gramSchmidt_orthogonal)
  show ⟪toEuclideanLin _ (v _), v _⟫_ℂ = 0
  simp [inner_eq_zero_symm, v, ← by simpa [e] using realFrameGram_eq_inner 1 (u * x), frameGram]
