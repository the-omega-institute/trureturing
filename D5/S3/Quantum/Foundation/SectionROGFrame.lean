/- GID: D5/S3/Quantum/Foundation/SectionROGFrame
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/SectionROGFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole pure carriers and full frames in native rank one generated PSD sections. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
import Mathlib.Tactic
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Proj
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme

/-! Whole pure carriers and ROG complement frames in the original native field. -/

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.SectionROGFrame

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Native rank one PSD matrix, without normalizing or changing fields. -/
def rankOne (v : ι → 𝕜) : HermitianMat ι 𝕜 :=
  ⟨Matrix.vecMulVec v (star v), (Matrix.posSemidef_vecMulVec_self_star v).isHermitian⟩

/-- The native outer product is positive semidefinite. -/
lemma rankOne_nonneg (v : ι → 𝕜) : 0 ≤ rankOne v :=
  HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_vecMulVec_self_star v)

/-- Trace pairing against a native outer product is its quadratic reading. -/
lemma pair_rankOne (A : HermitianMat ι 𝕜) (v : ι → 𝕜) :
    (⟪A, rankOne v⟫_ℝ : 𝕜) = star v ⬝ᵥ (A.mat *ᵥ v) := by
  rw [HermitianMat.inner_eq_trace_rc]
  change (A.mat * Matrix.vecMulVec v (star v)).trace = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- The whole original normalized PSD base, embedded in the ambient real space. -/
def base (L : Submodule ℝ (HermitianMat ι 𝕜)) : Set (HermitianMat ι 𝕜) :=
  {X | X ∈ L ∧ 0 ≤ X ∧ X.trace = 1}

/-- Every original positive matrix is a finite sum of original native rank one
PSD matrices. Zero has the empty decomposition. -/
def ROG (L : Submodule ℝ (HermitianMat ι 𝕜)) : Prop :=
  ∀ X ∈ L, 0 ≤ X → ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 ι),
    (∀ j, v j ≠ 0 ∧ rankOne (v j) ∈ L) ∧ X = ∑ j, rankOne (v j)

/-- All original normalized native rank one matrices, without selecting a subset. -/
def pureRanks (L : Submodule ℝ (HermitianMat ι 𝕜)) : Set (HermitianMat ι 𝕜) :=
  {X | ∃ v : EuclideanSpace 𝕜 ι, ‖v‖ = 1 ∧ rankOne v = X ∧ X ∈ L}

private lemma rankOne_real_smul (v : ι → 𝕜) (r : ℝ) :
    rankOne (r • v) = (r * r) • rankOne v := by
  apply HermitianMat.ext
  change Matrix.vecMulVec (r • v) (star (r • v)) =
    (r * r) • Matrix.vecMulVec v (star v)
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, Pi.star_apply,
    RCLike.real_smul_eq_coe_mul, star_mul, RCLike.star_def,
    RCLike.conj_ofReal, map_mul]
  ring

private lemma rankOne_trace_norm (v : EuclideanSpace 𝕜 ι) :
    (rankOne v).trace = ‖v‖ ^ 2 := by
  rw [HermitianMat.trace_eq_re_trace]
  change RCLike.re (Matrix.vecMulVec (v : ι → 𝕜) (star (v : ι → 𝕜))).trace = _
  rw [Matrix.trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct]
  exact (norm_sq_eq_re_inner (𝕜 := 𝕜) v).symm

private lemma normalized_rankOne (v : EuclideanSpace 𝕜 ι) (hv : v ≠ 0) :
    ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 ∧
    rankOne v = (‖v‖ ^ 2 : ℝ) • rankOne ((‖v‖⁻¹ : ℝ) • v) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨by simp [norm_smul, hn], ?_⟩
  rw [WithLp.ofLp_smul, rankOne_real_smul, smul_smul]
  have h : ‖v‖ ^ 2 * (‖v‖⁻¹ * ‖v‖⁻¹) = 1 := by field_simp
  rw [h, one_smul]

private lemma base_convex (L : Submodule ℝ (HermitianMat ι 𝕜)) : Convex ℝ (base L) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨L.add_mem (L.smul_mem a hX.1) (L.smul_mem b hY.1),
    add_nonneg (smul_nonneg ha hX.2.1) (smul_nonneg hb hY.2.1), ?_⟩
  simp [HermitianMat.trace_add, HermitianMat.trace_smul, hX.2.2, hY.2.2, hab]

private lemma base_eq_hull (L : Submodule ℝ (HermitianMat ι 𝕜)) (hrog : ROG L) :
    base L = convexHull ℝ (pureRanks L) := by
  apply Set.Subset.antisymm
  · intro X hX
    obtain ⟨m, v, hv, hsum⟩ := hrog X hX.1 hX.2.1
    let w : Fin m → ℝ := fun j => ‖v j‖ ^ 2
    let z : Fin m → HermitianMat ι 𝕜 := fun j => rankOne ((‖v j‖⁻¹ : ℝ) • v j)
    have hw : ∑ j, w j = 1 := by
      have hh := congrArg (fun Y => ⟪(1 : HermitianMat ι 𝕜), Y⟫_ℝ) hsum
      simpa [hX.2.2, rankOne_trace_norm, w, inner_sum] using hh.symm
    have hz (j : Fin m) : z j ∈ pureRanks L := by
      refine ⟨(‖v j‖⁻¹ : ℝ) • v j, (normalized_rankOne (v j) (hv j).1).1, rfl, ?_⟩
      dsimp [z]
      rw [rankOne_real_smul (v j)]
      exact L.smul_mem _ (hv j).2
    have hrepr : (∑ j, w j • z j) = X := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro j _
      exact (normalized_rankOne (v j) (hv j).1).2.symm
    rw [← hrepr]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => sq_nonneg _) hw
      (fun j _ => subset_convexHull ℝ _ (hz j))
  · apply convexHull_min
    · rintro X ⟨v, hv, rfl, hL⟩
      exact ⟨hL, rankOne_nonneg v, by rw [rankOne_trace_norm, hv, one_pow]⟩
    · exact base_convex L

private lemma rankOne_self (v : EuclideanSpace 𝕜 ι) (hv : ‖v‖ = 1) :
    ⟪rankOne v, rankOne v⟫_ℝ = 1 := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [pair_rankOne]
  have hunit : star (v : ι → 𝕜) ⬝ᵥ (v : ι → 𝕜) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hv]
    simp
  change star (v : ι → 𝕜) ⬝ᵥ
    (Matrix.vecMulVec (v : ι → 𝕜) (star (v : ι → 𝕜)) *ᵥ (v : ι → 𝕜)) = _
  simp [Matrix.vecMulVec_mulVec, hunit]

private lemma pairing_one_unique (v : EuclideanSpace 𝕜 ι) (hv : ‖v‖ = 1)
    (X : HermitianMat ι 𝕜) (hX : 0 ≤ X) (ht : X.trace = 1)
    (heq : ⟪rankOne v, X⟫_ℝ = 1) : X = rankOne v := by
  have hxx := HermitianMat.inner_le_mul_trace hX hX
  have hpp := rankOne_self v hv
  rw [ht, mul_one] at hxx
  have hnorm : ‖X - rankOne v‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hpp]
    rw [real_inner_comm (rankOne v) X, heq]
    linarith
  have hz := le_antisymm hnorm (sq_nonneg ‖X - rankOne v‖)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The pure carrier is exactly the normalized rank one family of the whole
original ROG section, in the original real or complex field. -/
theorem whole_pure_carrier (L : Submodule ℝ (HermitianMat ι 𝕜)) (hrog : ROG L) :
    (base L).extremePoints ℝ = pureRanks L := by
  apply Set.Subset.antisymm
  · rw [base_eq_hull L hrog]
    exact extremePoints_convexHull_subset
  · rintro X ⟨v, hv, rfl, hL⟩
    refine ⟨⟨hL, rankOne_nonneg v, by rw [rankOne_trace_norm, hv, one_pow]⟩, ?_⟩
    intro A hA B hB hseg
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    have ht : (rankOne v).trace = 1 := by rw [rankOne_trace_norm, hv, one_pow]
    have hpa := HermitianMat.inner_le_mul_trace (rankOne_nonneg v) hA.2.1
    have hpb := HermitianMat.inner_le_mul_trace (rankOne_nonneg v) hB.2.1
    rw [ht, hA.2.2, one_mul] at hpa
    rw [ht, hB.2.2, one_mul] at hpb
    have hvv := rankOne_self v hv
    have hr := congrArg (fun Y => ⟪rankOne v, Y⟫_ℝ) heq
    simp only [inner_add_right, real_inner_smul_right] at hr
    have hpA : ⟪rankOne v, A⟫_ℝ = 1 := by nlinarith
    exact pairing_one_unique v hv A hA.2.1 hA.2.2 hpA

private lemma frame_sum (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :
    (∑ j, rankOne (b j)) = 1 := by
  apply HermitianMat.ext
  rw [HermitianMat.mat_finset_sum]
  change (∑ j, Matrix.vecMulVec (b j : ι → 𝕜) (star (b j : ι → 𝕜))) = 1
  have h := congrArg
    (fun T : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι =>
      Matrix.toEuclideanLin.symm T.toLinearMap) b.sum_rankOne_eq_id
  simpa only [ContinuousLinearMap.toLinearMap_sum, map_sum,
    InnerProductSpace.symm_toEuclideanLin_rankOne, ContinuousLinearMap.coe_id,
    Matrix.toLpLin_symm_id] using h

set_option maxHeartbeats 1000000 in
-- The maximal-family proof elaborates several dependent subspace bases and projectors.
/-- Every original unit rank one point extends to a full orthonormal rank one
frame inside the same ROG section. The initial point is one of its entries;
no division by the complement dimension is used. -/
theorem rog_frame
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L)
    (hrog : ROG L) (v : EuclideanSpace 𝕜 ι) (hv : ‖v‖ = 1) (hvL : rankOne v ∈ L)
    (i₀ : ι) :
    ∃ b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι), b i₀ = v ∧
      (∀ j, rankOne (b j) ∈ L) ∧
      (∀ j, rankOne (b j) ∈ (base L).extremePoints ℝ) ∧
      (∑ j, rankOne (b j)) = 1 := by
  classical
  let A : Set (EuclideanSpace 𝕜 ι) := {x | ‖x‖ = 1 ∧ rankOne x ∈ L}
  have hstart : ({v} : Set (EuclideanSpace 𝕜 ι)) ⊆ A ∧
      Orthonormal 𝕜 (Subtype.val : ({v} : Set (EuclideanSpace 𝕜 ι)) → _) := by
    refine ⟨by simpa [A] using And.intro hv hvL, ?_⟩
    rw [orthonormal_subtype_iff_ite]
    simp [inner_self_eq_norm_sq_to_K, hv]
  obtain ⟨s, hvs, hs⟩ := zorn_subset_nonempty
    {s : Set (EuclideanSpace 𝕜 ι) | s ⊆ A ∧ Orthonormal 𝕜 (Subtype.val : s → _)}
    (by
      intro c hc hchain hne
      refine ⟨⋃₀ c, ⟨?_, orthonormal_sUnion_of_directed hchain.directedOn
        (fun t ht => (hc ht).2)⟩, fun t ht => Set.subset_sUnion_of_mem ht⟩
      intro x hx
      obtain ⟨t, ht, hxt⟩ := hx
      exact (hc ht).1 hxt) {v} hstart
  have hsA : s ⊆ A := hs.1.1
  have hson : Orthonormal 𝕜 (Subtype.val : s → EuclideanSpace 𝕜 ι) := hs.1.2
  have hsfin := hson.linearIndependent.setFinite
  letI : Fintype s := hsfin.fintype
  let S := Submodule.span 𝕜 (Set.range (Subtype.val : s → EuclideanSpace 𝕜 ι))
  let bs : OrthonormalBasis s 𝕜 S :=
    (Module.Basis.span hson.linearIndependent).toOrthonormalBasis
      (by
        convert orthonormal_span hson using 1
        funext j
        exact Module.Basis.span_apply hson.linearIndependent j)
  have hbs (j : s) : (bs j : EuclideanSpace 𝕜 ι) = j.val := by
    simp [bs, Module.Basis.coe_toOrthonormalBasis]
  have hproj : HermitianMat.projector S ∈ L := by
    have heq : HermitianMat.projector S = ∑ j : s, rankOne (j : EuclideanSpace 𝕜 ι) := by
      apply HermitianMat.ext
      rw [HermitianMat.mat_finset_sum]
      change (HermitianMat.projector S).mat =
        ∑ j : s, Matrix.vecMulVec (j.val : ι → 𝕜) (star (j.val : ι → 𝕜))
      simpa [hbs] using HermitianMat.projector_eq_sum_rankOne S bs
    rw [heq]
    exact L.sum_mem (fun j _ => (hsA j.property).2)
  have hbot : Sᗮ = ⊥ := by
    by_contra hnot
    let R := HermitianMat.projector Sᗮ
    have hRpos : 0 ≤ R := HermitianMat.projector_nonneg Sᗮ
    have hRL : R ∈ L := by
      have heq : R = 1 - HermitianMat.projector S := by
        have h := HermitianMat.projector_add_orthogonal S
        dsimp [R]
        exact eq_sub_of_add_eq (by simpa [add_comm] using h)
      rw [heq]
      exact L.sub_mem hI hproj
    have hRne : R ≠ 0 := by
      intro hz
      apply hnot
      apply Submodule.finrank_eq_zero.mp
      have ht := HermitianMat.trace_projector Sᗮ
      change R.trace = _ at ht
      rw [hz, HermitianMat.trace_zero] at ht
      exact_mod_cast ht.symm
    obtain ⟨m, w, hw, hsum⟩ := hrog R hRL hRpos
    have hm : Nonempty (Fin m) := by
      by_contra hn
      haveI : IsEmpty (Fin m) := not_nonempty_iff.mp hn
      exact hRne (by simpa using hsum)
    obtain ⟨j⟩ := hm
    have hdom : rankOne (w j) ≤ R := by
      rw [hsum]
      exact Finset.single_le_sum (fun k _ => rankOne_nonneg (w k)) (Finset.mem_univ j)
    have horth (x : EuclideanSpace 𝕜 ι) (hx : x ∈ s) : ⟪x, w j⟫_𝕜 = 0 := by
      have hxS : x ∈ S := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have hxR : x ∈ R.ker := by
        simpa [R, HermitianMat.projector_ker] using hxS
      have hxP := HermitianMat.ker_antitone (rankOne_nonneg (w j)) hdom hxR
      have hmul := ((rankOne (w j)).mem_ker_iff_mulVec_zero x).mp hxP
      have hwne : (w j : ι → 𝕜) ≠ 0 := by
        intro hz
        apply (hw j).1
        ext k
        exact congrFun hz k
      have hsmul : (star (w j : ι → 𝕜) ⬝ᵥ (x : ι → 𝕜)) • (w j : ι → 𝕜) = 0 := by
        change Matrix.vecMulVec (w j : ι → 𝕜) (star (w j : ι → 𝕜)) *ᵥ
          (x : ι → 𝕜) = 0 at hmul
        simpa only [Matrix.vecMulVec_mulVec, op_smul_eq_smul] using hmul
      have hscalar := (smul_eq_zero.mp hsmul).resolve_right hwne
      rw [inner_eq_zero_symm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      exact hscalar
    let z : EuclideanSpace 𝕜 ι := (‖w j‖⁻¹ : ℝ) • w j
    have hzn : ‖z‖ = 1 := (normalized_rankOne (w j) (hw j).1).1
    have hzL : rankOne z ∈ L := by
      dsimp [z]
      rw [rankOne_real_smul (w j)]
      exact L.smul_mem _ (hw j).2
    have hxz (x : EuclideanSpace 𝕜 ι) (hx : x ∈ s) : ⟪x, z⟫_𝕜 = 0 := by
      have hz : z = ((‖w j‖⁻¹ : ℝ) : 𝕜) • w j := by
        ext k
        simp only [z, PiLp.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
      rw [hz, inner_smul_right, horth x hx, mul_zero]
    have hznot : z ∉ s := by
      intro hz
      have hh := hxz z hz
      rw [inner_self_eq_norm_sq_to_K, hzn] at hh
      norm_num at hh
    have hins : Orthonormal 𝕜 (Subtype.val : ↥(insert z s) → EuclideanSpace 𝕜 ι) := by
      rw [orthonormal_subtype_iff_ite]
      intro x hx y hy
      rcases Set.mem_insert_iff.mp hx with rfl | hx <;>
        rcases Set.mem_insert_iff.mp hy with rfl | hy
      · simp [inner_self_eq_norm_sq_to_K, hzn]
      · have hyz : y ≠ z := by rintro rfl; exact hznot hy
        simp [hyz, Ne.symm hyz, inner_eq_zero_symm.mpr (hxz y hy)]
      · have hxz' : x ≠ z := by rintro rfl; exact hznot hx
        simp [hxz', hxz x hx]
      · exact (orthonormal_subtype_iff_ite.mp hson) x hx y hy
    have heq : insert z s = s := hs.eq_of_ge
      ⟨by simpa [Set.insert_subset_iff, A, hzn, hzL] using hsA, hins⟩ (Set.subset_insert z s)
    exact hznot (heq ▸ Set.mem_insert z s)
  let B : OrthonormalBasis s 𝕜 (EuclideanSpace 𝕜 ι) :=
    OrthonormalBasis.mkOfOrthogonalEqBot hson hbot
  have hB (j : s) : B j = j.val := by simp [B]
  let e : s ≃ ι := Fintype.equivOfCardEq
    ((Module.finrank_eq_card_basis B.toBasis).symm.trans (finrank_euclideanSpace (𝕜 := 𝕜) (ι := ι)))
  let b := B.reindex e
  let i : ι := e ⟨v, hvs (Set.mem_singleton v)⟩
  have hbL (j : ι) : rankOne (b j) ∈ L := by
    dsimp only [b]
    rw [OrthonormalBasis.reindex_apply, hB]
    exact (hsA (e.symm j).property).2
  have hbi : b i = v := by simp [b, i, hB]
  let b' := b.reindex (Equiv.swap i i₀)
  have hb'L (j : ι) : rankOne (b' j) ∈ L := by
    dsimp only [b']
    rw [OrthonormalBasis.reindex_apply]
    exact hbL _
  refine ⟨b', ?_, hb'L, ?_, frame_sum b'⟩
  · simpa [b'] using hbi
  · intro j
    rw [whole_pure_carrier L hrog]
    exact ⟨b' j, b'.orthonormal.norm_eq_one j, rfl, hb'L j⟩

end D5.S3.Quantum.Foundation.SectionROGFrame
