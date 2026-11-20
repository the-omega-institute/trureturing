import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Weil.ZetaLinear.PoleCapacityRankOne

/-!
# Signed residue rank budget

For two positive semidefinite matrices with common lower and off-diagonal blocks,
the positive directions of the upper difference and the range of the lower block
together give a positive subspace for the first matrix. For a finite family in
these block coordinates, a positive definite total makes the sum of the lower
blocks full rank. This gives a rank budget for each sign of the upper differences.
-/

noncomputable section

open Matrix RHLinalg
open scoped BigOperators ComplexOrder

namespace SignedResidueRankBudget

variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [Fintype m]

private theorem hermForm_fromBlocks
    (A₀ : Matrix n n 𝕜) (E : Matrix n m 𝕜) (F : Matrix m n 𝕜) (C : Matrix m m 𝕜)
    (u : n → 𝕜) (v : m → 𝕜) :
    hermForm (fromBlocks A₀ E F C) (Sum.elim u v) =
      RCLike.re (star u ⬝ᵥ (A₀ *ᵥ u + E *ᵥ v) + star v ⬝ᵥ (F *ᵥ u + C *ᵥ v)) := by
  have hu : Sum.elim u v ∘ Sum.inl = u := rfl
  have hv : Sum.elim u v ∘ Sum.inr = v := rfl
  simp only [hermForm, Function.star_sumElim, Matrix.fromBlocks_mulVec, hu, hv,
    sumElim_dotProduct_sumElim]

private theorem posDefOn_range_of_posSemidef {C : Matrix m m 𝕜} (hC : C.PosSemidef) :
    PosDefOn C (LinearMap.range C.mulVecLin) := by
  rintro _ ⟨y, rfl⟩ hy
  change C *ᵥ y ≠ 0 at hy
  have hq : 0 < star (C *ᵥ y) ⬝ᵥ (C *ᵥ (C *ᵥ y)) := by
    refine lt_of_le_of_ne (hC.dotProduct_mulVec_nonneg (C *ᵥ y)) ?_
    intro hz
    have hzero : C *ᵥ (C *ᵥ y) = 0 := hC.dotProduct_mulVec_zero_iff.mp hz.symm
    apply hy
    apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero C y).mp
    simpa only [hC.isHermitian.eq, Matrix.mulVec_mulVec] using hzero
  exact (RCLike.pos_iff.mp hq).1

/-- Positive subspaces of the upper difference contribute their dimension in
addition to the rank of the common lower block. -/
private theorem finrank_add_rank_le_rank_fromBlocks
    {A₀ B₀ : Matrix n n 𝕜} {E : Matrix n m 𝕜} {C : Matrix m m 𝕜}
    (hA : (fromBlocks A₀ E Eᴴ C).PosSemidef)
    (hB : (fromBlocks B₀ E Eᴴ C).PosSemidef)
    {U : Submodule 𝕜 (n → 𝕜)} (hU : PosDefOn (A₀ - B₀) U) :
    Module.finrank 𝕜 U + C.rank ≤ (fromBlocks A₀ E Eᴴ C).rank := by
  classical
  have hC : C.PosSemidef := hA.submatrix (Sum.inr : m → n ⊕ m)
  let V := LinearMap.range C.mulVecLin
  let split := LinearEquiv.sumArrowLequivProdArrow n m 𝕜 𝕜
  let join : (↥U × ↥V) →ₗ[𝕜] ((n ⊕ m) → 𝕜) :=
    split.symm.toLinearMap.comp (U.subtype.prodMap V.subtype)
  have hjoin : Function.Injective join := by
    intro x y h
    have hcoords : ((x.1 : n → 𝕜), (x.2 : m → 𝕜)) =
        ((y.1 : n → 𝕜), (y.2 : m → 𝕜)) := split.symm.injective h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hcoords))
      (Subtype.ext (congrArg Prod.snd hcoords))
  have hpositive : PosDefOn (fromBlocks A₀ E Eᴴ C) (LinearMap.range join) := by
    rintro _ ⟨⟨u, v⟩, rfl⟩ hne
    change Sum.elim (u : n → 𝕜) (v : m → 𝕜) ≠ 0 at hne
    change 0 < hermForm (fromBlocks A₀ E Eᴴ C) (Sum.elim (u : n → 𝕜) (v : m → 𝕜))
    by_cases hu : (u : n → 𝕜) = 0
    · have hv : (v : m → 𝕜) ≠ 0 := by
        intro hv
        apply hne
        rw [hu, hv]
        funext i
        cases i <;> rfl
      rw [hu, hermForm_fromBlocks]
      simpa only [star_zero, zero_dotProduct, Matrix.mulVec_zero, zero_add, hermForm] using
        (posDefOn_range_of_posSemidef hC (v : m → 𝕜) v.property hv)
    · have hblocks : fromBlocks A₀ E Eᴴ C - fromBlocks B₀ E Eᴴ C =
          fromBlocks (A₀ - B₀) (0 : Matrix n m 𝕜) (0 : Matrix m n 𝕜)
            (0 : Matrix m m 𝕜) := by
        apply Matrix.ext
        intro i j
        cases i <;> cases j <;> simp
      let x := Sum.elim (u : n → 𝕜) (v : m → 𝕜)
      have hdiff : hermForm (fromBlocks A₀ E Eᴴ C) x - hermForm (fromBlocks B₀ E Eᴴ C) x =
          hermForm (A₀ - B₀) (u : n → 𝕜) := by
        rw [← hermForm_sub, hblocks]
        dsimp only [x]
        rw [hermForm_fromBlocks]
        simp only [Matrix.zero_mulVec, add_zero, dotProduct_zero, hermForm]
      change 0 < hermForm (fromBlocks A₀ E Eᴴ C) x
      apply lt_of_le_of_lt (hermForm_nonneg_of_posSemidef hB x)
      apply sub_pos.mp
      rw [hdiff]
      exact hU (u : n → 𝕜) u.property hu
  calc
    Module.finrank 𝕜 U + C.rank = Module.finrank 𝕜 (↥U × ↥V) :=
      Module.finrank_prod.symm
    _ = Module.finrank 𝕜 (LinearMap.range join) :=
      (LinearMap.finrank_range_of_inj hjoin).symm
    _ ≤ posIndex hA.isHermitian := finrank_le_posIndex_of_posDefOn hA.isHermitian hpositive
    _ = (fromBlocks A₀ E Eᴴ C).rank := posIndex_eq_rank_of_posSemidef hA

omit [Fintype n] [Fintype m] in
/-- The upper difference of two PSD block matrices is Hermitian. -/
theorem isHermitian_upper_sub_of_posSemidef_fromBlocks
    {A₀ B₀ : Matrix n n 𝕜} {E : Matrix n m 𝕜} {C : Matrix m m 𝕜}
    (hA : (fromBlocks A₀ E Eᴴ C).PosSemidef)
    (hB : (fromBlocks B₀ E Eᴴ C).PosSemidef) : (A₀ - B₀).IsHermitian := by
  have hA₀ : A₀.IsHermitian := hA.isHermitian.submatrix (Sum.inl : n → n ⊕ m)
  have hB₀ : B₀.IsHermitian := hB.isHermitian.submatrix (Sum.inl : n → n ⊕ m)
  exact hA₀.sub hB₀

variable [DecidableEq n]

/-- The positive index of the upper difference and the rank of the common lower
block are jointly bounded by the rank of the first matrix. -/
theorem posIndex_add_rank_le_rank_fromBlocks
    {A₀ B₀ : Matrix n n 𝕜} {E : Matrix n m 𝕜} {C : Matrix m m 𝕜}
    (hA : (fromBlocks A₀ E Eᴴ C).PosSemidef)
    (hB : (fromBlocks B₀ E Eᴴ C).PosSemidef)
    (hD : (A₀ - B₀).IsHermitian) :
    posIndex hD + C.rank ≤ (fromBlocks A₀ E Eᴴ C).rank := by
  rw [← finrank_range_hermPosPart hD]
  exact finrank_add_rank_le_rank_fromBlocks hA hB (posDefOn_range_hermPosPart hD)

/-- The negative part of the same upper difference is charged to the second matrix. -/
theorem rank_hermNegPart_add_rank_le_rank_fromBlocks
    {A₀ B₀ : Matrix n n 𝕜} {E : Matrix n m 𝕜} {C : Matrix m m 𝕜}
    (hA : (fromBlocks A₀ E Eᴴ C).PosSemidef)
    (hB : (fromBlocks B₀ E Eᴴ C).PosSemidef)
    (hD : (A₀ - B₀).IsHermitian) :
    (hermNegPart hD).rank + C.rank ≤ (fromBlocks B₀ E Eᴴ C).rank := by
  change Module.finrank 𝕜 (LinearMap.range (hermNegPart hD).mulVecLin) + C.rank ≤ _
  apply finrank_add_rank_le_rank_fromBlocks hB hA
  simpa only [neg_sub] using
    D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart hD

omit [DecidableEq n] in
private theorem rank_sum_le_sum_rank {ι : Type*} (s : Finset ι) (C : ι → Matrix m m 𝕜) :
    (∑ i ∈ s, C i).rank ≤ ∑ i ∈ s, (C i).rank := by
  classical
  have rank_add_le (P Q : Matrix m m 𝕜) : (P + Q).rank ≤ P.rank + Q.rank := by
    rw [Matrix.rank, Matrix.mulVecLin_add]
    exact (Submodule.finrank_mono (LinearMap.range_add_le P.mulVecLin Q.mulVecLin)).trans
      (Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range P.mulVecLin) (LinearMap.range Q.mulVecLin))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (rank_add_le (C i) (∑ j ∈ s, C j)).trans (Nat.add_le_add_left ih _)

/-- On a finite carrier in common block coordinates, each signed part has total
rank at most the upper dimension plus `r`. It suffices that the first total is
positive definite, since its lower compression is also the second total's. -/
theorem sum_signed_parts_rank_budget {ι : Type*} [Fintype ι]
    {A₀ B₀ : ι → Matrix n n 𝕜} {E : ι → Matrix n m 𝕜} {C : ι → Matrix m m 𝕜}
    (hA : ∀ i, (fromBlocks (A₀ i) (E i) (E i)ᴴ (C i)).PosSemidef)
    (hB : ∀ i, (fromBlocks (B₀ i) (E i) (E i)ᴴ (C i)).PosSemidef)
    (htotal : (∑ i, fromBlocks (A₀ i) (E i) (E i)ᴴ (C i)).PosDef) {r : ℕ}
    (hbudgetA : (∑ i, (fromBlocks (A₀ i) (E i) (E i)ᴴ (C i)).rank) ≤
      Fintype.card n + Fintype.card m + r)
    (hbudgetB : (∑ i, (fromBlocks (B₀ i) (E i) (E i)ᴴ (C i)).rank) ≤
      Fintype.card n + Fintype.card m + r) :
    let hD := fun i => isHermitian_upper_sub_of_posSemidef_fromBlocks (hA i) (hB i)
    (∑ i, (hermPosPart (hD i)).rank) ≤ Fintype.card n + r ∧
      (∑ i, (hermNegPart (hD i)).rank) ≤ Fintype.card n + r := by
  classical
  intro hD
  have hcompression :
      (∑ i, fromBlocks (A₀ i) (E i) (E i)ᴴ (C i)).submatrix
        (Sum.inr : m → n ⊕ m) (Sum.inr : m → n ⊕ m) = ∑ i, C i := by
    apply Matrix.ext
    intro j k
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.fromBlocks_apply₂₂]
  have hlower : (∑ i, C i).PosDef := by
    rw [← hcompression]
    exact htotal.submatrix Sum.inr_injective
  have hlowerRank : Fintype.card m ≤ ∑ i, (C i).rank :=
    (Matrix.rank_of_isUnit _ hlower.isUnit).symm.le.trans (rank_sum_le_sum_rank Finset.univ C)
  have hpos : (∑ i, (hermPosPart (hD i)).rank) + (∑ i, (C i).rank) ≤
      ∑ i, (fromBlocks (A₀ i) (E i) (E i)ᴴ (C i)).rank := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [rank_hermPosPart]
    exact posIndex_add_rank_le_rank_fromBlocks (hA i) (hB i) (hD i)
  have hneg : (∑ i, (hermNegPart (hD i)).rank) + (∑ i, (C i).rank) ≤
      ∑ i, (fromBlocks (B₀ i) (E i) (E i)ᴴ (C i)).rank := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ =>
      rank_hermNegPart_add_rank_le_rank_fromBlocks (hA i) (hB i) (hD i)
  constructor <;> omega

end SignedResidueRankBudget
