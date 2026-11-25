/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/CompactProjectiveGraphWalsh
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/CompactProjectiveGraphWalsh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reduce the actual compact projective graph-state Walsh coefficients to the characteristic product. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def char (B U : Finset ι) : ℝ := ∏ i ∈ U, if i ∈ B then -1 else 1

omit [Fintype ι] in
private theorem char_eq (B U : Finset ι) : char B U = (-1:ℝ)^(U ∩ B).card := by
  unfold char
  rw [← Finset.prod_filter]
  simp [Finset.filter_mem_eq_inter]

private theorem char_compl (B U : Finset ι) : char B Uᶜ = (-1:ℝ)^B.card * char B U := by
  have h : char B U * char B Uᶜ = char B univ := by
    unfold char
    rw [← prod_union disjoint_compl_right, union_compl]
  have hh : char B U * char B U = 1 := by
    rw [char_eq, ← mul_pow]
    norm_num
  calc
    char B Uᶜ = (char B U * char B U) * char B Uᶜ := by rw [hh, one_mul]
    _ = char B univ * char B U := by linear_combination char B U * h
    _ = _ := by rw [char_eq]; simp

private theorem char_sum_zero (B : Finset ι) (hB : B.Nonempty) :
    ∑ U : Finset ι, char B U = 0 := by
  obtain ⟨i,hi⟩ := hB
  change ∑ U : Finset ι, (∏ j ∈ U, if j ∈ B then (-1:ℝ) else 1) = 0
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

def signedSum (B : Finset ι) (f : Finset ι → ℝ) : ℝ :=
  ∑ U : Finset ι, char B U * f U

private theorem signed_comp_compl (B : Finset ι) (f : Finset ι → ℝ) :
    signedSum B (fun U => f Uᶜ) = (-1:ℝ)^B.card * signedSum B f := by
  let e : Finset ι ≃ Finset ι := ⟨compl, compl, compl_compl, compl_compl⟩
  unfold signedSum
  rw [← e.sum_comp (fun U => char B U * f Uᶜ), mul_sum]
  apply sum_congr rfl
  intro U _
  change char B Uᶜ * f (Uᶜ)ᶜ = _
  rw [compl_compl, char_compl, mul_assoc]

/-- Without the spanning-side assumption, precisely the two-deficient cuts
survive as a correction to the rank polynomial. The identity is denominator-free. -/
private theorem two_deficient_correction (B : Finset ι) (hB : B.Nonempty)
    (r k : Finset ι → ℕ) (d : ℕ) (x : ℝ)
    (hc : ∀ U, k U + d = r U + r Uᶜ) :
    x^d * signedSum B (fun U => x^k U) =
      x^d * ((1 + (-1:ℝ)^B.card) * signedSum B (fun U => x^r U)) +
        signedSum B (fun U => (x^r U - x^d) * (x^r Uᶜ - x^d)) := by
  have hbase (U : Finset ι) : x^d * x^k U = x^r U * x^r Uᶜ := by
    rw [mul_comm (x^d), ← pow_add, ← pow_add, hc U]
  have hzero : signedSum B (fun _ => x^d) = 0 := by
    unfold signedSum
    rw [← sum_mul, char_sum_zero B hB, zero_mul]
  have happly (f g : Finset ι → ℝ) : signedSum B (fun U => f U + g U) =
      signedSum B f + signedSum B g := by
    simp only [signedSum, mul_add, sum_add_distrib]
  have hscale (c : ℝ) (f : Finset ι → ℝ) :
      signedSum B (fun U => c * f U) = c * signedSum B f := by
    simp only [signedSum, mul_sum]
    apply sum_congr rfl
    intro U _
    ring
  have hs : signedSum B (fun U => x^r U + x^r Uᶜ + -(x^d)) =
      (1 + (-1:ℝ)^B.card) * signedSum B (fun U => x^r U) := by
    exact (happly _ _).trans <| by
      rw [show signedSum B (fun _ => -(x^d)) = -1 * signedSum B (fun _ => x^d) by
        simpa only [neg_one_mul] using hscale (-1) (fun _ => x^d), hzero, mul_zero, add_zero,
        happly, signed_comp_compl B (fun U => x^r U), add_mul, one_mul]
  calc
    _ = signedSum B (fun U => x^d * x^k U) := (hscale _ _).symm
    _ = signedSum B (fun U => x^d * (x^r U + x^r Uᶜ + -(x^d)) +
        (x^r U - x^d) * (x^r Uᶜ - x^d)) := by
      congr 1
      funext U
      rw [hbase]
      ring
    _ = _ := by
      rw [happly, hscale, hs]


end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

open Finset
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
variable {ι : Type*} [DecidableEq ι]

/-- If an added point is parallel to an existing point, the full alternating
rank polynomial is unchanged. Compare the three nonempty selections of the
pair; their signed coefficients are -1, -1, and +1. -/
private theorem duplicate_cancels (s : Finset ι) (a b : ι) (ha : a ∉ s) (hb : b ∉ s)
    (hab : a ≠ b) (f : Finset ι → ℝ)
    (h₁ : ∀ U ⊆ s, f (insert b U) = f (insert a U))
    (h₂ : ∀ U ⊆ s, f (insert b (insert a U)) = f (insert a U)) :
    (∑ U ∈ (insert b (insert a s)).powerset, (-1:ℝ)^U.card * f U) =
    ∑ U ∈ (insert a s).powerset, (-1:ℝ)^U.card * f U := by
  let g (U : Finset ι) := (-1:ℝ)^U.card * f U
  change ∑ U ∈ (insert b (insert a s)).powerset, g U = _
  rw [Finset.sum_powerset_insert (by simp [Ne.symm hab, hb])]
  change (∑ U ∈ (insert a s).powerset, g U) + _ = (∑ U ∈ (insert a s).powerset, g U)
  nth_rw 2 [← add_zero (∑ U ∈ (insert a s).powerset, g U)]
  apply congrArg ((∑ U ∈ (insert a s).powerset, g U) + ·)
  dsimp only [g]
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro U hU
  have hsub := Finset.mem_powerset.mp hU
  have hUa : a ∉ U := fun h => ha (hsub h)
  have hUb : b ∉ U := fun h => hb (hsub h)
  have hUab : b ∉ insert a U := by simp [Ne.symm hab,hUb]
  rw [h₁ U hsub, h₂ U hsub, card_insert_of_notMem hUab,
    card_insert_of_notMem hUa, card_insert_of_notMem hUb, pow_succ, pow_succ]
  ring

/-- Two proper linear subspaces cannot cover the ambient space. This
constructively supplies a missing projective point, even over F₂. -/
private theorem spanning_side_of_union {F M : Type*} [DivisionRing F] [AddCommGroup M] [Module F M]
    (U V : Submodule F M) (h : ∀ v : M, v ∈ U ∨ v ∈ V) : U = ⊤ ∨ V = ⊤ := by
  by_contra! hh
  have hU : ∃ x : M, x ∉ U := by
    by_contra! hU
    exact hh.1 (eq_top_iff.mpr (fun x _ => hU x))
  have hV : ∃ y : M, y ∉ V := by
    by_contra! hV
    exact hh.2 (eq_top_iff.mpr (fun x _ => hV x))
  obtain ⟨x,hx⟩ := hU
  obtain ⟨y,hy⟩ := hV
  have hxV : x ∈ V := (h x).resolve_left hx
  have hyU : y ∈ U := (h y).resolve_right hy
  rcases h (x+y) with hz | hz
  · exact hx (by simpa using U.sub_mem hz hyU)
  · exact hy (by simpa [add_comm x y] using V.sub_mem hz hxV)

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
open Matrix Finset
open scoped BigOperators Classical
variable {F I J O P : Type*} [Field F] [Fintype I] [Fintype J] [Fintype O] [Fintype P]

omit [Fintype I] [Fintype O] in
private theorem diagonal_blocks_rank (A : Matrix I J F) (B : Matrix O P F) :
    (fromBlocks A (0 : Matrix I P F) (0 : Matrix O J F) B).rank = A.rank + B.rank := by
  let M := fromBlocks A (0 : Matrix I P F) (0 : Matrix O J F) B
  let ei := LinearEquiv.sumArrowLequivProdArrow J P F F
  let eo := LinearEquiv.sumArrowLequivProdArrow I O F F
  have he : A.mulVecLin.prodMap B.mulVecLin =
      (eo : _ →ₗ[F] _).comp (M.mulVecLin.comp (ei.symm : _ →ₗ[F] _)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i
      change A.mulVec x.1 i = M.mulVec (ei.symm x) (Sum.inl i)
      have h : (ei.symm x) ∘ Sum.inl = x.1 := by funext j; rfl
      simp [M, fromBlocks_mulVec, h]
    · funext i
      change B.mulVec x.2 i = M.mulVec (ei.symm x) (Sum.inr i)
      have h : (ei.symm x) ∘ Sum.inr = x.2 := by funext j; rfl
      simp [M, fromBlocks_mulVec, h]
  change M.rank = A.rank + B.rank
  have hr := congrArg LinearMap.range he
  rw [LinearMap.range_prodMap, LinearMap.range_comp, LinearEquiv.range_comp] at hr
  change Module.finrank F M.mulVecLin.range =
    Module.finrank F A.mulVecLin.range + Module.finrank F B.mulVecLin.range
  rw [← LinearEquiv.finrank_map_eq eo M.mulVecLin.range, ← hr,
    (Submodule.prodEquiv A.mulVecLin.range B.mulVecLin.range).finrank_eq, Module.finrank_prod]

omit [Fintype O] in
private theorem pivot_blocks_rank [DecidableEq I] (B : Matrix I P F) (C : Matrix O P F) :
    (fromBlocks (1 : Matrix I I F) B (0 : Matrix O I F) C).rank =
      Fintype.card I + C.rank := by
  let N := fromBlocks (1 : Matrix I I F) (0 : Matrix I P F) (0 : Matrix O I F) C
  let M := fromBlocks (1 : Matrix I I F) B (0 : Matrix O I F) C
  have h₁ : N * fromBlocks (1 : Matrix I I F) B (0 : Matrix P I F) (1 : Matrix P P F) = M := by
    simp [N,M,fromBlocks_multiply]
  have h₂ : M * fromBlocks (1 : Matrix I I F) (-B) (0 : Matrix P I F) (1 : Matrix P P F) = N := by
    simp [N,M,fromBlocks_multiply]
  have hr : M.rank = N.rank := by
    apply le_antisymm
    · rw [← h₁]; exact rank_mul_le_left _ _
    · rw [← h₂]; exact rank_mul_le_left _ _
  change M.rank = _
  rw [hr, show N.rank = _ from diagonal_blocks_rank _ _, rank_one]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
open Matrix Finset
open scoped BigOperators Classical
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
local notation "F" => ZMod 2
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

def systematic (A : Matrix I J F) : Matrix I (I ⊕ J) F :=
  fun i => Sum.elim (fun j => if i=j then 1 else 0) (A i)

def fundamental (A : Matrix I J F) : Matrix (I ⊕ J) (I ⊕ J) F :=
  fromBlocks 0 A Aᵀ 0

def selectedRank (A : Matrix I J F) (s : Finset (I ⊕ J)) : ℕ :=
  ((systematic A).submatrix id (Subtype.val : s → I ⊕ J)).rank

abbrev L (s : Finset (I ⊕ J)) := {i : I // Sum.inl i ∈ s}
abbrev R (s : Finset (I ⊕ J)) := {j : J // Sum.inr j ∈ s}

def split (s : Finset (I ⊕ J)) : L s ⊕ R s ≃ s where
  toFun := Sum.elim (fun i => ⟨Sum.inl i.val,i.property⟩) (fun j => ⟨Sum.inr j.val,j.property⟩)
  invFun x := match x with
    | ⟨Sum.inl i,h⟩ => Sum.inl ⟨i,h⟩
    | ⟨Sum.inr j,h⟩ => Sum.inr ⟨j,h⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by obtain ⟨i,h⟩ := x; cases i <;> rfl

def leftRows (s : Finset (I ⊕ J)) : L s ⊕ L sᶜ ≃ I where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun i := if h : Sum.inl i ∈ s then Sum.inl ⟨i,h⟩ else Sum.inr ⟨i,mem_compl.mpr h⟩
  left_inv x := by cases x with | inl i => simp [i.property] | inr i =>
    simp [mem_compl.mp i.property]
  right_inv i := by by_cases hi : Sum.inl i ∈ s <;> simp [hi]

def crossed (A : Matrix I J F) (s t : Finset (I ⊕ J)) : Matrix (L s) (R t) F :=
  A.submatrix Subtype.val Subtype.val

private theorem selectedRank_eq (A : Matrix I J F) (s : Finset (I ⊕ J)) :
    selectedRank A s = Fintype.card (L s) + (crossed A sᶜ s).rank := by
  let M := (systematic A).submatrix id (Subtype.val : s → I ⊕ J)
  have h : M.submatrix (leftRows s) (split s) =
      fromBlocks (1 : Matrix (L s) (L s) F) (crossed A s s)
        (0 : Matrix (L sᶜ) (L s) F) (crossed A sᶜ s) := by
    funext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change (if i.val=j.val then (1:F) else 0) = _
        rw [fromBlocks_apply₁₁,one_apply]
        exact if_congr Subtype.ext_iff.symm rfl rfl
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        have hne : i.val ≠ j.val := by
          intro e
          exact (mem_compl.mp i.property) (e ▸ j.property)
        change (if i.val=j.val then (1:F) else 0) = _
        rw [ite_eq_right hne,fromBlocks_apply₂₁,Matrix.zero_apply]
      | inr j => rfl
  change M.rank = _
  rw [← M.rank_submatrix (leftRows s) (split s), h]
  exact pivot_blocks_rank (crossed A s s) (crossed A sᶜ s)

private theorem cut_submatrix_eq (A : Matrix I J F) (s : Finset (I ⊕ J)) :
    let M := cutMatrix (fundamental A) s sᶜ
    M.submatrix (split sᶜ) ((Equiv.sumComm (R s) (L s)).trans (split s)) =
      fromBlocks (crossed A sᶜ s) (0 : Matrix (L sᶜ) (L s) F)
        (0 : Matrix (R sᶜ) (R s) F) (crossed A s sᶜ)ᵀ := by
  dsimp only
  funext i j
  cases i <;> cases j <;> rfl

private theorem fundamental_cutRank_eq (A : Matrix I J F) (s : Finset (I ⊕ J)) :
    cutRank (fundamental A) s = (crossed A sᶜ s).rank + (crossed A s sᶜ).rank := by
  have hc : complement s = sᶜ := by ext j; simp [complement]
  unfold cutRank
  rw [hc]
  change (cutMatrix (fundamental A) s sᶜ).rank = _
  rw [← (cutMatrix (fundamental A) s sᶜ).rank_submatrix
    (split sᶜ) ((Equiv.sumComm (R s) (L s)).trans (split s)),
    cut_submatrix_eq, diagonal_blocks_rank, rank_transpose]

private theorem basis_card_partition (s : Finset (I ⊕ J)) :
    Fintype.card (L s) + Fintype.card (L sᶜ) = Fintype.card I := by
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (leftRows s)

private theorem rank_connectivity (A : Matrix I J F) (s : Finset (I ⊕ J)) :
    cutRank (fundamental A) s + Fintype.card I = selectedRank A s + selectedRank A sᶜ := by
  rw [fundamental_cutRank_eq, selectedRank_eq, selectedRank_eq, compl_compl]
  have h := basis_card_partition s
  omega

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
open Matrix Finset
open scoped BigOperators Classical
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
local notation "F" => ZMod 2
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

private theorem transport {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (A : Matrix X X F) (U : Finset X) :
    cutRank (reindex e e A) (U.map e.toEmbedding) = cutRank A U := by
  let V := (Finset.univ \ U : Finset X)
  let eU := e.subtypeEquiv (p := fun i => i ∈ U) (q := fun j => j ∈ U.map e.toEmbedding)
    (by intro i; simp)
  let eV := e.subtypeEquiv (p := fun i => i ∈ V)
    (q := fun j => j ∈ (Finset.univ \ U.map e.toEmbedding : Finset Y))
    (by intro i; simp [V])
  have he : cutMatrix (reindex e e A) (U.map e.toEmbedding)
      (Finset.univ \ U.map e.toEmbedding) =
      reindex eV eU (cutMatrix A U V) := by
    ext i j
    rfl
  unfold cutRank complement
  rw [he, rank_reindex]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private theorem fundamental_symm (A : Matrix I J F) (i j : I ⊕ J) :
    fundamental A i j = fundamental A j i := by
  cases i <;> cases j <;> rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private theorem fundamental_diag (A : Matrix I J F) (i : I ⊕ J) :
    fundamental A i i = 0 := by cases i <;> rfl

/-- Whenever each bipartition has a spanning side, the actual physical moment's
nonempty Walsh bins equal the signed restriction-rank sum times the parity
factor. The constant contribution is cancelled before evaluating any ranks. -/
private theorem physical_characteristic_walsh (A : Matrix I J F) {n : ℕ}
    (e : I ⊕ J ≃ Fin n) (K : ℝ) (hK : 1 < K) (B : Finset (I ⊕ J)) (hB : B.Nonempty)
    (hspan : ∀ U, selectedRank A U = Fintype.card I ∨ selectedRank A Uᶜ = Fintype.card I) :
    signedSum B (fun U => graphTraceMoment (reindex e e (fundamental A)) K (U.map e.toEmbedding)) =
    (1 + (-1:ℝ)^B.card) * signedSum B (fun U => ((2:ℝ)^(1-K))^(selectedRank A U)) := by
  let M := reindex e e (fundamental A)
  have hs (i j : Fin n) : M i j = M j i := fundamental_symm A _ _
  have hd (i : Fin n) : M i i = 0 := fundamental_diag A _
  have hU (U : Finset (I ⊕ J)) :
      graphTraceMoment M K (U.map e.toEmbedding) = ((2:ℝ)^(1-K))^(cutRank (fundamental A) U) := by
    rw [(physical_graph_gce_monotone n K M hs hd hK).1, transport]
    exact (Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)) _ _).trans
      (Real.rpow_natCast ((2:ℝ)^(1-K)) _)
  change signedSum B (fun U => graphTraceMoment M K (U.map e.toEmbedding)) = _
  simp_rw [hU]
  let x : ℝ := (2:ℝ)^(1-K)
  let d := Fintype.card I
  have hzero : signedSum B (fun U =>
      (x^selectedRank A U - x^d) * (x^selectedRank A Uᶜ - x^d)) = 0 := by
    unfold signedSum
    apply Finset.sum_eq_zero
    intro U _
    rcases hspan U with h | h <;> simp [d,h]
  have hh := two_deficient_correction B hB (selectedRank A)
    (cutRank (fundamental A)) d x (rank_connectivity A)
  rw [hzero, add_zero] at hh
  have hx : x^d ≠ 0 := ne_of_gt (by dsimp [x]; positivity)
  exact (mul_right_inj' hx).mp hh

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
open Matrix Finset
open scoped BigOperators Classical
local notation "F" => ZMod 2
local notation "Vec" d => (Fin d → F)
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

variable {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
abbrev colVec (A : Matrix (Fin d) J F) := (systematic A).col

omit [Fintype J] [DecidableEq J] in
private theorem selectedRank_span (A : Matrix (Fin d) J F) (U : Finset (Fin d ⊕ J)) :
    selectedRank A U = Module.finrank F (Submodule.span F ((U.image (colVec A) : Finset (Vec d)) : Set (Vec d))) := by
  unfold selectedRank
  rw [rank_eq_finrank_span_cols]
  have h : Set.range ((systematic A).submatrix id (Subtype.val : U → Fin d ⊕ J)).col =
      ((U.image (colVec A) : Finset (Vec d)) : Set (Vec d)) := by
    ext v
    constructor
    · rintro ⟨j,rfl⟩
      exact mem_image.mpr ⟨j.val,j.property,rfl⟩
    · intro hv
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
      exact ⟨⟨j,hj⟩,rfl⟩
  rw [h]

private theorem spanning_partition (A : Matrix (Fin d) J F)
    (hcover : ∀ v : Vec d, v ≠ 0 → ∃ j, colVec A j = v)
    (U : Finset (Fin d ⊕ J)) :
    selectedRank A U = Fintype.card (Fin d) ∨ selectedRank A Uᶜ = Fintype.card (Fin d) := by
  rw [selectedRank_span, selectedRank_span]
  let H (V : Finset (Fin d ⊕ J)) := Submodule.span F (↑(V.image (colVec A)) : Set (Vec d))
  change Module.finrank F (H U) = _ ∨ Module.finrank F (H Uᶜ) = _
  have hc : ∀ v : Vec d, v ∈ H U ∨ v ∈ H Uᶜ := by
    intro v
    by_cases hv : v = 0
    · exact Or.inl (hv ▸ (H U).zero_mem)
    · obtain ⟨j,rfl⟩ := hcover v hv
      by_cases hj : j ∈ U
      · exact Or.inl (Submodule.subset_span (mem_image_of_mem _ hj))
      · exact Or.inr (Submodule.subset_span (mem_image_of_mem _ (mem_compl.mpr hj)))
  have hfin : Module.finrank F (⊤ : Submodule F (Vec d)) = Fintype.card (Fin d) := by
    rw [finrank_top, Module.finrank_pi]
  rcases spanning_side_of_union (H U) (H Uᶜ) hc with h | h
  · exact Or.inl (h ▸ hfin)
  · exact Or.inr (h ▸ hfin)

omit [Fintype J] [DecidableEq J] in
private theorem base_projective_sum (A : Matrix (Fin d) J F) (s : Finset (Fin d ⊕ J))
    (himg : s.image (colVec A) = (univ : Finset (Vec d)).erase 0)
    (hinj : Set.InjOn (colVec A) (s : Set (Fin d ⊕ J))) (q : ℝ) :
    ∑ U ∈ s.powerset, (-1:ℝ)^U.card * (q⁻¹)^(selectedRank A U) =
      BinaryProjectiveRankPolynomial.normalizedRankSum d q := by
  unfold BinaryProjectiveRankPolynomial.normalizedRankSum
  classical
  rw [← himg]
  apply sum_bij (fun U _ => U.image (colVec A))
  · intro U hU
    exact mem_powerset.mpr (image_subset_image (mem_powerset.mp hU))
  · intro U hU V hV he
    apply le_antisymm
    · intro j hj
      have hc : colVec A j ∈ V.image (colVec A) := he ▸ mem_image_of_mem _ hj
      obtain ⟨k,hk,heq⟩ := mem_image.mp hc
      have e := hinj (mem_powerset.mp hV hk) (mem_powerset.mp hU hj) heq
      simpa [e] using hk
    · intro j hj
      have hc : colVec A j ∈ U.image (colVec A) := he.symm ▸ mem_image_of_mem _ hj
      obtain ⟨k,hk,heq⟩ := mem_image.mp hc
      have e := hinj (mem_powerset.mp hU hk) (mem_powerset.mp hV hj) heq
      simpa [e] using hk
  · intro V hV
    refine ⟨s.filter (fun j => colVec A j ∈ V),mem_powerset.mpr (filter_subset _ _),?_⟩
    ext v
    constructor
    · intro hv
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hj).2
    · intro hv
      obtain ⟨j,hj,rfl⟩ := mem_image.mp (mem_powerset.mp hV hv)
      exact mem_image.mpr ⟨j,mem_filter.mpr ⟨hj,hv⟩,rfl⟩
  · intro U hU
    rw [selectedRank_span, card_image_of_injOn (hinj.mono (mem_powerset.mp hU))]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
open Matrix Finset
open scoped BigOperators Classical
local notation "F" => ZMod 2
local notation "Vec" d => (Fin d → F)
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
variable {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] in
private theorem duplicate_rank_sum (A : Matrix (Fin d) J F) (a b : Fin d ⊕ J) (s : Finset (Fin d ⊕ J))
    (ha : a ∈ s) (hb : b ∉ s) (hab : colVec A a = colVec A b) (q : ℝ) :
    (∑ U ∈ (insert b s).powerset, (-1:ℝ)^U.card * (q⁻¹)^(selectedRank A U)) =
    ∑ U ∈ s.powerset, (-1:ℝ)^U.card * (q⁻¹)^(selectedRank A U) := by
  have hne : a ≠ b := fun e => hb (e ▸ ha)
  nth_rw 1 2 [← insert_erase ha]
  refine duplicate_cancels _ a b (notMem_erase _ _) (fun h => hb (mem_of_mem_erase h)) hne _ ?_ ?_
  · intro U _
    rw [selectedRank_span, selectedRank_span, image_insert, image_insert, hab]
  · intro U _
    rw [selectedRank_span, selectedRank_span, image_insert, image_insert, ← hab, insert_idem]

set_option maxHeartbeats 1500000 in
private theorem whole_projective_graph_factor (A : Matrix (Fin d) J F) {n : ℕ}
    (e : (Fin d ⊕ J) ≃ Fin n) (K : ℝ) (hK : 1 < K) (hn : Even n)
    (a b : Fin d ⊕ J) (s : Finset (Fin d ⊕ J))
    (ha : a ∈ s) (hb : b ∉ s) (hab : colVec A a = colVec A b)
    (hu : insert b s = univ)
    (himg : s.image (colVec A) = (univ : Finset (Vec d)).erase 0)
    (hinj : Set.InjOn (colVec A) (s : Set (Fin d ⊕ J))) :
    signedSum (univ : Finset (Fin d ⊕ J))
      (fun U => graphTraceMoment (reindex e e (fundamental A)) K (U.map e.toEmbedding)) =
    2 * ∏ j : Fin d, (1 - (2:ℝ)^j.val / (((2:ℝ)^(1-K))⁻¹)) := by
  have hcover (v : Vec d) (hv : v ≠ 0) : ∃ j, colVec A j = v := by
    have hmem : v ∈ s.image (colVec A) := by simp [himg,hv]
    obtain ⟨j,_,hj⟩ := mem_image.mp hmem
    exact ⟨j,hj⟩
  let x : ℝ := (2:ℝ)^(1-K)
  let q : ℝ := x⁻¹
  have hq : q ≠ 0 := by dsimp [q,x]; positivity
  have hx : q⁻¹ = x := inv_inv x
  have hne : (univ : Finset (Fin d ⊕ J)).Nonempty := ⟨a,mem_univ a⟩
  have hcard : (univ : Finset (Fin d ⊕ J)).card = n := by
    rw [card_univ, Fintype.card_congr e, Fintype.card_fin]
  have hparity : (1 + (-1:ℝ)^(univ : Finset (Fin d ⊕ J)).card) = 2 := by
    rw [hcard, hn.neg_one_pow]; norm_num
  have hr := physical_characteristic_walsh A e K hK _ hne (spanning_partition A hcover)
  rw [hparity] at hr
  refine hr.trans (congrArg ((2:ℝ) * ·) ?_)
  have hval := BinaryProjectiveRankPolynomial.normalized_factor d (R := ℝ) q hq
  change BinaryProjectiveRankPolynomial.normalizedRankSum d q = _ at hval
  refine Eq.trans ?_ hval
  refine Eq.trans ?_ ((duplicate_rank_sum A a b s ha hb hab q).trans
    (base_projective_sum A s himg hinj q))
  unfold signedSum
  rw [show (insert b s).powerset = (univ : Finset (Fin d ⊕ J)).powerset from congrArg Finset.powerset hu,
    Finset.powerset_univ]
  apply sum_congr rfl
  intro U _
  rw [char_eq, inter_univ, hx]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
open Matrix Finset
open scoped BigOperators Classical
local notation "F" => ZMod 2
local notation "Vec" d => (Fin d → F)
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

def basisPoint {d : ℕ} (i : Fin d) : Vec d := fun j => if j = i then 1 else 0

private theorem basisPoint_nz {d : ℕ} (i : Fin d) : basisPoint i ≠ 0 := by
  intro h
  have hh := congrFun h i
  simp [basisPoint] at hh

private theorem basisPoint_inj {d : ℕ} : Function.Injective (@basisPoint d) := by
  intro i j h
  by_contra! he
  have hh := congrFun h i
  simp [basisPoint,he] at hh

def NonBasis (d : ℕ) := {v : Vec d // v ≠ 0 ∧ ∀ i, v ≠ basisPoint i}
instance (d : ℕ) : Fintype (NonBasis d) := inferInstanceAs (Fintype {_v : Vec d // _})

abbrev ProjRight (d : ℕ) := NonBasis d ⊕ Unit
abbrev ProjSites (d : ℕ) := Fin d ⊕ ProjRight d

def duplication (d : ℕ) : ProjSites d := .inr (.inr ())

def projectiveA (n : ℕ) : Matrix (Fin (n+1)) (ProjRight (n+1)) F :=
  fun i => Sum.elim (fun v => v.val i) (fun _ => basisPoint (0 : Fin (n+1)) i)

def projectiveBase (d : ℕ) : Finset (ProjSites d) := univ.erase (duplication d)

private theorem projectiveBase_image (n : ℕ) :
    (projectiveBase (n+1)).image (colVec (projectiveA n)) =
    (univ : Finset (Vec (n+1))).erase 0 := by
  ext v
  simp only [mem_image, mem_erase, mem_univ, and_true]
  constructor
  · rintro ⟨i,hi,rfl⟩
    rcases i with i | (w | u)
    · exact basisPoint_nz i
    · exact w.property.1
    · cases u
      exact False.elim ((mem_erase.mp hi).1 rfl)
  · intro hv
    by_cases h : ∃ i, v = basisPoint i
    · obtain ⟨i,rfl⟩ := h
      exact ⟨.inl i,by simp [projectiveBase,duplication],rfl⟩
    · push Not at h
      exact ⟨.inr (.inl ⟨v,hv,h⟩),by simp [projectiveBase,duplication],rfl⟩

private theorem projectiveBase_inj (n : ℕ) :
    Set.InjOn (colVec (projectiveA n)) (projectiveBase (n+1) : Set (ProjSites (n+1))) := by
  intro a ha b hb h
  have ha' : a ≠ duplication (n+1) := (mem_erase.mp (mem_coe.mp ha)).1
  have hb' : b ≠ duplication (n+1) := (mem_erase.mp (mem_coe.mp hb)).1
  rcases a with i | (v | u) <;> rcases b with j | (w | t)
  all_goals try solve | cases u; exact False.elim (ha' rfl) | cases t; exact False.elim (hb' rfl)
  · exact congrArg Sum.inl (basisPoint_inj h)
  · exact False.elim (w.property.2 i h.symm)
  · exact False.elim (v.property.2 j h)
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (Subtype.ext h)

private theorem projectiveSites_card (n : ℕ) : Fintype.card (ProjSites (n+1)) = 2^(n+1) := by
  have h := card_image_of_injOn (projectiveBase_inj n)
  rw [projectiveBase_image,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fun,
    Fintype.card_fin,ZMod.card] at h
  unfold projectiveBase at h
  rw [card_erase_of_mem (mem_univ _),card_univ] at h
  have hpos : 0 < 2^(n+1) := by positivity
  have hsite : 0 < Fintype.card (ProjSites (n+1)) :=
    Fintype.card_pos_iff.mpr ⟨duplication _⟩
  change 2^(n+1) - 1 = Fintype.card (ProjSites (n+1)) - 1 at h
  rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hsite),
    ← Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), ← h]

def siteEquiv (n : ℕ) : ProjSites (n+1) ≃ Fin (2^(n+1)) :=
  Fintype.equivFinOfCardEq (projectiveSites_card n)

def projectiveGraph (n : ℕ) : Matrix (Fin (2^(n+1))) (Fin (2^(n+1))) F :=
  reindex (siteEquiv n) (siteEquiv n) (fundamental (projectiveA n))

set_option maxHeartbeats 900000 in
private theorem projectiveWalsh (n : ℕ) (K : ℝ) (hK : 1 < K) :
    signedSum (univ : Finset (ProjSites (n+1)))
      (fun U => graphTraceMoment (projectiveGraph n) K (U.map (siteEquiv n).toEmbedding)) =
    2 * ∏ j : Fin (n+1), (1 - (2:ℝ)^j.val / (((2:ℝ)^(1-K))⁻¹)) := by
  have hev : Even (2^(n+1)) := Nat.even_pow.mpr ⟨by decide, Nat.succ_ne_zero n⟩
  let a : ProjSites (n+1) := .inl 0
  let b : ProjSites (n+1) := duplication _
  let s := projectiveBase (n+1)
  have ha : a ∈ s := by simp [a,s,projectiveBase,duplication]
  have hb : b ∉ s := notMem_erase _ _
  have hab : colVec (projectiveA n) a = colVec (projectiveA n) b := rfl
  have hu : insert b s = univ := insert_erase (mem_univ _)
  have h := whole_projective_graph_factor (projectiveA n) (siteEquiv n) K hK hev
    a b s ha hb hab hu (projectiveBase_image n) (projectiveBase_inj n)
  exact h


/-- Full-set Walsh numerator for the actual reduced trace. -/
def actualFullBin {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (K : ℝ) : ℝ :=
  ∑ U : Finset (Fin n), (-1:ℝ)^U.card * graphTraceMoment A K U

/-- Exact coefficient on the actual, finitely indexed physical graph, without
any auxiliary coordinate or zero-vector vertex. -/
private theorem projectiveActualWalsh (n : ℕ) (K : ℝ) (hK : 1 < K) :
    actualFullBin (projectiveGraph n) K =
    2 * ∏ j : Fin (n+1), (1 - (2:ℝ)^j.val / (((2:ℝ)^(1-K))⁻¹)) := by
  rw [← projectiveWalsh n K hK]
  unfold actualFullBin signedSum
  simp_rw [char_eq, inter_univ]
  let E := (siteEquiv n).finsetCongr
  rw [← E.sum_comp (fun U => (-1:ℝ)^U.card * graphTraceMoment (projectiveGraph n) K U)]
  apply sum_congr rfl
  intro U _
  change (-1:ℝ)^(U.map (siteEquiv n).toEmbedding).card * _ = _
  rw [card_map]
  rfl

private theorem projective_actual_negative (m : ℕ) (K : ℝ) (hK : 1 < K)
    (hlo : (2:ℝ)^m < (((2:ℝ)^(1-K))⁻¹))
    (hhi : (((2:ℝ)^(1-K))⁻¹) < (2:ℝ)^(m+1)) :
    actualFullBin (projectiveGraph (m+1)) K < 0 := by
  let q := (((2:ℝ)^(1-K))⁻¹)
  have hq : 0 < q := lt_trans (by positivity) hlo
  rw [projectiveActualWalsh _ _ hK]
  apply mul_neg_of_pos_of_neg (by norm_num)
  rw [Fin.prod_univ_castSucc]
  apply mul_neg_of_pos_of_neg
  · apply Finset.prod_pos
    intro j _
    apply sub_pos.mpr
    change (2:ℝ)^j.val / q < 1
    rw [div_lt_one hq]
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_lt_succ j.isLt)).trans_lt hlo
  · apply sub_neg.mpr
    exact (one_lt_div hq).mpr hhi


end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic
open Matrix Finset
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh.Characteristic

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
open scoped BigOperators Classical

/-- Actual finite reduced-matrix traces, not a symbolic rank oracle. -/
def compactMomentFamily (K : ℝ) (n : ℕ) : Finset (Fin (2^(n+1))) → ℝ :=
  graphTraceMoment (Characteristic.projectiveGraph n) K

/-- Exact full-system characteristic product and negative intervals for the
same fixed graph within each open dyadic band. -/
theorem compact_projective_walsh (K : ℝ) (hK : 1 < K) :
    let observed := compactMomentFamily K
    (∀ n : ℕ, (∑ U : Finset (Fin (2^(n+1))), (-1:ℝ)^U.card * observed n U) =
      2 * ∏ j : Fin (n+1), (1 - (2:ℝ)^j.val / (2:ℝ)^(K-1))) ∧
    (∀ m : ℕ, (2:ℝ)^m < (2:ℝ)^(K-1) → (2:ℝ)^(K-1) < (2:ℝ)^(m+1) →
      (∑ U : Finset (Fin (2^(m+2))), (-1:ℝ)^U.card * observed (m+1) U) < 0) := by
  dsimp only
  constructor
  · intro n
    change Characteristic.actualFullBin (Characteristic.projectiveGraph n) K = _
    rw [Characteristic.projectiveActualWalsh _ _ hK,
      ← Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ)), neg_sub]
  · intro m hlo hhi
    change Characteristic.actualFullBin (Characteristic.projectiveGraph (m+1)) K < 0
    apply Characteristic.projective_actual_negative m K hK
    all_goals rwa [← Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ)), neg_sub]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
