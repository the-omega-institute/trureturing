/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateArticulation
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateArticulation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factor physical graph-state cut moments at a shared vertex by an exact rank increment. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Articulation gluing of physical graph-state coverage moments

At a cut's common vertex, the rank increment is the OR of the separate
increments. The resulting positive product factors give an explicit shared-bit
XOR law for the normalized root-deletion and surplus channels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped Classical BigOperators
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation
open Matrix Finset
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

section
variable {F I J O P : Type*} [Field F] [Fintype I] [Fintype J] [Fintype O] [Fintype P]
omit [Fintype I] [Fintype O] in
theorem diagonal_blocks_rank (A : Matrix I J F) (B : Matrix O P F) :
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
end

section
open Submodule
variable {F C D : Type*} [Field F]
variable [AddCommGroup C] [Module F C] [Module.Finite F C]
variable [AddCommGroup D] [Module F D] [Module.Finite F D]

/-- A common boundary row adds either zero or one, determined by membership
on each side of the disjoint blocks, independently. -/
theorem joint_row_rank (U : Submodule F C) (W : Submodule F D) (a : C) (b : D) :
    Module.finrank F (↥(U.prod W ⊔ span F {(a,b)})) =
      Module.finrank F U + Module.finrank F W +
        (if a ∈ U ∧ b ∈ W then 0 else 1) := by
  classical
  have hprod : Module.finrank F (U.prod W) = Module.finrank F U + Module.finrank F W := by
    rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
  by_cases h : a ∈ U ∧ b ∈ W
  · rw [sup_eq_left.mpr ((span_singleton_le_iff_mem _ _).mpr h), hprod]
    simp [h]
  · rw [finrank_sup_span_singleton (show (a,b) ∉ U.prod W from h), hprod]
    simp [h]

/-- The product cut moment is an exact algebraic split into a deletion
channel and a one-row remainder. No positivity assumptions are needed. -/
theorem row_gluing_moment (x : ℝ) (c d : ℕ) (coreFree branchesFree : Bool) :
    x^(c+d+(if coreFree && branchesFree then 0 else 1 : ℕ)) =
      (x^(c+(if coreFree then 0 else 1 : ℕ))-x*x^c)
        * (if branchesFree then x^d else 0) + x*x^c*x^d := by
  cases coreFree <;> cases branchesFree <;>
    simp [pow_succ, pow_add] <;> ring

theorem subspace_gluing_moment (x : ℝ) (U : Submodule F C) (W : Submodule F D)
    (a : C) (b : D) :
    x^(Module.finrank F (↥(U.prod W ⊔ span F {(a,b)}))) =
      (x^(Module.finrank F (↥(U ⊔ span F {a})))-x*x^(Module.finrank F U))
        * (if b ∈ W then x^(Module.finrank F W) else 0) +
      x*x^(Module.finrank F U)*x^(Module.finrank F W) := by
  classical
  have hcore : Module.finrank F (↥(U ⊔ span F {a})) =
      Module.finrank F U + (if a ∈ U then 0 else 1) := by
    by_cases h : a ∈ U
    · rw [sup_eq_left.mpr ((span_singleton_le_iff_mem _ _).mpr h)]; simp [h]
    · rw [finrank_sup_span_singleton h]; simp [h]
  rw [joint_row_rank, hcore]
  simpa using row_gluing_moment x (Module.finrank F U) (Module.finrank F W)
    (decide (a ∈ U)) (decide (b ∈ W))
end

section
open Matrix Submodule
variable {F I J C D : Type*} [Field F] [Fintype C] [Fintype D]

def glueRows (A : Matrix I C F) (B : Matrix J D F) (a : C → F) (b : D → F) :
    Matrix (Unit ⊕ (I ⊕ J)) (C ⊕ D) F :=
  fun i => Sum.elim (fun _ => Sum.elim a b)
    (Sum.elim (fun j => Sum.elim (A j) 0) (fun j => Sum.elim 0 (B j))) i

def singleRow (A : Matrix I C F) (a : C → F) : Matrix (Unit ⊕ I) C F :=
  fun i => Sum.elim (fun _ => a) A i

omit [Fintype C] in
private theorem addrow_span (A : Matrix I C F) (a : C → F) :
    span F (Set.range (singleRow A a).row) = span F (Set.range A.row) ⊔ span F {a} := by
  rw [← span_union]
  congr 1
  ext w
  constructor
  · rintro ⟨(_ | i), rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨i,rfl⟩
  · rintro (⟨i,rfl⟩ | h)
    · exact ⟨.inr i,rfl⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨.inl (),h.symm⟩

omit [Fintype C] [Fintype D] in
private theorem glueRow_span (A : Matrix I C F) (B : Matrix J D F) (a : C → F) (b : D → F) :
    (span F (Set.range (glueRows A B a b).row)).map
      (LinearEquiv.sumArrowLequivProdArrow C D F F).toLinearMap =
    (span F (Set.range A.row)).prod (span F (Set.range B.row)) ⊔ span F {(a,b)} := by
  rw [Submodule.map_span, ← LinearMap.span_inl_union_inr, ← Submodule.span_union]
  congr 1
  ext w
  constructor
  · rintro ⟨v,⟨(_ | (i | j)),rfl⟩,rfl⟩
    · exact Or.inr rfl
    · exact Or.inl (Or.inl ⟨A.row i,⟨i,rfl⟩,rfl⟩)
    · exact Or.inl (Or.inr ⟨B.row j,⟨j,rfl⟩,rfl⟩)
  · rintro ((⟨v,⟨i,rfl⟩,rfl⟩ | ⟨v,⟨j,rfl⟩,rfl⟩) | h)
    · exact ⟨_,⟨.inr (.inl i),rfl⟩,rfl⟩
    · exact ⟨_,⟨.inr (.inr j),rfl⟩,rfl⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨_,⟨.inl (),rfl⟩,h.symm⟩

/-- Actual cross-matrix rank moment after joining two disjoint blocks by
a single shared row; a column version follows by transposing the cut. -/
theorem glue_matrix_moment [Finite I] [Finite J] (A : Matrix I C F) (B : Matrix J D F)
    (a : C → F) (b : D → F) (x : ℝ) :
    x^((glueRows A B a b).rank) =
      (x^((singleRow A a).rank)-x*x^A.rank)
        * (if b ∈ span F (Set.range B.row) then x^B.rank else 0) +
      x*x^A.rank*x^B.rank := by
  simp only [Matrix.rank_eq_finrank_span_row]
  rw [addrow_span A a]
  rw [← (LinearEquiv.sumArrowLequivProdArrow C D F F).finrank_map_eq
      (span F (Set.range (glueRows A B a b).row)), glueRow_span]
  exact subspace_gluing_moment (F := F) x (span F (Set.range A.row)) (span F (Set.range B.row)) a b
end

section
open Matrix Finset
open scoped Classical
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

variable {F I J : Type*} [Field F] [Fintype I] [Fintype J]

def mask (A : Matrix I J F) (p : I → Prop) (q : J → Prop) : Matrix I J F :=
  fun i j => if p i ∧ q j then A i j else 0

omit [Fintype I] in
/-- Any retained submatrix has exactly the rank of its ambient padded
coordinate form, even if the underlying cut has an empty side. -/
theorem masked_rank (A : Matrix I J F) (p : I → Prop) (q : J → Prop) :
    (mask A p q).rank = (A.submatrix (Subtype.val : Subtype p → I)
      (Subtype.val : Subtype q → J)).rank := by
  let e := Equiv.sumCompl p
  let f := Equiv.sumCompl q
  rw [← Matrix.rank_submatrix _ e f]
  have h : (mask A p q).submatrix e f = fromBlocks
      (A.submatrix (Subtype.val : Subtype p → I) (Subtype.val : Subtype q → J))
      (0 : Matrix (Subtype p) {j // ¬q j} F) (0 : Matrix {i // ¬p i} (Subtype q) F)
      (0 : Matrix {i // ¬p i} {j // ¬q j} F) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [e,f,Matrix.submatrix,mask,i.property,j.property]
  rw [h, diagonal_blocks_rank, Matrix.rank_zero, add_zero]

variable {V : Type*} [Fintype V]

theorem actual_masked_cut (A : Matrix V V (ZMod 2)) (U : Finset V) :
    (mask A (fun i => i ∈ complement U) (fun j => j ∈ U)).rank = cutRank A U := by
  rw [masked_rank]
  unfold cutRank cutMatrix
  let cp := complement U
  let M : Matrix cp U (ZMod 2) := cutMatrix A U cp
  let f₁ : Fintype {j : V // j ∈ U} := @Subtype.fintype V (fun j => j ∈ U) (fun _ => Classical.propDecidable _) inferInstance
  let f₂ : Fintype (↥U) := Finset.Subtype.fintype U
  change @Matrix.rank cp U (ZMod 2) f₁ _ M = @Matrix.rank cp U (ZMod 2) f₂ _ M
  exact congrArg (fun f : Fintype (↥U) => @Matrix.rank cp U (ZMod 2) f _ M)
    (Subsingleton.elim f₁ f₂)


end

section
open Matrix Submodule
variable {F I J C D : Type*} [Field F] [Fintype C] [Fintype D]

theorem one_row_increment [Finite I] (A : Matrix I C F) (a : C → F) :
    (singleRow A a).rank = A.rank + (if a ∈ span F (Set.range A.row) then 0 else 1) := by
  simp only [Matrix.rank_eq_finrank_span_row]
  have h : span F (Set.range (singleRow A a).row) =
      span F (Set.range A.row) ⊔ span F {a} := by
    rw [← span_union]
    congr 1
    ext w
    constructor
    · rintro ⟨(_ | i), rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨i,rfl⟩
    · rintro (⟨i,rfl⟩ | h)
      · exact ⟨.inr i,rfl⟩
      · rw [Set.mem_singleton_iff] at h
        exact ⟨.inl (),h.symm⟩
  rw [h]
  by_cases hm : a ∈ span F (Set.range A.row)
  · rw [sup_eq_left.mpr ((span_singleton_le_iff_mem _ _).mpr hm)]
    simp [hm]
  · rw [finrank_sup_span_singleton hm]
    simp [hm]

/-- Two arbitrary cut charts glued at the same row. Since each independent
increment is either zero or one, the full increment is their logical OR. -/
theorem articulation_matrix [Finite I] [Finite J]
    (x : ℝ) (hx : x ≠ 1) (A : Matrix I C F) (B : Matrix J D F) (a : C → F) (b : D → F) :
    x^((glueRows A B a b).rank) =
      x*x^A.rank*x^B.rank +
      ((x^((singleRow A a).rank)-x*x^A.rank)*
        (x^((singleRow B b).rank)-x*x^B.rank))/(1-x) := by
  rw [glue_matrix_moment, one_row_increment A a, one_row_increment B b]
  by_cases hb : b ∈ span F (Set.range B.row)
  · simp only [hb, ite_true, add_zero]
    have hx0 : 1-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    field_simp
    ring
  · simp only [hb, ite_false, pow_succ, mul_zero, zero_add]
    ring
end

section
open Matrix Submodule Finset
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement

local notation "F" => ZMod 2
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Identify the two distinguished vertices and leave both nonroot parts
disjoint. No inter-piece edges are inserted. -/
def wedge (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F) : Matrix (Unit ⊕ (I ⊕ J)) (Unit ⊕ (I ⊕ J)) F
  | .inl _, .inl _ => 0
  | .inl _, .inr (.inl j) => A (.inl ()) (.inr j)
  | .inl _, .inr (.inr j) => B (.inl ()) (.inr j)
  | .inr (.inl i), .inl _ => A (.inr i) (.inl ())
  | .inr (.inr i), .inl _ => B (.inr i) (.inl ())
  | .inr (.inl i), .inr (.inl j) => A (.inr i) (.inr j)
  | .inr (.inr i), .inr (.inr j) => B (.inr i) (.inr j)
  | _, _ => 0

omit [Fintype I] [Fintype J] in
def cutSites {V : Type*} [Fintype V] (s : V → Prop) : Finset (Unit ⊕ V) :=
  (univ.filter s).map Function.Embedding.inr

theorem mem_cutSites {V : Type*} [Fintype V] (s : V → Prop) (i : V) :
    Sum.inr i ∈ cutSites s ↔ s i := by
  simp [cutSites]

theorem not_root_cutSites {V : Type*} [Fintype V] (s : V → Prop) (u : Unit) :
    Sum.inl u ∉ cutSites s := by
  simp [cutSites]

private theorem mem_complement {V : Type*} [Fintype V] (U : Finset V) (i : V) :
    i ∈ complement U ↔ i ∉ U := by simp [complement]

private def padColumn {R C : Type*} (A : Matrix R C F) : Matrix R (Unit ⊕ C) F :=
  fun i j => Sum.elim (fun _ => 0) (A i) j

private theorem padColumn_rank {R C : Type*} [Fintype C] (A : Matrix R C F) :
    (padColumn A).rank = A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have h : Set.range (padColumn A).col = insert 0 (Set.range A.col) := by
    ext v
    constructor
    · rintro ⟨(_ | j),rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j,rfl⟩
    · rintro (rfl | ⟨j,rfl⟩)
      · exact ⟨.inl (),rfl⟩
      · exact ⟨.inr j,rfl⟩
  rw [h, Submodule.span_insert_zero]

omit [Fintype I] in
def sideBlock (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F) (s : I → Prop) : Matrix I I F :=
  mask (A.submatrix Sum.inr Sum.inr) (fun i => ¬s i) s

omit [Fintype I] in
def border (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F) (s : I → Prop) : I → F :=
  fun i => if s i then A (.inl ()) (.inr i) else 0

theorem rooted_cut_rank (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F) (s : I → Prop) :
    cutRank A (cutSites s) = (singleRow (sideBlock A s) (border A s)).rank := by
  rw [← actual_masked_cut]
  have h : mask A (fun i => i ∈ complement (cutSites s)) (fun j => j ∈ cutSites s) =
      padColumn (singleRow (sideBlock A s) (border A s)) := by
    ext i j
    rcases i with u | i <;> rcases j with v | j
    · cases v; simp [mask,padColumn,not_root_cutSites]
    · cases u
      change mask A _ _ (.inl ()) (.inr j) = border A s j
      simp [mask,border,mem_complement,not_root_cutSites,mem_cutSites]
    · cases v; simp [mask,padColumn,not_root_cutSites]
    · change mask A _ _ (.inr i) (.inr j) = sideBlock A s i j
      simp [mask,sideBlock,mem_complement,mem_cutSites]
  rw [h,padColumn_rank]

theorem wedge_cut_rank (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F) (s : I → Prop) (t : J → Prop) :
    cutRank (wedge A B) (cutSites (Sum.elim s t)) =
      (glueRows (sideBlock A s) (sideBlock B t) (border A s) (border B t)).rank := by
  rw [← actual_masked_cut]
  have h : mask (wedge A B) (fun i => i ∈ complement (cutSites (Sum.elim s t)))
      (fun j => j ∈ cutSites (Sum.elim s t)) =
      padColumn (glueRows (sideBlock A s) (sideBlock B t) (border A s) (border B t)) := by
    ext i j
    rcases i with u | (i | i) <;> rcases j with v | (j | j) <;>
      simp [mask,padColumn,glueRows,sideBlock,border,mem_complement,not_root_cutSites,mem_cutSites,
        wedge]
  rw [h,padColumn_rank]

theorem deletion_cut_rank (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F) (s : I → Prop) :
    cutRank (A.submatrix Sum.inr Sum.inr) (univ.filter s) = (sideBlock A s).rank := by
  rw [← actual_masked_cut]
  congr 1
  ext i j
  simp [sideBlock,mask,mem_complement]

/-- Unconditional cut-rank moment formula for a concrete wedge and for
every cut whose common vertex lies outside the chosen side. -/
theorem wedge_moment (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F) (s : I → Prop) (t : J → Prop)
    (x : ℝ) (hx : x ≠ 1) :
    let hA := x^(cutRank (A.submatrix Sum.inr Sum.inr) (univ.filter s))
    let hB := x^(cutRank (B.submatrix Sum.inr Sum.inr) (univ.filter t))
    let gA := x^(cutRank A (cutSites s))
    let gB := x^(cutRank B (cutSites t))
    x^(cutRank (wedge A B) (cutSites (Sum.elim s t))) =
      x*hA*hB + ((gA-x*hA)*(gB-x*hB))/(1-x) := by
  dsimp only
  rw [wedge_cut_rank, rooted_cut_rank, rooted_cut_rank, deletion_cut_rank, deletion_cut_rank]
  exact articulation_matrix _ hx _ _ _ _
end

section
open Matrix Finset
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
local notation "F" => ZMod 2
variable {I J : Type*} [Fintype I] [Fintype J]

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
      (Finset.univ \ U.map e.toEmbedding) = reindex eV eU (cutMatrix A U V) := by
    ext i j
    rfl
  unfold cutRank complement
  rw [he, rank_reindex]

theorem trace_chart {X : Type*} [Fintype X] {n : ℕ}
    (e : X ≃ Fin n) (A : Matrix X X F) (U : Finset X)
    (hs : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 0)
    (K : ℝ) (hK : 1 < K) :
    graphTraceMoment (reindex e e A) K (U.map e.toEmbedding) =
      ((2:ℝ)^(1-K))^(cutRank A U) := by
  let M := reindex e e A
  have hS (i j : Fin n) : M i j = M j i := hs _ _
  have hD (i : Fin n) : M i i = 0 := hd _
  rw [(physical_graph_gce_monotone n K M hS hD hK).1, transport]
  exact (Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)) _ _).trans
    (Real.rpow_natCast ((2:ℝ)^(1-K)) _)

private theorem cut_flip {X : Type*} [Fintype X] (A : Matrix X X F)
    (hs : ∀ i j, A i j=A j i) (U : Finset X) :
    cutRank A (complement U) = cutRank A U := by
  have hc (i : X) (S : Finset X) : i ∈ complement S ↔ i ∉ S := by simp [complement]
  rw [← actual_masked_cut, ← actual_masked_cut, ← Matrix.rank_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, mask, hc, not_not]
  by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;> simp [hi,hj,hs j i]

omit [Fintype I] [Fintype J] in
private theorem wedge_symm (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F)
    (hs : ∀ i j, A i j = A j i) (ht : ∀ i j, B i j = B j i) :
    ∀ i j, wedge A B i j = wedge A B j i := by
  intro i j
  rcases i with i | (i|i) <;> rcases j with j | (j|j) <;>
    first | rfl | exact hs _ _ | exact ht _ _

omit [Fintype I] [Fintype J] in
private theorem wedge_diag (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F)
    (hs : ∀ i, A i i = 0) (ht : ∀ i, B i i = 0) :
    ∀ i, wedge A B i i = 0 := by
  rintro (i|(i|i))
  · rfl
  · exact hs _
  · exact ht _

def selectRoot {X : Type*} [Fintype X] (root : Prop) (s : X → Prop) : Finset (Unit ⊕ X) :=
  univ.filter (Sum.elim (fun _ => root) s)

private theorem root_off {X : Type*} [Fintype X] (s : X → Prop) :
    selectRoot False s = cutSites s := by
  ext i; rcases i with i|i
  · simp [selectRoot,not_root_cutSites]
  · simp [selectRoot,mem_cutSites]

private theorem root_on {X : Type*} [Fintype X] (s : X → Prop) :
    selectRoot True s = complement (cutSites (fun i => ¬s i)) := by
  ext i; rcases i with i|i
  · simp [selectRoot,complement,not_root_cutSites]
  · simp [selectRoot,complement,mem_cutSites]

private theorem filtered_flip {X : Type*} [Fintype X] (s : X → Prop) :
    (univ.filter s : Finset X) = complement (univ.filter (fun i => ¬s i)) := by
  ext i; simp [complement]

theorem wedge_moment_all (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F)
    (hA : ∀ i j, A i j=A j i) (hB : ∀ i j, B i j=B j i)
    (root : Prop) (s : I → Prop) (t : J → Prop) (x : ℝ) (hx : x ≠ 1) :
    let h := x^(cutRank (A.submatrix Sum.inr Sum.inr) (univ.filter s))
    let j := x^(cutRank (B.submatrix Sum.inr Sum.inr) (univ.filter t))
    let g := x^(cutRank A (selectRoot root s))
    let k := x^(cutRank B (selectRoot root t))
    x^(cutRank (wedge A B) (selectRoot root (Sum.elim s t))) =
      x*h*j + ((g-x*h)*(k-x*j))/(1-x) := by
  by_cases h : root
  · have hp : root = True := propext (iff_true_intro h)
    subst root
    dsimp only
    rw [root_on, root_on, root_on, cut_flip _ (wedge_symm A B hA hB), cut_flip _ hA, cut_flip _ hB,
      filtered_flip s, filtered_flip t, cut_flip (A.submatrix Sum.inr Sum.inr) (fun i j => hA (.inr i) (.inr j)),
      cut_flip (B.submatrix Sum.inr Sum.inr) (fun i j => hB (.inr i) (.inr j))]
    have he : (fun i => ¬Sum.elim s t i) = Sum.elim (fun i => ¬s i) (fun i => ¬t i) := by
      funext i; cases i <;> rfl
    rw [he]
    convert wedge_moment A B (fun i => ¬s i) (fun i => ¬t i) x hx using 9
  · have hp : root = False := propext (iff_false_intro h)
    subst root
    dsimp only
    rw [root_off, root_off, root_off]
    exact wedge_moment A B s t _ hx

def encodedTrace {X : Type*} [Fintype X] (A : Matrix X X F) (K : ℝ) (U : Finset X) : ℝ :=
  let e := Fintype.equivFin X
  graphTraceMoment (reindex e e A) K (U.map e.toEmbedding)

/-- Actual graph-state trace gluing at an articulation; no assumption on how
many other articulations or cycles the two pieces contain. -/
theorem actual_articulation_trace (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F)
    (hA : ∀ i j, A i j=A j i) (hB : ∀ i j, B i j=B j i)
    (dA : ∀ i, A i i=0) (dB : ∀ i, B i i=0)
    (K : ℝ) (hK : 1<K) (root : Prop) (s : I → Prop) (t : J → Prop) :
    let x := (2:ℝ)^(1-K)
    let h := encodedTrace (A.submatrix Sum.inr Sum.inr) K (univ.filter s)
    let j := encodedTrace (B.submatrix Sum.inr Sum.inr) K (univ.filter t)
    let g := encodedTrace A K (selectRoot root s)
    let k := encodedTrace B K (selectRoot root t)
    encodedTrace (wedge A B) K (selectRoot root (Sum.elim s t)) =
      x*h*j + ((g-x*h)*(k-x*j))/(1-x) := by
  have hx : (2:ℝ)^(1-K) ≠ 1 := ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  dsimp only [encodedTrace]
  rw [trace_chart _ _ _ (wedge_symm A B hA hB) (wedge_diag A B dA dB) K hK,
    trace_chart _ A _ hA dA K hK, trace_chart _ B _ hB dB K hK,
    trace_chart _ (A.submatrix Sum.inr Sum.inr) _ (fun i j => hA (.inr i) (.inr j)) (fun i => dA (.inr i)) K hK,
    trace_chart _ (B.submatrix Sum.inr Sum.inr) _ (fun i j => hB (.inr i) (.inr j)) (fun i => dB (.inr i)) K hK]
  exact wedge_moment_all A B hA hB root s t _ hx
end

section
def Law {X : Type*} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1

def obs {X : Type*} [Fintype X] (p χ : X → ℝ) : ℝ := ∑ u, p u * χ u

def mix {X : Type*} (a : ℝ) (p q : X → ℝ) (u : X) : ℝ :=
  a * p u + (1-a) * q u

theorem law_mix {X : Type*} [Fintype X] {p q : X → ℝ}
    (hp : Law p) (hq : Law q) {a : ℝ} (ha : 0≤a) (ha' : a≤1) :
    Law (mix a p q) := by
  refine ⟨fun u => add_nonneg (mul_nonneg ha (hp.1 u))
    (mul_nonneg (sub_nonneg.mpr ha') (hq.1 u)),?_⟩
  simp [mix, sum_add_distrib, ← mul_sum, hp.2, hq.2]

theorem obs_mix {X : Type*} [Fintype X] (a : ℝ) (p q χ : X → ℝ) :
    obs (mix a p q) χ = mix a (fun _ : Unit => obs p χ) (fun _ => obs q χ) () := by
  simp only [obs,mix, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
end

section
def bitSign (e b : Bool) : ℝ := if e && b then -1 else 1
end

section
open Finset

variable {P Q T : Type*} [Fintype P] [Fintype Q] [Fintype T]

def pushIndependent (p : P → ℝ) (q : Q → ℝ) (f : P → Q → T) (t : T) : ℝ :=
  ∑ i, ∑ j, if f i j = t then p i*q j else 0

theorem pushIndependent_obs (p : P → ℝ) (q : Q → ℝ) (f : P → Q → T) (χ : T → ℝ) :
    obs (pushIndependent p q f) χ = ∑ i, ∑ j, (p i*q j)*χ (f i j) := by
  unfold obs pushIndependent
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

theorem pushIndependent_law (p : P → ℝ) (q : Q → ℝ) (f : P → Q → T)
    (hp : Law p) (hq : Law q) : Law (pushIndependent p q f) := by
  constructor
  · intro t
    unfold pushIndependent
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      split
      · exact mul_nonneg (hp.1 i) (hq.1 j)
      · exact le_rfl))
  · have h := pushIndependent_obs p q f (fun _ => 1)
    simpa [obs, ← Finset.mul_sum, hq.2, hp.2] using h

theorem character_product (p : P → ℝ) (q : Q → ℝ) (f : P → Q → T)
    (χ : T → ℝ) (s : P → ℝ) (t : Q → ℝ)
    (h : ∀ i j, χ (f i j) = s i*t j) :
    obs (pushIndependent p q f) χ = obs p s * obs q t := by
  rw [pushIndependent_obs]
  unfold obs
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [h]
  ring

/-- Compose lifted characters by their XOR map; the normalized marked
channel uses the product alone, and the unmarked channel mixes it with deletion. -/
theorem two_channel_sample (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1)
    (p₀ p₁ : P → ℝ) (q₀ q₁ : Q → ℝ) (f : P → Q → T)
    (hp₀ : Law p₀) (hp₁ : Law p₁) (hq₀ : Law q₀) (hq₁ : Law q₁)
    (χ : T → ℝ) (s : P → ℝ) (t : Q → ℝ) (hm : ∀ i j, χ (f i j) = s i*t j) :
    let H := pushIndependent p₀ q₀ f
    let D := pushIndependent p₁ q₁ f
    Law (mix x H D) ∧ Law D ∧
      obs (mix x H D) χ = x*(obs p₀ s*obs q₀ t)+(1-x)*(obs p₁ s*obs q₁ t) ∧
      obs D χ = obs p₁ s*obs q₁ t := by
  dsimp only
  refine ⟨law_mix (pushIndependent_law _ _ _ hp₀ hq₀)
    (pushIndependent_law _ _ _ hp₁ hq₁) hx hX,
    pushIndependent_law _ _ _ hp₁ hq₁,?_,character_product _ _ _ _ _ _ hm⟩
  rw [obs_mix, character_product _ _ _ _ _ _ hm, character_product _ _ _ _ _ _ hm]
  rfl
end

section
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J]
local notation "F" => ZMod 2

abbrev RootWord (X : Type*) := Bool × (X → Bool)

def rootChar {X : Type*} [Fintype X] (root : Prop) (s : X → Prop) (a : RootWord X) : ℝ :=
  bitSign (decide root) a.1 * ∏ i, bitSign (decide (s i)) (a.2 i)

omit [Fintype I] [Fintype J] in
def glueWord (a : RootWord I) (b : RootWord J) : RootWord (I ⊕ J) :=
  (xor a.1 b.1, Sum.elim a.2 b.2)

theorem rootChar_glue (root : Prop) (s : I → Prop) (t : J → Prop)
    (a : RootWord I) (b : RootWord J) :
    rootChar root (Sum.elim s t) (glueWord a b) = rootChar root s a * rootChar root t b := by
  have h (e p q : Bool) : bitSign e (xor p q) = bitSign e p*bitSign e q := by
    cases e <;> cases p <;> cases q <;> norm_num [bitSign]
  unfold rootChar glueWord
  rw [Fintype.prod_sum_type, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ac_rfl

/-- The physical wedge readout is realized by an explicit classical law
when both pieces have laws for the root-deletion and normalized surplus
channels. This is a composition theorem at any real K>1. -/
theorem physical_wedge_law (A : Matrix (Unit ⊕ I) (Unit ⊕ I) F)
    (B : Matrix (Unit ⊕ J) (Unit ⊕ J) F)
    (hA : ∀ i j, A i j=A j i) (hB : ∀ i j, B i j=B j i)
    (dA : ∀ i, A i i=0) (dB : ∀ i, B i i=0)
    (K : ℝ) (hK : 1<K)
    (p₀ p₁ : RootWord I → ℝ) (q₀ q₁ : RootWord J → ℝ)
    (hp₀ : Law p₀) (hp₁ : Law p₁) (hq₀ : Law q₀) (hq₁ : Law q₁)
    (oA : ∀ r s, obs p₀ (rootChar r s) =
      encodedTrace (A.submatrix Sum.inr Sum.inr) K (Finset.univ.filter s))
    (oB : ∀ r t, obs q₀ (rootChar r t) =
      encodedTrace (B.submatrix Sum.inr Sum.inr) K (Finset.univ.filter t))
    (sA : ∀ r s, obs p₁ (rootChar r s) =
      (encodedTrace A K (selectRoot r s)-(2:ℝ)^(1-K)*obs p₀ (rootChar r s))/(1-(2:ℝ)^(1-K)))
    (sB : ∀ r t, obs q₁ (rootChar r t) =
      (encodedTrace B K (selectRoot r t)-(2:ℝ)^(1-K)*obs q₀ (rootChar r t))/(1-(2:ℝ)^(1-K))) :
    ∃ P : RootWord (I ⊕ J) → ℝ, Law P ∧ ∀ r s t,
      obs P (rootChar r (Sum.elim s t)) = encodedTrace (wedge A B) K (selectRoot r (Sum.elim s t)) := by
  let x := (2:ℝ)^(1-K)
  let P := mix x (pushIndependent p₀ q₀ glueWord) (pushIndependent p₁ q₁ glueWord)
  have hp : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hX : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨P, law_mix (pushIndependent_law _ _ _ hp₀ hq₀)
    (pushIndependent_law _ _ _ hp₁ hq₁) hp.le hX.le, ?_⟩
  intro r s t
  have ho := (two_channel_sample x hp.le hX.le p₀ p₁ q₀ q₁ glueWord hp₀ hp₁ hq₀ hq₁
    _ _ _ (rootChar_glue r s t)).2.2.1
  change obs P _ = _
  rw [show obs P (rootChar r (Sum.elim s t)) = _ from ho,
    sA r s, sB r t, oA r s, oB r t, actual_articulation_trace A B hA hB dA dB K hK]
  change x * (_ * _) + (1-x) * ((_ / (1-x)) * (_ / (1-x))) = _
  have hn : 1-x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hX)
  dsimp only [x] at hn ⊢
  field_simp [hn]
end

/-- An observation table for physical graph states indexed by finite graph
and cut. The scientific state is the real power K. -/
abbrev MomentTable := (n : ℕ) → Matrix (Fin n) (Fin n) (ZMod 2) → Finset (Fin n) → ℝ

def momentTable (K : ℝ) : MomentTable := fun _ A U => graphTraceMoment A K U

def observe {V : Type} [Fintype V] (f : MomentTable) (A : Matrix V V (ZMod 2))
    (U : Finset V) : ℝ :=
  let e := Fintype.equivFin V
  f (Fintype.card V) (reindex e e A) (U.map e.toEmbedding)

/-- Actual common-vertex gluing factors into the deleted graphs and the
two surplus channels. All reads are actual mixed-state trace moments. -/
theorem physical_articulation_readout (K : ℝ) (hK : 1<K) :
    let observed := momentTable K
    ∀ (I J : Type) [Fintype I] [Fintype J]
      (A : Matrix (Unit ⊕ I) (Unit ⊕ I) (ZMod 2)) (B : Matrix (Unit ⊕ J) (Unit ⊕ J) (ZMod 2)),
    (∀ i j, A i j=A j i) → (∀ i j, B i j=B j i) →
    (∀ i, A i i=0) → (∀ i, B i i=0) →
    ∀ (root : Prop) (s : I → Prop) (t : J → Prop),
    let x := (2:ℝ)^(1-K)
    let h := observe observed (A.submatrix Sum.inr Sum.inr) (univ.filter s)
    let j := observe observed (B.submatrix Sum.inr Sum.inr) (univ.filter t)
    let g := observe observed A (selectRoot root s)
    let k := observe observed B (selectRoot root t)
    observe observed (wedge A B) (selectRoot root (Sum.elim s t)) =
      x*h*j + ((g-x*h)*(k-x*j))/(1-x) := by
  dsimp only
  intro I J fi fj A B hA hB dA dB root s t
  exact actual_articulation_trace A B hA hB dA dB K hK root s t

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation
