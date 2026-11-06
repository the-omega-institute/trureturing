/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Batch
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Batch
   mirror-E: none(waiver:original-label-two-sum-batch)
   anchors: [mathlib/module/Mathlib.Data.List.Basic]
   utility: none
   digest: Finite noninterfering critical fibres produce actual native sequences with exact ordered pair coverage. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Fibre

/-! UNCOMPILED. This construction is consumed by both the parent's filling-main
and its separate collar stage. It assumes source-fibre intersection facts, never
a collapse of the parent or an output certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- Literal union of indexed fibre families. Repeated indices are not needed. -/
def fibreLayers (a : I → Finset V) (M : I → Family V) : List I → Family V
  | [] => ⊥
  | i :: is => rawJoin (delta (a i)) (M i) ⊔ fibreLayers a M is

/-- Membership retains the actual fibre index and local face. -/
theorem mem_fibreLayers (a : I → Finset V) (M : I → Family V)
    (is : List I) (s : Finset V) :
    s ∈ fibreLayers a M is ↔ ∃ i ∈ is, s ∈ rawJoin (delta (a i)) (M i) := by
  induction is with
  | nil => simp [fibreLayers]
  | cons i is ih =>
    simp only [fibreLayers,LowerSet.mem_sup_iff,ih,List.mem_cons]
    aesop

/-- A finite batch, with actual evolving base (finished N-fibres and unfinished
M-fibres). The pair list is precisely the concatenation of the lifted local
lists, in the supplied finite index order. -/
def batchFibre (is : List I) (hn : is.Nodup) (B : Family V)
    (a W : I → Finset V) (M N : I → Family V)
    (S : ∀ i, Sequence (project (M i)) (project (N i)))
    (hM0 : ∀ i ∈ is, (∅ : Finset V) ∈ M i)
    (hN0 : ∀ i ∈ is, (∅ : Finset V) ∈ N i)
    (hNM : ∀ i ∈ is, N i ≤ M i)
    (hd : ∀ i ∈ is, Disjoint (a i) (W i))
    (hs : ∀ i ∈ is, Supported (W i) (M i))
    (hb : ∀ i ∈ is, ∀ x ⊂ a i, ∀ t ∈ M i, x ∪ t ∈ B)
    (hbase : ∀ i ∈ is, ∀ t ⊆ W i, a i ∪ t ∈ B → t ∈ N i)
    (hcross : ∀ i ∈ is, ∀ j ∈ is, i ≠ j → ∀ t ⊆ W i,
      a i ∪ t ∈ rawJoin (delta (a j)) (M j) → t ∈ N i) :
    {T : Sequence (project (B ⊔ fibreLayers a M is))
        (project (B ⊔ fibreLayers a N is)) //
      T.pairs.map (fun P => (P.lower,P.upper)) =
        is.flatMap (fun i => (S i).pairs.map
          (fun P => (a i ∪ P.lower,a i ∪ P.upper)))} := by
  classical
  cases is with
  | nil =>
    exact ⟨(Sequence.refl _).cast rfl rfl,by rw [Sequence.pairs_cast]; rfl⟩
  | cons i is =>
    have hni := List.nodup_cons.mp hn
    let B' := B ⊔ fibreLayers a M is
    have hbi : ∀ t ⊆ W i, a i ∪ t ∈ B' → t ∈ N i := by
      intro t ht h
      rcases h with h | h
      · exact hbase i (by simp) t ht h
      · obtain ⟨j,hj,hjmem⟩ := (mem_fibreLayers a M is _).mp h
        exact hcross i (by simp) j (by simp [hj])
          (fun he => hni.1 (he.symm ▸ hj)) t ht hjmem
    let P := liftFibre (M i) (N i) B' (a i) (W i)
      (hM0 i (by simp)) (hN0 i (by simp)) (S i)
      (hd i (by simp)) (hs i (by simp))
      (fun x hx t ht => Or.inl (hb i (by simp) x hx t ht)) hbi
    let B'' := B ⊔ rawJoin (delta (a i)) (N i)
    have hbTail : ∀ j ∈ is, ∀ x ⊂ a j, ∀ t ∈ M j, x ∪ t ∈ B'' :=
      fun j hj x hx t ht => Or.inl (hb j (by simp [hj]) x hx t ht)
    have hbaseTail : ∀ j ∈ is, ∀ t ⊆ W j, a j ∪ t ∈ B'' → t ∈ N j := by
      intro j hj t ht h
      rcases h with h | ⟨x,hx,y,hy,he⟩
      · exact hbase j (by simp [hj]) t ht h
      · exact hcross j (by simp [hj]) i (by simp)
          (fun he => hni.1 (he ▸ hj)) t ht
          ⟨x,hx,y,hNM i (by simp) hy,he⟩
    let Q := batchFibre is hni.2 B'' a W M N S
      (fun j hj => hM0 j (by simp [hj]))
      (fun j hj => hN0 j (by simp [hj]))
      (fun j hj => hNM j (by simp [hj]))
      (fun j hj => hd j (by simp [hj]))
      (fun j hj => hs j (by simp [hj])) hbTail hbaseTail
      (fun j hj k hk => hcross j (by simp [hj]) k (by simp [hk]))
    have sourceEq : B' ⊔ rawJoin (delta (a i)) (M i) =
        B ⊔ fibreLayers a M (i :: is) := by
      dsimp [B',fibreLayers]
      ac_rfl
    have middleEq : B' ⊔ rawJoin (delta (a i)) (N i) =
        B'' ⊔ fibreLayers a M is := by
      dsimp [B',B'']
      ac_rfl
    have targetEq : B'' ⊔ fibreLayers a N is =
        B ⊔ fibreLayers a N (i :: is) := by
      dsimp [B'',fibreLayers]
      rw [sup_assoc]
    refine ⟨((P.cast (congrArg project sourceEq) (congrArg project middleEq)).append
      Q.1).cast rfl (congrArg project targetEq),?_⟩
    rw [Sequence.pairs_cast,Sequence.pairs_append,List.map_append,
      Sequence.pairs_cast]
    dsimp only [P]
    rw [liftFibre_pairs,Q.2]
    simp only [List.flatMap_cons]
    rfl

termination_by is.length

end D5.S3.Geometry.OriginalLabelTwoSum
