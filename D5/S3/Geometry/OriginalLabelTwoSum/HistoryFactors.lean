/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryFactors
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryFactors
   mirror-E: none(waiver:original-mask-physical-wheel-factors)
   anchors: [mathlib/module/Mathlib.Order.UpperLower.CompleteLattice]
   utility: none
   digest: Actual last-wheel corners factor on their original HistoryCorners.residual ground, with strictly predecessor original masks and indexed projected rim rows. -/
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory

/-! SOURCE_ONLY_UNCOMPILED. The only geometric input below is the existing
`PhysicalHistory.WheelInput g`. The physical root theorem consumed here was
derived from actual unique paths in the selected predecessor sources; those
sources, like this module, remain uncompiled premises of this source attempt.

The two-label interface is `image labels {1,2}`. It is never the full spoke
ground. `Readback` is a CONCLUSION constructed from geometric input and masks,
not an assumed factorization or a strong-output supplier. Its local index type
retains every original noninterface rim index, including repeated rows after
projection. All equalities are augmented-family equalities on full HistoryCorners.residual
grounds, before discarding the empty face. No native collapse, intact-terminal
construction, canonical handoff, or final history induction is asserted here.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryFactors
open HistoryCorners PhysicalHistory

section CornerAlgebra
variable {V : Type*} [DecidableEq V]

private theorem residual_union (X Y A B : Finset V) :
    HistoryCorners.residual (X ∪ Y) A B =
      HistoryCorners.residual X (A ∩ X) (B ∩ X) ∪ HistoryCorners.residual Y (A ∩ Y) (B ∩ Y) := by
  ext x
  simp only [HistoryCorners.residual, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

private theorem corner_sup (W A B : Finset V) (K L : Family V) :
    corner W A B (K ⊔ L) = corner W A B K ⊔ corner W A B L := by
  apply SetLike.ext
  intro s
  change (s ⊆ HistoryCorners.residual W A B ∧ (s ∪ A ∈ K ∨ s ∪ A ∈ L)) ↔
    (s ⊆ HistoryCorners.residual W A B ∧ s ∪ A ∈ K) ∨
      (s ⊆ HistoryCorners.residual W A B ∧ s ∪ A ∈ L)
  tauto

/-- Used only by the actual physical factorization below. Coordinate splitting
uses the existing raw `join_split`, including its support hypotheses. -/
private theorem corner_join (X Y A B : Finset V) (K L : Family V)
    (hXY : Disjoint X Y) (hK : Supported X K) (hL : Supported Y L)
    (hA : A ⊆ X ∪ Y) :
    corner (X ∪ Y) A B (rawJoin K L) =
      rawJoin (corner X (A ∩ X) (B ∩ X) K)
        (corner Y (A ∩ Y) (B ∩ Y) L) := by
  apply SetLike.ext
  intro s
  have hsplitA : A = (A ∩ X) ∪ (A ∩ Y) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    exact ⟨fun hx => (Finset.mem_union.mp (hA hx)).elim
      (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩), by tauto⟩
  constructor
  · rintro ⟨hs,h⟩
    have hh := (join_split hXY hK hL (s ∪ A)).mp h
    refine ⟨s ∩ X, ⟨?_,?_⟩, s ∩ Y, ⟨?_,?_⟩, ?_⟩
    · intro x hx
      obtain ⟨hxs,hxX⟩ := Finset.mem_inter.mp hx
      obtain ⟨_,hn⟩ := Finset.mem_sdiff.mp (hs hxs)
      refine Finset.mem_sdiff.mpr ⟨hxX,?_⟩
      simp only [Finset.mem_union, Finset.mem_inter] at hn ⊢
      tauto
    · have he : (s ∪ A) ∩ X = (s ∩ X) ∪ (A ∩ X) := by
        ext x; simp only [Finset.mem_union,Finset.mem_inter]; tauto
      exact he ▸ hh.2.1
    · intro x hx
      obtain ⟨hxs,hxY⟩ := Finset.mem_inter.mp hx
      obtain ⟨_,hn⟩ := Finset.mem_sdiff.mp (hs hxs)
      refine Finset.mem_sdiff.mpr ⟨hxY,?_⟩
      simp only [Finset.mem_union, Finset.mem_inter] at hn ⊢
      tauto
    · have he : (s ∪ A) ∩ Y = (s ∩ Y) ∪ (A ∩ Y) := by
        ext x; simp only [Finset.mem_union,Finset.mem_inter]; tauto
      exact he ▸ hh.2.2
    · ext x
      simp only [Finset.mem_union,Finset.mem_inter]
      exact ⟨fun hx => (Finset.mem_union.mp
        (Finset.mem_sdiff.mp (hs hx)).1).elim
          (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩), by tauto⟩
  · rintro ⟨a,⟨ha,haK⟩,b,⟨hb,hbL⟩,rfl⟩
    refine ⟨?_,a ∪ (A ∩ X),haK,b ∪ (A ∩ Y),hbL,?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxX,hn⟩ := Finset.mem_sdiff.mp (ha hx)
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hxX,?_⟩
        simp only [Finset.mem_union,Finset.mem_inter] at hn ⊢
        tauto
      · obtain ⟨hxY,hn⟩ := Finset.mem_sdiff.mp (hb hx)
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hxY,?_⟩
        simp only [Finset.mem_union,Finset.mem_inter] at hn ⊢
        tauto
    · calc
        (a ∪ b) ∪ A = (a ∪ b) ∪ ((A ∩ X) ∪ (A ∩ Y)) :=
          congrArg (fun t => (a ∪ b) ∪ t) hsplitA
        _ = (a ∪ (A ∩ X)) ∪ (b ∪ (A ∩ Y)) := by ac_rfl

private theorem corner_delta (W A B : Finset V) (hA : A ⊆ W) :
    corner W A B (delta W) = delta (HistoryCorners.residual W A B) := by
  apply SetLike.ext
  intro s
  change (s ⊆ HistoryCorners.residual W A B ∧ s ∪ A ⊆ W) ↔ s ⊆ HistoryCorners.residual W A B
  exact ⟨And.left,fun hs =>
    ⟨hs,Finset.union_subset (hs.trans Finset.sdiff_subset) hA⟩⟩

/-- The punctured LOCAL simplex is VOID exactly when its linked mask hits
the interface. The old factor may independently be VOID in the join. -/
private theorem corner_punctured (Y R A B : Finset V) (hA : A ⊆ Y) :
    corner Y A B (delta (Y \ R)) =
      if Disjoint A R then delta (HistoryCorners.residual Y A B \ R) else ⊥ := by
  apply SetLike.ext
  intro s
  by_cases hd : Disjoint A R
  · rw [if_pos hd]
    change (s ⊆ HistoryCorners.residual Y A B ∧ s ∪ A ⊆ Y \ R) ↔
      s ⊆ HistoryCorners.residual Y A B \ R
    constructor
    · rintro ⟨hs,ht⟩ x hx
      exact Finset.mem_sdiff.mpr ⟨hs hx,
        (Finset.mem_sdiff.mp (ht (Finset.mem_union_left _ hx))).2⟩
    · intro hs
      refine ⟨fun x hx => (Finset.mem_sdiff.mp (hs hx)).1,?_⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp (hs hx)
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hr).1,hn⟩
      · exact Finset.mem_sdiff.mpr ⟨hA hx,fun hr =>
          Finset.disjoint_left.mp hd hx hr⟩
  · rw [if_neg hd]
    change (s ⊆ HistoryCorners.residual Y A B ∧ s ∪ A ⊆ Y \ R) ↔ False
    constructor
    · rintro ⟨_,ht⟩
      apply hd
      exact Finset.disjoint_left.mpr (fun x hx hr =>
        (Finset.mem_sdiff.mp (ht (Finset.mem_union_right _ hx))).2 hr)
    · exact False.elim

private theorem corner_phi (X Y R A B : Finset V) (D L E : Family V)
    (hXY : Disjoint X Y) (hD : Supported X D) (hL : Supported X L)
    (hE : Supported Y E) (hA : A ⊆ X ∪ Y) :
    corner (X ∪ Y) A B (phi X Y (Y \ R) D L E) =
      (rawJoin (delta (HistoryCorners.residual X (A ∩ X) (B ∩ X)))
          (corner Y (A ∩ Y) (B ∩ Y) E) ⊔
        rawJoin (corner X (A ∩ X) (B ∩ X) L)
          (delta (HistoryCorners.residual Y (A ∩ Y) (B ∩ Y)))) ⊔
      (if Disjoint (A ∩ Y) R then
        rawJoin (corner X (A ∩ X) (B ∩ X) D)
          (delta (HistoryCorners.residual Y (A ∩ Y) (B ∩ Y) \ R)) else ⊥) := by
  unfold phi
  rw [corner_sup,corner_sup,
    corner_join X Y A B D (delta (Y \ R)) hXY hD
      (fun _ hs => hs.trans Finset.sdiff_subset) hA,
    corner_join X Y A B L (delta Y) hXY hL (fun _ hs => hs) hA,
    corner_join X Y A B (delta X) E hXY (fun _ hs => hs) hE hA,
    corner_punctured Y R (A ∩ Y) (B ∩ Y) Finset.inter_subset_right,
    corner_delta Y (A ∩ Y) (B ∩ Y) Finset.inter_subset_right,
    corner_delta X (A ∩ X) (B ∩ X) Finset.inter_subset_right]
  by_cases hd : Disjoint (A ∩ Y) R
  · simp only [if_pos hd]
    ac_rfl
  · simp only [if_neg hd,(rawJoin_void _).2,sup_bot_eq,bot_sup_eq]
    ac_rfl

end CornerAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : Type*} (g : GraphData G V) (i : WheelInput g)

/-- Full old ground after the PHYSICAL interface deletion. -/
def oldGround : Finset V := g.ground.erase i.e
/-- All actual fresh spokes, distinct from the old retained labels. -/
def wheelGround : Finset V := (AllMWheel.ground i.width).image i.labels
/-- Exactly the two interface spoke labels, never all spokes. -/
def interface : Finset V := (AllMWheel.rim i.width i.atLeastThree).image i.labels
def oldMask (M : Finset V) : Finset V := M ∩ oldGround g i
def localMask (M : Finset V) : Finset V := M ∩ wheelGround g i
def oldResidual (A B : Finset V) : Finset V :=
  HistoryCorners.residual (oldGround g i) (oldMask g i A) (oldMask g i B)
def localResidual (A B : Finset V) : Finset V :=
  HistoryCorners.residual (wheelGround g i) (localMask g i A) (localMask g i B)

/-- J is an actual corner of the old graph, retaining e. -/
def prior (A B : Finset V) : Family V :=
  corner g.ground (oldMask g i A) (oldMask g i B) g.rows.root
/-- Exact predecessor deletion masks, on the original old graph. -/
def deleted (A B : Finset V) : Family V :=
  corner g.ground (oldMask g i A) (oldMask g i B ∪ {i.e}) g.rows.root
/-- Exact predecessor link masks, on the original old graph. -/
def linked (A B : Finset V) : Family V :=
  corner g.ground (oldMask g i A ∪ {i.e}) (oldMask g i B) g.rows.root

/-- Original noninterface indices of the ACTUAL local wheel. -/
def localRows : Rows V :=
  ((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.without
    (AllMWheel.interfaceRow i.width i.atLeastThree))
/-- Link filters; deletion projects. The subtype retains its original index. -/
def projectedRimRows (A B : Finset V) : Rows V :=
  cornerRows (localRows g i) (localMask g i A) (localMask g i B)

private theorem prior_ground (A B : Finset V) :
    HistoryCorners.residual g.ground (oldMask g i A) (oldMask g i B) =
      insert i.e (oldResidual g i A B) := by
  ext x
  by_cases hx : x = i.e
  · subst x
    simp [HistoryCorners.residual,oldMask,oldGround,oldResidual,i.retained]
  · simp [HistoryCorners.residual,oldMask,oldGround,oldResidual,hx]

/-- Both equations consume genuine mask composition, rather than selecting a
same-rank corner supplier. The raw deletion/link are of the ACTUAL J. -/
private theorem prior_readbacks (A B : Finset V) :
    deleted g i A B = restrict (oldResidual g i A B) (prior g i A B) ∧
    linked g i A B = rawLink (oldResidual g i A B) i.e (prior g i A B) := by
  have hground := prior_ground g i A B
  have hdel := corner_compose g.ground (oldMask g i A) (oldMask g i B)
    ∅ {i.e} g.rows.root (Finset.empty_subset _)
  have hlink := corner_compose g.ground (oldMask g i A) (oldMask g i B)
    {i.e} ∅ g.rows.root (by rw [hground]; simp)
  constructor
  · rw [Finset.union_empty] at hdel
    change corner (HistoryCorners.residual g.ground (oldMask g i A) (oldMask g i B))
      ∅ {i.e} (prior g i A B) = deleted g i A B at hdel
    rw [← hdel,hground]
    apply SetLike.ext
    intro s
    change (s ⊆ HistoryCorners.residual (insert i.e (oldResidual g i A B)) ∅ {i.e} ∧
      s ∪ ∅ ∈ prior g i A B) ↔
        s ∈ prior g i A B ∧ s ⊆ oldResidual g i A B
    have he : i.e ∉ oldResidual g i A B := fun h =>
      Finset.notMem_erase _ _ (Finset.mem_sdiff.mp h).1
    have hr : HistoryCorners.residual (insert i.e (oldResidual g i A B)) ∅ {i.e} =
        oldResidual g i A B := by
      ext x
      simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.notMem_empty,
        false_or,Finset.mem_singleton,Finset.mem_insert]
      constructor
      · rintro ⟨h,hn⟩; exact h.resolve_left hn
      · intro h; exact ⟨Or.inr h,fun hx => he (hx ▸ h)⟩
    rw [hr,Finset.union_empty]
    tauto
  · rw [Finset.union_empty] at hlink
    change corner (HistoryCorners.residual g.ground (oldMask g i A) (oldMask g i B))
      {i.e} ∅ (prior g i A B) = linked g i A B at hlink
    rw [← hlink,hground]
    apply SetLike.ext
    intro s
    change (s ⊆ HistoryCorners.residual (insert i.e (oldResidual g i A B)) {i.e} ∅ ∧
      s ∪ {i.e} ∈ prior g i A B) ↔
        s ⊆ oldResidual g i A B ∧ insert i.e s ∈ prior g i A B
    have he : i.e ∉ oldResidual g i A B := fun h =>
      Finset.notMem_erase _ _ (Finset.mem_sdiff.mp h).1
    have hr : HistoryCorners.residual (insert i.e (oldResidual g i A B)) {i.e} ∅ =
        oldResidual g i A B := by
      ext x
      simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.notMem_empty,
        or_false,Finset.mem_singleton,Finset.mem_insert]
      constructor
      · rintro ⟨h,hn⟩; exact h.resolve_left hn
      · intro h; exact ⟨Or.inr h,fun hx => he (hx ▸ h)⟩
    have hu : s ∪ {i.e} = insert i.e s := by
      ext x; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert]; tauto
    rw [hr,hu]

/-- A typed exact factor package, with no collapse/certificate fields. All
three earlier factors are on g, not on the attached graph. -/
structure Readback (A B : Finset V) : Prop where
  ground : HistoryCorners.residual (physicalWheelStep g i).data.ground A B =
    oldResidual g i A B ∪ localResidual g i A B
  disjoint : Disjoint (oldResidual g i A B) (localResidual g i A B)
  masks_split : A = oldMask g i A ∪ localMask g i A ∧
    B = oldMask g i B ∪ localMask g i B
  current_port_absent : i.e ∉ HistoryCorners.residual (physicalWheelStep g i).data.ground A B
  interface_eq : interface g i =
    {i.labels (AllMWheel.firstLabel i.width i.atLeastThree),
      i.labels (AllMWheel.secondLabel i.width i.atLeastThree)}
  prior_ground : HistoryCorners.residual g.ground (oldMask g i A) (oldMask g i B) =
    insert i.e (oldResidual g i A B)
  factor_grounds :
    HistoryCorners.residual g.ground (oldMask g i A) (oldMask g i B ∪ {i.e}) = oldResidual g i A B ∧
    HistoryCorners.residual g.ground (oldMask g i A ∪ {i.e}) (oldMask g i B) = oldResidual g i A B
  prior_masks : oldMask g i A ⊆ g.ground ∧ oldMask g i B ⊆ g.ground ∧
    Disjoint (oldMask g i A) (oldMask g i B)
  deleted_masks : oldMask g i A ⊆ g.ground ∧
    oldMask g i B ∪ {i.e} ⊆ g.ground ∧
      Disjoint (oldMask g i A) (oldMask g i B ∪ {i.e})
  linked_masks : oldMask g i A ∪ {i.e} ⊆ g.ground ∧
    oldMask g i B ⊆ g.ground ∧
      Disjoint (oldMask g i A ∪ {i.e}) (oldMask g i B)
  deleted_readback : deleted g i A B =
    restrict (oldResidual g i A B) (prior g i A B)
  linked_readback : linked g i A B =
    rawLink (oldResidual g i A B) i.e (prior g i A B)
  row_ground : (projectedRimRows g i A B).ground = localResidual g i A B
  row : ∀ c : (projectedRimRows g i A B).chords,
    (projectedRimRows g i A B).row c =
      ((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image
        i.labels) \ localMask g i B
  face : ∀ s : Finset V, s ∈ (projectedRimRows g i A B).root ↔
    ∃ d : Fin i.width, d ≠ AllMWheel.interfaceRow i.width i.atLeastThree ∧
      Disjoint ((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d).image
        i.labels) (localMask g i A) ∧
      s ⊆ localResidual g i A B \
        (((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d).image
          i.labels) \ localMask g i B)
  no_rows : IsEmpty (projectedRimRows g i A B).chords →
    (projectedRimRows g i A B).root = ⊥
  raw_empty : (∅ : Finset V) ∈ (projectedRimRows g i A B).root ↔
    Nonempty (projectedRimRows g i A B).chords
  zero_ground : localResidual g i A B = ∅ →
    (projectedRimRows g i A B).root = ⊥ ∨
      (projectedRimRows g i A B).root = delta ∅
  empty_row : ∀ c : (projectedRimRows g i A B).chords,
    (projectedRimRows g i A B).row c = ∅ →
      (projectedRimRows g i A B).root = delta (localResidual g i A B)
  singleton_row : ∀ (c : (projectedRimRows g i A B).chords) (a : V),
    (projectedRimRows g i A B).row c = {a} →
      (projectedRimRows g i A B).root = delta ((localResidual g i A B).erase a) ⊔
        rawJoin (delta {a}) (avoiding (projectedRimRows g i A B) a).root
  absent_marker : (localResidual g i A B) \ interface g i =
    (localResidual g i A B) \ (interface g i ∩ localResidual g i A B)
  no_markers : Disjoint (localResidual g i A B) (interface g i) →
    localResidual g i A B \ interface g i = localResidual g i A B
  one_marker : ∀ r : V, interface g i ∩ localResidual g i A B = {r} →
    localResidual g i A B \ interface g i = (localResidual g i A B).erase r
  factorization : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
    (rawJoin (delta (oldResidual g i A B)) (projectedRimRows g i A B).root ⊔
      rawJoin (linked g i A B) (delta (localResidual g i A B))) ⊔
    (if Disjoint (localMask g i A) (interface g i) then
      rawJoin (deleted g i A B) (delta (localResidual g i A B \ interface g i)) else ⊥)

/-- Literal original-mask last-wheel factorization for every geometric input,
every width >=3, and every retained old/interior port. No factor/output/collapse
identity is an input. In a MixedHistory.attach old i, every displayed prior
corner is on the graph of old, hence at the strictly earlier history rank. -/
theorem physicalWheelStep_factorization (A B : Finset V)
    (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B) :
    Readback g i A B := by
  classical
  have hXY : Disjoint (oldGround g i) (wheelGround g i) :=
    i.fresh.mono_left (Finset.erase_subset _ _)
  have hAX : oldMask g i A ⊆ g.ground :=
    Finset.inter_subset_right.trans (Finset.erase_subset _ _)
  have hBX : oldMask g i B ⊆ g.ground :=
    Finset.inter_subset_right.trans (Finset.erase_subset _ _)
  have heA : i.e ∉ oldMask g i A := fun h =>
    Finset.notMem_erase _ _ (Finset.mem_inter.mp h).2
  have heB : i.e ∉ oldMask g i B := fun h =>
    Finset.notMem_erase _ _ (Finset.mem_inter.mp h).2
  have hab : Disjoint (oldMask g i A) (oldMask g i B) :=
    hAB.mono Finset.inter_subset_left Finset.inter_subset_left
  have hread := prior_readbacks g i A B
  have hrow : ∀ c : (projectedRimRows g i A B).chords,
      (projectedRimRows g i A B).row c =
        ((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image
          i.labels) \ localMask g i B := by
    intro c
    change (PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1 \
      localMask g i B = _
    exact congrArg (fun q : Finset V => q \ localMask g i B)
      (PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels c.1.1)
  have hground : (projectedRimRows g i A B).ground = localResidual g i A B := rfl
  refine {
    ground := ?_
    disjoint := hXY.mono Finset.sdiff_subset Finset.sdiff_subset
    masks_split := ?_
    current_port_absent := fun h => (physicalWheelStep_ground g i).2
      (Finset.mem_sdiff.mp h).1
    interface_eq := ?_
    prior_ground := prior_ground g i A B
    factor_grounds := ?_
    prior_masks := ⟨hAX,hBX,hab⟩
    deleted_masks := ⟨hAX,Finset.union_subset hBX (by simpa using i.retained),?_⟩
    linked_masks := ⟨Finset.union_subset hAX (by simpa using i.retained),hBX,?_⟩
    deleted_readback := hread.1
    linked_readback := hread.2
    row_ground := rfl
    row := hrow
    face := ?_
    no_rows := ?_
    raw_empty := ?_
    zero_ground := ?_
    empty_row := ?_
    singleton_row := ?_
    absent_marker := ?_
    no_markers := ?_
    one_marker := ?_
    factorization := ?_ }
  · exact residual_union (oldGround g i) (wheelGround g i) A B
  · have splitMask : ∀ M : Finset V,
        M ⊆ (physicalWheelStep g i).data.ground →
          M = oldMask g i M ∪ localMask g i M := by
      intro M hM
      ext x
      change x ∈ M ↔ x ∈ (M ∩ oldGround g i) ∪ (M ∩ wheelGround g i)
      simp only [Finset.mem_inter,Finset.mem_union]
      exact ⟨fun hx => (Finset.mem_union.mp (hM hx)).elim
        (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩),by tauto⟩
    exact ⟨splitMask A hA,splitMask B hB⟩
  · simp only [interface,AllMWheel.rim,Finset.image_insert,Finset.image_singleton]
  · constructor <;> ext x <;>
      simp only [HistoryCorners.residual,oldResidual,oldGround,Finset.mem_sdiff,
        Finset.mem_union,Finset.mem_singleton,Finset.mem_erase] <;> tauto
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.disjoint_left.mp hab hx hy
    · have he : x = i.e := Finset.mem_singleton.mp hy
      exact heA (he ▸ hx)
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.disjoint_left.mp hab hx hy
    · have he : x = i.e := Finset.mem_singleton.mp hx
      exact heB (he ▸ hy)
  · intro s
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c.1.1,c.1.2,?_,?_⟩
      · have hdis := c.2
        change Disjoint
          ((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1)
          (localMask g i A) at hdis
        exact (PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels c.1.1) ▸ hdis
      · simpa only [hrow, hground] using hc
    · rintro ⟨d,hd,hdis,hs⟩
      have hdis' : Disjoint ((localRows g i).row ⟨d,hd⟩) (localMask g i A) := by
        change Disjoint
          ((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row d)
          (localMask g i A)
        exact (PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels d).symm ▸ hdis
      refine ⟨⟨⟨d,hd⟩,hdis'⟩,?_⟩
      simpa only [hrow, hground] using hs
  · intro hempty
    apply SetLike.ext
    intro s
    change (∃ c : (projectedRimRows g i A B).chords,
      s ⊆ (projectedRimRows g i A B).ground \ (projectedRimRows g i A B).row c) ↔ False
    exact ⟨fun ⟨c,_⟩ => hempty.false c,False.elim⟩
  · constructor
    · rintro ⟨c,_⟩
      exact ⟨c⟩
    · rintro ⟨c⟩
      exact ⟨c,Finset.empty_subset _⟩
  · intro hzero
    by_cases hn : Nonempty (projectedRimRows g i A B).chords
    · right
      obtain ⟨c⟩ := hn
      apply SetLike.ext
      intro s
      constructor
      · rintro ⟨d,hd⟩
        exact hzero ▸ (hd.trans Finset.sdiff_subset)
      · intro hs
        have hs0 : s = ∅ := Finset.subset_empty.mp hs
        subst s
        exact ⟨c,Finset.empty_subset _⟩
    · left
      apply SetLike.ext
      intro s
      change (∃ c : (projectedRimRows g i A B).chords,
        s ⊆ (projectedRimRows g i A B).ground \ (projectedRimRows g i A B).row c) ↔ False
      exact ⟨fun ⟨c,_⟩ => hn ⟨c⟩,False.elim⟩
  · intro c hc
    apply SetLike.ext
    intro s
    constructor
    · rintro ⟨d,hd⟩
      exact hd.trans Finset.sdiff_subset
    · intro hs
      refine ⟨c,?_⟩
      simpa only [hc,Finset.sdiff_empty,hground] using hs
  · intro c a hc
    have ha : a ∈ (projectedRimRows g i A B).ground :=
      (projectedRimRows g i A B).row_supported c (hc.symm ▸ Finset.mem_singleton_self a)
    exact singleton_cap (projectedRimRows g i A B) a ha c hc
  · ext x
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  · intro hd
    ext x
    simp only [Finset.mem_sdiff]
    exact ⟨And.left,fun hx => ⟨hx,fun hr => Finset.disjoint_left.mp hd hx hr⟩⟩
  · intro r hr
    ext x
    have hh : x ∈ interface g i ∩ localResidual g i A B ↔ x = r := by
      rw [hr,Finset.mem_singleton]
    simp only [Finset.mem_inter] at hh
    simp only [Finset.mem_sdiff,Finset.mem_erase]
    tauto
  · have hD : Supported (oldGround g i) (restrict (oldGround g i) g.rows.root) :=
      fun _ hs => hs.2
    have hL : Supported (oldGround g i) (rawLink (oldGround g i) i.e g.rows.root) :=
      fun _ hs => hs.1
    have hE : Supported (wheelGround g i) (localRows g i).root :=
      (localRows g i).root_supported
    have hroot : (physicalWheelStep g i).data.rows.root =
        phi (oldGround g i) (wheelGround g i) (wheelGround g i \ interface g i)
          (restrict (oldGround g i) g.rows.root)
          (rawLink (oldGround g i) i.e g.rows.root) (localRows g i).root := by
      rw [physicalWheelStep_root]
      rw [← PhysicalMWheel.ambient_without]
      have hz : (AllMWheel.tailGround i.width i.atLeastThree).image i.labels =
          wheelGround g i \ interface g i := by
        exact Finset.image_sdiff _ _ i.labels.injective
      rw [hz]
      rfl
    have hc := corner_phi (oldGround g i) (wheelGround g i) (interface g i)
      A B (restrict (oldGround g i) g.rows.root)
      (rawLink (oldGround g i) i.e g.rows.root) (localRows g i).root hXY hD hL hE hA
    have hd : corner (oldGround g i) (oldMask g i A) (oldMask g i B)
        (restrict (oldGround g i) g.rows.root) = deleted g i A B := by
      rw [hread.1]
      apply SetLike.ext
      intro s
      change (s ⊆ oldResidual g i A B ∧
        (s ∪ oldMask g i A ∈ g.rows.root ∧ s ∪ oldMask g i A ⊆ oldGround g i)) ↔
          ((s ⊆ HistoryCorners.residual g.ground (oldMask g i A) (oldMask g i B) ∧
            s ∪ oldMask g i A ∈ g.rows.root) ∧ s ⊆ oldResidual g i A B)
      constructor
      · rintro ⟨hs,hk,_⟩
        exact ⟨⟨fun x hx => by
          obtain ⟨hxX,hn⟩ := Finset.mem_sdiff.mp (hs hx)
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hxX,hn⟩,hk⟩,hs⟩
      · rintro ⟨⟨_,hk⟩,hs⟩
        exact ⟨hs,hk,Finset.union_subset (hs.trans Finset.sdiff_subset)
          Finset.inter_subset_right⟩
    have hl : corner (oldGround g i) (oldMask g i A) (oldMask g i B)
        (rawLink (oldGround g i) i.e g.rows.root) = linked g i A B := by
      rw [hread.2]
      apply SetLike.ext
      intro s
      change (s ⊆ oldResidual g i A B ∧ s ∪ oldMask g i A ⊆ oldGround g i ∧
        insert i.e (s ∪ oldMask g i A) ∈ g.rows.root) ↔
          (s ⊆ oldResidual g i A B ∧
            insert i.e s ⊆ HistoryCorners.residual g.ground (oldMask g i A) (oldMask g i B) ∧
              insert i.e s ∪ oldMask g i A ∈ g.rows.root)
      have hu : insert i.e (s ∪ oldMask g i A) = insert i.e s ∪ oldMask g i A := by
        ext x; simp only [Finset.mem_insert,Finset.mem_union]; tauto
      rw [hu,prior_ground g i A B]
      constructor
      · rintro ⟨hs,_,hk⟩
        exact ⟨hs,Finset.insert_subset_insert i.e hs,hk⟩
      · rintro ⟨hs,_,hk⟩
        exact ⟨hs,Finset.union_subset (hs.trans Finset.sdiff_subset)
          Finset.inter_subset_right,hk⟩
    have he : corner (wheelGround g i) (localMask g i A) (localMask g i B)
        (localRows g i).root = (projectedRimRows g i A B).root :=
      corner_root (localRows g i) (localMask g i A) (localMask g i B)
        Finset.inter_subset_right
    rw [hroot]
    change corner (oldGround g i ∪ wheelGround g i) A B _ = _
    rw [hc]
    change (rawJoin (delta (oldResidual g i A B))
      (corner (wheelGround g i) (localMask g i A) (localMask g i B) (localRows g i).root) ⊔
        rawJoin (corner (oldGround g i) (oldMask g i A) (oldMask g i B)
          (rawLink (oldGround g i) i.e g.rows.root)) (delta (localResidual g i A B))) ⊔
      (if Disjoint (localMask g i A) (interface g i) then
        rawJoin (corner (oldGround g i) (oldMask g i A) (oldMask g i B)
          (restrict (oldGround g i) g.rows.root))
            (delta (localResidual g i A B \ interface g i)) else ⊥) = _
    rw [hd,hl,he]

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryFactors
