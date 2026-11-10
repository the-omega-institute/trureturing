/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryRecursion
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryRecursion
   mirror-E: none(waiver:original-mask-history-recursion)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]
   utility: none
   digest: Original-mask usable physical leaves, decreasing local solver and mixed-history recursion. -/

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryFactors
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryPhysicalSteps
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact
import D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed

/-! These are actual proof bodies for the physical induction. The local solver
recurses on the complete remaining local ground, and allCornersOutput supplies
its external old-corner input by genuine MixedHistory induction.
The only external physical recursive supplier is on the graph of the OLD history.
The local reduction lemmas consume only the explicitly displayed smaller corner.
All grounds are full original residual grounds; rows keep their original indices.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion
open OriginalLabelTwoSum HistoryCorners HistoryLeafCap PhysicalHistory

attribute [local instance] historyRecursionPropDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]


open private D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion.groundOutput D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion.corner_supported from D5.S3.Geometry.OriginalLabelTwoSum.HistoryLocalLeaves

open private D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion.projectedRimIndexEquiv D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion.projectedRim_ground_image D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion.priorOutput D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion.linkedOutput from D5.S3.Geometry.OriginalLabelTwoSum.HistoryPhysicalSteps

section EarlierHistory
variable {n : Nat} {G : Type} {g : GraphData G V}

private theorem groundOutput_mainPairsOf {W U : Finset V} {K : Family V}
    (h : W = U) (o : Output W K) :
    HistoryIntact.mainPairsOf (groundOutput h o) = HistoryIntact.mainPairsOf o := by
  subst U
  rfl

private theorem groundOutput_corePairsOf {W U : Finset V} {K : Family V}
    (h : W = U) (o : Output W K) :
    HistoryIntact.corePairsOf (groundOutput h o) = HistoryIntact.corePairsOf o := by
  subst U
  rfl

section IntactOriginalLists
open AllMWheel HistoryIntact HistoryIntactProduct HistoryIsolated HistoryCycles
open private zeroFilling from D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactTwo
open private goodOneFilling from D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact

/-- Literal main list at the actual physical intact terminal.
The residue-zero expansion consumes the completed ORIGINAL marker readback. -/
theorem stepIntactOutput_main_faces (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hLA : HistoryFactors.localMask g i A = ∅)
    (hLB : HistoryFactors.localMask g i B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root))
    (hX : (HistoryFactors.oldResidual g i A B).Nonempty) :
    let X := HistoryFactors.oldResidual g i A B
    let J := HistoryFactors.prior g i A B
    let oJ := priorOutput h i A B hA hB hAB old
    let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
    let oL := changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback
    mainPairsOf (stepIntactOutput h i A B hA hB hAB hLA hLB old) =
      if h0 : i.width % 3 = 0 then
        (zeroOneSequence i.width i.atLeastThree h0 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X i.e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (zeroZeroSequence i.width i.atLeastThree h0 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oJ).map (fun p =>
          ((eta0 i.width i.atLeastThree).image i.labels ∪ p.1.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))),
           (eta0 i.width i.atLeastThree).image i.labels ∪ p.2.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))))) ++
        (mainPairsOf oL).map (fun p =>
          (zeroOtherTop i.width i.atLeastThree i.labels ∪ p.1, zeroOtherTop i.width i.atLeastThree i.labels ∪ p.2))
      else if h2 : i.width % 3 = 2 then
        (twoZeroSequence i.width i.atLeastThree h2 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J ∧ a ∉ rawLink X i.e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (twoPathSequence i.width i.atLeastThree h2 i.labels).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X i.e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oL).map (fun p => (twoPathTop i.width i.atLeastThree i.labels ∪ p.1, twoPathTop i.width i.atLeastThree i.labels ∪ p.2))
      else match oJ with
        | .void _ => []
        | .unit _ => (fill0 i.width i.atLeastThree).main.pairs.map
            (fun P => (P.lower.image i.labels, P.upper.image i.labels))
        | .strong c =>
            (mainPairsOf oJ).flatMap (fun p =>
              replayFacePairs ((ground i.width).image i.labels) ((tailGround i.width i.atLeastThree).image i.labels) i.e
                (renameFamily i.labels (pathRoot i.width i.atLeastThree)) p
                (rightGammaPairs ((ground i.width).image i.labels) (renameFamily i.labels (pathRoot i.width i.atLeastThree)))) ++
            (fibres c.critical).flatMap (fun q =>
              (selectFilling i.e (zeroFilling i.width i.atLeastThree i.labels) (goodOneFilling i.width i.atLeastThree i.labels) q).main.pairs.map
                (fun P => (criticalPart i.e q ∪ P.lower, criticalPart i.e q ∪ P.upper))) := by
  classical
  dsimp only
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have hXY : Disjoint X ((ground i.width).image i.labels) :=
    i.fresh.mono (Finset.sdiff_subset.trans (Finset.erase_subset _ _)) le_rfl
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  simp only [stepIntactOutput, dif_pos hX,
    HistoryIntact.changeOutput_mainPairsOf, groundOutput_mainPairsOf]
  have hf := HistoryIntact.intactOutput_main_faces i.width i.atLeastThree X i.e J i.labels
    i.zero heX hX hXY hJ (priorOutput h i A B hA hB hAB old)
    (changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback)
  simp only [HistoryIntact.changeOutput_mainPairsOf, X, J] at hf
  convert hf using 1
  split_ifs <;> congr 12
  all_goals first
    | (cases priorOutput h i A B hA hB hAB old <;> rfl)
    | (cases changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback <;> rfl)

/-- Literal core list at the actual physical intact terminal.
The residue-zero expansion consumes the completed ORIGINAL marker readback. -/
theorem stepIntactOutput_core_faces (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hLA : HistoryFactors.localMask g i A = ∅)
    (hLB : HistoryFactors.localMask g i B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root))
    (hX : (HistoryFactors.oldResidual g i A B).Nonempty) :
    let X := HistoryFactors.oldResidual g i A B
    let J := HistoryFactors.prior g i A B
    let oJ := priorOutput h i A B hA hB hAB old
    let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
    let oL := changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback
    let Y := (ground i.width).image i.labels
    let E := renameFamily i.labels (pathRoot i.width i.atLeastThree)
    let cone := (fibres (((X ∪ Y).erase hX.choose).powerset.filter
      (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) E))).map
      (fun s => (s, insert hX.choose s))
    corePairsOf (stepIntactOutput h i A B hA hB hAB hLA hLB old) =
      if h0 : i.width % 3 = 0 then
        (corePairsOf oJ).map (fun p =>
          ((eta0 i.width i.atLeastThree).image i.labels ∪ p.1.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))),
           (eta0 i.width i.atLeastThree).image i.labels ∪ p.2.image (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree))))) ++
        (match oJ with
          | .void _ => []
          | .unit _ => []
          | .strong c => [((eta0 i.width i.atLeastThree).image i.labels,
              insert (HistoryMarkers.markerMap i.e (i.labels (firstLabel i.width i.atLeastThree)) c.vertex) ((eta0 i.width i.atLeastThree).image i.labels))]) ++
        (corePairsOf oL).map (fun p => (zeroOtherTop i.width i.atLeastThree i.labels ∪ p.1, zeroOtherTop i.width i.atLeastThree i.labels ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(zeroOtherTop i.width i.atLeastThree i.labels, insert c.vertex (zeroOtherTop i.width i.atLeastThree i.labels))]) ++ cone
      else if h2 : i.width % 3 = 2 then
        (corePairsOf oL).map (fun p => (twoPathTop i.width i.atLeastThree i.labels ∪ p.1, twoPathTop i.width i.atLeastThree i.labels ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(twoPathTop i.width i.atLeastThree i.labels, insert c.vertex (twoPathTop i.width i.atLeastThree i.labels))]) ++ cone
      else match oJ with
        | .void _ => cone
        | .unit _ => cone
        | .strong c =>
            (fibres c.critical).flatMap (fun q =>
              (selectFilling i.e (zeroFilling i.width i.atLeastThree i.labels) (goodOneFilling i.width i.atLeastThree i.labels) q).separate.pairs.map
                (fun P => (criticalPart i.e q ∪ P.lower, criticalPart i.e q ∪ P.upper))) ++
            (corePairsOf oJ).flatMap (fun p =>
              replayFacePairs Y ((tailGround i.width i.atLeastThree).image i.labels) i.e E p (rightGammaPairs Y E)) ++
            finishFacePairs X Y ((tailGround i.width i.atLeastThree).image i.labels) ((rim i.width i.atLeastThree).image i.labels)
              i.e c.vertex E (Finset.image_nonempty.mpr ⟨firstLabel i.width i.atLeastThree, by simp [rim]⟩)
              (rightGammaPairs Y E) := by
  classical
  dsimp only
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have hXY : Disjoint X ((ground i.width).image i.labels) :=
    i.fresh.mono (Finset.sdiff_subset.trans (Finset.erase_subset _ _)) le_rfl
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  simp only [stepIntactOutput, dif_pos hX,
    HistoryIntact.changeOutput_corePairsOf, groundOutput_corePairsOf]
  have hf := HistoryIntact.intactOutput_core_faces i.width i.atLeastThree X i.e J i.labels
    i.zero heX hX hXY hJ (priorOutput h i A B hA hB hAB old)
    (changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback)
  simp only [HistoryIntact.changeOutput_corePairsOf, X, J] at hf
  convert hf using 1
  split_ifs <;> congr 12
  all_goals first
    | (cases priorOutput h i A B hA hB hAB old <;> rfl)
    | (cases changeOutput (linkedOutput h i A B hA hB hAB old) r.linked_readback <;> rfl)

end IntactOriginalLists

private theorem local_subset_current (i : WheelInput g) (A B : Finset V) :
    HistoryFactors.localResidual g i A B ⊆
      HistoryCorners.residual (physicalWheelStep g i).data.ground A B := by
  intro x hx
  change x ∈ HistoryCorners.residual (g.ground.erase i.e ∪ HistoryFactors.wheelGround g i) A B
  simp only [HistoryFactors.localResidual,HistoryFactors.localMask,HistoryCorners.residual,
    Finset.mem_sdiff,Finset.mem_union,Finset.mem_inter] at hx ⊢
  tauto

private def stepSingletonFrom (i : WheelInput g) (A B : Finset V)
    (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (a : V) (ha : a ∈ HistoryFactors.localResidual g i A B)
    (d : (cornerRows (wheelStepRows g i) A B).chords)
    (hd : (cornerRows (wheelStepRows g i) A B).row d = {a})
    (small : Output (HistoryCorners.residual (physicalWheelStep g i).data.ground (A ∪ {a}) B)
      (corner (physicalWheelStep g i).data.ground (A ∪ {a}) B
        (physicalWheelStep g i).data.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let W := (physicalWheelStep g i).data.ground
  have hg : HistoryCorners.residual W (A ∪ {a}) B = (HistoryCorners.residual W A B).erase a := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,Finset.mem_erase]
    tauto
  have hr := physicalWheelStep_rowRoot g i
  have small' := changeOutput (groundOutput hg small)
    (congrArg (corner W (A ∪ {a}) B) hr)
  have out := singletonCornerOutput (wheelStepRows g i) A B hA a
    (local_subset_current i A B ha) d hd small'
  exact changeOutput out (congrArg (corner W A B) hr).symm

private def stepOneLeafFrom (i : WheelInput g) (A B : Finset V)
    (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (a b : V) (ha : a ∈ HistoryFactors.localResidual g i A B)
    (hb : b ∈ HistoryFactors.localResidual g i A B) (hab : a ≠ b)
    (d : (cornerRows (wheelStepRows g i) A B).chords)
    (hd : (cornerRows (wheelStepRows g i) A B).row d = {a,b})
    (leaf : ∀ c : (cornerRows (wheelStepRows g i) A B).chords,
      a ∈ (cornerRows (wheelStepRows g i) A B).row c →
        (cornerRows (wheelStepRows g i) A B).row c = {a,b})
    (small : Output (HistoryCorners.residual (physicalWheelStep g i).data.ground (A ∪ {a}) (B ∪ {b}))
      (corner (physicalWheelStep g i).data.ground (A ∪ {a}) (B ∪ {b})
        (physicalWheelStep g i).data.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let W := (physicalWheelStep g i).data.ground
  have ha' := local_subset_current i A B ha
  have hb' := local_subset_current i A B hb
  have hg : HistoryCorners.residual W (A ∪ {a}) (B ∪ {b}) = ((HistoryCorners.residual W A B).erase a).erase b := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,Finset.mem_erase]
    tauto
  have hr := physicalWheelStep_rowRoot g i
  have he : corner (HistoryCorners.residual W A B) {a} {b} (cornerRows (wheelStepRows g i) A B).root =
      corner W (A ∪ {a}) (B ∪ {b}) (wheelStepRows g i).root := by
    rw [← corner_root (wheelStepRows g i) A B hA]
    exact corner_compose W A B {a} {b} _ (Finset.singleton_subset_iff.mpr ha')
  have small' := changeOutput (groundOutput hg small)
    ((congrArg (corner W (A ∪ {a}) (B ∪ {b})) hr).trans he.symm)
  have out := oneLeafRowsOutput (cornerRows (wheelStepRows g i) A B) a b
    ha' hb' hab d hd leaf small'
  exact changeOutput out ((corner_root (wheelStepRows g i) A B hA).symm.trans
    (congrArg (corner W A B) hr).symm)

private def stepTwoLeafFrom (i : WheelInput g) (A B : Finset V)
    (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (a b c : V) (ha : a ∈ HistoryFactors.localResidual g i A B)
    (hb : b ∈ HistoryFactors.localResidual g i A B)
    (hc : c ∈ HistoryFactors.localResidual g i A B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (dab dbc : (cornerRows (wheelStepRows g i) A B).chords)
    (habrow : (cornerRows (wheelStepRows g i) A B).row dab = {a,b})
    (hbcrow : (cornerRows (wheelStepRows g i) A B).row dbc = {b,c})
    (leafa : ∀ d : (cornerRows (wheelStepRows g i) A B).chords,
      a ∈ (cornerRows (wheelStepRows g i) A B).row d →
        (cornerRows (wheelStepRows g i) A B).row d = {a,b})
    (leafb : ∀ d : (cornerRows (wheelStepRows g i) A B).chords,
      b ∈ (cornerRows (wheelStepRows g i) A B).row d →
        (cornerRows (wheelStepRows g i) A B).row d = {a,b} ∨
          (cornerRows (wheelStepRows g i) A B).row d = {b,c})
    (small : Output (HistoryCorners.residual (physicalWheelStep g i).data.ground (A ∪ {a,b,c}) B)
      (corner (physicalWheelStep g i).data.ground (A ∪ {a,b,c}) B
        (physicalWheelStep g i).data.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let W := (physicalWheelStep g i).data.ground
  have ha' := local_subset_current i A B ha
  have hb' := local_subset_current i A B hb
  have hc' := local_subset_current i A B hc
  have hg : HistoryCorners.residual W (A ∪ {a,b,c}) B =
      (((HistoryCorners.residual W A B).erase a).erase b).erase c := by
    ext x
    simp only [HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.mem_erase]
    tauto
  have hr := physicalWheelStep_rowRoot g i
  have he : corner (HistoryCorners.residual W A B) {a,b,c} ∅ (cornerRows (wheelStepRows g i) A B).root =
      corner W (A ∪ {a,b,c}) B (wheelStepRows g i).root := by
    rw [← corner_root (wheelStepRows g i) A B hA]
    change corner (HistoryCorners.residual W A B) {a,b,c} ∅
      (corner W A B (wheelStepRows g i).root) = _
    simpa only [Finset.union_empty] using
      corner_compose W A B {a,b,c} ∅ (wheelStepRows g i).root (by
        intro x hx
        rcases (show x = a ∨ x = b ∨ x = c by simpa using hx) with rfl | rfl | rfl
        · exact ha'
        · exact hb'
        · exact hc')
  have small' := changeOutput (groundOutput hg small)
    ((congrArg (corner W (A ∪ {a,b,c}) B) hr).trans he.symm)
  have out := twoLeafRowsOutput (cornerRows (wheelStepRows g i) A B) a b c
    ha' hb' hc' hab hac hbc dab dbc habrow hbcrow leafa leafb small'
  exact changeOutput out ((corner_root (wheelStepRows g i) A B hA).symm.trans
    (congrArg (corner W A B) hr).symm)

private theorem subset_pair_cases (W : Finset V) (p q : V) (hW : W ⊆ {p,q}) :
    W = ∅ ∨ W = {p} ∨ W = {q} ∨ W = {p,q} := by
  classical
  by_cases hp : p ∈ W <;> by_cases hq : q ∈ W
  · exact Or.inr (Or.inr (Or.inr (Finset.Subset.antisymm hW (by
      intro x hx
      rcases (show x = p ∨ x = q by simpa using hx) with he | he
      · exact he.symm ▸ hp
      · exact he.symm ▸ hq))))
  · apply Or.inr
    apply Or.inl
    ext x
    constructor
    · intro hx
      rcases (show x = p ∨ x = q by simpa using hW hx) with he | he
      · exact Finset.mem_singleton.mpr he
      · exact (hq (he ▸ hx)).elim
    · intro hx
      exact (Finset.mem_singleton.mp hx).symm ▸ hp
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    ext x
    constructor
    · intro hx
      rcases (show x = p ∨ x = q by simpa using hW hx) with he | he
      · exact (hp (he ▸ hx)).elim
      · simpa only [Finset.mem_singleton] using he
    · intro hx
      exact (Finset.mem_singleton.mp hx).symm ▸ hq
  · apply Or.inl
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases (show x = p ∨ x = q by simpa using hW hx) with he | he
    · exact hp (he ▸ hx)
    · exact hq (he ▸ hx)

/-- Total no-local-row terminal, including all retained marker and ghost states.
The only old outputs selected here are exact supported/disjoint corners on g. -/
def stepNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  by_cases hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i)
  · by_cases hmark : Disjoint (HistoryFactors.localResidual g i A B) (HistoryFactors.interface g i)
    · exact stepNoMarkersNoRowsOutput h i A B hA hB hAB hrows hR hmark old
    · by_cases hunused : (HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i).Nonempty
      · let a := hunused.choose
        have ha := hunused.choose_spec
        exact stepUnusedLocalOutput h i A B hA hB hAB a ha
          (fun d => (hrows.false d).elim)
      · have hsub : HistoryFactors.localResidual g i A B ⊆ HistoryFactors.interface g i := by
          intro x hx
          by_contra hn
          exact hunused ⟨x,Finset.mem_sdiff.mpr ⟨hx,hn⟩⟩
        let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
        rw [r.interface_eq] at hsub
        by_cases hz : HistoryFactors.localResidual g i A B = ∅
        · exact stepZeroLocalOutput h i A B hA hB hAB hz old
        by_cases hp : HistoryFactors.localResidual g i A B =
            {i.labels (AllMWheel.firstLabel i.width i.atLeastThree)}
        · exact stepSingleMarkerNoRowsOutput h i A B hA hB hAB hrows hR _
            (by rw [r.interface_eq]; simp) hp old
        by_cases hq : HistoryFactors.localResidual g i A B =
            {i.labels (AllMWheel.secondLabel i.width i.atLeastThree)}
        · exact stepSingleMarkerNoRowsOutput h i A B hA hB hAB hrows hR _
            (by rw [r.interface_eq]; simp) hq old
        have hpq : HistoryFactors.localResidual g i A B =
            {i.labels (AllMWheel.firstLabel i.width i.atLeastThree),
              i.labels (AllMWheel.secondLabel i.width i.atLeastThree)} :=
          (((subset_pair_cases _ _ _ hsub).resolve_left hz).resolve_left hp).resolve_left hq
        have hpq' : i.labels (AllMWheel.firstLabel i.width i.atLeastThree) ≠
            i.labels (AllMWheel.secondLabel i.width i.atLeastThree) := by
          intro he
          have hh := congrArg Fin.val (i.labels.injective he)
          change 1 = 2 at hh
          omega
        exact stepTwinMarkersNoRowsOutput h i A B hA hB hAB hrows hR _ _ hpq'
          (by rw [r.interface_eq]; simp) (by rw [r.interface_eq]; simp) hpq old
  · exact stepAbsorbedNoRowsOutput h i A B hA hB hAB hrows hR old

private theorem residual_singleton_erase (W : Finset V) (a : V) :
    HistoryCorners.residual W {a} ∅ = W.erase a := by
  ext x
  simp only [HistoryCorners.residual, Finset.union_empty, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_erase]
  tauto

private theorem residual_pair_erase (W : Finset V) (a b : V) :
    HistoryCorners.residual W {a} {b} = (W.erase a).erase b := by
  ext x
  simp only [HistoryCorners.residual, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_erase]
  tauto

set_option maxHeartbeats 2000000 in
/-- The total physical local solver. Recursive calls at the CURRENT history
rank use only the exact original masks proved below and strictly decrease the
cardinality of the ACTUAL remaining local ground. The external supplier ranges
only over corners of the strictly earlier graph g. -/
def stepOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  have parent := step_parent_readback h i A B hA hB hAB
  let C := Classical.choose parent
  have parentC := Classical.choose_spec parent
  let D := Classical.choose parentC
  have parentD := Classical.choose_spec parentC
  have hC := Classical.choose parentD
  have parentHC := Classical.choose_spec parentD
  have hD := Classical.choose parentHC
  have parentHD := Classical.choose_spec parentHC
  have hCD := parentHD.1
  have hCi := parentHD.2.1
  have hDi := parentHD.2.2.1
  let s := Classical.choose parentHD.2.2.2
  have hparent := Classical.choose_spec parentHD.2.2.2
  cases hs : s.rowState with
  | simplex c hc =>
      let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
      have hg := projectedRim_ground_image g i A B C D hCi hDi
      have hground : HistoryCorners.residual (physicalWheelStep g i).data.ground A B =
          HistoryFactors.oldResidual g i A B ∪
            (HistoryForests.localRows i.width i.atLeastThree C D).ground.image i.labels :=
        r.ground.trans (congrArg (fun Y => HistoryFactors.oldResidual g i A B ∪ Y) hg)
      have he : corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root =
          delta (HistoryCorners.residual (physicalWheelStep g i).data.ground A B) := by
        rw [hparent,hs]
        change delta (HistoryFactors.oldResidual g i A B ∪
          (HistoryForests.localRows i.width i.atLeastThree C D).ground.image i.labels) = _
        rw [← hground]
      exact changeOutput (HistoryIsolated.simplexOutput _) he.symm
  | void hi =>
      let e := projectedRimIndexEquiv g i A B C D hCi
      exact stepNoRowsOutput h i A B hA hB hAB ⟨fun d => hi.false (e d)⟩ old
  | forest hi hzero =>
      by_cases hV : HistoryFactors.localResidual g i A B = ∅
      · exact stepZeroLocalOutput h i A B hA hB hAB hV old
      · by_cases h0 : ∃ d : (HistoryFactors.projectedRimRows g i A B).chords,
            (HistoryFactors.projectedRimRows g i A B).row d = ∅
        · let d := Classical.choose h0
          have hd := Classical.choose_spec h0
          exact stepEmptyRowOutput h i A B hA hB hAB d hd
        · by_cases h1 : ∃ (d : (HistoryFactors.projectedRimRows g i A B).chords) (a : V),
              (HistoryFactors.projectedRimRows g i A B).row d = {a}
          · let d := Classical.choose h1
            have singleton := Classical.choose_spec h1
            let a := Classical.choose singleton
            have hd := Classical.choose_spec singleton
            have ha : a ∈ HistoryFactors.localResidual g i A B :=
              (HistoryFactors.projectedRimRows g i A B).row_supported d (hd.symm ▸ (by simp only [a, Finset.mem_singleton]))
            have ha' := local_subset_current i A B ha
            have indexed := physical_rim_indexed g i A B d
            let q := Classical.choose indexed
            have hq := Classical.choose_spec indexed
            have hm := next_masks (physicalWheelStep g i).data.ground A B {a} ∅ hA hB hAB
              (Finset.singleton_subset_iff.mpr ha') (Finset.empty_subset _) (by simp)
            have hdis : Disjoint (A ∪ {a}) B := by simpa only [Finset.union_empty] using hm.2.2
            have hdec : (HistoryFactors.localResidual g i (A ∪ {a}) B).card <
                (HistoryFactors.localResidual g i A B).card := by
              have he := localResidual_update i A B {a} ∅
              simp only [Finset.union_empty] at he
              rw [he, residual_singleton_erase]
              exact Finset.card_erase_lt_of_mem ha
            exact stepSingletonFrom i A B hA a ha q (hq.trans hd)
              (stepOutput h i (A ∪ {a}) B hm.1 hB hdis old)
          · have hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
                ((HistoryFactors.projectedRimRows g i A B).row d).card = 2 := by
              intro d
              rcases physical_projected_row_cases g i A B d with he | ⟨a,he⟩ | he
              · exact (h0 ⟨d,he⟩).elim
              · exact (h1 ⟨d,a,he⟩).elim
              · exact he
            by_cases hsome : Nonempty (HistoryFactors.projectedRimRows g i A B).chords
            · by_cases hcut : HistoryFactors.localMask g i A ≠ ∅ ∨ HistoryFactors.localMask g i B ≠ ∅
              · have leafExists :=
                  physical_unmarked_leaf g i A B hA hB hAB hcut hrows hsome
                let a := Classical.choose leafExists
                have aleaf := Classical.choose_spec leafExists
                have ha := aleaf.1
                let b := Classical.choose aleaf.2
                have bleaf := Classical.choose_spec aleaf.2
                have hb := bleaf.1
                have hab := bleaf.2.1
                let d := Classical.choose bleaf.2.2
                have dleaf := Classical.choose_spec bleaf.2.2
                have hd := dleaf.1
                have leaf := dleaf.2
                have haV := (Finset.mem_sdiff.mp ha).1
                have ha' := local_subset_current i A B haV
                have hb' := local_subset_current i A B hb
                have cases :
                    (b ∈ HistoryFactors.interface g i ∨
                      ∀ q : (cornerRows (wheelStepRows g i) A B).chords,
                        b ∈ (cornerRows (wheelStepRows g i) A B).row q →
                          (cornerRows (wheelStepRows g i) A B).row q = {a,b}) ∨
                    ∃ c ∈ HistoryFactors.localResidual g i A B, a ≠ c ∧ b ≠ c ∧
                      ∃ dbc : (cornerRows (wheelStepRows g i) A B).chords,
                        (cornerRows (wheelStepRows g i) A B).row dbc = {b,c} ∧
                        ∀ q : (cornerRows (wheelStepRows g i) A B).chords,
                          b ∈ (cornerRows (wheelStepRows g i) A B).row q →
                            (cornerRows (wheelStepRows g i) A B).row q = {a,b} ∨
                              (cornerRows (wheelStepRows g i) A B).row q = {b,c} := by
                  by_cases hbR : b ∈ HistoryFactors.interface g i
                  · exact Or.inl (Or.inl hbR)
                  · rcases physical_neighbour_cases g i A B hrows a b hab
                      (Finset.mem_sdiff.mpr ⟨hb,hbR⟩) d hd with only | second
                    · exact Or.inl (Or.inr only)
                    · exact Or.inr second
                by_cases one :
                    b ∈ HistoryFactors.interface g i ∨
                      ∀ q : (cornerRows (wheelStepRows g i) A B).chords,
                        b ∈ (cornerRows (wheelStepRows g i) A B).row q →
                          (cornerRows (wheelStepRows g i) A B).row q = {a,b}
                · have hm := next_masks (physicalWheelStep g i).data.ground A B {a} {b}
                    hA hB hAB (Finset.singleton_subset_iff.mpr ha')
                    (Finset.singleton_subset_iff.mpr hb') (by simpa only [Finset.disjoint_singleton] using (show a ≠ b from hab))
                  have hdec : (HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b})).card <
                      (HistoryFactors.localResidual g i A B).card := by
                    rw [localResidual_update]
                    rw [residual_pair_erase]
                    exact lt_of_le_of_lt
                      (Finset.card_le_card (Finset.erase_subset _ _))
                      (Finset.card_erase_lt_of_mem
                        (show a ∈ HistoryFactors.localResidual g i A B from haV))
                  exact stepOneLeafFrom i A B hA a b haV hb hab d hd leaf
                    (stepOutput h i (A ∪ {a}) (B ∪ {b}) hm.1 hm.2.1 hm.2.2 old)
                · have second := cases.resolve_left one
                  let c := Classical.choose second
                  have csecond := Classical.choose_spec second
                  have hc := csecond.1
                  have hac := csecond.2.1
                  have hbc := csecond.2.2.1
                  let dbc := Classical.choose csecond.2.2.2
                  have dbcsecond := Classical.choose_spec csecond.2.2.2
                  have hbcrow := dbcsecond.1
                  have leafb := dbcsecond.2
                  have hc' := local_subset_current i A B hc
                  have hm := next_masks (physicalWheelStep g i).data.ground A B {a,b,c} ∅
                    hA hB hAB (by
                      intro x hx
                      rcases (show x = a ∨ x = b ∨ x = c by simpa using hx) with rfl | rfl | rfl
                      · exact ha'
                      · exact hb'
                      · exact hc') (Finset.empty_subset _) (by simp)
                  have hdis : Disjoint (A ∪ {a,b,c}) B := by
                    simpa only [Finset.union_empty] using hm.2.2
                  have hdec : (HistoryFactors.localResidual g i (A ∪ {a,b,c}) B).card <
                      (HistoryFactors.localResidual g i A B).card :=
                    (localCorner_decreases i A B a b c haV hb hc hab hac hbc).2.2.2.2.2
                  exact stepTwoLeafFrom i A B hA a b c haV hb hc hab hac hbc d dbc hd hbcrow leaf leafb
                    (stepOutput h i (A ∪ {a,b,c}) B hm.1 hB hdis old)
              · have hLA : HistoryFactors.localMask g i A = ∅ :=
                  Classical.byContradiction (fun hn => hcut (Or.inl hn))
                have hLB : HistoryFactors.localMask g i B = ∅ :=
                  Classical.byContradiction (fun hn => hcut (Or.inr hn))
                exact stepIntactOutput h i A B hA hB hAB hLA hLB old
            · exact stepNoRowsOutput h i A B hA hB hAB ⟨fun d => hsome ⟨d⟩⟩ old
termination_by (HistoryFactors.localResidual g i A B).card
decreasing_by all_goals assumption

end EarlierHistory

/-- The actual prescribed K4 seed, using the bound all-mask seed proof and
the actual physical label/root bridge. Only this FIXED seed uses finite reasoning. -/
def seedOutput (f : K4.SeedLabel ↪ V) (A B : Finset V)
    (hA : A ⊆ (seedGraph f).ground) :
    Output (HistoryCorners.residual (seedGraph f).ground A B)
      (corner (seedGraph f).ground A B (seedGraph f).rows.root) := by
  have out := HistorySeed.seedCornerOutput f A B hA
  have hr : (seedGraph f).rows.root = renameFamily f K4.seedGraphData.rows.root :=
    PhysicalLabels.root K4.seedGraphData f s(0,0)
  rw [hr]
  exact out

/-- Simultaneous all-original-mask construction for EVERY actual finite
MixedHistory. In the attach case ih supplies corners of old at rank n; the
target is the actual physical attach at rank n+1, at every retained port.
No desired Output, forest classification or collapse is an input of this theorem. -/
def allCornersOutput {n : Nat} {G : Type} {g : GraphData G V}
    (h : MixedHistory n G g) :
    ∀ (A B : Finset V), A ⊆ g.ground → B ⊆ g.ground → Disjoint A B →
      Output (HistoryCorners.residual g.ground A B) (corner g.ground A B g.rows.root) := by
  induction h with
  | seed f =>
      intro A B hA hB hAB
      exact seedOutput f A B hA
  | attach old i ih =>
      intro A B hA hB hAB
      exact stepOutput old i A B hA hB hAB ih

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion
