/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryIntact
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryIntact
   mirror-E: none(waiver:physical-history-intact-terminal)
   anchors: [mathlib/module/Mathlib.Order.UpperLower.CompleteLattice]
   utility: none
   digest: Original-coordinate intact terminals, exact excluded-residue normalizations and actual relative product lists. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCycles
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactTwo
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIsolated
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactProduct
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactLayers
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryMarkers
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Consumer


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
attribute [local instance] historyIntactPropDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact
open OriginalLabelTwoSum AllMWheel HistoryLeafCap HistoryIsolated HistoryCycles


open private D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.join_comm D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.join_mono D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.join_sup D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.facets_single D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.tail_subset D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.local_support D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.local_empty D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.base_support D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.base_vertex D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.base_cone D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.local_part D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.base_local D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.parent_supported D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.retargetFilling D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.zeroFilling D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.zero_collar D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.zero_tops D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.replaceCertificate D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.ground_mainPairsOf D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.ground_corePairsOf D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.pointFaces D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.ground_pointFaces D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.changeOutput_pointFaces D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.renameOutput_lists D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.renameOutput_pointFaces D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.layer_main_readback D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.layer_strip_readback D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.two_layer_main_readback D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.two_layer_core_readback D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact.faces_flatMap from D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactTwo

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem chosen_snoc_two {U : Type*} [DecidableEq U]
    (vs : List U) (z : U) (hn : vs.length % 3 = 2) :
    FiniteIndependentPathGreedy.pathChosen (vs ++ [z]) =
      FiniteIndependentPathGreedy.pathChosen vs := by
  match vs with
  | [] => simp at hn
  | [a] => simp at hn
  | [a, b] => simp [FiniteIndependentPathGreedy.pathChosen]
  | a :: b :: c :: vs =>
      have ht : vs.length % 3 = 2 := by simp only [List.length_cons] at hn; omega
      simp only [List.cons_append, FiniteIndependentPathGreedy.pathChosen,
        chosen_snoc_two vs z ht]
termination_by vs.length

private theorem zero_chosen (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) :
    FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm) = labelsCongruent m 0 3 := by
  rw [pathRootPath, chosen_snoc_two _ _ (by simp only [labelInterval_length]; omega)]
  ext x
  simp only [pathChosen_labelInterval, labelsCongruent, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have := x.isLt
  omega

private theorem zero_rho (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) :
    eta1 m hm = insert (firstLabel m hm) (eta0 m hm) := by
  ext x
  simp only [eta1, eta0, tailGround, tailCritical, if_neg (by omega : m % 3 ≠ 2),
    ground, rim, labelsCongruent, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
    true_and, and_true, Fin.ext_iff, firstLabel, secondLabel,
    ne_eq, Fin.val_zero, Fin.val_mk]
  have := x.isLt
  omega

/-- The two ACTUAL residue-zero local tops: rho is the first-marker extension
of eta; d is the path-filling top and has its entire proper boundary in E. -/
def zeroOtherTop (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) : Finset V :=
  (ground m \ labelsCongruent m 0 3).image f

private theorem zeroOtherCells (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (f : Label m ↪ V) :
    CriticalData (renameFamily f (pathRoot m hm)) {zeroOtherTop m hm f} := by
  let g := renameFilling f (pathFilling m hm)
  have hq : g.critical = {zeroOtherTop m hm f} := by
    change (pathFilling m hm).critical.image (fun s => s.image f) = _
    rw [pathFilling_critical, if_neg (by omega : m % 3 ≠ 1), zero_chosen m hm h0]
    simp only [Finset.image_singleton, zeroOtherTop]
  rw [← hq]
  exact g.cells

private theorem one_interface (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    renameFamily f (A1 m hm) =
      renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f) := by
  change renameFamily f (pathRoot m hm ⊔ delta (tailGround m hm)) = _
  rw [(rename_operations f (tailGround m hm) (pathRoot m hm)
    (delta (tailGround m hm)) ∅).2.1,
    (rename_operations f (tailGround m hm) (pathRoot m hm) (pathRoot m hm) ∅).1]

private def goodOneFilling (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    Filling ((ground m).image f)
      (renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f)) :=
  retargetFilling (renameFilling f (fill1 m hm)) (one_interface m hm f)

/-- The good strong branch consumes the ORIGINAL compiler list expansion at
the actual fillings, including child pairs which involve the removed port.
rightGammaPairs is the selected compiler's classical choice; this theorem
does not identify that choice with a particular witness of gammaGood. -/
theorem goodStrong_main_faces (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (c : Certificate (insert e X) J) :
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.strong c)).main =
      c.main.pairs.flatMap (fun P =>
        replayFacePairs ((ground m).image f) ((tailGround m hm).image f) e
          (renameFamily f (pathRoot m hm)) (orderedPair P)
          (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm)))) ++
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).main.pairs.map
          (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) := by
  change orderedPairs (AllMWheel.oneStep m hm hg c f hf0 heX hXY).main = _
  unfold AllMWheel.oneStep
  apply compileParent_main_orderedPairs

/-- Exact good strong C-ALONE readback. Collars precede the original child
core replay and the actual compiler terminal. The e=source-core-vertex case
uses the compiler's real Gamma permission, with no new supplier premise. -/
theorem goodStrong_core_faces (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (c : Certificate (insert e X) J) :
    orderedPairs (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY (.strong c)).separate =
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).separate.pairs.map
          (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) ++
      c.separate.pairs.flatMap (fun P =>
        replayFacePairs ((ground m).image f) ((tailGround m hm).image f) e
          (renameFamily f (pathRoot m hm)) (orderedPair P)
          (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm)))) ++
      finishFacePairs X ((ground m).image f) ((tailGround m hm).image f)
        ((rim m hm).image f) e c.vertex (renameFamily f (pathRoot m hm))
        (Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [rim]⟩)
        (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm))) := by
  change orderedPairs (AllMWheel.oneStep m hm hg c f hf0 heX hXY).separate = _
  unfold AllMWheel.oneStep
  rw [compileParent_separate_orderedPairs, finishPairSchedule_faces]
  rfl

/-- The original excluded-cycle filling in residue zero, including BOTH
critical tops and its exact ordinary native sequence. -/
def zeroOneSequence (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) (f : Label m ↪ V) :
    Sequence (project (delta ((ground m).image f)))
      (project ((renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f)) ⊔
        (delta ((eta1 m hm).image f) ⊔ delta (zeroOtherTop m hm f)))) := by
  let g := renameFilling f (fill1Excluded m hm (by omega))
  have hq : g.critical = {(eta1 m hm).image f, zeroOtherTop m hm f} := by
    change (fill1Excluded m hm (by omega)).critical.image (fun s => s.image f) = _
    rw [fill1Excluded_critical]
    simp only [cycleCritical, if_pos h0, Finset.image_insert, Finset.image_singleton,
      eta1, zeroOtherTop]
  have hf : facets {(eta1 m hm).image f, zeroOtherTop m hm f} =
      delta ((eta1 m hm).image f) ⊔ delta (zeroOtherTop m hm f) := by
    apply SetLike.ext
    intro s
    simp [facets]
  have hcollar : g.collar = renameFamily f (pathRoot m hm) ⊔
      delta ((tailGround m hm).image f) := one_interface m hm f
  exact g.main.cast rfl (congrArg project
    (congrArg₂ (fun A B : Family V => A ⊔ B) hcollar ((congrArg facets hq).trans hf)))

/-- The original zero filling with eta retained, at every residue-zero width
including m=3 where its genuine local list is empty. -/
def zeroZeroSequence (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0) (f : Label m ↪ V) :
    Sequence (project (delta ((tailGround m hm).image f)))
      (project ((renameFamily f (pathRoot m hm) ⊓ delta ((tailGround m hm).image f)) ⊔
        delta ((eta0 m hm).image f))) := by
  let g := zeroFilling m hm f
  exact g.main.cast rfl (by
    rw [zero_collar, zero_tops, if_neg (by omega : m % 3 ≠ 2), endpoint, facets_single])

private theorem join_assoc (K L M : Family V) :
    rawJoin (rawJoin K L) M = rawJoin K (rawJoin L M) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b ∪ c, ⟨b, hb, c, hc, rfl⟩, Finset.union_assoc _ _ _⟩
  · rintro ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a ∪ b, ⟨a, ha, b, hb, rfl⟩, c, hc, (Finset.union_assoc _ _ _).symm⟩

private theorem join_delta (a b : Finset V) :
    rawJoin (delta a) (delta b) = delta (a ∪ b) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact Finset.union_subset_union hx hy
  · intro hs
    refine ⟨s ∩ a, Finset.inter_subset_right, s ∩ b, Finset.inter_subset_right, ?_⟩
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    exact ⟨fun hv => (Finset.mem_union.mp (hs hv)).elim
      (fun ha => Or.inl ⟨hv, ha⟩) (fun hb => Or.inr ⟨hv, hb⟩), by tauto⟩

private theorem marker_pad (D L : Family V) (r : V) (d : Finset V) :
    rawJoin (HistoryIsolated.singleFamily D L r) (delta d) =
      rawJoin D (delta d) ⊔ rawJoin L (delta (insert r d)) := by
  rw [join_comm, HistoryIsolated.singleFamily, join_sup,
    join_comm (delta d) D, join_comm (delta d) (rawJoin (delta {r}) L),
    join_assoc, join_comm L (delta d), ← join_assoc, join_delta,
    Finset.singleton_union, join_comm (delta (insert r d)) L]

/-- The residue-zero parent is normalized to the EXACT two factor layers,
B union Jhat*Delta(eta) union L*Delta(d). Jhat is the actual coordinate swap
of J, not its collapsed surrogate. BOTH emitted blocks have complete native
ordered readbacks. This is a normalization theorem, not the missing two-factor
strong recovery or the universal history theorem. -/
def zeroNormalization (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J) :
    {T : Sequence
        (project (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
          (renameFamily f (pathRoot m hm)) J))
        (project ((rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔
          rawJoin (renameFamily (HistoryMarkers.markerMap e (f (firstLabel m hm))) J)
            (delta ((eta0 m hm).image f))) ⊔
          rawJoin (rawLink X e J) (delta (zeroOtherTop m hm f)))) //
      T.pairs.map (fun P => (P.lower, P.upper)) =
        (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a)))} := by
  classical
  let Y := (ground m).image f
  let Z := (tailGround m hm).image f
  let E := renameFamily f (pathRoot m hm)
  let B := rawJoin (delta X) E
  let D := restrict X J
  let L := rawLink X e J
  let eta := (eta0 m hm).image f
  let rho := (eta1 m hm).image f
  let d := zeroOtherTop m hm f
  let r := f (firstLabel m hm)
  let N1 := (E ⊔ delta Z) ⊔ (delta rho ⊔ delta d)
  let N0 := (E ⊓ delta Z) ⊔ delta eta
  let C1 := B ⊔ rawJoin D (delta Z)
  let C0 := B ⊔ rawJoin L (delta rho ⊔ delta d)
  have hD : Supported X D := fun _ hs => hs.2
  have hL : Supported X L := fun _ hs => hs.1
  have hLD : L ≤ D := fun s hs => ⟨J.lower (Finset.subset_insert _ _) hs.2, hs.1⟩
  have hZY : Z ⊆ Y := tail_subset m hm f
  have hrY : r ∈ Y := Finset.mem_image.mpr
    ⟨firstLabel m hm, by simp [ground, firstLabel], rfl⟩
  have hrX : r ∉ X := fun hr => Finset.disjoint_left.mp hXY hr hrY
  have hrZ : r ∉ Z := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    have hi' := (f.injective he)
    subst i
    simpa [tailGround, rim] using hi
  have hRho : rho = insert r eta := by
    dsimp [rho, eta, r]
    rw [zero_rho m hm h0, Finset.image_insert]
  have hdCells : CriticalData E {d} := zeroOtherCells m hm h0 f
  have hdZ : ¬ d ⊆ Z := by
    intro h
    have h2d : f (secondLabel m hm) ∈ d := Finset.mem_image.mpr
      ⟨secondLabel m hm, by simp [ground, labelsCongruent, secondLabel], rfl⟩
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (h h2d)
    have hi' := f.injective he
    subst i
    simpa [tailGround, rim] using hi
  let T1 := relativeProduct X Y L ⊥ C1 (delta Y) N1 hXY hL
    (by rintro s ⟨a, ha, _, _, _⟩; exact ha.elim)
    (Finset.empty_subset _) (Or.inl (Or.inl (local_empty m hm f)))
    (fun _ hs => hs) (zeroOneSequence m hm h0 f) (by
      intro a _ _ t ht h
      rcases h with hB | ⟨u, hu, v, hv, he⟩
      · exact Or.inl (Or.inl (base_local hXY ht hB))
      · exact Or.inl (Or.inr ((local_part hXY ht (hD u hu) (by rw [← he])).trans hv)))
  have hS1 : C1 ⊔ rawJoin L (delta Y) = parentOf X Y Z e E J := by
    dsimp [C1, B, D, L, parentOf, phi]
    ac_rfl
  have hT1 : C1 ⊔ rawJoin L N1 = C0 ⊔ rawJoin D (delta Z) := by
    dsimp [C1, C0, N1]
    rw [join_sup, join_sup]
    have hLE : rawJoin L E ≤ B := join_mono hL le_rfl
    have hLZ : rawJoin L (delta Z) ≤ rawJoin D (delta Z) := join_mono hLD le_rfl
    have h : (B ⊔ rawJoin D (delta Z)) ⊔
          ((rawJoin L E ⊔ rawJoin L (delta Z)) ⊔ rawJoin L (delta rho ⊔ delta d)) =
        ((B ⊔ rawJoin L E) ⊔
          (rawJoin D (delta Z) ⊔ rawJoin L (delta Z))) ⊔
          rawJoin L (delta rho ⊔ delta d) := by ac_rfl
    rw [h, sup_eq_left.mpr hLE, sup_eq_left.mpr hLZ]
    ac_rfl
  have hXZ : Disjoint X Z := Finset.disjoint_left.mpr
    (fun v hv hz => Finset.disjoint_left.mp hXY hv (hZY hz))
  let T0 := relativeProduct X Z D ⊥ C0 (delta Z) N0 hXZ hD
    (by rintro s ⟨a, ha, _, _, _⟩; exact ha.elim)
    (Finset.empty_subset _) (Or.inl ⟨local_empty m hm f, Finset.empty_subset _⟩)
    (fun _ hs => hs) (zeroZeroSequence m hm h0 f) (by
      intro a _ _ t ht h
      rcases h with hB | ⟨u, hu, v, hv | hv, he⟩
      · exact Or.inl ⟨base_local hXY (ht.trans hZY) hB, ht⟩
      · have htr : t ⊆ rho := (local_part hXY (ht.trans hZY) (hL u hu)
          (by rw [← he])).trans hv
        right
        intro w hw
        exact (Finset.mem_insert.mp (hRho ▸ htr hw)).resolve_left
          (fun (heq : w = r) => hrZ (heq ▸ ht hw))
      · have htd : t ⊆ d := (local_part hXY (ht.trans hZY) (hL u hu)
          (by rw [← he])).trans hv
        have hp : t ⊂ d := Finset.ssubset_iff_subset_ne.mpr
          ⟨htd, fun heq => hdZ (heq ▸ ht)⟩
        exact Or.inl ⟨hdCells.boundary d (by simp) t hp, ht⟩)
  have hT0 : C0 ⊔ rawJoin D N0 =
      (B ⊔ rawJoin
        (renameFamily (HistoryMarkers.markerMap e r) J) (delta eta)) ⊔ rawJoin L (delta d) := by
    have hDA : rawJoin D (E ⊓ delta Z) ≤ B := join_mono hD (fun _ h => h.1)
    rw [HistoryMarkers.single_marker_family X e r J heX hrX hJ, marker_pad]
    dsimp [C0, N0]
    rw [join_sup, join_sup]
    have hs : (B ⊔ (rawJoin L (delta rho) ⊔ rawJoin L (delta d))) ⊔
        (rawJoin D (E ⊓ delta Z) ⊔ rawJoin D (delta eta)) =
        ((B ⊔ rawJoin D (E ⊓ delta Z)) ⊔ rawJoin D (delta eta)) ⊔
          (rawJoin L (delta rho) ⊔ rawJoin L (delta d)) := by ac_rfl
    rw [hs, sup_eq_left.mpr hDA, ← hRho]
    dsimp only [D, L]
    ac_rfl
  refine ⟨(T1.1.cast (congrArg project hS1) (congrArg project hT1)).append
    (T0.1.cast rfl (congrArg project hT0)), ?_⟩
  rw [Sequence.pairs_append, List.map_append, Sequence.pairs_cast,
    Sequence.pairs_cast, T1.2, T0.2]
  have hbot (K : Family V) :
      (fun a : Finset V => a ∈ K ∧ a ∉ (⊥ : Family V)) = (fun a => a ∈ K) := by
    funext a
    apply propext
    change (a ∈ K ∧ ¬ False) ↔ a ∈ K
    tauto
  simp only [hbot, D, L]

private theorem zeroCycleCells (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (f : Label m ↪ V) :
    CriticalData (renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f))
      {(eta1 m hm).image f, zeroOtherTop m hm f} := by
  let g := renameFilling f (fill1Excluded m hm (by omega))
  have hq : g.critical = {(eta1 m hm).image f, zeroOtherTop m hm f} := by
    change (fill1Excluded m hm (by omega)).critical.image (fun s => s.image f) = _
    rw [fill1Excluded_critical]
    simp only [cycleCritical, if_pos h0, Finset.image_insert, Finset.image_singleton,
      eta1, zeroOtherTop]
  have hc : g.collar = renameFamily f (pathRoot m hm) ⊔
      delta ((tailGround m hm).image f) := one_interface m hm f
  rw [← hc, ← hq]
  exact g.cells

/-- The actual J predecessor, with e replaced by the FIRST original wheel
coordinate, retaining every old coordinate and ghost in X. -/
def zeroMarkerOutput (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V) (J : Family V)
    (f : Label m ↪ V) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J) (oJ : Output (insert e X) J) :
    Output (insert (f (firstLabel m hm)) X)
      (renameFamily (HistoryMarkers.markerMap e (f (firstLabel m hm))) J) := by
  have hr : f (firstLabel m hm) ∉ X := fun h => Finset.disjoint_left.mp hXY h
    (Finset.mem_image.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩)
  exact changeOutput (HistoryMarkers.singleMarkerOutput X e _ J heX hr hJ oJ)
    (HistoryMarkers.single_marker_family X e _ J heX hr hJ).symm


/-- Both lists of the actual marker output are the injective images of the
ORIGINAL oJ lists. Ground equality and the two family equalities change no
pair. renameSequence_pairs is used independently for main and C ALONE. -/
theorem zeroMarkerOutput_lists (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V)
    (J : Family V) (f : Label m ↪ V) (heX : e ∉ X)
    (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J) (oJ : Output (insert e X) J) :
    let g := HistoryMarkers.markerMap e (f (firstLabel m hm))
    mainPairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
        (mainPairsOf oJ).map (fun p => (p.1.image g, p.2.image g)) ∧
    corePairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
        (corePairsOf oJ).map (fun p => (p.1.image g, p.2.image g)) := by
  dsimp only
  have hr : f (firstLabel m hm) ∉ X := fun h => Finset.disjoint_left.mp hXY h
    (Finset.mem_image.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩)
  have hg := HistoryMarkers.marker_ground X e (f (firstLabel m hm)) heX hr
  have h := renameOutput_lists (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ
  constructor
  · calc
      mainPairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
          mainPairsOf (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) := by
        simpa only [zeroMarkerOutput, HistoryMarkers.singleMarkerOutput,
          changeOutput_mainPairsOf] using ground_mainPairsOf hg
            (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ)
      _ = _ := h.1
  · calc
      corePairsOf (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
          corePairsOf (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) := by
        simpa only [zeroMarkerOutput, HistoryMarkers.singleMarkerOutput,
          changeOutput_corePairsOf] using ground_corePairsOf hg
            (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ)
      _ = _ := h.2

private theorem zeroMarkerOutput_pointFaces (m : Nat) (hm : 3 ≤ m)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V) (heX : e ∉ X)
    (hXY : Disjoint X ((ground m).image f)) (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (d : Finset V) :
    pointFaces d id (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
      pointFaces d (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ := by
  have hr : f (firstLabel m hm) ∉ X := fun h => Finset.disjoint_left.mp hXY h
    (Finset.mem_image.mpr ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩)
  have hg := HistoryMarkers.marker_ground X e (f (firstLabel m hm)) heX hr
  calc
    pointFaces d id (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) =
        pointFaces d id (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) := by
      simpa only [zeroMarkerOutput, HistoryMarkers.singleMarkerOutput,
        changeOutput_pointFaces] using ground_pointFaces hg
          (HistoryMarkers.renameOutput (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ) d id
    _ = _ := renameOutput_pointFaces (HistoryMarkers.markerMap e (f (firstLabel m hm))) oJ d

/-- Recovery of BOTH literal residue-zero layers, with all tag combinations.
The first factor is the actual renamed J; the second is its actual old link.
The other full layer is fixed during each main lift. On C ALONE the first
core is stripped, then the second, and the common original-ground cone runs
exactly once. The displayed list equations belong to the constructed value.
-/
def zeroRecovered (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    {c : Certificate (X ∪ (ground m).image f)
        ((rawJoin (delta X) (renameFamily f (pathRoot m hm)) ⊔
          rawJoin (renameFamily (HistoryMarkers.markerMap e (f (firstLabel m hm))) J)
            (delta ((eta0 m hm).image f))) ⊔
          rawJoin (rawLink X e J) (delta (zeroOtherTop m hm f))) //
      orderedPairs c.main =
        HistoryIntactLayers.mainFaces ((eta0 m hm).image f)
          (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
        HistoryIntactLayers.mainFaces (zeroOtherTop m hm f) oL ∧
      orderedPairs c.separate =
        HistoryIntactLayers.stripFaces ((eta0 m hm).image f)
          (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
        HistoryIntactLayers.stripFaces (zeroOtherTop m hm f) oL ++
        (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
          (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
          (fun s => (s, insert hX.choose s))} := by
  classical
  let Y := (ground m).image f
  let Z := (tailGround m hm).image f
  let E := renameFamily f (pathRoot m hm)
  let B := rawJoin (delta X) E
  let r := f (firstLabel m hm)
  let eta := (eta0 m hm).image f
  let rho := (eta1 m hm).image f
  let d := zeroOtherTop m hm f
  let U := insert r X
  let M := renameFamily (HistoryMarkers.markerMap e r) J
  let L := rawLink X e J
  let ohat := zeroMarkerOutput m hm X e J f heX hXY hJ oJ
  let x := hX.choose
  have hx : x ∈ X := hX.choose_spec
  have hrY : r ∈ Y := Finset.mem_image.mpr
    ⟨firstLabel m hm, by simp [ground, firstLabel, Fin.ext_iff], rfl⟩
  have hrX : r ∉ X := fun h => Finset.disjoint_left.mp hXY h hrY
  have hrZ : r ∉ Z := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    have hi' := f.injective he
    subst i
    simpa [tailGround, rim] using hi
  have hZY : Z ⊆ Y := tail_subset m hm f
  have hRho : rho = insert r eta := by
    dsimp [rho, eta, r]
    rw [zero_rho m hm h0, Finset.image_insert]
  let g := zeroFilling m hm f
  have hgQ : g.critical = {eta} := by rw [zero_tops, if_neg (by omega : m % 3 ≠ 2)]
  have hEtaZ : eta ⊆ Z := g.critical_supported eta (by rw [hgQ]; simp)
  have hEtaCells : CriticalData (E ⊓ delta Z) {eta} := by
    rw [← zero_collar m hm f, ← hgQ]
    exact g.cells
  have hEtaE : eta ∉ E := fun h => hEtaCells.absent eta (by simp) ⟨h, hEtaZ⟩
  have hdCells : CriticalData E {d} := zeroOtherCells m hm h0 f
  have hdY : d ⊆ Y := Finset.image_subset_image Finset.sdiff_subset
  have hdE : d ∉ E := hdCells.absent d (by simp)
  have hrEta : r ∉ eta := fun h => hrZ (hEtaZ h)
  have hEtaU : Disjoint eta U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    rcases Finset.mem_insert.mp hu with he | hx'
    · exact hrEta (he ▸ hv)
    · exact Finset.disjoint_left.mp hXY hx' (hZY (hEtaZ hv))
  have hdX : Disjoint d X := Finset.disjoint_left.mpr
    (fun v hv hx' => Finset.disjoint_left.mp hXY hx' (hdY hv))
  have hM : Supported U M := by
    change Supported U (renameFamily (HistoryMarkers.markerMap e r) J)
    rw [HistoryMarkers.single_marker_family X e r J heX hrX hJ]
    rintro s (hs | ⟨a, ha, t, ht, rfl⟩)
    · exact hs.2.trans (Finset.subset_insert _ _)
    · exact Finset.union_subset
        (ha.trans (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))
        (ht.1.trans (Finset.subset_insert _ _))
  have hL : Supported X L := fun _ hs => hs.1
  have hCycle := zeroCycleCells m hm h0 f
  have hEtaNotD : ¬ eta ⊆ d := by
    let i : Label m := ⟨3, by omega⟩
    have hiEta : i ∈ eta0 m hm := by
      simp [i, eta0, tailGround, rim, tailCritical, h0, labelsCongruent,
        firstLabel, secondLabel, ground]
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨i, hiEta, rfl⟩))
    have hi' := f.injective he
    subst j
    simpa [i, labelsCongruent] using (Finset.mem_sdiff.mp hj).2
  have hDNotRho : ¬ d ⊆ rho := by
    have hiD : secondLabel m hm ∈ ground m \ labelsCongruent m 0 3 := by
      simp [ground, labelsCongruent, secondLabel]
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp
      (h (Finset.mem_image.mpr ⟨secondLabel m hm, hiD, rfl⟩))
    have hi' := f.injective he
    subst j
    simpa [eta1, labelsCongruent, secondLabel] using hj
  have hMissing : ∀ s ∈ B ⊔ rawJoin (delta d) (delta X), ¬ eta ⊆ s := by
    intro s hs hsub
    rcases hs with hs | ⟨a, ha, t, ht, rfl⟩
    · exact hEtaE (base_local (a := ∅) hXY (hEtaZ.trans hZY)
        (by change ∅ ∪ _ ∈ B; rw [Finset.empty_union]; exact B.lower hsub hs))
    · exact hEtaNotD ((local_part (a := ∅) hXY (hEtaZ.trans hZY) ht
        (by simpa only [Finset.empty_union, Finset.union_comm] using hsub)).trans ha)
  have hMissing' : ∀ s ∈ B ⊔ rawJoin (delta eta) (delta U), ¬ d ⊆ s := by
    intro s hs hsub
    rcases hs with hs | ⟨a, ha, t, ht, rfl⟩
    · exact hdE (base_local (a := ∅) hXY hdY
        (by change ∅ ∪ _ ∈ B; rw [Finset.empty_union]; exact B.lower hsub hs))
    · apply hDNotRho
      intro v hv
      rcases Finset.mem_union.mp (hsub hv) with hva | hvt
      · rw [hRho]; exact Finset.mem_insert_of_mem (ha hva)
      · rcases Finset.mem_insert.mp (ht hvt) with hvr | hvX
        · rw [hRho]; exact Finset.mem_insert.mpr (Or.inl hvr)
        · exact False.elim (Finset.disjoint_left.mp hXY hvX (hdY hv))
  have hBoundary : ∀ z ⊂ eta, ∀ t ⊆ U, z ∪ t ∈ B := by
    intro z hz t ht
    by_cases hrt : r ∈ t
    · have hp : insert r z ⊂ rho := by
        rw [hRho]
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.insert_subset_insert r hz.subset, ?_⟩
        intro he
        apply hz.ne
        apply Finset.Subset.antisymm hz.subset
        intro v hv
        exact (Finset.mem_insert.mp (he.symm ▸ Finset.mem_insert_of_mem hv)).resolve_left
          (fun (hvr : v = r) => hrEta (hvr ▸ hv))
      have hLocal : insert r z ∈ E :=
        (hCycle.boundary rho (by simp [rho]) _ hp).resolve_right
          (fun hZ => hrZ (hZ (Finset.mem_insert_self _ _)))
      have htX : t.erase r ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hv).2)).resolve_left
          (Finset.mem_erase.mp hv).1
      exact ⟨t.erase r, htX, insert r z, hLocal, by
        rw [Finset.union_insert, ← Finset.insert_union, Finset.insert_erase hrt]
        exact Finset.union_comm _ _⟩
    · have htX : t ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (ht hv)).resolve_left (fun hvr => hrt (hvr ▸ hv))
      exact ⟨t, htX, z, (hEtaCells.boundary eta (by simp) z hz).1,
        Finset.union_comm _ _⟩
  let R := HistoryIntactLayers.twoLayers (X ∪ Y) B x U eta M ohat X d L oL
    hM hL (hEtaCells.nonempty eta (by simp)) (hdCells.nonempty d (by simp)) hEtaU hdX
    (Finset.union_subset ((hEtaZ.trans hZY).trans Finset.subset_union_right)
      (Finset.insert_subset (Finset.mem_union_right _ hrY) Finset.subset_union_left))
    (Finset.union_subset (hdY.trans Finset.subset_union_right) Finset.subset_union_left)
    (base_support X Y E (local_support m hm f))
    (base_vertex X E x hx (local_empty m hm f)) (base_cone X E x hx)
    hMissing hMissing' hBoundary (by
      intro z hz t ht
      exact ⟨t, ht, z, hdCells.boundary d (by simp) z hz, Finset.union_comm _ _⟩)
  have hSource : (B ⊔ rawJoin (delta eta) M) ⊔ rawJoin (delta d) L =
      (B ⊔ rawJoin M (delta eta)) ⊔ rawJoin L (delta d) := by
    rw [join_comm (delta eta) M, join_comm (delta d) L]
  refine ⟨replaceCertificate R.1 hSource, ?_, ?_⟩
  · simpa only [replaceCertificate, orderedPairs, orderedPair, Sequence.pairs_cast]
      using R.2.1
  · exact R.2.2

/-- Residue zero: both normalization blocks precede BOTH recovered factor
mains. The independent separate sequence is the one in zeroRecovered. -/
def zeroIntactCertificate (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    Certificate (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) J) := by
  let T := zeroNormalization m hm h0 X e J f heX hXY hJ
  let c := (zeroRecovered m hm h0 X e J f heX hX hXY hJ oJ oL).1
  exact {
    supported := parent_supported X _ _ e _ J (tail_subset m hm f) (local_support m hm f)
    core := c.core
    critical := c.critical
    vertex := c.vertex
    vertex_mem := c.vertex_mem
    core_supported := c.core_supported
    critical_supported := c.critical_supported
    cells := c.cells
    main := T.1.append c.main
    separate := c.separate }

/-- Complete ordered main readback of the constructed zero-residue value. -/
theorem zeroIntact_main_faces (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).main =
      (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      HistoryIntactLayers.mainFaces ((eta0 m hm).image f)
        (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
      HistoryIntactLayers.mainFaces (zeroOtherTop m hm f) oL := by
  have hT := (zeroNormalization m hm h0 X e J f heX hXY hJ).2
  have hR := (zeroRecovered m hm h0 X e J f heX hX hXY hJ oJ oL).2.1
  have h := congrArg₂ (fun (xs ys : List (Finset V × Finset V)) => xs ++ ys) hT hR
  unfold orderedPairs orderedPair at h ⊢
  simpa only [zeroIntactCertificate, Sequence.pairs_append, List.map_append,
    List.append_assoc] using h

/-- Complete C-ALONE readback: the two core strips precede the sole cone. -/
theorem zeroIntact_core_faces (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).separate =
      HistoryIntactLayers.stripFaces ((eta0 m hm).image f)
        (zeroMarkerOutput m hm X e J f heX hXY hJ oJ) ++
      HistoryIntactLayers.stripFaces (zeroOtherTop m hm f) oL ++
      (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
        (fun s => (s, insert hX.choose s)) :=
  (zeroRecovered m hm h0 X e J f heX hX hXY hJ oJ oL).2.2


/-- Original-factor main readback. The normalization is local-pair-major,
then the original oJ list is renamed and padded, then original oL is padded.
This consumes the existing normalization/recovery proof without changing it. -/
theorem zeroIntact_main_original (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    let g := HistoryMarkers.markerMap e (f (firstLabel m hm))
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).main =
      (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
      (mainPairsOf oJ).map (fun p =>
        ((eta0 m hm).image f ∪ p.1.image g, (eta0 m hm).image f ∪ p.2.image g)) ++
      (mainPairsOf oL).map (fun p =>
        (zeroOtherTop m hm f ∪ p.1, zeroOtherTop m hm f ∪ p.2)) := by
  dsimp only
  rw [zeroIntact_main_faces]
  simp only [layer_main_readback, (zeroMarkerOutput_lists m hm X e J f heX hXY hJ oJ).1,
    List.map_map, Function.comp_def]

/-- Original-factor C-ALONE readback. Only a strong factor contributes its
point-layer pair; the marker point is mapped by the same original swap.
The first core strip, second core strip and common cone keep their order. -/
theorem zeroIntact_core_original (m : Nat) (hm : 3 ≤ m) (h0 : m % 3 = 0)
    (X : Finset V) (e : V) (J : Family V) (f : Label m ↪ V)
    (heX : e ∉ X) (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    let g := HistoryMarkers.markerMap e (f (firstLabel m hm))
    let eta := (eta0 m hm).image f
    let d := zeroOtherTop m hm f
    orderedPairs (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL).separate =
      (corePairsOf oJ).map (fun p => (eta ∪ p.1.image g, eta ∪ p.2.image g)) ++
      (match oJ with
        | .void _ => []
        | .unit _ => []
        | .strong c => [(eta, insert (g c.vertex) eta)]) ++
      (corePairsOf oL).map (fun p => (d ∪ p.1, d ∪ p.2)) ++
      (match oL with
        | .void _ => []
        | .unit _ => []
        | .strong c => [(d, insert c.vertex d)]) ++
      (fibres (((X ∪ (ground m).image f).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) (renameFamily f (pathRoot m hm))))).map
        (fun s => (s, insert hX.choose s)) := by
  dsimp only
  rw [zeroIntact_core_faces]
  simp only [layer_strip_readback,
    (zeroMarkerOutput_lists m hm X e J f heX hXY hJ oJ).2,
    zeroMarkerOutput_pointFaces, List.map_map, Function.comp_def, List.append_assoc]
  simp only [pointFaces, id_eq]
  congr 10
  · cases oJ <;> rfl
  · cases oL <;> rfl

/-- The intended nonempty-X local terminal at EVERY m>=3, on actual original
coordinates. oJ and oL are the exact strictly-earlier predecessor factors;
they are NOT hypotheses of a final universal physical-history theorem.
No same-rank parent, core, link or deletion output is supplied here. -/
def intactOutput (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V) (J : Family V)
    (f : Label m ↪ V) (hf0 : f 0 = e) (heX : e ∉ X) (hX : X.Nonempty)
    (hXY : Disjoint X ((ground m).image f)) (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    Output (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) J) := by
  classical
  by_cases h0 : m % 3 = 0
  · exact .strong (zeroIntactCertificate m hm h0 X e J f heX hX hXY hJ oJ oL)
  · by_cases h2 : m % 3 = 2
    · exact .strong (twoIntactCertificate m hm h2 X e J f hX hXY oL)
    · have hg : goodResidue m := ⟨m / 3, by omega⟩
      exact .strong (goodIntactCertificate m hm hg X e J f hf0 heX hX hXY oJ)


/-- Full main-list readback of intactOutput, at every residue and every
actual tag, explicitly in the ORIGINAL oJ/oL lists. No list is permuted. -/
theorem intactOutput_main_faces (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V)
    (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e) (heX : e ∉ X)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    mainPairsOf (intactOutput m hm X e J f hf0 heX hX hXY hJ oJ oL) =
      if h0 : m % 3 = 0 then
        (zeroOneSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (zeroZeroSequence m hm h0 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oJ).map (fun p =>
          ((eta0 m hm).image f ∪ p.1.image (HistoryMarkers.markerMap e (f (firstLabel m hm))),
           (eta0 m hm).image f ∪ p.2.image (HistoryMarkers.markerMap e (f (firstLabel m hm))))) ++
        (mainPairsOf oL).map (fun p =>
          (zeroOtherTop m hm f ∪ p.1, zeroOtherTop m hm f ∪ p.2))
      else if h2 : m % 3 = 2 then
        (twoZeroSequence m hm h2 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ restrict X J ∧ a ∉ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (twoPathSequence m hm h2 f).pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ rawLink X e J))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a))) ++
        (mainPairsOf oL).map (fun p => (twoPathTop m hm f ∪ p.1, twoPathTop m hm f ∪ p.2))
      else match oJ with
        | .void _ => []
        | .unit _ => (fill0 m hm).main.pairs.map
            (fun P => (P.lower.image f, P.upper.image f))
        | .strong c =>
            (mainPairsOf oJ).flatMap (fun p =>
              replayFacePairs ((ground m).image f) ((tailGround m hm).image f) e
                (renameFamily f (pathRoot m hm)) p
                (rightGammaPairs ((ground m).image f) (renameFamily f (pathRoot m hm)))) ++
            (fibres c.critical).flatMap (fun q =>
              (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).main.pairs.map
                (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) := by
  classical
  split_ifs with h0 h2
  · simpa only [intactOutput, dif_pos h0, mainPairsOf] using
      zeroIntact_main_original m hm h0 X e J f heX hX hXY hJ oJ oL
  · simpa only [intactOutput, dif_neg h0, dif_pos h2, mainPairsOf,
      two_layer_main_readback] using twoIntact_main_faces m hm h2 X e J f hX hXY oL
  · have hg : goodResidue m := ⟨m / 3, by omega⟩
    cases oJ with
    | void hv =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, mainPairsOf] using
          (goodVoid_lists m hm hg X e J f hf0 heX hX hXY hv).1
    | unit hu =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, mainPairsOf] using
          (goodUnit_lists m hm hg X e J f hf0 heX hX hXY hu).1
    | strong c =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, mainPairsOf,
          orderedPairs, faces_flatMap] using
          goodStrong_main_faces m hm hg X e J f hf0 heX hX hXY c

/-- Full separate C-ALONE readback of intactOutput. The zero and two
branches finish their actual core strips before the common cone. The good
branch retains original collar order, original core replay and its actual
compiler terminal, including source-core vertex e. -/
theorem intactOutput_core_faces (m : Nat) (hm : 3 ≤ m) (X : Finset V) (e : V)
    (J : Family V) (f : Label m ↪ V) (hf0 : f 0 = e) (heX : e ∉ X)
    (hX : X.Nonempty) (hXY : Disjoint X ((ground m).image f))
    (hJ : Supported (insert e X) J)
    (oJ : Output (insert e X) J) (oL : Output X (rawLink X e J)) :
    let Y := (ground m).image f
    let E := renameFamily f (pathRoot m hm)
    let cone := (fibres (((X ∪ Y).erase hX.choose).powerset.filter
      (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) E))).map
      (fun s => (s, insert hX.choose s))
    corePairsOf (intactOutput m hm X e J f hf0 heX hX hXY hJ oJ oL) =
      if h0 : m % 3 = 0 then
        (corePairsOf oJ).map (fun p =>
          ((eta0 m hm).image f ∪ p.1.image (HistoryMarkers.markerMap e (f (firstLabel m hm))),
           (eta0 m hm).image f ∪ p.2.image (HistoryMarkers.markerMap e (f (firstLabel m hm))))) ++
        (match oJ with
          | .void _ => []
          | .unit _ => []
          | .strong c => [((eta0 m hm).image f,
              insert (HistoryMarkers.markerMap e (f (firstLabel m hm)) c.vertex) ((eta0 m hm).image f))]) ++
        (corePairsOf oL).map (fun p => (zeroOtherTop m hm f ∪ p.1, zeroOtherTop m hm f ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(zeroOtherTop m hm f, insert c.vertex (zeroOtherTop m hm f))]) ++ cone
      else if h2 : m % 3 = 2 then
        (corePairsOf oL).map (fun p => (twoPathTop m hm f ∪ p.1, twoPathTop m hm f ∪ p.2)) ++
        (match oL with
          | .void _ => []
          | .unit _ => []
          | .strong c => [(twoPathTop m hm f, insert c.vertex (twoPathTop m hm f))]) ++ cone
      else match oJ with
        | .void _ => cone
        | .unit _ => cone
        | .strong c =>
            (fibres c.critical).flatMap (fun q =>
              (selectFilling e (zeroFilling m hm f) (goodOneFilling m hm f) q).separate.pairs.map
                (fun P => (criticalPart e q ∪ P.lower, criticalPart e q ∪ P.upper))) ++
            (corePairsOf oJ).flatMap (fun p =>
              replayFacePairs Y ((tailGround m hm).image f) e E p (rightGammaPairs Y E)) ++
            finishFacePairs X Y ((tailGround m hm).image f) ((rim m hm).image f)
              e c.vertex E (Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [rim]⟩)
              (rightGammaPairs Y E) := by
  classical
  dsimp only
  split_ifs with h0 h2
  · simpa only [intactOutput, dif_pos h0, corePairsOf] using
      zeroIntact_core_original m hm h0 X e J f heX hX hXY hJ oJ oL
  · simp only [intactOutput, dif_neg h0, dif_pos h2, corePairsOf]
    rw [twoIntact_core_faces, two_layer_core_readback]
    simp only [corePairsOf, pointFaces, id_eq, List.append_assoc]
    congr 10
    cases oL <;> rfl
  · have hg : goodResidue m := ⟨m / 3, by omega⟩
    cases oJ with
    | void hv =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, corePairsOf] using
          (goodVoid_lists m hm hg X e J f hf0 heX hX hXY hv).2
    | unit hu =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, corePairsOf] using
          (goodUnit_lists m hm hg X e J f hf0 heX hX hXY hu).2
    | strong c =>
        simpa only [intactOutput, dif_neg h0, dif_neg h2, corePairsOf,
          orderedPairs, faces_flatMap] using
          goodStrong_core_faces m hm hg X e J f hf0 heX hX hXY c

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact

