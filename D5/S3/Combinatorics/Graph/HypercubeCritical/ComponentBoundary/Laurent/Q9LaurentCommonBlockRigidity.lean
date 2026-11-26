/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonBlockRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonBlockRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: A shared block forces one row partition and order fifty-four in a connected cubic Laurent component of the nine-cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentFiveTypeExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentNormalizedBoxes
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentSharedCutBoxes
import Mathlib.Tactic.Choose

/-! A common direction triple reduces the transverse components to
balanced cut boxes with a shared height, forcing a constant row partition. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions

open Finset
open scoped symmDiff
open BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9LaurentCommonTriple (Axes commonAxes inside outside UniqueCommonNeighbor
  exists_chart outside_eq_iff_inside_of_partition)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity pathEnd)
open Q9CutBoxRigidity (Point Box HasHeight)
open Q3StarHeight (isLeaf)

private abbrev Split := Fin 3 ⊕ Fin 3 ≃ Fin 6

/-- The three coordinates in the first block. -/
private def splitCut (e : Split) : Point := univ.image fun i => e (.inl i)

private theorem card_splitCut (e : Split) : (splitCut e).card = 3 := by
  unfold splitCut
  change #(univ.image (e ∘ Sum.inl : Fin 3 → Fin 6)) = 3
  rw [card_image_of_injective _ (e.injective.comp Sum.inl_injective), card_univ, Fintype.card_fin]

/-- Place two words on the two halves of a coordinate split. -/
private def pack (e : Split) (l r : BitVec 3) : Point :=
  univ.filter (fun k => Sum.elim (fun j : Fin 3 => l.getLsbD j.val)
    (fun j : Fin 3 => r.getLsbD j.val) (e.symm k))

private theorem mem_pack_left (e : Split) (l r : BitVec 3) (i : Fin 3) :
    e (.inl i) ∈ pack e l r ↔ l.getLsbD i.val = true := by
  simp [pack]

private theorem mem_pack_right (e : Split) (l r : BitVec 3) (i : Fin 3) :
    e (.inr i) ∈ pack e l r ↔ r.getLsbD i.val = true := by
  simp [pack]

private theorem mem_left (e : Split) (i : Fin 3) : e (.inl i) ∈ splitCut e :=
  mem_image.mpr ⟨i, mem_univ _, rfl⟩

private theorem not_mem_right (e : Split) (j : Fin 3) : e (.inr j) ∉ splitCut e := by
  rintro h
  obtain ⟨i,_,he⟩ := mem_image.mp h
  exact Sum.inl_ne_inr (e.injective he)

private theorem leaf_bits (u v : BitVec 3) :
    isLeaf u v = true ↔ ∃ i : Fin 3, ∀ j : Fin 3,
      (u ^^^ v).getLsbD j.val = decide (j = i) := by
  have h : ∀ a b : Fin 8,
      isLeaf (BitVec.ofFin a) (BitVec.ofFin b) = true ↔
      ∃ i : Fin 3, ∀ j : Fin 3,
        ((BitVec.ofFin a : BitVec 3) ^^^ (BitVec.ofFin b : BitVec 3)).getLsbD j.val =
          decide (j = i) := by
    decide +kernel
  exact h u.toFin v.toFin

private theorem mem_diff_pack_left (e : Split) (a b u v : BitVec 3) (i : Fin 3) :
    e (.inl i) ∈ pack e a b ∆ pack e u v ↔ (a ^^^ u).getLsbD i.val = true := by
  simp only [mem_symmDiff, mem_pack_left, BitVec.getLsbD_xor]
  cases a.getLsbD i.val <;> cases u.getLsbD i.val <;> decide

private theorem mem_diff_pack_right (e : Split) (a b u v : BitVec 3) (i : Fin 3) :
    e (.inr i) ∈ pack e a b ∆ pack e u v ↔ (b ^^^ v).getLsbD i.val = true := by
  simp only [mem_symmDiff, mem_pack_right, BitVec.getLsbD_xor]
  cases b.getLsbD i.val <;> cases v.getLsbD i.val <;> decide

private theorem crossing_pair_iff (e : Split) (a b u v : BitVec 3) :
    Box (splitCut e) (pack e a b) (pack e u v) ↔
      ∃ i j : Fin 3, pack e a b ∆ pack e u v = {e (.inl i), e (.inr j)} := by
  constructor
  · rintro ⟨i,j,hij,he⟩
    obtain ⟨ii,rfl⟩ := e.surjective i
    obtain ⟨jj,rfl⟩ := e.surjective j
    rcases ii with i | i <;> rcases jj with j | j
    · exact ((hij.mp (mem_left e i)) (mem_left e j)).elim
    · exact ⟨i,j,he⟩
    · exact ⟨j,i,he.trans (pair_comm _ _)⟩
    · exact ((not_mem_right e i) (hij.mpr (not_mem_right e j))).elim
  · rintro ⟨i,j,he⟩
    exact ⟨_,_,iff_of_true (mem_left e i) (not_mem_right e j),he⟩

/-- On an arbitrary coordinate split, the product of two star leaf sets is
the translated balanced cut box centered at the packed star centers. -/
private theorem box_pack_iff (e : Split) (a b u v : BitVec 3) :
    Box (splitCut e) (pack e a b) (pack e u v) ↔ isLeaf a u = true ∧ isLeaf b v = true := by
  rw [crossing_pair_iff, leaf_bits, leaf_bits]
  have left_pair (i j k : Fin 3) : e (.inl k) ∈ ({e (.inl i),e (.inr j)} : Point) ↔ k = i := by
    simp [e.injective.eq_iff]
  have right_pair (i j k : Fin 3) : e (.inr k) ∈ ({e (.inl i),e (.inr j)} : Point) ↔ k = j := by
    simp [e.injective.eq_iff]
  constructor
  · rintro ⟨i,j,he⟩
    refine ⟨⟨i,fun k => ?_⟩,⟨j,fun k => ?_⟩⟩
    · apply Bool.eq_iff_iff.mpr
      rw [← mem_diff_pack_left, he, left_pair, decide_eq_true_eq]
    · apply Bool.eq_iff_iff.mpr
      rw [← mem_diff_pack_right, he, right_pair, decide_eq_true_eq]
  · rintro ⟨⟨i, hi⟩,⟨j,hj⟩⟩
    refine ⟨i,j,?_⟩
    ext x
    obtain ⟨k,rfl⟩ := e.surjective x
    cases k with
    | inl k => rw [mem_diff_pack_left, hi, left_pair, decide_eq_true_eq]
    | inr k => rw [mem_diff_pack_right, hj, right_pair, decide_eq_true_eq]

/-- If a block other than `S` occurs in only one realized partition `P`,
then deleting the directions in `S` preserves the partition `P` throughout
the resulting transverse component. -/
private theorem neighborPartition_eq_of_private_transverse_blocks
    {C : Finset (Q 9)} {b : Bool} {P : Partition} {S : Block}
    (hprivate : ∀ x : Side C b, ∀ T ∈ P, T ≠ S →
      T ∈ neighborPartition C x.val → neighborPartition C x.val = P)
    {x y : Side C b} (hx : neighborPartition C x.val = P)
    (hpath : Relation.ReflTransGen (transverseMove S) x y) :
    neighborPartition C y.val = P := by
  induction hpath with
  | refl => exact hx
  | @tail u v _ hstep ih =>
    obtain ⟨p, hiS, _, rfl⟩ := hstep
    obtain ⟨T, hu, hv, hne⟩ := exists_shared_block_of_first_axis_outside u p hiS
    exact hprivate (pathEnd u p) T (ih ▸ hu) hne hv

open scoped Classical in
/-- The two complementary blocks give a product of three-point stars on
a transverse component, with a coordinatewise height on each factor. -/
private theorem leaf_partition_star_product
    {C : Finset (Q 9)} {b : Bool} {a : Side C b → Exponent}
    {P : Partition} {root : Side C b} (s l r : Axes)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) (hP : IsTriplePartition P)
    (hS : commonAxes s ∈ P) (hL : commonAxes l ∈ P) (hR : commonAxes r ∈ P)
    (hLS : commonAxes l ≠ commonAxes s) (hRS : commonAxes r ≠ commonAxes s)
    (hLR : commonAxes l ≠ commonAxes r)
    (hcover : commonAxes s ∪ commonAxes l ∪ commonAxes r = univ)
    (hroot : neighborPartition C root.val = P)
    (hprivate : ∀ x : Side C b, ∀ T ∈ P, T ≠ commonAxes s →
      T ∈ neighborPartition C x.val → neighborPartition C x.val = P) :
    ∃ (c d : BitVec 3) (kl kr : Fin 3 → ℤ),
      (∀ u v : BitVec 3, (Q3StarHeight.isLeaf c u = true ∧ Q3StarHeight.isLeaf d v = true) ↔
        ∃ x ∈ transverseSide (commonAxes s) root,
          (cubeBitVec 3).symm (inside l x.val) = u ∧
          (cubeBitVec 3).symm (inside r x.val) = v) ∧
      ∀ x ∈ transverseSide (commonAxes s) root, ∀ j : Fin 3,
        a x (l (.inl j)) = kl j + ((c ^^^ (cubeBitVec 3).symm (inside l x.val)).getLsbD j.val).toNat ∧
        a x (r (.inl j)) = kr j + ((d ^^^ (cubeBitVec 3).symm (inside r x.val)).getLsbD j.val).toNat := by
  classical
  let S := commonAxes s
  let T := transverseSupport S root
  have label (x : Side C b) (hx : x ∈ transverseSide S root) :
      neighborPartition C x.val = P :=
    neighborPartition_eq_of_private_transverse_blocks hprivate hroot (mem_transverseSide.mp hx)
  have parts (x : Side C b) (hx : x ∈ transverseSide S root) :
      IsTriplePartition (neighborPartition C x.val) := label x hx ▸ hP
  have partsL (x : Side C b) (hx : x ∈ transverseSide S root) :
      commonAxes l ∈ neighborPartition C x.val := label x hx ▸ hL
  have partsR (x : Side C b) (hx : x ∈ transverseSide S root) :
      commonAxes r ∈ neighborPartition C x.val := label x hx ▸ hR
  have shared (x : Side C b) (hx : x ∈ transverseSide S root) :
      S ∈ neighborPartition C x.val := label x hx ▸ hS
  have lStar : UniqueCommonNeighbor T b l :=
    uniqueCommonNeighbor_transverse_of_partitions hC h parts shared
      (hP.disjoint_blocks hL hS hLS) partsL
  have rStar : UniqueCommonNeighbor T b r :=
    uniqueCommonNeighbor_transverse_of_partitions hC h parts shared
      (hP.disjoint_blocks hR hS hRS) partsR
  have insideS (x : Side T b) : inside s x.val = inside s root.val := by
    obtain ⟨y, hy, he⟩ := exists_transverseSide_of_selected_mem x
    rw [← he]
    exact inside_eq_on_transverseSide rfl hy
  have disj := hP.disjoint_blocks hL hR hLR
  have disjAxes (i j : Fin 3) : r (.inl i) ≠ l (.inl j) := by
    intro he
    have hi : r (.inl i) ∈ commonAxes r := mem_image.mpr ⟨i, mem_univ _, rfl⟩
    have hj : l (.inl j) ∈ commonAxes l := mem_image.mpr ⟨j, mem_univ _, rfl⟩
    exact disjoint_left.mp disj hj (he ▸ hi)
  have cover' : S ∪ commonAxes r ∪ commonAxes l = univ := by
    rw [union_right_comm, hcover]
  have chartsL (x y : Side T b) : outside l x.val = outside l y.val ↔ inside r x.val = inside r y.val :=
    outside_eq_iff_inside_of_partition hcover disj ((insideS x).trans (insideS y).symm)
  have chartsR (x y : Side T b) : outside r x.val = outside r y.val ↔ inside l x.val = inside l y.val :=
    outside_eq_iff_inside_of_partition cover' disj.symm ((insideS x).trans (insideS y).symm)
  have rootMem : root ∈ transverseSide S root := mem_transverseSide.mpr .refl
  let base : Side T b := ⟨root.val, by
    unfold T transverseSupport
    exact mem_union_left _ (mem_image.mpr ⟨root, rootMem, rfl⟩), root.property.2⟩
  obtain ⟨c, d, box⟩ := actual_transverse_star_product h l r _ _ base lStar rStar
    (fun x => by
      obtain ⟨y, hy, he⟩ := exists_transverseSide_of_selected_mem x
      rw [← he]
      exact blockParity_eq_on_transverseSide parts partsL hy)
    (fun x => by
      obtain ⟨y, hy, he⟩ := exists_transverseSide_of_selected_mem x
      rw [← he]
      exact blockParity_eq_on_transverseSide parts partsR hy)
    chartsL chartsR disjAxes
  obtain ⟨kr, hkr⟩ := right_height_on_transverse_product h l r base c d lStar rStar
    chartsL chartsR disjAxes box
  have swapBox (u v : BitVec 3) :
      (Q3StarHeight.isLeaf d u = true ∧ Q3StarHeight.isLeaf c v = true) ↔
      ∃ x : Side T b, (cubeBitVec 3).symm (inside r x.val) = u ∧
        (cubeBitVec 3).symm (inside l x.val) = v := by
    simpa only [and_comm] using box v u
  obtain ⟨kl, hkl⟩ := right_height_on_transverse_product h r l base d c rStar lStar
    chartsR chartsL (fun i j => (disjAxes j i).symm) swapBox
  refine ⟨c, d, kl, kr, fun u v => (box u v).trans ?_, ?_⟩
  · constructor
    · rintro ⟨x, hx, hx'⟩
      obtain ⟨y, hy, he⟩ := exists_transverseSide_of_selected_mem x
      exact ⟨y, hy, by rwa [he], by rwa [he]⟩
    · rintro ⟨y, hy, hyl, hyr⟩
      have hym : y.val ∈ T := by
        unfold T transverseSupport
        exact mem_union_left _ (mem_image.mpr ⟨y, hy, rfl⟩)
      exact ⟨⟨y.val, hym, y.property.2⟩, hyl, hyr⟩
  · intro y hy j
    have hym : y.val ∈ T := by
      unfold T transverseSupport
      exact mem_union_left _ (mem_image.mpr ⟨y, hy, rfl⟩)
    exact ⟨hkl ⟨y.val, hym, y.property.2⟩ j, hkr ⟨y.val, hym, y.property.2⟩ j⟩

/-- Identify a six-cube word with its set of active coordinates. -/
private def encodePoint : Q 6 ≃ Point where
  toFun x := univ.filter fun i => x i = true
  invFun s := fun i => decide (i ∈ s)
  left_inv x := by
    funext i
    cases he : x i <;> simp [he]
  right_inv s := by
    ext i
    simp

private theorem exists_split (e l r : Axes)
    (hl : Disjoint (commonAxes l) (commonAxes e))
    (hr : Disjoint (commonAxes r) (commonAxes e))
    (hlr : Disjoint (commonAxes l) (commonAxes r))
    (hc : commonAxes e ∪ commonAxes l ∪ commonAxes r = univ) :
    ∃ f : Split, (∀ i, e (.inr (f (.inl i))) = l (.inl i)) ∧
      (∀ i, e (.inr (f (.inr i))) = r (.inl i)) := by
  classical
  have find (g : Axes) (hd : Disjoint (commonAxes g) (commonAxes e)) (i : Fin 3) :
      ∃ j : Fin 6, e (.inr j) = g (.inl i) := by
    obtain ⟨j, hj⟩ := e.surjective (g (.inl i))
    cases j with
    | inl j =>
      exact (disjoint_left.mp hd (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
        (mem_image.mpr ⟨j,mem_univ _,hj⟩)).elim
    | inr j => exact ⟨j,hj⟩
  let fL (i : Fin 3) := (find l hl i).choose
  let fR (i : Fin 3) := (find r hr i).choose
  have hL (i : Fin 3) : e (.inr (fL i)) = l (.inl i) := (find l hl i).choose_spec
  have hR (i : Fin 3) : e (.inr (fR i)) = r (.inl i) := (find r hr i).choose_spec
  let f := Sum.elim fL fR
  have hF : Function.Injective f := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl (Sum.inl.inj (l.injective
          ((hL x).symm.trans ((congrArg (fun i => e (.inr i)) h).trans (hL y)))))
      | inr y =>
        have he := (hL x).symm.trans ((congrArg (fun i => e (.inr i)) h).trans (hR y))
        exact (disjoint_left.mp hlr (mem_image.mpr ⟨x,mem_univ _,rfl⟩)
          (mem_image.mpr ⟨y,mem_univ _,he.symm⟩)).elim
    | inr x =>
      cases y with
      | inl y =>
        have he := (hL y).symm.trans ((congrArg (fun i => e (.inr i)) h.symm).trans (hR x))
        exact (disjoint_left.mp hlr (mem_image.mpr ⟨y,mem_univ _,rfl⟩)
          (mem_image.mpr ⟨x,mem_univ _,he.symm⟩)).elim
      | inr y =>
        exact congrArg Sum.inr (Sum.inl.inj (r.injective
          ((hR x).symm.trans ((congrArg (fun i => e (.inr i)) h).trans (hR y)))))
  have surj : Function.Surjective f := by
    intro j
    have hm : e (.inr j) ∈ commonAxes e ∪ commonAxes l ∪ commonAxes r := by rw [hc]; simp
    rcases mem_union.mp hm with hm | hm
    · rcases mem_union.mp hm with hs | hm
      · obtain ⟨i,_,he⟩ := mem_image.mp hs
        exact (Sum.inl_ne_inr (e.injective he)).elim
      · obtain ⟨i,_,he⟩ := mem_image.mp hm
        exact ⟨.inl i, Sum.inr.inj (e.injective ((hL i).trans he))⟩
    · obtain ⟨i,_,he⟩ := mem_image.mp hm
      exact ⟨.inr i, Sum.inr.inj (e.injective ((hR i).trans he))⟩
  exact ⟨Equiv.ofBijective f ⟨hF,surj⟩, hL, hR⟩

private theorem encode_eq_pack (f : Split) (x : Q 6) :
    encodePoint x = pack f ((cubeBitVec 3).symm fun i => x (f (.inl i)))
      ((cubeBitVec 3).symm fun i => x (f (.inr i))) := by
  ext k
  obtain ⟨j,rfl⟩ := f.surjective k
  cases j with
  | inl j =>
    rw [mem_pack_left]
    change f (.inl j) ∈ univ.filter (fun i => x i = true) ↔
      cubeBitVec 3 ((cubeBitVec 3).symm (fun i => x (f (.inl i)))) j = true
    simp
  | inr j =>
    rw [mem_pack_right]
    change f (.inr j) ∈ univ.filter (fun i => x i = true) ↔
      cubeBitVec 3 ((cubeBitVec 3).symm (fun i => x (f (.inr i)))) j = true
    simp

open scoped Classical in
/-- Realize one transverse component in the common projection as a cut box,
with height inherited from the original Laurent exponent. -/
private theorem exists_cut_box_of_private_transverse_blocks
    {C : Finset (Q 9)} {b : Bool} {a : Side C b → Exponent}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) (e l r : Axes) (x : Side C b) {P : Partition}
    (hP : IsTriplePartition P)
    (hS : commonAxes e ∈ P) (hL : commonAxes l ∈ P) (hR : commonAxes r ∈ P)
    (hLS : commonAxes l ≠ commonAxes e) (hRS : commonAxes r ≠ commonAxes e)
    (hLR : commonAxes l ≠ commonAxes r)
    (hcover : commonAxes e ∪ commonAxes l ∪ commonAxes r = univ)
    (hx : neighborPartition C x.val = P)
    (hprivate : ∀ y : Side C b, ∀ T ∈ P, T ≠ commonAxes e →
      T ∈ neighborPartition C y.val → neighborPartition C y.val = P)
    (g : Q 6 → Fin 6 → ℤ)
    (hg : ∀ y : Side C b, ∀ k : Fin 6, g (outside e y.val) k = a y (e (.inr k))) :
    ∃ A c : Point, A.card = 3 ∧
      A.map (⟨fun j => e (.inr j), e.injective.comp Sum.inr_injective⟩ : Fin 6 ↪ Fin 9) =
        commonAxes l ∧
      Aᶜ.map (⟨fun j => e (.inr j), e.injective.comp Sum.inr_injective⟩ : Fin 6 ↪ Fin 9) =
        commonAxes r ∧
      HasHeight (g ∘ encodePoint.symm) A c ∧
      ∀ u : Q 6, Box A c (encodePoint u) ↔
        ∃ y ∈ transverseSide (commonAxes e) x, outside e y.val = u := by
  classical
  obtain ⟨f, hfL, hfR⟩ := exists_split e l r (hP.disjoint_blocks hL hS hLS)
    (hP.disjoint_blocks hR hS hRS) (hP.disjoint_blocks hL hR hLR) hcover
  obtain ⟨aL, aR, kL, kR, product, height⟩ := leaf_partition_star_product e l r hC h hP
    hS hL hR hLS hRS hLR hcover hx hprivate
  let A := splitCut f
  let c := pack f aL aR
  have complement : Aᶜ = univ.image fun i => f (.inr i) := by
    ext j
    obtain ⟨i,rfl⟩ := f.surjective j
    cases i with
    | inl i => simp [A, splitCut, f.injective.eq_iff]
    | inr i => simp [A, splitCut, f.injective.eq_iff]
  let emb : Fin 6 ↪ Fin 9 := ⟨fun j => e (.inr j), e.injective.comp Sum.inr_injective⟩
  have mappedL : A.map emb = commonAxes l := by
    simp [A, splitCut, commonAxes, emb, map_eq_image, image_image, Function.comp_def, hfL]
  have mappedR : Aᶜ.map emb = commonAxes r := by
    rw [complement]
    simp [commonAxes, emb, map_eq_image, image_image, Function.comp_def, hfR]
  have encode_outside (y : Q 9) :
      encodePoint (outside e y) = pack f ((cubeBitVec 3).symm (inside l y))
        ((cubeBitVec 3).symm (inside r y)) := by
    rw [encode_eq_pack f]
    have left : (fun i => outside e y (f (.inl i))) = inside l y := by
      funext i
      exact congrArg y (hfL i)
    have right : (fun i => outside e y (f (.inr i))) = inside r y := by
      funext i
      exact congrArg y (hfR i)
    rw [left, right]
  have realize (u : Q 6) : Box A c (encodePoint u) ↔
      ∃ y ∈ transverseSide (commonAxes e) x, outside e y.val = u := by
    constructor
    · intro hu
      rw [encode_eq_pack f] at hu
      have hleaves := (box_pack_iff f _ _ _ _).mp hu
      obtain ⟨y,hy,hl,hr⟩ := (product _ _).mp hleaves
      refine ⟨y,hy,encodePoint.injective ?_⟩
      rw [encode_outside, encode_eq_pack f u, hl, hr]
    · rintro ⟨y,hy,rfl⟩
      rw [encode_outside]
      exact (box_pack_iff f _ _ _ _).mpr ((product _ _).mpr ⟨y,hy,rfl,rfl⟩)
  refine ⟨A,c,card_splitCut _,mappedL,mappedR,?_,realize⟩
  refine ⟨fun j => Sum.elim kL kR (f.symm j), ?_⟩
  intro v hv j
  obtain ⟨u,rfl⟩ := encodePoint.surjective v
  obtain ⟨y,hy,he⟩ := (realize u).mp hv
  subst u
  obtain ⟨i,rfl⟩ := f.surjective j
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hg y, encode_outside]
  cases i with
  | inl i =>
    rw [hfL, (height y hy i).1]
    simp only [c, mem_diff_pack_left, Sum.elim_inl]
    cases (aL ^^^ (cubeBitVec 3).symm (inside l y.val)).getLsbD i.val <;> simp
  | inr i =>
    rw [hfR, (height y hy i).2]
    simp only [c, mem_diff_pack_right, Sum.elim_inr]
    cases (aR ^^^ (cubeBitVec 3).symm (inside r y.val)).getLsbD i.val <;> simp

private theorem axes_cover_of_three_blocks {P : Partition} (hP : IsTriplePartition P)
    {S L R : Block} (hS : S ∈ P) (hL : L ∈ P) (hR : R ∈ P)
    (hLS : L ≠ S) (hRS : R ≠ S) (hLR : L ≠ R) :
    S ∪ L ∪ R = univ := by
  classical
  have leftDisj := hP.disjoint_blocks hL hS hLS
  have rightDisj := hP.disjoint_blocks hR hS hRS
  have otherDisj := hP.disjoint_blocks hL hR hLR
  have hall : Disjoint (S ∪ L) R := Finset.disjoint_union_left.mpr ⟨rightDisj.symm,otherDisj⟩
  apply eq_of_subset_of_card_le (subset_univ _)
  rw [card_union_of_disjoint hall, card_union_of_disjoint leftDisj.symm, card_univ,
    Fintype.card_fin, hP.block_card _ hS, hP.block_card _ hL, hP.block_card _ hR]

open scoped Classical in
/-- If one triple occurs in all row partitions of a connected induced cubic
component with a one-sided Laurent identity, every row partition is equal. -/
private theorem neighborPartition_eq_of_common_block
    {C : Finset (Q 9)} {b : Bool} {a : Side C b → Exponent}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hconn : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (h : LaurentIdentity a) (x y : Side C b) (S : Block)
    (shared : ∀ z : Side C b, S ∈ neighborPartition C z.val) :
    neighborPartition C x.val = neighborPartition C y.val := by
  classical
  have parts (z : Side C b) : IsTriplePartition (neighborPartition C z.val) :=
    isTriplePartition_neighborPartition hC h z
  obtain ⟨e,he⟩ := exists_chart S ((parts x).block_card _ (shared x))
  subst S
  let S := commonAxes e
  let emb : Fin 6 ↪ Fin 9 := ⟨fun j => e (.inr j), e.injective.comp Sum.inr_injective⟩
  let K := Quotient (transverseComponents (C := C) (b := b) S)
  let q : Side C b → K := Quotient.mk _
  have hcommon := Q9LaurentCommonTriple.uniqueCommonNeighbor_of_laurent (e := e) hC h
    (fun z => mem_image.mp (shared z))
  obtain ⟨g,hg⟩ := Q9LaurentCommonTriple.exists_projected_exponent h hcommon
  have available (i : K) : ∃ A c : Q9CutBoxRigidity.Point,
      A.card = 3 ∧
      (∀ z, q z = i → A.map emb ∈ neighborPartition C z.val ∧ A.map emb ≠ S ∧
        Aᶜ.map emb ∈ neighborPartition C z.val) ∧
      Q9CutBoxRigidity.HasHeight (g ∘ encodePoint.symm) A c ∧
      ∀ p : Q9CutBoxRigidity.Point, Q9CutBoxRigidity.Box A c p ↔
        ∃ z : Side C b, q z = i ∧ encodePoint (outside e z.val) = p := by
    obtain ⟨u, rfl⟩ := (Quotient.mk_surjective : Function.Surjective q) i
    let P := neighborPartition C u.val
    have hP : IsTriplePartition P := parts u
    have hS : S ∈ P := shared u
    obtain ⟨L,hL,hLS⟩ := exists_other hP hS
    obtain ⟨R,hR,hRS,hRL⟩ := exists_third_block hP hLS.symm
    obtain ⟨l,hl⟩ := exists_chart L (hP.block_card L hL)
    obtain ⟨r,hr⟩ := exists_chart R (hP.block_card R hR)
    have priv (z : Side C b) (T : Block) (hTP : T ∈ P) (hTS : T ≠ S)
        (hT : T ∈ neighborPartition C z.val) : neighborPartition C z.val = P :=
      eq_of_two_common_blocks (parts z) hP hT (shared z) hTP hS hTS
    have cover : S ∪ commonAxes l ∪ commonAxes r = univ := by
      rw [hl,hr]
      exact axes_cover_of_three_blocks hP hS hL hR hLS hRS hRL.symm
    obtain ⟨A,c,hA,hAL,hAR,hh,hbox⟩ :=
      exists_cut_box_of_private_transverse_blocks hC h e l r u hP hS
        (hl.symm ▸ hL) (hr.symm ▸ hR) (hl.symm ▸ hLS) (hr.symm ▸ hRS)
        (hl.symm ▸ hr.symm ▸ hRL.symm) cover rfl priv g
        (fun z k => congrFun (hg z) k)
    refine ⟨A,c,hA,?_,hh,?_⟩
    · intro z hz
      have hrel : (transverseComponents S).r u z := Quotient.exact hz.symm
      have heq := neighborPartition_eq_of_private_transverse_blocks priv rfl hrel
      rw [heq,show A.map emb = commonAxes l from hAL,
        show Aᶜ.map emb = commonAxes r from hAR,hl,hr]
      exact ⟨hL,hLS,hR⟩
    · intro p
      obtain ⟨v,rfl⟩ := encodePoint.surjective p
      rw [hbox]
      constructor
      · rintro ⟨z,hz,hzV⟩
        exact ⟨z,(Quotient.sound (mem_transverseSide.mp hz)).symm,congrArg encodePoint hzV⟩
      · rintro ⟨z,hz,hzV⟩
        exact ⟨z,mem_transverseSide.mpr (Quotient.exact hz.symm),encodePoint.injective hzV⟩
  choose cut center card props height ofbox using available
  have same := same_cut_of_realized_common_star_boxes hconn hcommon encodePoint cut center
    card height ofbox (fun z =>
      transverse_or_same_projection_of_partition (e := e) (x := z) (parts z) (shared z)) (q x) (q y)
  obtain ⟨hTx, hne, _⟩ := props (q x) x rfl
  obtain ⟨hTy,_,hTyc⟩ := props (q y) y rfl
  have hyT : (cut (q x)).map emb ∈ neighborPartition C y.val := by
    rcases same.2 with he | he
    · exact he.symm ▸ hTy
    · exact he.symm ▸ hTyc
  exact eq_of_two_common_blocks (parts x) (parts y) hTx (shared x) hyT (shared y) hne

open scoped Classical in
/-- A triple shared by all selected-side row partitions forces a constant
partition and order fifty-four in a connected induced cubic Laurent component. -/
theorem constant_partition_and_card_eq_fiftyFour_of_common_block
    {C : Finset (Q 9)} {b : Bool} {a : Side C b → Exponent}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hconn : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (h : LaurentIdentity a) (S : Block)
    (hshared : ∀ x : Side C b, S ∈ neighborPartition C x.val) :
    (∀ x y : Side C b, neighborPartition C x.val = neighborPartition C y.val) ∧
      C.card = 54 := by
  classical
  have hconst (x y : Side C b) :
      neighborPartition C x.val = neighborPartition C y.val :=
    neighborPartition_eq_of_common_block hC hconn h x y S hshared
  refine ⟨hconst, ?_⟩
  rcases card_eq_fiftyFour_or_seven_le_directionTypes hconn hC h with horder | hlarge
  · exact horder
  · rw [← blockTypes_partitionsOn hC] at hlarge
    obtain ⟨T, hT⟩ := card_pos.mp (show 0 < (blockTypes (partitionsOn C b)).card by omega)
    change T ∈ (partitionsOn C b).biUnion id at hT
    obtain ⟨P, hP, _⟩ := mem_biUnion.mp hT
    obtain ⟨x, _, _⟩ := mem_image.mp hP
    have hsubset : blockTypes (partitionsOn C b) ⊆ neighborPartition C x.val := by
      intro U hU
      change U ∈ (partitionsOn C b).biUnion id at hU
      obtain ⟨R, hR, hUR⟩ := mem_biUnion.mp hU
      obtain ⟨y, _, rfl⟩ := mem_image.mp hR
      exact hconst y x ▸ hUR
    have hsmall := card_le_card hsubset
    rw [(isTriplePartition_neighborPartition hC h x).card_eq] at hsmall
    omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions
