/- GID: D5/S3/Combinatorics/OrderedTrees/LeafGapCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrderedTrees/LeafGapCount
   mirror-E: none(waiver:ordered-tree-leaf-pruning)
   anchors: [D5/S3/Combinatorics/OrderedTrees/LeafPruning]
   utility: none
   digest: Ordered leaf-gap compositions give a finite binomial sum for every actual tree count. -/

import D5.S3.Combinatorics.OrderedTrees.LeafPruning
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Sym.NatCard
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin

/-! Counting the ordered leaf-gap decorations of the pruned skeletons. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.OrderedTrees.LeafPruning

mutual
private def Decoration.gaps : Decoration → List ℕ
  | .tip n => [n]
  | .branch n t f => n :: (t.gaps ++ f.forestGaps)

private def DecorationForest.forestGaps : DecorationForest → List ℕ
  | .last n => [n]
  | .more n t f => n :: (t.gaps ++ f.forestGaps)
end

mutual
private def Tree.shapeSlots : Tree → ℕ
  | .node .nil => 1
  | .node (.cons t f) => 1 + t.shapeSlots + f.forestShapeSlots

private def Forest.forestShapeSlots : Forest → ℕ
  | .nil => 1
  | .cons t f => 1 + t.shapeSlots + f.forestShapeSlots
end

mutual
private theorem gap_stats (d : Decoration) :
    d.gaps.length = d.slots ∧ d.gaps.sum = d.gapTotal ∧ d.slots = d.skeleton.shapeSlots := by
  cases d with
  | tip n => simp [Decoration.gaps, Decoration.gapTotal, Decoration.slots,
      Decoration.skeleton, Tree.shapeSlots]
  | branch n t f =>
    obtain ⟨ht₁, ht₂, ht₃⟩ := gap_stats t
    obtain ⟨hf₁, hf₂, hf₃⟩ := forest_gap_stats f
    simp [Decoration.gaps, Decoration.gapTotal, Decoration.slots, Decoration.skeleton,
      Tree.shapeSlots, ht₁, ht₂, ht₃, hf₁, hf₂, hf₃, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm]

private theorem forest_gap_stats (d : DecorationForest) :
    d.forestGaps.length = d.forest_slots ∧ d.forestGaps.sum = d.gap_total_forest ∧
      d.forest_slots = d.skeleton_forest.forestShapeSlots := by
  cases d with
  | last n => simp [DecorationForest.forestGaps, DecorationForest.gap_total_forest,
      DecorationForest.forest_slots, DecorationForest.skeleton_forest, Forest.forestShapeSlots]
  | more n t f =>
    obtain ⟨ht₁, ht₂, ht₃⟩ := gap_stats t
    obtain ⟨hf₁, hf₂, hf₃⟩ := forest_gap_stats f
    simp [DecorationForest.forestGaps, DecorationForest.gap_total_forest,
      DecorationForest.forest_slots, DecorationForest.skeleton_forest, Forest.forestShapeSlots,
      ht₁, ht₂, ht₃, hf₁, hf₂, hf₃, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
end

mutual
private def Tree.readGaps : Tree → List ℕ → Decoration × List ℕ
  | .node .nil, xs => (.tip (xs.headD 0), xs.tail)
  | .node (.cons t f), xs =>
    let (dt, ys) := t.readGaps xs.tail
    let (df, zs) := f.readForestGaps ys
    (.branch (xs.headD 0) dt df, zs)

private def Forest.readForestGaps : Forest → List ℕ → DecorationForest × List ℕ
  | .nil, xs => (.last (xs.headD 0), xs.tail)
  | .cons t f, xs =>
    let (dt, ys) := t.readGaps xs.tail
    let (df, zs) := f.readForestGaps ys
    (.more (xs.headD 0) dt df, zs)
end

mutual
private theorem read_append (d : Decoration) (ys : List ℕ) :
    d.skeleton.readGaps (d.gaps ++ ys) = (d, ys) := by
  cases d with
  | tip n => simp [Decoration.skeleton, Decoration.gaps, Tree.readGaps]
  | branch n t f =>
    simp [Decoration.skeleton, Decoration.gaps, Tree.readGaps, List.append_assoc,
      read_append t, read_forest_append f]

private theorem read_forest_append (d : DecorationForest) (ys : List ℕ) :
    d.skeleton_forest.readForestGaps (d.forestGaps ++ ys) = (d, ys) := by
  cases d with
  | last n => simp [DecorationForest.skeleton_forest, DecorationForest.forestGaps,
      Forest.readForestGaps]
  | more n t f =>
    simp [DecorationForest.skeleton_forest, DecorationForest.forestGaps,
      Forest.readForestGaps, List.append_assoc, read_append t, read_forest_append f]
end

mutual
private theorem read_sound (s : Tree) (xs : List ℕ) (h : s.shapeSlots ≤ xs.length) :
    (s.readGaps xs).1.skeleton = s ∧ (s.readGaps xs).1.gaps ++ (s.readGaps xs).2 = xs := by
  cases s with
  | node ch =>
    cases ch with
    | nil =>
      cases xs with
      | nil => simp [Tree.shapeSlots] at h
      | cons n ns => simp [Tree.readGaps, Decoration.skeleton, Decoration.gaps]
    | cons t f =>
      cases xs with
      | nil => simp [Tree.shapeSlots] at h
      | cons n ns =>
        have ht : t.shapeSlots ≤ ns.length := by
          simp only [Tree.shapeSlots, List.length_cons] at h
          omega
        obtain ⟨ht₁, ht₂⟩ := read_sound t ns ht
        let pt := t.readGaps ns
        change pt.1.skeleton = t at ht₁
        change pt.1.gaps ++ pt.2 = ns at ht₂
        have hw := congrArg List.length ht₂
        simp only [List.length_append] at hw
        have hsz := (gap_stats pt.1).1.trans (gap_stats pt.1).2.2
        rw [ht₁] at hsz
        have hf : f.forestShapeSlots ≤ pt.2.length := by
          simp only [Tree.shapeSlots, List.length_cons] at h
          omega
        obtain ⟨hf₁, hf₂⟩ := read_forest_sound f pt.2 hf
        simp only [Tree.readGaps, List.headD_cons, List.tail_cons]
        change (Decoration.branch n pt.1 (f.readForestGaps pt.2).1).skeleton = _ ∧
          (Decoration.branch n pt.1 (f.readForestGaps pt.2).1).gaps ++
            (f.readForestGaps pt.2).2 = _
        simp [Decoration.skeleton, Decoration.gaps, ht₁, hf₁, List.append_assoc, hf₂, ht₂]

private theorem read_forest_sound (s : Forest) (xs : List ℕ) (h : s.forestShapeSlots ≤ xs.length) :
    (s.readForestGaps xs).1.skeleton_forest = s ∧
      (s.readForestGaps xs).1.forestGaps ++ (s.readForestGaps xs).2 = xs := by
  cases s with
  | nil =>
    cases xs with
    | nil => simp [Forest.forestShapeSlots] at h
    | cons n ns => simp [Forest.readForestGaps, DecorationForest.skeleton_forest,
        DecorationForest.forestGaps]
  | cons t f =>
    cases xs with
    | nil => simp [Forest.forestShapeSlots] at h
    | cons n ns =>
      have ht : t.shapeSlots ≤ ns.length := by
        simp only [Forest.forestShapeSlots, List.length_cons] at h
        omega
      obtain ⟨ht₁, ht₂⟩ := read_sound t ns ht
      let pt := t.readGaps ns
      change pt.1.skeleton = t at ht₁
      change pt.1.gaps ++ pt.2 = ns at ht₂
      have hw := congrArg List.length ht₂
      simp only [List.length_append] at hw
      have hsz := (gap_stats pt.1).1.trans (gap_stats pt.1).2.2
      rw [ht₁] at hsz
      have hf : f.forestShapeSlots ≤ pt.2.length := by
        simp only [Forest.forestShapeSlots, List.length_cons] at h
        omega
      obtain ⟨hf₁, hf₂⟩ := read_forest_sound f pt.2 hf
      simp only [Forest.readForestGaps, List.headD_cons, List.tail_cons]
      change (DecorationForest.more n pt.1 (f.readForestGaps pt.2).1).skeleton_forest = _ ∧
        (DecorationForest.more n pt.1 (f.readForestGaps pt.2).1).forestGaps ++
          (f.readForestGaps pt.2).2 = _
      simp [DecorationForest.skeleton_forest, DecorationForest.forestGaps, ht₁, hf₁,
        List.append_assoc, hf₂, ht₂]
end

private def gapFiber (s : Tree) (w : ℕ) :
    {d : Decoration // d.skeleton = s ∧ d.gapTotal = w} ≃
      {xs : List ℕ // xs.length = s.shapeSlots ∧ xs.sum = w} where
  toFun d := ⟨d.1.gaps, by
    obtain ⟨hl, hw, hs⟩ := gap_stats d.1
    exact ⟨by rw [hl, hs, d.2.1], hw.trans d.2.2⟩⟩
  invFun xs := ⟨(s.readGaps xs.1).1, by
    have h := read_sound s xs.1 (by rw [xs.2.1])
    have he := congrArg List.length h.2
    have hs := (gap_stats (s.readGaps xs.1).1).1.trans (gap_stats (s.readGaps xs.1).1).2.2
    rw [h.1] at hs
    simp only [List.length_append, hs, xs.2.1] at he
    have hnil : (s.readGaps xs.1).2 = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hnil, List.append_nil] at h
    exact ⟨h.1, (gap_stats _).2.1.symm.trans ((congrArg List.sum h.2).trans xs.2.2)⟩⟩
  left_inv d := by
    apply Subtype.ext
    change (s.readGaps d.1.gaps).1 = d.1
    obtain ⟨dt, he, _⟩ := d
    change (s.readGaps dt.gaps).1 = dt
    subst s
    simpa using congrArg Prod.fst (read_append dt [])
  right_inv xs := by
    apply Subtype.ext
    change (s.readGaps xs.1).1.gaps = xs.1
    have h := read_sound s xs.1 (by rw [xs.2.1])
    have he := congrArg List.length h.2
    have hs := (gap_stats (s.readGaps xs.1).1).1.trans (gap_stats (s.readGaps xs.1).1).2.2
    rw [h.1] at hs
    simp only [List.length_append, hs, xs.2.1] at he
    have hnil : (s.readGaps xs.1).2 = [] := List.length_eq_zero_iff.mp (by omega)
    simpa only [hnil, List.append_nil] using h.2

private abbrev Actual (n : ℕ) := {t : Tree // t.vertices = n ∧ t.height = t.internal}
private abbrev Part (n : ℕ) (u : Fin (n - 4)) (s : ↑(skeletons u)) :=
  {d : Decoration // d.skeleton = s.val ∧ d.gapTotal = n - (u.val + 5)}
private abbrev Pieces (n : ℕ) := Σ u : Fin (n - 4), Σ s : ↑(skeletons u), Part n u s

private theorem valid_of_mem (d : Decoration) (u : ℕ) (hs : d.skeleton ∈ skeletons u) :
    d.inflate.height = d.inflate.internal := by
  apply (height_eq_internal_iff _).mpr
  exact ⟨(decorationEquiv d).property, by
    rw [inflate_prune]
    exact ((skeletons_spec u).1 d.skeleton |>.mp hs).2⟩

private def piecesTree {n : ℕ} (p : Pieces n) : Actual n := by
  rcases p with ⟨u, s, d, hds, hdw⟩
  have hs : d.skeleton ∈ skeletons u := hds ▸ s.property
  have hw := (decoration_weight d u hs).1
  rw [hdw] at hw
  exact ⟨d.inflate, by have hu := u.isLt; omega, valid_of_mem d u hs⟩

private noncomputable def actualEquiv (n : ℕ) : Pieces n ≃ Actual n :=
  Equiv.ofBijective piecesTree (by
    constructor
    · rintro ⟨u, s, d, hd⟩ ⟨v, t, e, he⟩ h
      have heq : d.inflate = e.inflate := congrArg (fun a : Actual n => a.val) h
      have hde : d = e := decorationEquiv.injective (Subtype.ext heq)
      subst e
      have hvs := ((skeletons_spec u).1 s.val |>.mp s.property).1
      have hvt := ((skeletons_spec v).1 t.val |>.mp t.property).1
      rw [← hd.1] at hvs
      rw [← he.1] at hvt
      have huv : u = v := Fin.ext (by omega)
      subst v
      have hst : s = t := Subtype.ext (hd.1.symm.trans he.1)
      subst t
      rfl
    · rintro ⟨t, ht, hv⟩
      obtain ⟨hn, hpr⟩ := (height_eq_internal_iff t).mp hv
      let d := decorationEquiv.symm ⟨t, hn⟩
      have hd : d.inflate = t :=
        congrArg Subtype.val (decorationEquiv.apply_symm_apply ⟨t, hn⟩)
      have hsk : d.skeleton.vertices = d.skeleton.height + 1 := by
        rw [← inflate_prune, hd]
        exact hpr
      obtain ⟨b, l, r, hz, he⟩ := (excess_one_iff_fork _).mp hsk
      have hf : fork b l r ∈ skeletons (b + l + r) := by
        unfold skeletons
        by_cases hr : r = 0
        · subst r
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨l, Finset.mem_range.mpr (by omega), ?_⟩
          rw [show b + l + 0 - l = b by omega]
        · have hl : l = 0 := hz.resolve_right hr
          subst l
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨r - 1, Finset.mem_range.mpr (by omega), ?_⟩
          rw [show r - 1 + 1 = r by omega, show b + 0 + r - r = b by omega]
      rw [← he] at hf
      have hw := (decoration_weight d (b + l + r) hf).1
      rw [hd, ht] at hw
      let u : Fin (n - 4) := ⟨b + l + r, by omega⟩
      refine ⟨⟨u, ⟨d.skeleton, hf⟩, d, rfl, ?_⟩, Subtype.ext hd⟩
      change d.gapTotal = n - (b + l + r + 5)
      omega)

private noncomputable def listTuple (k w : ℕ) :
    {f : Fin k → ℕ // ∑ i, f i = w} ≃ {xs : List ℕ // xs.length = k ∧ xs.sum = w} :=
  Equiv.ofBijective
    (fun f ↦ ⟨List.ofFn f.val, List.length_ofFn, (List.sum_ofFn (f := f.val)).trans f.property⟩)
    (by
      constructor
      · intro f g h
        exact Subtype.ext (List.ofFn_injective (congrArg Subtype.val h))
      · rintro ⟨xs, hlen, hsum⟩
        subst k
        have hs := List.sum_ofFn (f := xs.get)
        rw [List.ofFn_get, hsum] at hs
        exact ⟨⟨xs.get, hs.symm⟩, Subtype.ext (List.ofFn_get _)⟩)

private noncomputable def partEquiv {n : ℕ} (u : Fin (n - 4)) (s : ↑(skeletons u)) :
    Part n u s ≃ {f : Fin (2 * u.val + 5) → ℕ // ∑ i, f i = n - (u.val + 5)} := by
  have hk : s.val.shapeSlots = 2 * u.val + 5 := by
    let d := (s.val.readGaps (List.replicate s.val.shapeSlots 0)).1
    have hs : d.skeleton = s.val := (read_sound _ _ (by simp)).1
    have hm : d.skeleton ∈ skeletons u := hs ▸ s.property
    rw [← hs, ← (gap_stats d).2.2]
    exact (decoration_weight d u hm).2
  exact (gapFiber s.val _).trans (by rw [hk]; exact (listTuple _ _).symm)

/-- Count all ordered trees in the source class by the size of their pruned skeleton. -/
theorem count_eq_sum (n : ℕ) :
    count n = ∑ u ∈ Finset.range (n - 4), (2 * u + 1) * (n + u - 1).choose (2 * u + 4) := by
  classical
  have hfinite (u : Fin (n - 4)) (s : ↑(skeletons u)) : Finite (Part n u s) := by
    let e := (partEquiv u s).trans (Sym.equivNatSumOfFintype _ _).symm
    exact Finite.of_injective e e.injective
  have hcard (u : Fin (n - 4)) (s : ↑(skeletons u)) :
      Nat.card (Part n u s) = (n + u.val - 1).choose (2 * u.val + 4) := by
    rw [Nat.card_congr (partEquiv u s),
      ← Nat.card_congr (Sym.equivNatSumOfFintype _ _),
      Sym.natCard_sym_eq_choose, Nat.card_fin]
    have hu := u.isLt
    have hn : 2 * u.val + 5 + (n - (u.val + 5)) - 1 =
        (2 * u.val + 4) + (n - (u.val + 5)) := by omega
    rw [hn, ← Nat.choose_symm_add]
    congr 1
    omega
  rw [(count_spec n).2]
  change Nat.card (Actual n) = _
  rw [← Nat.card_congr (actualEquiv n)]
  let _ (u : Fin (n - 4)) (s : ↑(skeletons u)) : Finite (Part n u s) := hfinite u s
  let _ (u : Fin (n - 4)) : Finite (Σ s : ↑(skeletons u), Part n u s) := by
    let _ (s : ↑(skeletons u)) : Fintype (Part n u s) := Fintype.ofFinite _
    infer_instance
  change Nat.card (Σ u : Fin (n - 4), Σ s : ↑(skeletons u), Part n u s) = _
  rw [Nat.card_sigma, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro u _
  rw [Nat.card_sigma]
  simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    (skeletons_spec _).2, nsmul_eq_mul]
  rfl

end D5.S3.Combinatorics.OrderedTrees.LeafPruning
