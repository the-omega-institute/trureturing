/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Every induced cubical once-subdivision of K3,3 has the translated six-coordinate grid normal form. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-! Coordinate cuts are classified from their six branch bits;
edge coverage then excludes mixed cuts. -/

set_option maxRecDepth 4096
set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity

open SimpleGraph BalancedCriticalSpectrum FifteenSliceStructure
open D5.S3.Combinatorics.Graph.Hypercube
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

private abbrev Triple := Fin 3
private abbrev Pattern := Option Triple × Option Triple

private def highBit (p : Pattern) (s : Bool) (i : Triple) : Bool :=
  decide ((if s then p.2 else p.1) = some i)

private def midBit (p : Pattern) (i j : Triple) : Bool :=
  highBit p false i || highBit p true j

private def Eligible (A B : Triple → Bool) : Prop :=
  ∀ i j, A i ≠ B j →
    (∀ k, k ≠ j → B k = A i) ∨ (∀ k, k ≠ i → A k = B j)

set_option maxHeartbeats 4000000 in
-- Small Boolean classification certificates are reduced by the kernel.
set_option maxSynthPendingDepth 16 in
private theorem high_classification :
    ∀ A B : Triple → Bool, Eligible A B →
      ∃ t : Bool, ∃ p : Pattern,
        (∀ i, A i = (t ^^ highBit p false i)) ∧
        (∀ j, B j = (t ^^ highBit p true j)) := by
  unfold Eligible highBit
  decide

set_option maxHeartbeats 4000000 in
-- Small Boolean classification certificates are reduced by the kernel.
set_option maxSynthPendingDepth 16 in
private theorem middle_forced :
    ∀ (t : Bool) (p : Pattern) (i j : Triple) (m : Bool),
      ((t ^^ highBit p false i) ≠ m →
        m = (t ^^ highBit p true j) ∧
        ∀ k, k ≠ j → (t ^^ highBit p true k) = (t ^^ highBit p false i)) →
      ((t ^^ highBit p true j) ≠ m →
        m = (t ^^ highBit p false i) ∧
        ∀ k, k ≠ i → (t ^^ highBit p false k) = (t ^^ highBit p true j)) →
      m = (t ^^ midBit p i j) := by
  rintro t ⟨u, v⟩ i j m
  fin_cases t <;> fin_cases u <;> fin_cases v <;>
    fin_cases i <;> fin_cases j <;> fin_cases m <;> decide

private theorem edge_cross {n : Nat} {x y : Q n}
    (h : (hypercube n).Adj x y) {k : Fin n} (hk : x k ≠ y k) :
    y = flip x k := by
  obtain ⟨r, rfl⟩ := adjacent_exists_flip h
  by_cases hr : k = r
  · subst r; rfl
  · exact (hk (by simp [BalancedCriticalSpectrum.flip, hr])).elim

private theorem edge_direction_unique {n : Nat} {x y : Q n}
    (h : (hypercube n).Adj x y) {k l : Fin n}
    (hk : x k ≠ y k) (hl : x l ≠ y l) : k = l := by
  rw [edge_cross h hk] at hl
  by_contra hkl
  exact hl (by simp [BalancedCriticalSpectrum.flip, Ne.symm hkl])

private theorem matching {n : Nat} {x y z : Q n}
    (hxy : (hypercube n).Adj x y) (hxz : (hypercube n).Adj x z)
    (hyz : y ≠ z) {k : Fin n} (hk : x k ≠ y k) : x k = z k := by
  by_contra hz
  exact hyz ((edge_cross hxy hk).trans (edge_cross hxz hz).symm)

private theorem flip_adj {n : Nat} {x y : Q n}
    (h : (hypercube n).Adj x y) (k : Fin n) :
    (hypercube n).Adj (flip x k) (flip y k) := by
  change (Finset.univ.filter (fun i => flip x k i ≠ flip y k i)).card = 1
  change (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 at h
  convert h using 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i = k
  · subst i; simp
  · simp only [BalancedCriticalSpectrum.flip, Function.update_of_ne hi]

private theorem separated {n : Nat} {x y z w : Q n}
    (hxy : (hypercube n).Adj x y) (hzw : (hypercube n).Adj z w)
    (hxz : (hypercube n).Adj x z) (hn : ¬ (hypercube n).Adj y w)
    {k : Fin n} (hk : x k ≠ y k) : z k = w k := by
  by_contra hw
  apply hn
  rw [edge_cross hxy hk, edge_cross hzw hw]
  exact flip_adj hxz k

private def CutConstraints (A B : Triple → Bool) (M : Triple → Triple → Bool) : Prop :=
  (∀ i j, A i ≠ M i j → M i j = B j ∧ ∀ k, k ≠ j → B k = A i) ∧
  (∀ i j, B j ≠ M i j → M i j = A i ∧ ∀ k, k ≠ i → A k = B j)

private theorem classify_cut {A B : Triple → Bool} {M : Triple → Triple → Bool}
    (h : CutConstraints A B M) :
    ∃ t : Bool, ∃ p : Pattern,
      (∀ i, A i = (t ^^ highBit p false i)) ∧
      (∀ j, B j = (t ^^ highBit p true j)) ∧
      (∀ i j, M i j = (t ^^ midBit p i j)) := by
  have he : Eligible A B := by
    intro i j hij
    by_cases hm : A i = M i j
    · right
      exact (h.2 i j (by simpa [← hm] using Ne.symm hij)).2
    · left
      exact (h.1 i j hm).2
  obtain ⟨t, p, ha, hb⟩ := high_classification A B he
  refine ⟨t, p, ha, hb, ?_⟩
  intro i j
  apply middle_forced t p i j (M i j)
  · simpa only [← ha, ← hb] using h.1 i j
  · simpa only [← ha, ← hb] using h.2 i j

private def starPattern (h : Bool × Triple) : Pattern :=
  if h.1 then (none, some h.2) else (some h.2, none)

set_option maxHeartbeats 4000000 in
-- Small Boolean classification certificates are reduced by the kernel.
set_option maxSynthPendingDepth 16 in
private theorem crossing_bits : ∀ (t : Bool) (p : Pattern) (i j : Triple),
    (((t ^^ highBit p false i) ≠ (t ^^ midBit p i j)) ↔
      p.2 = some j ∧ p.1 ≠ some i) ∧
    (((t ^^ highBit p true j) ≠ (t ^^ midBit p i j)) ↔
      p.1 = some i ∧ p.2 ≠ some j) := by
  unfold midBit highBit
  decide

private theorem third_index : ∀ (j : Triple) (o : Option Triple),
    ∃ k : Triple, k ≠ j ∧ o ≠ some k := by decide

attribute [local instance] Classical.propDecidable

private structure Labels {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) where
  A : Triple → V
  B : Triple → V
  M : Triple → Triple → V
  high_inj : Function.Injective (fun h : Bool × Triple => if h.1 then B h.2 else A h.2)
  neighbors : ∀ i j v, G.Adj (M i j) v ↔ v = A i ∨ v = B j
  row_inj : ∀ i, Function.Injective (M i)
  col_inj : ∀ j, Function.Injective (fun i => M i j)
  cover : ∀ v, (∃ i, v = A i) ∨ (∃ j, v = B j) ∨ ∃ i j, v = M i j

private theorem get_labels {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (h : IsK33Subdivision G) : Nonempty (Labels G) := by
  classical
  obtain ⟨L, R, hpart, hcover, _, _, _, hdeg, A, B, hA, hB, hdis, hAB, hpair, hmid⟩ := h
  let ea : Triple ≃ A := (Finset.equivFinOfCardEq hA).symm
  let eb : Triple ≃ B := (Finset.equivFinOfCardEq hB).symm
  let a (i : Triple) : V := (ea i).val.val
  let b (j : Triple) : V := (eb j).val.val
  have ha (i : Triple) : (ea i).val ∈ A := (ea i).property
  have hb (j : Triple) : (eb j).val ∈ B := (eb j).property
  have hai : Function.Injective a := fun i j hij =>
    ea.injective (Subtype.ext (Subtype.ext hij))
  have hbi : Function.Injective b := fun i j hij =>
    eb.injective (Subtype.ext (Subtype.ext hij))
  have hab (i j : Triple) : a i ≠ b j := by
    intro hij
    exact Finset.disjoint_left.mp hdis (ha i)
      (by convert hb j using 1; exact Subtype.ext hij)
  have hp (i j : Triple) : ∃! m, m ∈ R ∧ G.Adj (a i) m ∧ G.Adj (b j) m :=
    hpair (ea i).val (ha i) (eb j).val (hb j)
  choose m hm using fun i j => (hp i j).exists
  have hn (i j : Triple) : G.neighborFinset (m i j) = {a i, b j} := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      have hsub : ({a i, b j} : Finset V) ⊆ G.neighborFinset (m i j) := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_neighborFinset]
        exact ⟨(hm i j).2.1.symm, (hm i j).2.2.symm⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        simp [card_neighborFinset_eq_degree, hdeg _ (hm i j).1, hab i j])
      exact heq.symm.subset hv
    · simp [card_neighborFinset_eq_degree, hdeg _ (hm i j).1, hab i j]
  have hrow (i : Triple) : Function.Injective (m i) := by
    intro j k hjk
    have hx : b j ∈ ({a i, b k} : Finset V) := by
      rw [← hn i k, ← hjk, hn i j]; simp
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact (hab i j hx.symm).elim
    · exact hbi (Finset.mem_singleton.mp hx)
  have hcol (j : Triple) : Function.Injective (fun i => m i j) := by
    intro i k hik
    change m i j = m k j at hik
    have hx : a i ∈ ({a k, b j} : Finset V) := by
      rw [← hn k j, ← hik, hn i j]; simp
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact hai hx
    · exact (hab i j (Finset.mem_singleton.mp hx)).elim
  refine ⟨{ A := a
            B := b
            M := m
            neighbors := by
              intro i j v
              rw [← G.mem_neighborFinset, hn]
              simp
            row_inj := hrow
            col_inj := hcol
            high_inj := ?_
            cover := ?_ }⟩
  · rintro ⟨s, i⟩ ⟨t, j⟩ hij
    cases s <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] at hij
    · exact Prod.ext rfl (hai hij)
    · exact (hab i j hij).elim
    · exact (hab j i hij.symm).elim
    · exact Prod.ext rfl (hbi hij)
  · intro v
    have hv : v ∈ L ∨ v ∈ R := by
      have := Finset.mem_univ v
      rw [← hcover] at this
      exact Finset.mem_union.mp this
    rcases hv with hv | hv
    · have hvAB : (⟨v, hv⟩ : L) ∈ A ∨ (⟨v, hv⟩ : L) ∈ B := by
        rw [← Finset.mem_union, hAB]; exact Finset.mem_univ _
      rcases hvAB with hva | hvb
      · obtain ⟨i, hi⟩ := ea.surjective ⟨⟨v, hv⟩, hva⟩
        exact Or.inl ⟨i, (congrArg (fun x : A => x.val.val) hi).symm⟩
      · obtain ⟨j, hj⟩ := eb.surjective ⟨⟨v, hv⟩, hvb⟩
        exact Or.inr (Or.inl ⟨j, (congrArg (fun x : B => x.val.val) hj).symm⟩)
    · obtain ⟨x, hx, y, hy, hn⟩ := hmid v hv
      obtain ⟨i, hi⟩ := ea.surjective ⟨x, hx⟩
      obtain ⟨j, hj⟩ := eb.surjective ⟨y, hy⟩
      have hxa : a i = x.val := congrArg (fun x : A => x.val.val) hi
      have hyb : b j = y.val := congrArg (fun x : B => x.val.val) hj
      right; right; refine ⟨i, j, (hp i j).unique ?_ (hm i j)⟩
      refine ⟨hv, ?_, ?_⟩
      · apply Adj.symm; rw [← G.mem_neighborFinset, hn]; simp [hxa]
      · apply Adj.symm; rw [← G.mem_neighborFinset, hn]; simp [hyb]

private theorem labels_cut {n : Nat} {C : Finset (Q n)}
    (l : Labels ((hypercube n).induce (C : Set (Q n)))) (k : Fin n) :
    CutConstraints (fun i => (l.A i).val k) (fun j => (l.B j).val k)
      (fun i j => (l.M i j).val k) := by
  have hA (i j : Triple) : (hypercube n).Adj (l.A i).val (l.M i j).val :=
    ((l.neighbors i j (l.A i)).mpr (Or.inl rfl)).symm
  have hB (i j : Triple) : (hypercube n).Adj (l.B j).val (l.M i j).val :=
    ((l.neighbors i j (l.B j)).mpr (Or.inr rfl)).symm
  have hab (i j : Triple) : (l.A i).val ≠ (l.B j).val := by
    intro h
    have := @l.high_inj (false, i) (true, j) (show (if false then l.B i else l.A i) =
      (if true then l.B j else l.A j) from Subtype.ext h)
    cases congrArg Prod.fst this
  have hnA (i j r : Triple) (hr : r ≠ i) :
      ¬ (hypercube n).Adj (l.A r).val (l.M i j).val := by
    intro h
    have hm := (l.neighbors i j (l.A r)).mp h.symm
    rcases hm with hm | hm
    · have hh := @l.high_inj (false, r) (false, i) (show (if false then l.B r else l.A r) =
        (if false then l.B i else l.A i) from hm)
      exact hr (congrArg Prod.snd hh)
    · exact hab r j (congrArg Subtype.val hm)
  have hnB (i j r : Triple) (hr : r ≠ j) :
      ¬ (hypercube n).Adj (l.B r).val (l.M i j).val := by
    intro h
    have hm := (l.neighbors i j (l.B r)).mp h.symm
    rcases hm with hm | hm
    · exact hab i r (congrArg Subtype.val hm).symm
    · have hh := @l.high_inj (true, r) (true, j) (show (if true then l.B r else l.A r) =
        (if true then l.B j else l.A j) from hm)
      exact hr (congrArg Prod.snd hh)
  constructor
  · intro i j hij
    refine ⟨matching (hA i j).symm (hB i j).symm (hab i j) (Ne.symm hij), ?_⟩
    intro r hr
    have h1 := matching (hA i j) (hA i r)
      (fun h => hr (l.row_inj i (Subtype.ext h)).symm) hij
    have h2 := separated (hA i j) (hB i r).symm (hA i r)
      (fun h => hnB i j r hr h.symm) hij
    exact h2.symm.trans h1.symm
  · intro i j hij
    refine ⟨matching (hB i j).symm (hA i j).symm (Ne.symm (hab i j)) (Ne.symm hij), ?_⟩
    intro r hr
    have h1 := matching (hB i j) (hB r j)
      (fun h => hr (l.col_inj j (Subtype.ext h)).symm) hij
    have h2 := separated (hB i j) (hA r j).symm (hB r j)
      (fun h => hnA i j r hr h.symm) hij
    exact h2.symm.trans h1.symm

private theorem edge_has_cross {n : Nat} {x y : Q n}
    (h : (hypercube n).Adj x y) : ∃ k, x k ≠ y k := by
  classical
  by_contra hn
  push Not at hn
  exact h.ne (funext hn)

private theorem coordinate_stars {n : Nat} {C : Finset (Q n)}
    (l : Labels ((hypercube n).induce (C : Set (Q n)))) :
    ∃ (d : Bool × Triple → Fin n) (t : Fin n → Bool) (p : Fin n → Pattern),
      Function.Injective d ∧
      (∀ k h, p k = starPattern h ↔ k = d h) ∧
      (∀ k, (p k).1 = none ∨ (p k).2 = none) ∧
      (∀ k i, (l.A i).val k = (t k ^^ highBit (p k) false i)) ∧
      (∀ k j, (l.B j).val k = (t k ^^ highBit (p k) true j)) ∧
      (∀ k i j, (l.M i j).val k = (t k ^^ midBit (p k) i j)) := by
  classical
  choose t p ha hb hm using fun k => classify_cut (labels_cut l k)
  have hA (i j : Triple) : (hypercube n).Adj (l.A i).val (l.M i j).val :=
    ((l.neighbors i j (l.A i)).mpr (Or.inl rfl)).symm
  have hB (i j : Triple) : (hypercube n).Adj (l.B j).val (l.M i j).val :=
    ((l.neighbors i j (l.B j)).mpr (Or.inr rfl)).symm
  have ca (k : Fin n) (i j : Triple) :
      (l.A i).val k ≠ (l.M i j).val k ↔ (p k).2 = some j ∧ (p k).1 ≠ some i := by
    rw [ha, hm]; exact (crossing_bits (t k) (p k) i j).1
  have cb (k : Fin n) (i j : Triple) :
      (l.B j).val k ≠ (l.M i j).val k ↔ (p k).1 = some i ∧ (p k).2 ≠ some j := by
    rw [hb, hm]; exact (crossing_bits (t k) (p k) i j).2
  have noMixed (k : Fin n) : (p k).1 = none ∨ (p k).2 = none := by
    cases hi : (p k).1 with
    | none => exact Or.inl rfl
    | some i =>
      cases hj : (p k).2 with
      | none => exact Or.inr rfl
      | some j =>
        obtain ⟨r, hr⟩ := edge_has_cross (hB i j)
        obtain ⟨hr1, hr2⟩ := (cb r i j).mp hr
        obtain ⟨q, hqj, hrq⟩ := third_index j (p r).2
        have hkq := (cb k i q).mpr ⟨hi, by simpa [hj] using hqj.symm⟩
        have hrq' := (cb r i q).mpr ⟨hr1, hrq⟩
        have hkr := edge_direction_unique (hB i q) hkq hrq'
        subst r
        exact (hr2 hj).elim
  have existsStar (h : Bool × Triple) : ∃ k, p k = starPattern h := by
    rcases h with ⟨s, i⟩
    cases s
    · obtain ⟨k, hk⟩ := edge_has_cross (hB i 0)
      have hki := (cb k i 0).mp hk
      have hkn : (p k).2 = none := (noMixed k).resolve_left (by simp [hki.1])
      exact ⟨k, Prod.ext hki.1 hkn⟩
    · obtain ⟨k, hk⟩ := edge_has_cross (hA 0 i)
      have hki := (ca k 0 i).mp hk
      have hkn : (p k).1 = none := (noMixed k).resolve_right (by simp [hki.1])
      exact ⟨k, Prod.ext hkn hki.1⟩
  choose d hd using existsStar
  have uniqueStar (h : Bool × Triple) (k r : Fin n)
      (hk : p k = starPattern h) (hr : p r = starPattern h) : k = r := by
    rcases h with ⟨s, i⟩
    cases s
    · apply edge_direction_unique (hB i 0)
      · apply (cb k i 0).mpr; simp [hk, starPattern]
      · apply (cb r i 0).mpr; simp [hr, starPattern]
    · apply edge_direction_unique (hA 0 i)
      · apply (ca k 0 i).mpr; simp [hk, starPattern]
      · apply (ca r 0 i).mpr; simp [hr, starPattern]
  refine ⟨d, t, p, ?_, ?_, noMixed, ha, hb, hm⟩
  · intro h g heq
    have hh : starPattern h = starPattern g := (hd h).symm.trans (heq ▸ hd g)
    rcases h with ⟨s, i⟩; rcases g with ⟨r, j⟩
    cases s <;> cases r <;> simp_all [starPattern]
  · intro k h
    constructor
    · exact fun hk => uniqueStar h k (d h) hk (hd h)
    · intro hk; rw [hk]; exact hd h

/-- The six branch vertices in coordinates indexed by the six branch stars.
The distinguished branch `(false,0)` is exactly the translated root. -/
def gridHigh {n : Nat} (X : Q n) (d : Bool × Fin 3 → Fin n)
    (h : Bool × Fin 3) : Q n :=
  flip (flip X (d (false, 0))) (d h)

/-- The middle on the subdivided edge from branch `(false,i)` to `(true,j)`. -/
def gridMiddle {n : Nat} (X : Q n) (d : Bool × Fin 3 → Fin n)
    (ij : Fin 3 × Fin 3) : Q n :=
  flip (gridHigh X d (false, ij.1)) (d (true, ij.2))

/-- All six branch vertices and all nine middle vertices, with no other points. -/
def gridSupport {n : Nat} (X : Q n) (d : Bool × Fin 3 → Fin n) : Finset (Q n) :=
  Finset.univ.image (gridHigh X d) ∪ Finset.univ.image (gridMiddle X d)

private theorem flip_value {n : Nat} (x : Q n) (i k : Fin n) :
    flip x i k = (x k ^^ decide (k = i)) := by
  by_cases h : k = i
  · subst k; simp
  · simp [BalancedCriticalSpectrum.flip, h]

private theorem normal_labels {n : Nat} {C : Finset (Q n)}
    (l : Labels ((hypercube n).induce (C : Set (Q n)))) :
    ∃ d : Bool × Fin 3 → Fin n, Function.Injective d ∧
      (∀ i, (l.A i).val = gridHigh (l.A 0).val d (false, i)) ∧
      (∀ j, (l.B j).val = gridHigh (l.A 0).val d (true, j)) ∧
      (∀ i j, (l.M i j).val = gridMiddle (l.A 0).val d (i, j)) := by
  classical
  obtain ⟨d, t, p, hd, hs, hn, ha, hb, hm⟩ := coordinate_stars l
  have bits (k : Fin n) (h : Bool × Triple) :
      highBit (p k) h.1 h.2 = decide (k = d h) := by
    have he : highBit (p k) h.1 h.2 = true ↔ p k = starPattern h := by
      rcases h with ⟨s, i⟩
      rcases hn k with hn | hn
      · cases s <;> simp [highBit, starPattern, hn, Prod.ext_iff]
      · cases s <;> simp [highBit, starPattern, hn, Prod.ext_iff]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using he.trans (hs k h))
  have hH (s : Bool) (i : Triple) :
      (if s then l.B i else l.A i).val = gridHigh (l.A 0).val d (s, i) := by
    funext k
    simp only [gridHigh, flip_value, ← bits k (false, 0), ← bits k (s, i), ha]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, ha, hb]
    all_goals simp
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · exact hH false
  · exact hH true
  · intro i j
    funext k
    rw [hm]
    simp only [midBit, gridMiddle, flip_value, ← hH false i,
      Bool.false_eq_true, ↓reduceIte, ha, ← bits k (true, j)]
    have hnbit : ¬ (highBit (p k) false i = true ∧ highBit (p k) true j = true) := by
      rw [bits k (false, i), bits k (true, j)]
      simp only [decide_eq_true_eq]
      rintro ⟨hki, hkj⟩
      have he := hd (hki.symm.trans hkj)
      cases congrArg Prod.fst he
    cases hi : highBit (p k) false i <;> cases hj : highBit (p k) true j
    all_goals first | exact (hnbit ⟨hi, hj⟩).elim | cases t k <;> rfl

/-- Every actual induced cubical once-subdivision of K3,3 has precisely the
translated six-direction grid support. All remaining coordinates are fixed. -/
theorem cubical_subdivision_normal_form {n : Nat} (C : Finset (Q n))
    (h : IsK33Subdivision ((hypercube n).induce (C : Set (Q n)))) :
    ∃ (X : Q n) (d : Bool × Fin 3 → Fin n), Function.Injective d ∧
      C = gridSupport X d ∧
      ∀ k : Fin n, k ∉ Set.range d → ∀ x ∈ C, x k = X k := by
  classical
  obtain ⟨l⟩ := get_labels h
  obtain ⟨d, hd, ha, hb, hm⟩ := normal_labels l
  have hC : C = gridSupport (l.A 0).val d := by
    ext x
    constructor
    · intro hx
      rcases l.cover ⟨x, hx⟩ with ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨i, j, hij⟩
      · rw [show x = gridHigh (l.A 0).val d (false, i) from
          (congrArg Subtype.val hi).trans (ha i)]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(false, i), Finset.mem_univ _, rfl⟩)
      · rw [show x = gridHigh (l.A 0).val d (true, j) from
          (congrArg Subtype.val hj).trans (hb j)]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(true, j), Finset.mem_univ _, rfl⟩)
      · rw [show x = gridMiddle (l.A 0).val d (i, j) from
          (congrArg Subtype.val hij).trans (hm i j)]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨⟨s, i⟩, _, rfl⟩ := Finset.mem_image.mp hx
        cases s
        · rw [← ha]; exact (l.A i).property
        · rw [← hb]; exact (l.B i).property
      · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hx
        rw [← hm]; exact (l.M i j).property
  refine ⟨(l.A 0).val, d, hd, hC, ?_⟩
  intro k hk x hx
  have hne (h : Bool × Fin 3) : k ≠ d h := fun he => hk ⟨h, he.symm⟩
  rw [hC] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hx
    simp [gridHigh, BalancedCriticalSpectrum.flip, hne]
  · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hx
    simp [gridMiddle, gridHigh, BalancedCriticalSpectrum.flip, hne]

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity
