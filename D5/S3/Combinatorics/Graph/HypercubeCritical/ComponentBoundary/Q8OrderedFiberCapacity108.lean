/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q8OrderedFiberCapacity108
   generality: I
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Excludes closed neighborhood cap 108 by ordered fibre projections. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrderedFiberCapacityCertificate

/-! At higher levels, the projection omitting axis zero constrains the overlap
in each pair of consecutive patterns of the common marginal. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrderedFiberCapacity108

open Q8FourFiberCapacityCertificate (dropAxis neighborhoodCost ProjectionConstraints)
open Q8OrderedFiberCapacityCertificate (OrderedProjections)
open private Blocks glue overlap glue_complete zipWith_add_cross fastCost lookupCost_eq dropAxis_last
  singles singles_complete from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8FourFiberCapacityCertificate
open private key keepProjection sharedGroup checkGroup checkGroups checkedStep complete_of_step
  all_cons_true covers_bases from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrderedFiberCapacityCertificate

private def pairSums : List ℕ → List ℕ
  | a :: b :: rest => (a + b) :: pairSums rest
  | _ => []

private theorem pairSums_append (a b : List ℕ) (ha : a.length % 2 = 0) :
    pairSums (a ++ b) = pairSums a ++ pairSums b := by
  induction a using pairSums.induct with
  | case1 a c rest ih =>
    simp only [List.length_cons] at ha
    have hr : rest.length % 2 = 0 := by omega
    simp [pairSums, ih hr]
  | case2 a h =>
    cases a with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => simp at ha
      | cons y ys => exact (h x y ys rfl).elim

private theorem pairSums_eq_dropAxis (d : ℕ) (a : List ℕ)
    (ha : a.length = 2 ^ (d + 1)) : pairSums a = dropAxis d 0 a := by
  induction d generalizing a with
  | zero =>
    obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp ha
    rfl
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 ^ d * 2 := by rw [pow_succ]
    have ht : (a.take (2 ^ (d + 1))).length = 2 ^ (d + 1) := by
      rw [List.length_take, min_eq_left]
      rw [ha, pow_succ]
      omega
    have hd : (a.drop (2 ^ (d + 1))).length = 2 ^ (d + 1) := by
      rw [List.length_drop, ha, pow_succ (a := 2) (n := d + 1)]
      omega
    conv_lhs => rw [← List.take_append_drop (2 ^ (d + 1)) a]
    rw [pairSums_append _ _ (by omega), ih _ ht, ih _ hd]
    rfl

private theorem pairSums_length (a : List ℕ) : (pairSums a).length = a.length / 2 := by
  induction a using pairSums.induct with
  | case1 a b rest ih => simp only [pairSums, List.length_cons, ih]; omega
  | case2 a h =>
    cases a with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => simp [pairSums]
      | cons y ys => exact (h x y ys rfl).elim

private def block (base left right both : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (base + both - (left + right), left - both, right - both, both)

private def within (capacity : ℕ) (q : ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (max (max q.1 q.2.1) (max q.2.2.1 q.2.2.2) ≤ capacity)

private def consBlock (q : ℕ × ℕ × ℕ × ℕ) (t : Blocks) : Blocks :=
  (q.1 :: t.1, q.2.1 :: t.2.1, q.2.2.1 :: t.2.2.1, q.2.2.2 :: t.2.2.2)

private def glueBySums (capacity : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ → List Blocks
  | [], [], [], [] => [([], [], [], [])]
  | a₀ :: a₁ :: as, l₀ :: l₁ :: ls, r₀ :: r₁ :: rs, s :: ss =>
    (overlap a₀ l₀ r₀).flatMap fun b₀ =>
      let b₁ := s - b₀
      let q₀ := block a₀ l₀ r₀ b₀
      let q₁ := block a₁ l₁ r₁ b₁
      if b₀ ≤ s && (overlap a₁ l₁ r₁).contains b₁ &&
          within capacity q₀ && within capacity q₁ then
        (glueBySums capacity as ls rs ss).map fun t => consBlock q₀ (consBlock q₁ t)
      else []
  | _, _, _, _ => []

private theorem mem_glue_cons {capacity a l r : ℕ} {as ls rs : List ℕ} {t : Blocks}
    (ht : t ∈ glue capacity (a :: as) (l :: ls) (r :: rs)) :
    ∃ b ∈ overlap a l r, within capacity (block a l r b) = true ∧
      ∃ u ∈ glue capacity as ls rs, t = consBlock (block a l r b) u := by
  obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
  by_cases hc : within capacity (block a l r b) = true
  · refine ⟨b, hb, hc, ?_⟩
    have hc' := of_decide_eq_true hc
    change max (max (a + b - (l + r)) (l - b)) (max (r - b) b) ≤ capacity at hc'
    simp only [hc', ite_true] at ht
    obtain ⟨⟨p, q, s, t'⟩, hu, he⟩ := List.mem_map.mp ht
    exact ⟨(p, q, s, t'), hu, he.symm⟩
  · have hc' : ¬ max (max (a + b - (l + r)) (l - b)) (max (r - b) b) ≤ capacity :=
      fun hh => hc (decide_eq_true hh)
    simp only [ite_eq_right hc', List.not_mem_nil] at ht

private theorem glueBySums_complete (capacity : ℕ) (as ls rs : List ℕ)
    (ha : as.length % 2 = 0) (t : Blocks) (ht : t ∈ glue capacity as ls rs) :
    t ∈ glueBySums capacity as ls rs (pairSums t.2.2.2) := by
  induction as using pairSums.induct generalizing ls rs t with
  | case1 a₀ a₁ as ih =>
    match ls, rs with
    | l₀ :: l₁ :: ls, r₀ :: r₁ :: rs =>
      obtain ⟨b₀, hb₀, hc₀, u, hu, rfl⟩ := mem_glue_cons ht
      obtain ⟨b₁, hb₁, hc₁, v, hv, rfl⟩ := mem_glue_cons hu
      have hlen : as.length % 2 = 0 := by simp only [List.length_cons] at ha; omega
      have htail := ih ls rs hlen v hv
      have hsum : b₀ + b₁ - b₀ = b₁ := by omega
      have hle : b₀ ≤ b₀ + b₁ := by omega
      have bothField (a l r b : ℕ) : (block a l r b).2.2.2 = b := rfl
      simp only [consBlock, bothField, pairSums, glueBySums, List.mem_flatMap]
      refine ⟨b₀, hb₀, ?_⟩
      simp only [hsum, hle, decide_true, Bool.true_and, List.contains_iff_mem.mpr hb₁,
        hc₀, hc₁, ite_true]
      exact List.mem_map.mpr ⟨v, htail, rfl⟩
    | [], rs => cases rs <;> exact (List.not_mem_nil ht).elim
    | [_], [] => exact (List.not_mem_nil ht).elim
    | [_], _ :: rs =>
      obtain ⟨_, _, _, _, hmem, _⟩ := mem_glue_cons ht
      cases rs <;> exact (List.not_mem_nil hmem).elim
    | _ :: _ :: _, [] => exact (List.not_mem_nil ht).elim
    | _ :: _ :: _, [_] =>
      obtain ⟨_, _, _, _, hmem, _⟩ := mem_glue_cons ht
      exact (List.not_mem_nil hmem).elim
  | case2 as hf =>
    cases as with
    | nil =>
      cases ls <;> cases rs <;> simp [glue] at ht
      subst t
      simp [glueBySums, pairSums]
    | cons a as =>
      cases as with
      | nil => simp at ha
      | cons b as => exact (hf a b as rfl).elim

private theorem pairSums_zip (a b : List ℕ) :
    pairSums (List.zipWith (· + ·) a b) = List.zipWith (· + ·) (pairSums a) (pairSums b) := by
  induction a using pairSums.induct generalizing b with
  | case1 x y a ih =>
    cases b with
    | nil => rfl
    | cons z b =>
      cases b with
      | nil => rfl
      | cons w b => simp [pairSums, ih, add_left_comm, add_comm, add_assoc]
  | case2 a h =>
    cases a with
    | nil => rfl
    | cons x a =>
      cases a with
      | nil => cases b <;> rfl
      | cons y a => exact (h x y a rfl).elim

-- The key orders the index for the first projection. The subsequent tests
-- use the whole overlap array and check exact inclusion in the next level.
private def thirdKey (d : ℕ) (third : List ℕ) : ℕ × ℕ :=
  (key (dropAxis d d third), key (dropAxis d (d - 1) third))

private def thirdsAt (d : ℕ) (previous : List (List ℕ)) (base : List ℕ) : List (List ℕ) :=
  previous.filter fun t => dropAxis (d - 1) (d - 1) (dropAxis d d t) == pairSums base

private def candidate (d cap : ℕ) (keep : List ℕ → Bool) (t : Blocks) : Option (List ℕ) :=
  let (a, b, c, e) := t
  let counts := a ++ b ++ c ++ e
  if keep counts && decide (fastCost (d + 2) counts ≤ cap) then some counts else none

private inductive TableTree
  | empty
  | node (k : ℕ) (value : List ℕ) (lower upper : TableTree)

private def TableTree.values : TableTree → List (List ℕ)
  | .empty => []
  | .node _ value lower upper => value :: lower.values ++ upper.values

private def TableTree.find (k : ℕ) : TableTree → Option (List ℕ)
  | .empty => none
  | .node pivot value lower upper =>
    if k < pivot then lower.find k else if pivot < k then upper.find k else some value

private def TableTree.contains (tree : TableTree) (counts : List ℕ) : Bool :=
  tree.find (key counts) == some counts

private theorem TableTree.mem_values_of_find {tree : TableTree} {k : ℕ} {counts : List ℕ}
    (h : tree.find k = some counts) : counts ∈ tree.values := by
  induction tree with
  | empty => simp [TableTree.find] at h
  | node pivot value lower upper hl hu =>
    dsimp only [TableTree.find] at h
    split at h
    · simp only [TableTree.values, List.mem_cons, List.mem_append]
      exact Or.inl (Or.inr (hl h))
    · split at h
      · simp only [TableTree.values, List.mem_cons, List.mem_append]
        exact Or.inr (hu h)
      · have heq := Option.some.inj h
        simp [TableTree.values, heq]

private theorem TableTree.mem_values_of_contains {tree : TableTree} {counts : List ℕ}
    (h : tree.contains counts = true) : counts ∈ tree.values :=
  mem_values_of_find (beq_iff_eq.mp h)

private def keepRemaining (d : ℕ) (tree : TableTree) (counts : List ℕ) : Bool :=
  (List.range' 1 (d - 1)).all fun axis => tree.contains (dropAxis (d + 1) axis counts)

private theorem keepRemaining_of_children {d : ℕ} {tree : TableTree} {counts : List ℕ}
    (hcovered : tree.values.all tree.contains = true)
    (hchild : ∀ axis : Fin (d + 2), dropAxis (d + 1) axis counts ∈ tree.values) :
    keepRemaining d tree counts = true := by
  refine List.all_eq_true.mpr fun axis ha => ?_
  have hlt : axis < d + 2 := by
    have := List.mem_range'.mp ha
    omega
  exact List.all_eq_true.mp hcovered _ (hchild ⟨axis, hlt⟩)

private def checkTripleRows (d cap : ℕ) (keep : List ℕ → Bool) (base : List ℕ)
    (thirds : List ((ℕ × ℕ) × List ℕ)) (next : TableTree) (lefts rights : List (List ℕ)) : Bool :=
  let width := 2 ^ d
  lefts.all fun left =>
    let lk := key (pairSums left)
    rights.all fun right =>
      let rk := key (pairSums right)
      thirds.all fun (k, sums) =>
        (k != (lk, rk)) ||
          ((glueBySums (2 ^ (8 - (d + 2))) base (left.drop width) (right.drop width)
            sums).filterMap (candidate d cap keep)).all next.contains

private def thirdRows (d : ℕ) (thirds : List (List ℕ)) : List ((ℕ × ℕ) × List ℕ) :=
  thirds.map fun t => (thirdKey d t, t.drop (3 * 2 ^ (d - 1)))

private def checkTripleGroup (d cap : ℕ) (previous : List (List ℕ)) (next : TableTree) (base : List ℕ)
    (keep : List ℕ → Bool) : Bool :=
  let group := sharedGroup d previous base
  checkTripleRows d cap keep base (thirdRows d (thirdsAt d previous base)) next group group

private theorem checkedTripleStep {d cap : ℕ} (hd : 0 < d)
    {previous bases : List (List ℕ)} {next : TableTree} {keep : List ℕ → Bool}
    (hbase : ∀ t ∈ previous, dropAxis d d t ∈ bases)
    (hcheck : bases.all (fun base => checkTripleGroup d cap previous next base keep) = true)
    (hkeep : ∀ counts : List ℕ,
      (∀ axis : Fin (d + 2), dropAxis (d + 1) axis counts ∈ previous) → keep counts = true)
    (counts : List ℕ) (hlen : counts.length = 2 ^ (d + 2))
    (hcap : ∀ x ∈ counts, x ≤ 2 ^ (8 - (d + 2)))
    (hcost : neighborhoodCost (d + 2) counts ≤ cap)
    (_ : OrderedProjections (d + 2) counts)
    (hchild : ∀ axis : Fin (d + 2), dropAxis (d + 1) axis counts ∈ previous) :
    counts ∈ next.values := by
  let w := 2 ^ d
  let v := 2 ^ (d - 1)
  have hw : w = v + v := by
    change 2 ^ d = _
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := congrArg (2 ^ ·) (by omega)
      _ = v + v := by rw [pow_succ, Nat.mul_two]
  let low := counts.take (w + w)
  let high := counts.drop (w + w)
  let a := low.take w
  let b := low.drop w
  let c := high.take w
  let e := high.drop w
  have hlen' : counts.length = w + w + (w + w) := by
    rw [hlen, pow_succ (a := 2) (n := d + 1), pow_succ (a := 2) (n := d)]
    simp [w, Nat.mul_two]
  have hl : low.length = w + w := by simp [low, hlen']
  have hh : high.length = w + w := by simp [high, hlen']
  have ha : a.length = w := by simp [a, hl]
  have hb : b.length = w := by simp [b, hl]
  have hc : c.length = w := by simp [c, hh]
  have he : e.length = w := by simp [e, hh]
  have hsplit : a ++ b ++ c ++ e = counts := by
    rw [List.append_assoc (a ++ b) c e,
      show a ++ b = low from List.take_append_drop _ _,
      show c ++ e = high from List.take_append_drop _ _]
    exact List.take_append_drop _ _
  let add : List ℕ → List ℕ → List ℕ := List.zipWith (· + ·)
  let left := dropAxis (d + 1) (d + 1) counts
  let right := dropAxis (d + 1) d counts
  let base := dropAxis d d left
  have hw₂ : 2 ^ (d + 1) = w + w := by rw [pow_succ, Nat.mul_two]
  have htake : counts.take (2 ^ (d + 1)) = a ++ b := by
    rw [hw₂]; exact (List.take_append_drop _ _).symm
  have hdrop : counts.drop (2 ^ (d + 1)) = c ++ e := by
    rw [hw₂]; exact (List.take_append_drop _ _).symm
  have hleft : left = add a c ++ add b e := by
    unfold left
    rw [dropAxis_last, htake, hdrop, List.zipWith_append (ha.trans hc.symm)]
  have hright : right = add a b ++ add c e := by
    simp [right, dropAxis, htake, hdrop, dropAxis_last, List.take_left' ha, List.drop_left' ha,
      List.take_left' hc, List.drop_left' hc, add, w]
  have addLen (u v : List ℕ) (hu : u.length = w) (hv : v.length = w) :
      (add u v).length = w := by simp [add, List.length_zipWith, hu, hv]
  have hlenAC := addLen a c ha hc
  have hlenAB := addLen a b ha hb
  have hbaseVal : base = add (add a c) (add b e) := by
    dsimp only [base]
    rw [hleft, dropAxis_last, List.take_left' hlenAC, List.drop_left' hlenAC]
  have hcross : add (add a c) (add b e) = add (add a b) (add c e) :=
    zipWith_add_cross _ _ _ _
  have hbaseRight : dropAxis d d right = base := by
    rw [hright, dropAxis_last, List.take_left' hlenAB, List.drop_left' hlenAB, hbaseVal, hcross]
  let A := pairSums a
  let B := pairSums b
  let U := pairSums c
  let E := pairSums e
  have HA : A.length = v := by dsimp only [A]; rw [pairSums_length, ha, hw]; omega
  have HB : B.length = v := by dsimp only [B]; rw [pairSums_length, hb, hw]; omega
  have HU : U.length = v := by dsimp only [U]; rw [pairSums_length, hc, hw]; omega
  have HE : E.length = v := by dsimp only [E]; rw [pairSums_length, he, hw]; omega
  have halfLen (x y : List ℕ) (hx : x.length = v) (hy : y.length = v) :
      (x ++ y).length = w := by simp [hx, hy, hw]
  let third := dropAxis (d + 1) 0 counts
  have hthird : third = (A ++ B) ++ (U ++ E) := by
    dsimp only [third]
    rw [← pairSums_eq_dropAxis _ _ hlen, ← hsplit]
    simp only [List.append_assoc, pairSums_append a _ (by rw [ha, hw]; omega),
      pairSums_append b _ (by rw [hb, hw]; omega),
      pairSums_append c _ (by rw [hc, hw]; omega), A, B, U, E]
  have hfold (x y u t : List ℕ) (hx : x.length = w) (hy : y.length = w) :
      pairSums (add x y ++ add u t) = add (pairSums x) (pairSums y) ++
        add (pairSums u) (pairSums t) := by
    rw [pairSums_append _ _ (by simp only [add, List.length_zipWith, hx, hy, min_self, hw]; omega)]
    simp only [add, pairSums_zip]
  have hthirdLeft : dropAxis d d third = pairSums left := by
    rw [hthird, dropAxis_last, List.take_left' (halfLen A B HA HB),
      List.drop_left' (halfLen A B HA HB), List.zipWith_append (HA.trans HU.symm), hleft,
      hfold _ _ _ _ ha hc]
  have hthirdRight : dropAxis d (d - 1) third = pairSums right := by
    obtain ⟨n, hn⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    have hsplitAxis (x y : List ℕ) (hx : x.length = w) :
        dropAxis d (d - 1) (x ++ y) =
          dropAxis (d - 1) (d - 1) x ++ dropAxis (d - 1) (d - 1) y := by
      have hx' : x.length = 2 ^ (n + 1) := hx.trans (congrArg (2 ^ ·) hn)
      rw [show d - 1 = n by omega, hn]
      simp [dropAxis, List.take_left' hx', List.drop_left' hx']
    rw [hthird, hsplitAxis _ _ (halfLen A B HA HB), dropAxis_last, dropAxis_last,
      List.take_left' HA, List.drop_left' HA, List.take_left' HU, List.drop_left' HU,
      hright, hfold _ _ _ _ ha hb]
  have hlenAU : (add A U).length = v := by simp [add, List.length_zipWith, HA, HU]
  have hthirdBase : dropAxis (d - 1) (d - 1) (dropAxis d d third) = pairSums base := by
    rw [hthirdLeft, hleft, hfold _ _ _ _ ha hc, dropAxis_last, List.take_left' hlenAU,
      List.drop_left' hlenAU, hbaseVal]
    simp only [A, B, U, E, add, pairSums_zip]
  have hthirdSums : third.drop (3 * v) = E := by
    rw [hthird, ← List.append_assoc (A ++ B) U E]
    apply List.drop_left'
    simp [HA, HB, HU]
    omega
  have hmLeft : left ∈ previous := hchild ⟨d + 1, by omega⟩
  have hmRight : right ∈ previous := hchild ⟨d, by omega⟩
  have hmThird : third ∈ previous := hchild ⟨0, by omega⟩
  have hm : (a, b, c, e) ∈ glue (2 ^ (8 - (d + 2))) base (left.drop w) (right.drop w) := by
    rw [hbaseVal, hleft, hright, List.drop_left' hlenAC, List.drop_left' hlenAB, hcross]
    exact glue_complete _ _ _ _ _ (hb.trans ha.symm) (hc.trans ha.symm) (he.trans ha.symm)
      (hsplit.symm ▸ hcap)
  have hbaseLen : base.length = w := by
    rw [hbaseVal]
    exact addLen _ _ hlenAC (addLen b e hb he)
  have hglue := glueBySums_complete _ _ _ _ (by rw [hbaseLen, hw]; omega) _ hm
  have hrow : (thirdKey d third, third.drop (3 * v)) ∈ thirdRows d (thirdsAt d previous base) := by
    apply List.mem_map_of_mem
    exact List.mem_filter.mpr ⟨hmThird, by simp [hthirdBase]⟩
  have hg := List.all_eq_true.mp hcheck base (hbase _ hmLeft)
  have hL : left ∈ sharedGroup d previous base := by simp [sharedGroup, hmLeft, base]
  have hR : right ∈ sharedGroup d previous base := by simp [sharedGroup, hmRight, hbaseRight]
  have hres := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hg _ hL) _ hR) _ hrow
  have hthirdKey : thirdKey d third = (key (pairSums left), key (pairSums right)) := by
    rw [thirdKey, hthirdLeft, hthirdRight]
  rw [hthirdKey, hthirdSums] at hres
  simp only [bne_self_eq_false, Bool.false_or] at hres
  apply TableTree.mem_values_of_contains (List.all_eq_true.mp hres counts ?_)
  refine List.mem_filterMap.mpr ⟨(a, b, c, e), hglue, ?_⟩
  have hfast : fastCost (d + 2) counts ≤ cap := by
    rw [lookupCost_eq _ _ (by omega) hcap]
    exact hcost
  simp only [candidate, hsplit, hkeep _ hchild, hfast, decide_true, Bool.and_self, ite_true]

private abbrev level1 := singles 36 108

private def tree2 : TableTree :=
  .node 268567056
    [16, 2, 2, 16]
    (.node 201721611
      [12, 6, 7, 11]
      (.node 118230276
        [7, 12, 13, 4]
        (.node 101453826
          [6, 12, 16, 2]
          (.node 51384321
            [3, 16, 16, 1]
            (.node 51318531
              [3, 15, 15, 3]
              (.node 34607106
                [2, 16, 16, 2]
                .empty
                .empty)
              (.node 51318786
                [3, 15, 16, 2]
                .empty
                .empty))
            (.node 101453571
              [6, 12, 15, 3]
              (.node 101452806
                [6, 12, 12, 6]
                .empty
                .empty)
              .empty))
          (.node 118165251
            [7, 11, 15, 3]
            (.node 118164486
              [7, 11, 12, 6]
              (.node 118164231
                [7, 11, 11, 7]
                .empty
                .empty)
              .empty)
            (.node 118230021
              [7, 12, 12, 5]
              (.node 118165506
                [7, 11, 16, 2]
                .empty
                .empty)
              .empty)))
        (.node 185009931
          [11, 7, 7, 11]
          (.node 118295811
            [7, 13, 13, 3]
            (.node 118230786
              [7, 12, 15, 2]
              (.node 118230531
                [7, 12, 14, 3]
                .empty
                .empty)
              (.node 118231041
                [7, 12, 16, 1]
                .empty
                .empty))
            (.node 168561666
              [10, 12, 12, 2]
              (.node 118296066
                [7, 13, 14, 2]
                .empty
                .empty)
              .empty))
          (.node 185273346
            [11, 11, 12, 2]
            (.node 185011206
              [11, 7, 12, 6]
              (.node 185010951
                [11, 7, 11, 7]
                .empty
                .empty)
              .empty)
            (.node 201721356
              [12, 6, 6, 12]
              (.node 185338881
                [11, 12, 12, 1]
                .empty
                .empty)
              .empty))))
      (.node 218564871
        [13, 7, 9, 7]
        (.node 201788676
          [12, 7, 13, 4]
          (.node 201787911
            [12, 7, 10, 7]
            (.node 201722886
              [12, 6, 12, 6]
              (.node 201722631
                [12, 6, 11, 7]
                .empty
                .empty)
              (.node 201787146
                [12, 7, 7, 10]
                .empty
                .empty))
            (.node 201788421
              [12, 7, 12, 5]
              (.node 201788166
                [12, 7, 11, 6]
                .empty
                .empty)
              .empty))
          (.node 202050561
            [12, 11, 12, 1]
            (.node 202050306
              [12, 11, 11, 2]
              (.node 201985026
                [12, 10, 12, 2]
                .empty
                .empty)
              .empty)
            (.node 218564361
              [13, 7, 7, 9]
              (.node 202116096
                [12, 12, 12, 0]
                .empty
                .empty)
              .empty)))
        (.node 251856396
          [15, 3, 6, 12]
          (.node 235341576
            [14, 7, 7, 8]
            (.node 218696706
              [13, 9, 12, 2]
              (.node 218565636
                [13, 7, 12, 4]
                .empty
                .empty)
              .empty)
            (.node 251855631
              [15, 3, 3, 15]
              (.node 235341831
                [14, 7, 8, 7]
                .empty
                .empty)
              .empty))
          (.node 252053511
            [15, 6, 8, 7]
            (.node 252053256
              [15, 6, 7, 8]
              (.node 251856651
                [15, 3, 7, 11]
                .empty
                .empty)
              .empty)
            (.node 252119046
              [15, 7, 8, 6]
              (.node 252118791
                [15, 7, 7, 7]
                .empty
                .empty)
              .empty)))))
    (.node 285542151
      [17, 5, 7, 7]
      (.node 268765191
        [16, 5, 8, 7]
        (.node 268633611
          [16, 3, 6, 11]
          (.node 268632846
            [16, 3, 3, 14]
            (.node 268568076
              [16, 2, 6, 12]
              (.node 268567311
                [16, 2, 3, 15]
                .empty
                .empty)
              (.node 268568331
                [16, 2, 7, 11]
                .empty
                .empty))
            (.node 268633356
              [16, 3, 5, 12]
              (.node 268633101
                [16, 3, 4, 13]
                .empty
                .empty)
              .empty))
          (.node 268699401
            [16, 4, 7, 9]
            (.node 268698636
              [16, 4, 4, 12]
              (.node 268633866
                [16, 3, 7, 10]
                .empty
                .empty)
              .empty)
            (.node 268764936
              [16, 5, 7, 8]
              (.node 268699911
                [16, 4, 9, 7]
                .empty
                .empty)
              .empty)))
        (.node 268896516
          [16, 7, 9, 4]
          (.node 268830726
            [16, 6, 8, 6]
            (.node 268830471
              [16, 6, 7, 7]
              (.node 268830216
                [16, 6, 6, 8]
                .empty
                .empty)
              .empty)
            (.node 268896261
              [16, 7, 8, 5]
              (.node 268896006
                [16, 7, 7, 6]
                .empty
                .empty)
              .empty))
          (.node 285411081
            [17, 3, 7, 9]
            (.node 285410316
              [17, 3, 4, 12]
              (.node 269027586
                [16, 9, 9, 2]
                .empty
                .empty)
              .empty)
            (.node 285476871
              [17, 4, 8, 7]
              (.node 285476616
                [17, 4, 7, 8]
                .empty
                .empty)
              .empty))))
      (.node 302450436
        [18, 7, 7, 4]
        (.node 302253576
          [18, 4, 6, 8]
          (.node 285673476
            [17, 7, 8, 4]
            (.node 285607686
              [17, 6, 7, 6]
              (.node 285607431
                [17, 6, 6, 7]
                .empty
                .empty)
              (.node 285673221
                [17, 7, 7, 5]
                .empty
                .empty))
            (.node 302188296
              [18, 3, 7, 8]
              (.node 285739011
                [17, 8, 8, 3]
                .empty
                .empty)
              .empty))
          (.node 302319366
            [18, 5, 7, 6]
            (.node 302319111
              [18, 5, 6, 7]
              (.node 302253831
                [18, 4, 7, 7]
                .empty
                .empty)
              .empty)
            (.node 302384901
              [18, 6, 7, 5]
              (.node 302384646
                [18, 6, 6, 6]
                .empty
                .empty)
              .empty)))
        (.node 319096326
          [19, 5, 6, 6]
          (.node 319030536
            [19, 4, 5, 8]
            (.node 319030281
              [19, 4, 4, 9]
              (.node 318965256
                [19, 3, 6, 8]
                .empty
                .empty)
              .empty)
            (.node 319096071
              [19, 5, 5, 7]
              (.node 319030791
                [19, 4, 6, 7]
                .empty
                .empty)
              .empty))
          (.node 335807751
            [20, 4, 5, 7]
            (.node 335807496
              [20, 4, 4, 8]
              (.node 319161861
                [19, 6, 6, 5]
                .empty
                .empty)
              .empty)
            (.node 352584711
              [21, 4, 4, 7]
              (.node 335873286
                [20, 5, 5, 6]
                .empty
                .empty)
              .empty)))))

private abbrev level2 := tree2.values

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem coversKeys2 : level2.all tree2.contains = true := by

  decide +kernel

private def tree3 : TableTree :=
  .node 722265894146868741
    [10, 6, 1, 1, 6, 1, 6, 5]
    (.node 434035535242135041
      [6, 6, 1, 5, 10, 1, 6, 1]
      (.node 432352187235303936
        [6, 0, 6, 6, 10, 6, 2, 0]
        (.node 146659466740367616
          [2, 9, 10, 2, 10, 2, 1, 0]
          (.node 144126209130103296
            [2, 0, 10, 6, 10, 6, 2, 0]
            (.node 73751967327127041
              [1, 6, 5, 6, 6, 5, 6, 1]
              (.node 72350090068886016
                [1, 1, 10, 6, 10, 6, 2, 0]
                (.node 2825753641222656
                  [0, 10, 10, 2, 10, 2, 2, 0]
                  (.node 1695472800892416
                    [0, 6, 6, 6, 6, 6, 6, 0]
                    .empty
                    .empty)
                  (.node 72350090068885761
                    [1, 1, 10, 6, 10, 6, 1, 1]
                    .empty
                    .empty))
                (.node 73471591862109696
                  [1, 5, 6, 6, 6, 6, 6, 0]
                  (.node 73471591862109441
                    [1, 5, 6, 6, 6, 6, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 74601872702439936
                [1, 9, 10, 2, 10, 2, 2, 0]
                (.node 73753062543787521
                  [1, 6, 6, 5, 6, 5, 6, 1]
                  (.node 73753062527075841
                    [1, 6, 6, 5, 5, 6, 6, 1]
                    .empty
                    .empty)
                  (.node 73753062543853056
                    [1, 6, 6, 5, 6, 6, 6, 0]
                    .empty
                    .empty))
                (.node 144126209130103041
                  [2, 0, 10, 6, 10, 6, 1, 1]
                  (.node 74883343384183296
                    [1, 10, 10, 1, 10, 2, 2, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 144407679811846401
              [2, 1, 10, 5, 10, 6, 1, 1]
              (.node 144406584595186176
                [2, 1, 9, 6, 10, 6, 2, 0]
                (.node 144406584595120641
                  [2, 1, 9, 6, 10, 5, 2, 1]
                  (.node 144406584578408961
                    [2, 1, 9, 6, 9, 6, 2, 1]
                    .empty
                    .empty)
                  (.node 144406584595185921
                    [2, 1, 9, 6, 10, 6, 1, 1]
                    .empty
                    .empty))
                (.node 144407679811781121
                  [2, 1, 10, 5, 10, 5, 2, 1]
                  (.node 144407679795069441
                    [2, 1, 10, 5, 9, 6, 2, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 146377991763657216
                [2, 8, 10, 2, 10, 2, 2, 0]
                (.node 144407684106813441
                  [2, 1, 10, 6, 10, 6, 0, 1]
                  (.node 144407679811846656
                    [2, 1, 10, 5, 10, 6, 2, 0]
                    .empty
                    .empty)
                  (.node 144407684106813696
                    [2, 1, 10, 6, 10, 6, 1, 0]
                    .empty
                    .empty))
                (.node 146659462445400576
                  [2, 9, 10, 1, 10, 2, 2, 0]
                  (.node 146658367228740096
                    [2, 9, 9, 2, 10, 2, 2, 0]
                    .empty
                    .empty)
                  .empty))))
          (.node 361977945499174401
            [5, 6, 1, 6, 10, 1, 6, 1]
            (.node 360576068106978561
              [5, 1, 6, 6, 6, 6, 5, 1]
              (.node 146940937422045696
                [2, 10, 10, 1, 10, 1, 2, 0]
                (.node 146940933127143936
                  [2, 10, 10, 0, 10, 2, 2, 0]
                  (.node 146939842205385216
                    [2, 10, 9, 2, 10, 1, 2, 0]
                    .empty
                    .empty)
                  (.node 146940937405334016
                    [2, 10, 10, 1, 9, 2, 2, 0]
                    .empty
                    .empty))
                (.node 360576068106977541
                  [5, 1, 6, 6, 6, 6, 1, 5]
                  (.node 218154110824874496
                    [3, 7, 10, 2, 10, 2, 2, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 360576068174086401
                [5, 1, 6, 6, 10, 6, 1, 1]
                (.node 360576068157309441
                  [5, 1, 6, 6, 9, 6, 2, 1]
                  (.node 360576068106978816
                    [5, 1, 6, 6, 6, 6, 6, 0]
                    .empty
                    .empty)
                  (.node 360576068174021121
                    [5, 1, 6, 6, 10, 5, 2, 1]
                    .empty
                    .empty))
                (.node 361977945432065541
                  [5, 6, 1, 6, 6, 1, 6, 5]
                  (.node 360576068174086656
                    [5, 1, 6, 6, 10, 6, 2, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 432352187168194566
              [6, 0, 6, 6, 6, 6, 0, 6]
              (.node 361983421515367941
                [5, 6, 6, 1, 6, 1, 6, 5]
                (.node 361983421498918401
                  [5, 6, 6, 1, 5, 6, 6, 1]
                  (.node 361983421431809541
                    [5, 6, 6, 1, 1, 6, 6, 5]
                    .empty
                    .empty)
                  (.node 361983421515367686
                    [5, 6, 6, 1, 6, 1, 5, 6]
                    .empty
                    .empty))
                (.node 361983421515695616
                  [5, 6, 6, 1, 6, 6, 6, 0]
                  (.node 361983421515630081
                    [5, 6, 6, 1, 6, 5, 6, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 432352187218526721
                [6, 0, 6, 6, 9, 6, 2, 1]
                (.node 432352187168195841
                  [6, 0, 6, 6, 6, 6, 5, 1]
                  (.node 432352187168194821
                    [6, 0, 6, 6, 6, 6, 1, 5]
                    .empty
                    .empty)
                  (.node 432352187168196096
                    [6, 0, 6, 6, 6, 6, 6, 0]
                    .empty
                    .empty))
                (.node 432352187235303681
                  [6, 0, 6, 6, 10, 6, 1, 1]
                  (.node 432352187235238401
                    [6, 0, 6, 6, 10, 5, 2, 1]
                    .empty
                    .empty)
                  .empty)))))
        (.node 432633662211818241
          [6, 1, 6, 6, 10, 3, 3, 1]
          (.node 432633657849939201
            [6, 1, 6, 5, 6, 6, 5, 1]
            (.node 432632562700321281
              [6, 1, 5, 6, 10, 5, 2, 1]
              (.node 432632562633278721
                [6, 1, 5, 6, 6, 6, 5, 1]
                (.node 432632562633212166
                  [6, 1, 5, 6, 6, 5, 1, 6]
                  (.node 432632562616501761
                    [6, 1, 5, 6, 5, 6, 6, 1]
                    .empty
                    .empty)
                  (.node 432632562633213441
                    [6, 1, 5, 6, 6, 5, 6, 1]
                    .empty
                    .empty))
                (.node 432632562683609601
                  [6, 1, 5, 6, 9, 6, 2, 1]
                  (.node 432632562633278976
                    [6, 1, 5, 6, 6, 6, 6, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 432633657849872646
                [6, 1, 6, 5, 6, 5, 1, 6]
                (.node 432633657833160966
                  [6, 1, 6, 5, 5, 6, 1, 6]
                  (.node 432632562700386816
                    [6, 1, 5, 6, 10, 6, 2, 0]
                    .empty
                    .empty)
                  (.node 432633657833162241
                    [6, 1, 6, 5, 5, 6, 6, 1]
                    .empty
                    .empty))
                (.node 432633657849938181
                  [6, 1, 6, 5, 6, 6, 1, 5]
                  (.node 432633657849873921
                    [6, 1, 6, 5, 6, 5, 6, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 432633662144906241
              [6, 1, 6, 6, 6, 6, 4, 1]
              (.node 432633657917047041
                [6, 1, 6, 5, 10, 6, 1, 1]
                (.node 432633657900270081
                  [6, 1, 6, 5, 9, 6, 2, 1]
                  (.node 432633657849939456
                    [6, 1, 6, 5, 6, 6, 6, 0]
                    .empty
                    .empty)
                  (.node 432633657916981761
                    [6, 1, 6, 5, 10, 5, 2, 1]
                    .empty
                    .empty))
                (.node 432633662144905476
                  [6, 1, 6, 6, 6, 6, 1, 4]
                  (.node 432633657917047296
                    [6, 1, 6, 5, 10, 6, 2, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 432633662195171841
                [6, 1, 6, 6, 9, 5, 2, 1]
                (.node 432633662161683201
                  [6, 1, 6, 6, 7, 6, 3, 1]
                  (.node 432633662144906496
                    [6, 1, 6, 6, 6, 6, 5, 0]
                    .empty
                    .empty)
                  (.node 432633662178460161
                    [6, 1, 6, 6, 8, 6, 2, 1]
                    .empty
                    .empty))
                (.node 432633662195237376
                  [6, 1, 6, 6, 9, 6, 2, 0]
                  (.node 432633662195237121
                    [6, 1, 6, 6, 9, 6, 1, 1]
                    .empty
                    .empty)
                  .empty))))
          (.node 433754064560457216
            [6, 5, 1, 6, 10, 2, 6, 0]
            (.node 432634761690087681
              [6, 1, 7, 6, 8, 6, 1, 1]
              (.node 432633662212014336
                [6, 1, 6, 6, 10, 6, 1, 0]
                (.node 432633662211948801
                  [6, 1, 6, 6, 10, 5, 1, 1]
                  (.node 432633662211883521
                    [6, 1, 6, 6, 10, 4, 2, 1]
                    .empty
                    .empty)
                  (.node 432633662211949056
                    [6, 1, 6, 6, 10, 5, 2, 0]
                    .empty
                    .empty))
                (.node 432634761673310721
                  [6, 1, 7, 6, 7, 6, 2, 1]
                  (.node 432633662228595201
                    [6, 1, 6, 6, 11, 3, 2, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 433754064493282821
                [6, 5, 1, 6, 6, 1, 6, 5]
                (.node 432638047323292161
                  [6, 1, 10, 3, 7, 6, 2, 1]
                  (.node 432634761723445761
                    [6, 1, 7, 6, 10, 3, 2, 1]
                    .empty
                    .empty)
                  (.node 433754064493282566
                    [6, 5, 1, 6, 6, 1, 5, 6]
                    .empty
                    .empty))
                (.node 433754064560391681
                  [6, 5, 1, 6, 10, 1, 6, 1]
                  (.node 433754064543680001
                    [6, 5, 1, 6, 9, 2, 6, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 433759540576912641
              [6, 5, 6, 1, 6, 6, 5, 1]
              (.node 433759540576584966
                [6, 5, 6, 1, 6, 1, 5, 6]
                (.node 433759540493026821
                  [6, 5, 6, 1, 1, 6, 6, 5]
                  (.node 433759540493026566
                    [6, 5, 6, 1, 1, 6, 5, 6]
                    .empty
                    .empty)
                  (.node 433759540560135681
                    [6, 5, 6, 1, 5, 6, 6, 1]
                    .empty
                    .empty))
                (.node 433759540576847361
                  [6, 5, 6, 1, 6, 5, 6, 1]
                  (.node 433759540576585221
                    [6, 5, 6, 1, 6, 1, 6, 5]
                    .empty
                    .empty)
                  .empty))
              (.node 434035535158248966
                [6, 6, 1, 5, 5, 1, 6, 6]
                (.node 434034439958300166
                  [6, 6, 0, 6, 6, 0, 6, 6]
                  (.node 433759540576912896
                    [6, 5, 6, 1, 6, 6, 6, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 434035535175026181
                  [6, 6, 1, 5, 6, 1, 6, 5]
                  (.node 434035535174960646
                    [6, 6, 1, 5, 6, 0, 6, 6]
                    .empty
                    .empty)
                  .empty))))))
      (.node 650212698155450886
        [9, 6, 5, 1, 6, 1, 2, 6]
        (.node 434041015553296131
          [6, 6, 6, 1, 6, 1, 7, 3]
          (.node 434041011241551366
            [6, 6, 6, 0, 5, 1, 6, 6]
            (.node 434039916041602566
              [6, 6, 5, 1, 6, 0, 6, 6]
              (.node 434035539537102336
                [6, 6, 1, 6, 10, 1, 6, 0]
                (.node 434035539520325121
                  [6, 6, 1, 6, 9, 1, 6, 1]
                  (.node 434035539469993476
                    [6, 6, 1, 6, 6, 1, 6, 4]
                    .empty
                    .empty)
                  (.node 434035539537036801
                    [6, 6, 1, 6, 10, 0, 6, 1]
                    .empty
                    .empty))
                (.node 434039916024890886
                  [6, 6, 5, 1, 5, 1, 6, 6]
                  (.node 434039915958044166
                    [6, 6, 5, 1, 1, 5, 6, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 434041011157992966
                [6, 6, 6, 0, 0, 6, 6, 6]
                (.node 434039916041668101
                  [6, 6, 5, 1, 6, 1, 6, 5]
                  (.node 434039916041667846
                    [6, 6, 5, 1, 6, 1, 5, 6]
                    .empty
                    .empty)
                  (.node 434039916041930241
                    [6, 6, 5, 1, 6, 5, 6, 1]
                    .empty
                    .empty))
                (.node 434041011174770181
                  [6, 6, 6, 0, 1, 6, 6, 5]
                  (.node 434041011174704646
                    [6, 6, 6, 0, 1, 5, 6, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 434041015469737476
              [6, 6, 6, 1, 1, 6, 6, 4]
              (.node 434041011258328581
                [6, 6, 6, 0, 6, 1, 6, 5]
                (.node 434041011258263046
                  [6, 6, 6, 0, 6, 0, 6, 6]
                  (.node 434041011241879041
                    [6, 6, 6, 0, 5, 6, 6, 1]
                    .empty
                    .empty)
                  (.node 434041011258328326
                    [6, 6, 6, 0, 6, 1, 5, 6]
                    .empty
                    .empty))
                (.node 434041011258656256
                  [6, 6, 6, 0, 6, 6, 6, 0]
                  (.node 434041011258590721
                    [6, 6, 6, 0, 6, 5, 6, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 434041015553295366
                [6, 6, 6, 1, 6, 1, 4, 6]
                (.node 434041015536780801
                  [6, 6, 6, 1, 5, 5, 6, 1]
                  (.node 434041015520069121
                    [6, 6, 6, 1, 4, 6, 6, 1]
                    .empty
                    .empty)
                  (.node 434041015536846336
                    [6, 6, 6, 1, 5, 6, 6, 0]
                    .empty
                    .empty))
                (.node 434041015553295876
                  [6, 6, 6, 1, 6, 1, 6, 4]
                  (.node 434041015553295621
                    [6, 6, 6, 1, 6, 1, 5, 5]
                    .empty
                    .empty)
                  .empty))))
          (.node 648806444258689281
            [9, 1, 6, 6, 6, 6, 1, 1]
            (.node 506098609541219841
              [7, 6, 6, 1, 3, 6, 6, 1]
              (.node 434041015570204161
                [6, 6, 6, 1, 7, 3, 6, 1]
                (.node 434041015553557761
                  [6, 6, 6, 1, 6, 5, 5, 1]
                  (.node 434041015553492481
                    [6, 6, 6, 1, 6, 4, 6, 1]
                    .empty
                    .empty)
                  (.node 434041015553558016
                    [6, 6, 6, 1, 6, 5, 6, 0]
                    .empty
                    .empty))
                (.node 434323594403774976
                  [6, 7, 7, 2, 10, 2, 2, 0]
                  (.node 434041015620535041
                    [6, 6, 6, 1, 10, 3, 3, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 578156203562370561
                [8, 6, 6, 1, 2, 6, 6, 1]
                (.node 506098609591223811
                  [7, 6, 6, 1, 6, 1, 6, 3]
                  (.node 506098609591223046
                    [7, 6, 6, 1, 6, 1, 3, 6]
                    .empty
                    .empty)
                  (.node 506098609591354881
                    [7, 6, 6, 1, 6, 3, 6, 1]
                    .empty
                    .empty))
                (.node 578156203645927686
                  [8, 6, 6, 1, 7, 1, 1, 6]
                  (.node 578156203629150726
                    [8, 6, 6, 1, 6, 1, 2, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 650209399553460741
              [9, 6, 2, 1, 2, 1, 10, 5]
              (.node 649932322690433286
                [9, 5, 6, 1, 6, 2, 1, 6]
                (.node 649932322623587841
                  [9, 5, 6, 1, 2, 6, 6, 1]
                  (.node 649087897760497926
                    [9, 2, 6, 1, 6, 5, 1, 6]
                    .empty
                    .empty)
                  (.node 649932322690368006
                    [9, 5, 6, 1, 6, 1, 2, 6]
                    .empty
                    .empty))
                (.node 650209399553460486
                  [9, 6, 2, 1, 2, 1, 9, 6]
                  (.node 650208321583777281
                    [9, 6, 1, 6, 6, 1, 6, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 650209399620568326
                [9, 6, 2, 1, 6, 1, 5, 6]
                (.node 650209399620503046
                  [9, 6, 2, 1, 6, 0, 6, 6]
                  (.node 650209399603791366
                    [9, 6, 2, 1, 5, 1, 6, 6]
                    .empty
                    .empty)
                  .empty)
                (.node 650209416800437761
                  [9, 6, 2, 5, 6, 1, 6, 1]
                  (.node 650209399620568581
                    [9, 6, 2, 1, 6, 1, 6, 5]
                    .empty
                    .empty)
                  .empty)))))
        (.node 721985518614677766
          [10, 5, 2, 1, 2, 1, 9, 6]
          (.node 721145487503458566
            [10, 2, 6, 0, 6, 5, 1, 6]
            (.node 650213797667078661
              [9, 6, 6, 1, 6, 1, 2, 5]
              (.node 650213797600232961
                [9, 6, 6, 1, 2, 5, 6, 1]
                (.node 650213793372111366
                  [9, 6, 6, 0, 6, 1, 2, 6]
                  (.node 650213793305331201
                    [9, 6, 6, 0, 2, 6, 6, 1]
                    .empty
                    .empty)
                  (.node 650213797583521281
                    [9, 6, 6, 1, 1, 6, 6, 1]
                    .empty
                    .empty))
                (.node 650213797667078406
                  [9, 6, 6, 1, 6, 1, 1, 6]
                  (.node 650213797600298496
                    [9, 6, 6, 1, 2, 6, 6, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 720864016821780741
                [10, 1, 6, 1, 6, 6, 1, 5]
                (.node 720864016805003526
                  [10, 1, 6, 1, 5, 6, 1, 6]
                  (.node 720582563319906561
                    [10, 0, 6, 6, 6, 6, 1, 1]
                    .empty
                    .empty)
                  (.node 720864016821715206
                    [10, 1, 6, 1, 6, 5, 1, 6]
                    .empty
                    .empty))
                (.node 720864038296617216
                  [10, 1, 6, 6, 6, 6, 1, 0]
                  (.node 720864034001649921
                    [10, 1, 6, 5, 6, 6, 1, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 721426966775005446
              [10, 3, 6, 1, 6, 3, 1, 6]
              (.node 721145508978295041
                [10, 2, 6, 5, 6, 5, 1, 1]
                (.node 721145491798360326
                  [10, 2, 6, 1, 6, 4, 1, 6]
                  (.node 721145491781648646
                    [10, 2, 6, 1, 5, 5, 1, 6]
                    .empty
                    .empty)
                  (.node 721145491798425861
                    [10, 2, 6, 1, 6, 5, 1, 5]
                    .empty
                    .empty))
                (.node 721426966774874886
                  [10, 3, 6, 1, 6, 1, 3, 6]
                  (.node 721426966724871681
                    [10, 3, 6, 1, 3, 6, 6, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 721708441751650566
                [10, 4, 6, 1, 6, 2, 1, 6]
                (.node 721708441684805121
                  [10, 4, 6, 1, 2, 6, 6, 1]
                  (.node 721426966775202561
                    [10, 3, 6, 1, 6, 6, 3, 1]
                    .empty
                    .empty)
                  (.node 721708441751585286
                    [10, 4, 6, 1, 6, 1, 2, 6]
                    .empty
                    .empty))
                (.node 721984440644994561
                  [10, 5, 1, 6, 6, 1, 6, 1]
                  (.node 721708441768362246
                    [10, 4, 6, 1, 7, 1, 1, 6]
                    .empty
                    .empty)
                  .empty))))
          (.node 721989916661450241
            [10, 5, 6, 1, 2, 5, 6, 1]
            (.node 721988817149888001
              [10, 5, 5, 1, 2, 6, 6, 1]
              (.node 721985518681785606
                [10, 5, 2, 1, 6, 1, 5, 6]
                (.node 721985518665008646
                  [10, 5, 2, 1, 5, 1, 6, 6]
                  (.node 721985518614678021
                    [10, 5, 2, 1, 2, 1, 10, 5]
                    .empty
                    .empty)
                  (.node 721985518681720326
                    [10, 5, 2, 1, 6, 0, 6, 6]
                    .empty
                    .empty))
                (.node 721985535861655041
                  [10, 5, 2, 5, 6, 1, 6, 1]
                  (.node 721985518681785861
                    [10, 5, 2, 1, 6, 1, 6, 5]
                    .empty
                    .empty)
                  .empty))
              (.node 721989912433328646
                [10, 5, 6, 0, 6, 1, 2, 6]
                (.node 721988821511635206
                  [10, 5, 5, 2, 6, 1, 1, 6]
                  (.node 721988817216668166
                    [10, 5, 5, 1, 6, 1, 2, 6]
                    .empty
                    .empty)
                  (.node 721989912366548481
                    [10, 5, 6, 0, 2, 6, 6, 1]
                    .empty
                    .empty))
                (.node 721989916644738561
                  [10, 5, 6, 1, 1, 6, 6, 1]
                  (.node 721989912433393926
                    [10, 5, 6, 0, 6, 2, 1, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 722265894062983686
              [10, 6, 1, 1, 1, 1, 10, 6]
              (.node 721989916728295686
                [10, 5, 6, 1, 6, 1, 1, 6]
                (.node 721989916661515776
                  [10, 5, 6, 1, 2, 6, 6, 0]
                  (.node 721989916661515521
                    [10, 5, 6, 1, 2, 6, 5, 1]
                    .empty
                    .empty)
                  (.node 721989916711584006
                    [10, 5, 6, 1, 5, 2, 1, 6]
                    .empty
                    .empty))
                (.node 721989916728361221
                  [10, 5, 6, 1, 6, 2, 1, 5]
                  (.node 721989916728295941
                    [10, 5, 6, 1, 6, 1, 2, 5]
                    .empty
                    .empty)
                  .empty))
              (.node 722265894079760901
                [10, 6, 1, 1, 2, 1, 10, 5]
                (.node 722265894079760646
                  [10, 6, 1, 1, 2, 1, 9, 6]
                  (.node 722265894079695366
                    [10, 6, 1, 1, 2, 0, 10, 6]
                    .empty
                    .empty)
                  .empty)
                (.node 722265894146803206
                  [10, 6, 1, 1, 6, 0, 6, 6]
                  (.node 722265894130091526
                    [10, 6, 1, 1, 5, 1, 6, 6]
                    .empty
                    .empty)
                  .empty)))))))
    (.node 937596450303444486
      [13, 3, 3, 1, 3, 1, 6, 6]
      (.node 793484560812867846
        [11, 3, 6, 1, 6, 2, 1, 6]
        (.node 722268093119792646
          [10, 6, 3, 1, 3, 1, 6, 6]
          (.node 722266993608165126
            [10, 6, 2, 1, 3, 1, 7, 6]
            (.node 722266989346752006
              [10, 6, 2, 0, 5, 1, 6, 6]
              (.node 722266989296355846
                [10, 6, 2, 0, 2, 0, 10, 6]
                (.node 722265915621705216
                  [10, 6, 1, 6, 6, 1, 6, 0]
                  (.node 722265911326737921
                    [10, 6, 1, 5, 6, 1, 6, 1]
                    .empty
                    .empty)
                  (.node 722266989279644166
                    [10, 6, 2, 0, 1, 1, 10, 6]
                    .empty
                    .empty))
                (.node 722266989296421381
                  [10, 6, 2, 0, 2, 1, 10, 5]
                  (.node 722266989296421126
                    [10, 6, 2, 0, 2, 1, 9, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 722266993591388166
                [10, 6, 2, 1, 2, 1, 8, 6]
                (.node 722266989363528966
                  [10, 6, 2, 0, 6, 1, 5, 6]
                  (.node 722266989363463686
                    [10, 6, 2, 0, 6, 0, 6, 6]
                    .empty
                    .empty)
                  (.node 722266989363529221
                    [10, 6, 2, 0, 6, 1, 6, 5]
                    .empty
                    .empty))
                (.node 722266993591388676
                  [10, 6, 2, 1, 2, 1, 10, 4]
                  (.node 722266993591388421
                    [10, 6, 2, 1, 2, 1, 9, 5]
                    .empty
                    .empty)
                  .empty)))
            (.node 722266993658430981
              [10, 6, 2, 1, 6, 0, 6, 5]
              (.node 722266993641719046
                [10, 6, 2, 1, 5, 1, 5, 6]
                (.node 722266993624942086
                  [10, 6, 2, 1, 4, 1, 6, 6]
                  (.node 722266993608165891
                    [10, 6, 2, 1, 3, 1, 10, 3]
                    .empty
                    .empty)
                  (.node 722266993641653766
                    [10, 6, 2, 1, 5, 0, 6, 6]
                    .empty
                    .empty))
                (.node 722266993658430726
                  [10, 6, 2, 1, 6, 0, 5, 6]
                  (.node 722266993641719301
                    [10, 6, 2, 1, 5, 1, 6, 5]
                    .empty
                    .empty)
                  .empty))
              (.node 722267006543398401
                [10, 6, 2, 4, 6, 1, 6, 1]
                (.node 722266993658496516
                  [10, 6, 2, 1, 6, 1, 6, 4]
                  (.node 722266993658496261
                    [10, 6, 2, 1, 6, 1, 5, 5]
                    .empty
                    .empty)
                  (.node 722266993658496771
                    [10, 6, 2, 1, 6, 1, 7, 3]
                    .empty
                    .empty))
                (.node 722267010838365696
                  [10, 6, 2, 5, 6, 1, 6, 0]
                  (.node 722267010838365441
                    [10, 6, 2, 5, 6, 1, 5, 1]
                    .empty
                    .empty)
                  .empty))))
          (.node 722271387410039046
            [10, 6, 6, 0, 6, 1, 1, 6]
            (.node 722270292193313286
              [10, 6, 5, 1, 6, 0, 2, 6]
              (.node 722270287898411526
                [10, 6, 5, 0, 6, 1, 2, 6]
                (.node 722268093170255361
                  [10, 6, 3, 1, 6, 3, 6, 1]
                  (.node 722268093170124291
                    [10, 6, 3, 1, 6, 1, 6, 3]
                    .empty
                    .empty)
                  (.node 722268101760058881
                    [10, 6, 3, 3, 6, 1, 6, 1]
                    .empty
                    .empty))
                (.node 722270292176601606
                  [10, 6, 5, 1, 5, 1, 2, 6]
                  (.node 722270292126533121
                    [10, 6, 5, 1, 2, 5, 6, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 722271387343259136
                [10, 6, 6, 0, 2, 6, 6, 0]
                (.node 722271387326481921
                  [10, 6, 6, 0, 1, 6, 6, 1]
                  (.node 722270292193378821
                    [10, 6, 5, 1, 6, 1, 2, 5]
                    .empty
                    .empty)
                  (.node 722271387343193601
                    [10, 6, 6, 0, 2, 5, 6, 1]
                    .empty
                    .empty))
                (.node 722271387409973766
                  [10, 6, 6, 0, 6, 0, 2, 6]
                  (.node 722271387393262086
                    [10, 6, 6, 0, 5, 1, 2, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 722271391705006851
              [10, 6, 6, 1, 6, 1, 3, 3]
              (.node 722271391638160896
                [10, 6, 6, 1, 2, 5, 6, 0]
                (.node 722271391621449216
                  [10, 6, 6, 1, 1, 6, 6, 0]
                  (.node 722271387410039301
                    [10, 6, 6, 0, 6, 1, 2, 5]
                    .empty
                    .empty)
                  (.node 722271391638160641
                    [10, 6, 6, 1, 2, 5, 5, 1]
                    .empty
                    .empty))
                (.node 722271391705006596
                  [10, 6, 6, 1, 6, 1, 2, 4]
                  (.node 722271391705006341
                    [10, 6, 6, 1, 6, 1, 1, 5]
                    .empty
                    .empty)
                  .empty))
              (.node 793203085836222726
                [11, 2, 6, 1, 6, 3, 1, 6]
                (.node 722271391721783556
                  [10, 6, 6, 1, 7, 1, 1, 4]
                  (.node 722271391705137921
                    [10, 6, 6, 1, 6, 3, 3, 1]
                    .empty
                    .empty)
                  .empty)
                (.node 793484560812802566
                  [11, 3, 6, 1, 6, 1, 2, 6]
                  (.node 793484560746022401
                    [11, 3, 6, 1, 2, 6, 6, 1]
                    .empty
                    .empty)
                  .empty)))))
        (.node 865822530315813126
          [12, 4, 5, 1, 6, 1, 1, 6]
          (.node 794328985742934276
            [11, 6, 6, 1, 6, 1, 1, 4]
            (.node 794324587646092806
              [11, 6, 2, 1, 3, 1, 6, 6]
              (.node 794047506471256326
                [11, 5, 6, 0, 6, 1, 1, 6]
                (.node 793766035789512966
                  [11, 4, 6, 1, 6, 1, 1, 6]
                  (.node 793484560829579526
                    [11, 3, 6, 1, 7, 1, 1, 6]
                    .empty
                    .empty)
                  (.node 794046411254595846
                    [11, 5, 5, 1, 6, 1, 1, 6]
                    .empty
                    .empty))
                (.node 794047510766223621
                  [11, 5, 6, 1, 6, 1, 1, 5]
                  (.node 794047510766223366
                    [11, 5, 6, 1, 6, 1, 0, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 794328981431189766
                [11, 6, 6, 0, 5, 1, 1, 6]
                (.node 794324596286359041
                  [11, 6, 2, 3, 6, 1, 6, 1]
                  (.node 794324587696424451
                    [11, 6, 2, 1, 6, 1, 6, 3]
                    .empty
                    .empty)
                  (.node 794327886231240966
                    [11, 6, 5, 1, 6, 0, 1, 6]
                    .empty
                    .empty))
                (.node 794328981447966981
                  [11, 6, 6, 0, 6, 1, 1, 5]
                  (.node 794328981447901446
                    [11, 6, 6, 0, 6, 0, 1, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 865541055339168006
              [12, 3, 5, 1, 6, 2, 1, 6]
              (.node 794328990037967361
                [11, 6, 6, 2, 6, 2, 2, 1]
                (.node 794328985743000066
                  [11, 6, 6, 1, 6, 2, 2, 2]
                  (.node 794328985742934531
                    [11, 6, 6, 1, 6, 1, 2, 3]
                    .empty
                    .empty)
                  (.node 794328985759711491
                    [11, 6, 6, 1, 7, 1, 1, 3]
                    .empty
                    .empty))
                (.node 865541055339102726
                  [12, 3, 5, 1, 6, 1, 2, 6]
                  (.node 865260679874085126
                    [12, 2, 6, 1, 6, 2, 1, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 865542154850730246
                [12, 3, 6, 1, 6, 1, 1, 6]
                (.node 865542150555828486
                  [12, 3, 6, 0, 6, 2, 1, 6]
                  (.node 865541059634069766
                    [12, 3, 5, 2, 6, 1, 1, 6]
                    .empty
                    .empty)
                  (.node 865542154834018566
                    [12, 3, 6, 1, 5, 2, 1, 6]
                    .empty
                    .empty))
                (.node 865542154850795781
                  [12, 3, 6, 1, 6, 2, 1, 5]
                  (.node 865542154850795526
                    [12, 3, 6, 1, 6, 2, 0, 6]
                    .empty
                    .empty)
                  .empty))))
          (.node 866105104804217091
            [12, 5, 6, 1, 6, 2, 1, 3]
            (.node 866104005292523781
              [12, 5, 5, 1, 6, 1, 1, 5]
              (.node 866104000997556486
                [12, 5, 5, 0, 6, 1, 1, 6]
                (.node 865823629827440646
                  [12, 4, 6, 1, 6, 1, 0, 6]
                  (.node 865823625532473606
                    [12, 4, 6, 0, 6, 1, 1, 6]
                    .empty
                    .empty)
                  (.node 865823629827440901
                    [12, 4, 6, 1, 6, 1, 1, 5]
                    .empty
                    .empty))
                (.node 866104005292458246
                  [12, 5, 5, 1, 6, 0, 1, 6]
                  (.node 866104005275746566
                    [12, 5, 5, 1, 5, 1, 1, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 866105100509184261
                [12, 5, 6, 0, 6, 1, 1, 5]
                (.node 866105100509118726
                  [12, 5, 6, 0, 6, 0, 1, 6]
                  (.node 866105100492407046
                    [12, 5, 6, 0, 5, 1, 1, 6]
                    .empty
                    .empty)
                  (.node 866105100509184006
                    [12, 5, 6, 0, 6, 1, 0, 6]
                    .empty
                    .empty))
                (.node 866105104804151556
                  [12, 5, 6, 1, 6, 1, 1, 4]
                  (.node 866105104804151301
                    [12, 5, 6, 1, 6, 1, 0, 5]
                    .empty
                    .empty)
                  .empty)))
            (.node 866386575485894916
              [12, 6, 6, 0, 6, 1, 1, 4]
              (.node 866386575469117701
                [12, 6, 6, 0, 5, 1, 1, 5]
                (.node 866385480269168901
                  [12, 6, 5, 1, 6, 0, 1, 5]
                  (.node 866385475974201606
                    [12, 6, 5, 0, 6, 0, 1, 6]
                    .empty
                    .empty)
                  (.node 866385480269234691
                    [12, 6, 5, 1, 6, 1, 2, 3]
                    .empty
                    .empty))
                (.node 866386575485829381
                  [12, 6, 6, 0, 6, 0, 1, 5]
                  (.node 866386575485829126
                    [12, 6, 6, 0, 6, 0, 0, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 937317178695287046
                [13, 2, 5, 2, 6, 1, 1, 6]
                (.node 937317174400385286
                  [13, 2, 5, 1, 6, 2, 1, 6]
                  (.node 866386579780862211
                    [12, 6, 6, 1, 6, 1, 1, 3]
                    .empty
                    .empty)
                  .empty)
                (.node 937318273912012806
                  [13, 2, 6, 1, 6, 2, 0, 6]
                  (.node 937318273895235846
                    [13, 2, 6, 1, 5, 2, 1, 6]
                    .empty
                    .empty)
                  .empty))))))
      (.node 938444169507045636
        [13, 6, 6, 0, 5, 1, 1, 4]
        (.node 937880124353740806
          [13, 4, 5, 1, 6, 1, 0, 6]
          (.node 937598653671997446
            [13, 3, 5, 2, 6, 1, 0, 6]
            (.node 937597554160369926
              [13, 3, 4, 2, 6, 1, 1, 6]
              (.node 937597549865402886
                [13, 3, 4, 1, 6, 1, 2, 6]
                (.node 937596450353775366
                  [13, 3, 3, 1, 6, 1, 3, 6]
                  (.node 937596450303772161
                    [13, 3, 3, 1, 3, 6, 6, 1]
                    .empty
                    .empty)
                  (.node 937596458943709446
                    [13, 3, 3, 3, 6, 1, 1, 6]
                    .empty
                    .empty))
                (.node 937597549882179846
                  [13, 3, 4, 1, 7, 1, 1, 6]
                  (.node 937597549865468166
                    [13, 3, 4, 1, 6, 2, 1, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 937598649377030406
                [13, 3, 5, 1, 6, 1, 1, 6]
                (.node 937598649360253446
                  [13, 3, 5, 1, 5, 1, 2, 6]
                  (.node 937598645082128646
                    [13, 3, 5, 0, 6, 2, 1, 6]
                    .empty
                    .empty)
                  (.node 937598649360318726
                    [13, 3, 5, 1, 5, 2, 1, 6]
                    .empty
                    .empty))
                (.node 937598649377095941
                  [13, 3, 5, 1, 6, 2, 1, 5]
                  (.node 937598649377095686
                    [13, 3, 5, 1, 6, 2, 0, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 937599748888657926
              [13, 3, 6, 1, 6, 1, 0, 6]
              (.node 937599748838654721
                [13, 3, 6, 1, 3, 6, 3, 1]
                (.node 937599744576979206
                  [13, 3, 6, 0, 5, 2, 1, 6]
                  (.node 937598653671997701
                    [13, 3, 5, 2, 6, 1, 1, 5]
                    .empty
                    .empty)
                  (.node 937599744593756166
                    [13, 3, 6, 0, 6, 2, 0, 6]
                    .empty
                    .empty))
                (.node 937599748871946501
                  [13, 3, 6, 1, 5, 2, 1, 5]
                  (.node 937599748871946246
                    [13, 3, 6, 1, 5, 2, 0, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 937880120058773766
                [13, 4, 5, 0, 6, 1, 1, 6]
                (.node 937877925330485766
                  [13, 4, 3, 1, 6, 1, 2, 6]
                  (.node 937599748888723461
                    [13, 3, 6, 1, 6, 2, 0, 5]
                    .empty
                    .empty)
                  (.node 937879024842113286
                    [13, 4, 4, 1, 6, 1, 1, 6]
                    .empty
                    .empty))
                (.node 937880124353675526
                  [13, 4, 5, 1, 6, 0, 1, 6]
                  (.node 937880124336963846
                    [13, 4, 5, 1, 5, 1, 1, 6]
                    .empty
                    .empty)
                  .empty))))
          (.node 938161603625419011
            [13, 5, 5, 2, 6, 1, 1, 3]
            (.node 938161595018707206
              [13, 5, 5, 0, 5, 1, 1, 6]
              (.node 937881223865368581
                [13, 4, 6, 1, 6, 1, 0, 5]
                (.node 937881219553624326
                  [13, 4, 6, 0, 5, 1, 1, 6]
                  (.node 937880124353741061
                    [13, 4, 5, 1, 6, 1, 1, 5]
                    .empty
                    .empty)
                  (.node 937881219570401286
                    [13, 4, 6, 0, 6, 1, 0, 6]
                    .empty
                    .empty))
                (.node 938160499818758406
                  [13, 5, 4, 1, 6, 0, 1, 6]
                  (.node 938159400307130886
                    [13, 5, 3, 1, 6, 0, 2, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 938161599330385926
                [13, 5, 5, 1, 6, 0, 0, 6]
                (.node 938161595035484421
                  [13, 5, 5, 0, 6, 1, 1, 5]
                  (.node 938161595035418886
                    [13, 5, 5, 0, 6, 0, 1, 6]
                    .empty
                    .empty)
                  (.node 938161599313674501
                    [13, 5, 5, 1, 5, 1, 1, 5]
                    .empty
                    .empty))
                (.node 938161599330451716
                  [13, 5, 5, 1, 6, 1, 1, 4]
                  (.node 938161599330386181
                    [13, 5, 5, 1, 6, 0, 1, 5]
                    .empty
                    .empty)
                  .empty)))
            (.node 938440875233576451
              [13, 6, 3, 1, 3, 1, 6, 3]
              (.node 938162694547111941
                [13, 5, 6, 0, 6, 1, 0, 5]
                (.node 938162694530334981
                  [13, 5, 6, 0, 5, 1, 1, 5]
                  (.node 938162694530334726
                    [13, 5, 6, 0, 5, 1, 0, 6]
                    .empty
                    .empty)
                  (.node 938162694547046406
                    [13, 5, 6, 0, 6, 0, 0, 6]
                    .empty
                    .empty))
                (.node 938162698842079236
                  [13, 5, 6, 1, 6, 1, 0, 4]
                  (.node 938162698825367811
                    [13, 5, 6, 1, 5, 2, 1, 3]
                    .empty
                    .empty)
                  .empty))
              (.node 938443070012129541
                [13, 6, 5, 0, 6, 0, 1, 5]
                (.node 938443069995352326
                  [13, 6, 5, 0, 5, 0, 1, 6]
                  (.node 938440875233707521
                    [13, 6, 3, 1, 3, 3, 6, 1]
                    .empty
                    .empty)
                  .empty)
                (.node 938443074307096836
                  [13, 6, 5, 1, 6, 0, 1, 4]
                  (.node 938443074290385411
                    [13, 6, 5, 1, 5, 1, 2, 3]
                    .empty
                    .empty)
                  .empty)))))
        (.node 1010500664033280261
          [14, 6, 5, 0, 5, 0, 1, 5]
          (.node 1009937718374891781
            [14, 4, 5, 1, 5, 1, 1, 5]
            (.node 1009936614585073926
              [14, 4, 4, 0, 6, 1, 1, 6]
              (.node 1009655143903330566
                [14, 3, 4, 1, 6, 1, 1, 6]
                (.node 1009654044391703046
                  [14, 3, 3, 1, 6, 1, 2, 6]
                  (.node 938444169523757061
                    [13, 6, 6, 0, 6, 0, 0, 5]
                    .empty
                    .empty)
                  (.node 1009654048686670086
                    [14, 3, 3, 2, 6, 1, 1, 6]
                    .empty
                    .empty))
                (.node 1009656243414958086
                  [14, 3, 5, 1, 6, 1, 0, 6]
                  (.node 1009656243398181126
                    [14, 3, 5, 1, 5, 1, 1, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 1009937714079924486
                [14, 4, 5, 0, 5, 1, 1, 6]
                (.node 1009936618879975686
                  [14, 4, 4, 1, 6, 0, 1, 6]
                  (.node 1009936618863264006
                    [14, 4, 4, 1, 5, 1, 1, 6]
                    .empty
                    .empty)
                  (.node 1009936618880041221
                    [14, 4, 4, 1, 6, 1, 1, 5]
                    .empty
                    .empty))
                (.node 1009937718374891526
                  [14, 4, 5, 1, 5, 1, 0, 6]
                  (.node 1009937714096701446
                    [14, 4, 5, 0, 6, 1, 0, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 1010219189039857926
              [14, 5, 5, 0, 4, 1, 1, 6]
              (.node 1010218089561719046
                [14, 5, 4, 0, 6, 0, 1, 6]
                (.node 1009937718391668741
                  [14, 4, 5, 1, 6, 1, 0, 5]
                  (.node 1009937718391603206
                    [14, 4, 5, 1, 6, 0, 0, 6]
                    .empty
                    .empty)
                  (.node 1009938813591552006
                    [14, 4, 6, 0, 5, 1, 0, 6]
                    .empty
                    .empty))
                (.node 1010218093856686341
                  [14, 5, 4, 1, 6, 0, 1, 5]
                  (.node 1010218093839909126
                    [14, 5, 4, 1, 5, 0, 1, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 1010219193351602436
                [14, 5, 5, 1, 5, 1, 1, 4]
                (.node 1010219189056635141
                  [14, 5, 5, 0, 5, 1, 1, 5]
                  (.node 1010219189056569606
                    [14, 5, 5, 0, 5, 0, 1, 6]
                    .empty
                    .empty)
                  (.node 1010219189073346566
                    [14, 5, 5, 0, 6, 0, 0, 6]
                    .empty
                    .empty))
                (.node 1010220288568262661
                  [14, 5, 6, 0, 5, 1, 0, 5]
                  (.node 1010219193368313861
                    [14, 5, 5, 1, 6, 0, 0, 5]
                    .empty
                    .empty)
                  .empty))))
          (.node 1082275683582869766
            [15, 5, 4, 0, 5, 0, 1, 6]
            (.node 1081994212884414726
              [15, 4, 4, 1, 4, 1, 1, 6]
              (.node 1081713837436108806
                [15, 3, 5, 1, 5, 1, 0, 6]
                (.node 1081712737924481286
                  [15, 3, 4, 1, 5, 1, 1, 6]
                  (.node 1081711638429630726
                    [15, 3, 3, 1, 6, 1, 1, 6]
                    .empty
                    .empty)
                  (.node 1081712737941258246
                    [15, 3, 4, 1, 6, 1, 0, 6]
                    .empty
                    .empty))
                (.node 1081994208606224646
                  [15, 4, 4, 0, 5, 1, 1, 6]
                  (.node 1081993113406275846
                    [15, 4, 3, 1, 6, 0, 1, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 1081995308101075206
                [15, 4, 5, 0, 4, 1, 1, 6]
                (.node 1081994212901191941
                  [15, 4, 4, 1, 5, 1, 1, 5]
                  (.node 1081994212901126406
                    [15, 4, 4, 1, 5, 0, 1, 6]
                    .empty
                    .empty)
                  (.node 1081994212917903366
                    [15, 4, 4, 1, 6, 0, 0, 6]
                    .empty
                    .empty))
                (.node 1081995312412819461
                  [15, 4, 5, 1, 5, 1, 0, 5]
                  (.node 1081995308117852166
                    [15, 4, 5, 0, 5, 1, 0, 6]
                    .empty
                    .empty)
                  .empty)))
            (.node 1154050707427426566
              [16, 4, 3, 1, 5, 0, 1, 6]
              (.node 1153769232450781446
                [16, 3, 3, 1, 5, 1, 1, 6]
                (.node 1082276783077785861
                  [15, 5, 5, 0, 4, 1, 1, 5]
                  (.node 1082275687877837061
                    [15, 5, 4, 1, 5, 0, 1, 5]
                    .empty
                    .empty)
                  (.node 1082276783094497286
                    [15, 5, 5, 0, 5, 0, 0, 6]
                    .empty
                    .empty))
                (.node 1153770331962408966
                  [16, 3, 4, 1, 5, 1, 0, 6]
                  (.node 1153770331945632006
                    [16, 3, 4, 1, 4, 1, 1, 6]
                    .empty
                    .empty)
                  .empty))
              (.node 1154051806939054086
                [16, 4, 4, 1, 5, 0, 0, 6]
                (.node 1154051806922342661
                  [16, 4, 4, 1, 4, 1, 1, 5]
                  (.node 1154051802627375366
                    [16, 4, 4, 0, 4, 1, 1, 6]
                    .empty
                    .empty)
                  .empty)
                (.node 1154333277604020486
                  [16, 5, 4, 0, 4, 0, 1, 6]
                  (.node 1154052902139002886
                    [16, 4, 5, 0, 4, 1, 0, 6]
                    .empty
                    .empty)
                  .empty)))))))

private abbrev level3 := tree3.values

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem coversKeys3 : level3.all tree3.contains = true := by

  decide +kernel

private def tree4 : TableTree :=
  .node 6651352558507062187198364629162066176
    [5, 1, 1, 0, 1, 4, 5, 1, 0, 5, 5, 1, 5, 1, 1, 0]
    (.node 1355290972592924471134677237131183361
      [1, 5, 5, 1, 4, 1, 1, 0, 0, 1, 1, 4, 1, 5, 5, 1]
      (.node 1334440576606547642601393713550786816
        [1, 1, 1, 0, 5, 5, 5, 0, 5, 4, 5, 1, 1, 1, 1, 0]
        (.node 1329329409381572921143040573681500161
          [1, 0, 5, 0, 5, 1, 1, 5, 5, 1, 1, 5, 0, 5, 0, 1]
          (.node 5212975724504301445945440688210176
            [0, 1, 1, 5, 1, 5, 5, 0, 1, 5, 5, 0, 5, 1, 1, 0]
            (.node 5212896496341805628351925148713216
              [0, 1, 1, 4, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0]
              (.node 5212580821631788144612201939927296
                [0, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0]
                (.node 101492824819562503571106961883136
                  [0, 0, 5, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 5, 0, 0]
                  (.node 20678865969492264159022363508736
                    [0, 0, 1, 5, 1, 5, 5, 1, 1, 5, 5, 1, 5, 1, 0, 0]
                    .empty
                    .empty)
                  (.node 5192693314900668222265571441377536
                    [0, 1, 0, 5, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0]
                    .empty
                    .empty))
                (.node 5212896496341805628351925132001536
                  [0, 1, 1, 4, 1, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0]
                  (.node 5212580821631788144612201956638976
                    [0, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 5212975724499597525925174070804736
                [0, 1, 1, 5, 1, 5, 4, 1, 1, 4, 5, 1, 5, 1, 1, 0]
                (.node 5212975723295394073073790006395136
                  [0, 1, 1, 5, 1, 4, 5, 1, 1, 5, 4, 1, 5, 1, 1, 0]
                  (.node 5212975415019310071344445672980736
                    [0, 1, 1, 5, 0, 5, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 5212975723295394073074885223055616
                    [0, 1, 1, 5, 1, 4, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 5212975724504301445663970006466816
                  [0, 1, 1, 5, 1, 5, 5, 0, 1, 4, 5, 1, 5, 1, 1, 0]
                  (.node 5212975724504301373887850945249536
                    [0, 1, 1, 5, 1, 5, 5, 0, 0, 5, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 26062977117493608412503198568613121
              [0, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
              (.node 26062977117493608053345530710917376
                [0, 5, 5, 1, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0]
                (.node 26062975570068651539498223509243136
                  [0, 5, 5, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 5, 0]
                  (.node 25961565069475442294103852351227136
                    [0, 5, 0, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 5, 0]
                    .empty
                    .empty)
                  (.node 26062977117493608052215249870587136
                    [0, 5, 5, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 5, 0]
                    .empty
                    .empty))
                (.node 26062977117493608125403120453878016
                  [0, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]
                  (.node 26062977117493608125121649772134656
                    [0, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 1329248279748012833419888765907763456
                [1, 0, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                (.node 26062977117493608412503198585390336
                  [0, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                  (.node 26062977117493608412503198585324801
                    [0, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                    .empty
                    .empty)
                  (.node 1329248279748012833419888765891051776
                    [1, 0, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0]
                    .empty
                    .empty))
                (.node 1329309206200131783736954219990876161
                  [1, 0, 4, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 4, 0, 1]
                  (.node 1329248279748012833419888765907828736
                    [1, 0, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0]
                    .empty
                    .empty)
                  .empty))))
          (.node 1334440576297062651227074189217300736
            [1, 1, 1, 0, 4, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0]
            (.node 1329329488609735416888576499494748161
              [1, 0, 5, 1, 5, 1, 1, 4, 4, 1, 1, 5, 1, 5, 0, 1]
              (.node 1329329488608526509587762438555893761
                [1, 0, 5, 1, 5, 0, 1, 5, 5, 1, 0, 5, 1, 5, 0, 1]
                (.node 1329329409381572921143040573698277376
                  [1, 0, 5, 0, 5, 1, 1, 5, 5, 1, 1, 5, 1, 5, 0, 0]
                  (.node 1329329409381572921143040573698211841
                    [1, 0, 5, 0, 5, 1, 1, 5, 5, 1, 1, 5, 1, 4, 0, 1]
                    .empty
                    .empty)
                  (.node 1329329488300250425586033094222479361
                    [1, 0, 5, 1, 4, 1, 1, 5, 5, 1, 1, 4, 1, 5, 0, 1]
                    .empty
                    .empty))
                (.node 1329329488609730713040613822620303361
                  [1, 0, 5, 1, 5, 1, 0, 5, 5, 0, 1, 5, 1, 5, 0, 1]
                  (.node 1329329488608526509587763533772554241
                    [1, 0, 5, 1, 5, 0, 1, 5, 5, 1, 1, 4, 1, 5, 0, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 1334420294196944009377995314985697536
                [1, 1, 0, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                (.node 1329329488609735416960634089237708801
                  [1, 0, 5, 1, 5, 1, 1, 4, 5, 1, 1, 4, 1, 5, 0, 1]
                  (.node 1329329488609735416960352618555965441
                    [1, 0, 5, 1, 5, 1, 1, 4, 5, 0, 1, 5, 1, 5, 0, 1]
                    .empty
                    .empty)
                  (.node 1329329488609735416960634093532676096
                    [1, 0, 5, 1, 5, 1, 1, 4, 5, 1, 1, 5, 1, 5, 0, 0]
                    .empty
                    .empty))
                (.node 1334440576297062651226792718535557376
                  [1, 1, 1, 0, 4, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                  (.node 1334440576297062651155016599474340096
                    [1, 1, 1, 0, 4, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 1334440576605338735228804633045565696
              [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0]
              (.node 1334440576605338735228523158085632256
                [1, 1, 1, 0, 5, 4, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                (.node 1334440576297062651227074193512202496
                  [1, 1, 1, 0, 4, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                  (.node 1334440576297062651227074193495490816
                    [1, 1, 1, 0, 4, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 1334440576605338735156747039024414976
                    [1, 1, 1, 0, 5, 4, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 1334440576605338735228804628767375616
                  [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0]
                  (.node 1334440576605338735228803533550715136
                    [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 4, 1, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 1334440576606542938681654917615124736
                [1, 1, 1, 0, 5, 5, 4, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                (.node 1334440576605338735228804633062342656
                  [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0]
                  (.node 1334440576605338735228804633062277376
                    [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 1334440576606547642529617594489569536
                  [1, 1, 1, 0, 5, 5, 5, 0, 4, 5, 5, 1, 1, 1, 1, 0]
                  (.node 1334440576606542938681936392591769856
                    [1, 1, 1, 0, 5, 5, 4, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                    .empty
                    .empty)
                  .empty)))))
        (.node 1355189560854391296750885363945309441
          [1, 5, 0, 1, 5, 1, 1, 4, 5, 0, 1, 5, 1, 0, 5, 1]
          (.node 1350098676043874653400678589188342016
            [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 4, 1, 5, 1, 1, 0]
            (.node 1349997263995856487569380416302351616
              [1, 4, 0, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 5, 0]
              (.node 1334440576606547661048419262220206336
                [1, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 0, 0, 1, 0]
                (.node 1334440576606547642601675188510720256
                  [1, 1, 1, 0, 5, 5, 5, 0, 5, 5, 5, 1, 0, 1, 1, 0]
                  (.node 1334440576606547642601675184232530176
                    [1, 1, 1, 0, 5, 5, 5, 0, 5, 5, 5, 0, 1, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 1334440576606547642601675188527431936
                    [1, 1, 1, 0, 5, 5, 5, 0, 5, 5, 5, 1, 1, 0, 1, 0]
                    .empty
                    .empty))
                (.node 1349997263995856487569380416302351361
                  [1, 4, 0, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 4, 1]
                  (.node 1334440576606547661048419262236983296
                    [1, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 0, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 1350098676043874653327491813821711616
                [1, 4, 5, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 5, 0]
                (.node 1350098674496449696814774787460367616
                  [1, 4, 5, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 5, 0]
                  (.node 1350098674496449696814774787460367361
                    [1, 4, 5, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 4, 1]
                    .empty
                    .empty)
                  (.node 1350098676043874653327491813821711361
                    [1, 4, 5, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 4, 1]
                    .empty
                    .empty))
                (.node 1350098676043874653400398213723259136
                  [1, 4, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]
                  (.node 1350098676043874653328622094662041856
                    [1, 4, 5, 1, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 1355189481626228800933573319070844161
              [1, 5, 0, 0, 5, 1, 1, 5, 5, 1, 1, 5, 0, 0, 5, 1]
              (.node 1350098676043874653687779762536449281
                [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                (.node 1350098676043874653400679688699969536
                  [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 5, 1, 5, 1, 0, 0]
                  (.node 1350098676043874653400679684405002496
                    [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 1350098676043874653687779762519737601
                    [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
                    .empty
                    .empty))
                (.node 1350098676043874653687779762536514816
                  [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                  (.node 1350098676043874653687779762536514561
                    [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 1355189560853182389378296279161898241
                [1, 5, 0, 1, 5, 0, 1, 5, 5, 1, 1, 4, 1, 0, 5, 1]
                (.node 1355189560544906305376565839611823361
                  [1, 5, 0, 1, 4, 1, 1, 5, 5, 1, 1, 4, 1, 0, 5, 1]
                  (.node 1355189481626228800933573319087621376
                    [1, 5, 0, 0, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 5, 0]
                    .empty
                    .empty)
                  (.node 1355189560853182389378295183945237761
                    [1, 5, 0, 1, 5, 0, 1, 5, 5, 1, 0, 5, 1, 0, 5, 1]
                    .empty
                    .empty))
                (.node 1355189560854391296679109244884092161
                  [1, 5, 0, 1, 5, 1, 1, 4, 4, 1, 1, 5, 1, 0, 5, 1]
                  (.node 1355189560854386592831146568009647361
                    [1, 5, 0, 1, 5, 1, 0, 5, 5, 0, 1, 5, 1, 0, 5, 1]
                    .empty
                    .empty)
                  .empty))))
          (.node 1355290893674246966692814997447311616
            [1, 5, 5, 0, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0]
            (.node 1355270690492805829645886311614383361
              [1, 5, 4, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
              (.node 1355270690492805829285598362899580161
                [1, 5, 4, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 4, 5, 1]
                (.node 1355189560854391296751166838922020096
                  [1, 5, 0, 1, 5, 1, 1, 4, 5, 1, 1, 5, 1, 0, 5, 0]
                  (.node 1355189560854391296751166834627052801
                    [1, 5, 0, 1, 5, 1, 1, 4, 5, 1, 1, 4, 1, 0, 5, 1]
                    .empty
                    .empty)
                  (.node 1355270688945380872772881336538236161
                    [1, 5, 4, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 4, 5, 1]
                    .empty
                    .empty))
                (.node 1355270690492805829358786237777838336
                  [1, 5, 4, 1, 5, 1, 1, 0, 1, 5, 5, 1, 5, 0, 1, 0]
                  (.node 1355270690492805829358504762801193216
                    [1, 5, 4, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 1355290893674246966691684716590204161
                [1, 5, 5, 0, 5, 1, 1, 0, 0, 1, 1, 5, 0, 5, 5, 1]
                (.node 1355290892126822010178967690245571841
                  [1, 5, 5, 0, 0, 1, 1, 5, 5, 1, 1, 0, 1, 4, 5, 1]
                  (.node 1355290892126822010178967690228860161
                    [1, 5, 5, 0, 0, 1, 1, 5, 5, 1, 1, 0, 0, 5, 5, 1]
                    .empty
                    .empty)
                  (.node 1355290892126822010178967690245637376
                    [1, 5, 5, 0, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty))
                (.node 1355290893674246966691684716606981376
                  [1, 5, 5, 0, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 5, 0]
                  (.node 1355290893674246966691684716606915841
                    [1, 5, 5, 0, 5, 1, 1, 0, 0, 1, 1, 5, 1, 4, 5, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 1355290893674246967051972665321784576
              [1, 5, 5, 0, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
              (.node 1355290893674246966764872591485174016
                [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 1, 5, 0, 1, 0]
                (.node 1355290893674246966764872587190272256
                  [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]
                  (.node 1355290893674246966764591116508528896
                    [1, 5, 5, 0, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 1355290893674246966764872591468462336
                    [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 1, 4, 1, 1, 0]
                    .empty
                    .empty))
                (.node 1355290893674246967051972665321719041
                  [1, 5, 5, 0, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                  (.node 1355290893674246967051972665305007361
                    [1, 5, 5, 0, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 1355290971354984505924503616042108161
                [1, 5, 5, 1, 0, 1, 1, 4, 4, 1, 1, 0, 1, 5, 5, 1]
                (.node 1355290971354979802076540939167663361
                  [1, 5, 5, 1, 0, 1, 0, 5, 5, 0, 1, 0, 1, 5, 5, 1]
                  (.node 1355290971353775598623689555103253761
                    [1, 5, 5, 1, 0, 0, 1, 5, 5, 1, 0, 0, 1, 5, 5, 1]
                    .empty
                    .empty)
                  .empty)
                (.node 1355290971354984505996561210080036096
                  [1, 5, 5, 1, 0, 1, 1, 4, 5, 1, 1, 0, 1, 5, 5, 0]
                  (.node 1355290971354984505996279735103325441
                    [1, 5, 5, 1, 0, 1, 1, 4, 5, 0, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty)
                  .empty))))))
      (.node 5322205772823017789513328000888012801
        [4, 1, 5, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 1]
        (.node 1355290972902409481029209085517496576
          [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 4, 1, 5, 0, 1, 0]
          (.node 1355290972901200555496695629674251521
            [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
            (.node 1355290972901200555136406581464597761
              [1, 5, 5, 1, 5, 0, 1, 0, 0, 1, 0, 5, 1, 5, 5, 1]
              (.node 1355290972592924471494965190124176641
                [1, 5, 5, 1, 4, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
                (.node 1355290972592924471422907596103025921
                  [1, 5, 5, 1, 4, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]
                  (.node 1355290972592924471207865112009441536
                    [1, 5, 5, 1, 4, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 1355290972592924471494683715164243201
                    [1, 5, 5, 1, 4, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty))
                (.node 1355290972592924471494965190140953856
                  [1, 5, 5, 1, 4, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                  (.node 1355290972592924471494965190140888321
                    [1, 5, 5, 1, 4, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 1355290972901200555424638035653100801
                [1, 5, 5, 1, 5, 0, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]
                (.node 1355290972901200555209594456342855936
                  [1, 5, 5, 1, 5, 0, 1, 0, 1, 5, 4, 1, 5, 1, 1, 0]
                  (.node 1355290972901200555136407676681258241
                    [1, 5, 5, 1, 5, 0, 1, 0, 0, 1, 1, 4, 1, 5, 5, 1]
                    .empty
                    .empty)
                  (.node 1355290972901200555209595551559516416
                    [1, 5, 5, 1, 5, 0, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 1355290972901200555496694530179400961
                  [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 0, 0, 1, 5, 5, 1]
                  (.node 1355290972901200555496414154714318081
                    [1, 5, 5, 1, 5, 0, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 1355290972902404758949827389220455681
              [1, 5, 5, 1, 5, 1, 0, 0, 5, 1, 1, 0, 1, 4, 5, 1]
              (.node 1355290972902404758589257965529007361
                [1, 5, 5, 1, 5, 1, 0, 0, 0, 0, 1, 5, 1, 5, 5, 1]
                (.node 1355290972901200555496695629691028481
                  [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1]
                  (.node 1355290972901200555496695629690963201
                    [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                    .empty
                    .empty)
                  (.node 1355290972901200555496695629691028736
                    [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty))
                (.node 1355290972902404758949545914243810561
                  [1, 5, 5, 1, 5, 1, 0, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                  (.node 1355290972902404758662445840407265536
                    [1, 5, 5, 1, 5, 1, 0, 0, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 1355290972902409481028927610540851456
                [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 4, 1, 5, 1, 1, 0]
                (.node 1355290972902409480957152586696294656
                  [1, 5, 5, 1, 5, 1, 1, 0, 0, 5, 5, 0, 5, 1, 1, 0]
                  (.node 1355290972902409480956871116014551296
                    [1, 5, 5, 1, 5, 1, 1, 0, 0, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 1355290972902409481028647235075768576
                    [1, 5, 5, 1, 5, 1, 1, 0, 1, 3, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 1355290972902409481028928710052478976
                  [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 0, 0]
                  (.node 1355290972902409481028928705757511936
                    [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))))
          (.node 5322124562723355240186229792010469636
            [4, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 4]
            (.node 1355290972902409481316310258865669121
              [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 4, 1]
              (.node 1355290972902409481316310258848892161
                [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 4, 5, 1]
                (.node 1355290972902409481029210180734157056
                  [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 0, 1, 0]
                  (.node 1355290972902409481029210180717445376
                    [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 4, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 1355290972902409481100423354136985856
                    [1, 5, 5, 1, 5, 1, 1, 0, 2, 2, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 1355290972902409481316310258865603841
                  [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 3, 5, 1]
                  (.node 1355290972902409481316310258848957696
                    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 1355290972902409481316592837715886336
                [1, 5, 5, 1, 5, 1, 1, 0, 5, 2, 2, 1, 5, 1, 1, 0]
                (.node 1355290972902409481316310258882315521
                  [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 2, 2, 5, 1]
                  (.node 1355290972902409481316310258865669376
                    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 0]
                    .empty
                    .empty)
                  (.node 1355290972902409481316310258932646401
                    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 5, 2, 2, 1]
                    .empty
                    .empty))
                (.node 2684518968687325354220117319145882881
                  [2, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 2, 5, 1]
                  (.node 2684518968687325353932172820379402496
                    [2, 5, 5, 1, 5, 1, 1, 0, 1, 2, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 5322124562723355240474460168178893056
              [4, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
              (.node 5322124562723355240474178693202247936
                [4, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                (.node 5322124562723355240186229792094290176
                  [4, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0]
                  (.node 5322124562723355240186229792077578496
                    [4, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 5322124562723355240402402574141030656
                    [4, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 5322124562723355240474460168162181376
                  [4, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0]
                  (.node 5322124562723355240474460163883991296
                    [4, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 5322124958858123182698070587750809856
                [4, 1, 1, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0]
                (.node 5322124958858123182698069492534149376
                  [4, 1, 1, 5, 1, 0, 5, 1, 5, 5, 0, 1, 5, 1, 1, 0]
                  (.node 5322124958858123182409839116382437636
                    [4, 1, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 4]
                    .empty
                    .empty)
                  .empty)
                (.node 5322124958864144199962326412856197376
                  [4, 1, 1, 5, 1, 5, 0, 1, 5, 0, 5, 1, 5, 1, 1, 0]
                  (.node 5322124958864144199674096036704485636
                    [4, 1, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 4]
                    .empty
                    .empty)
                  .empty)))))
        (.node 6646160657790525244949372600655609861
          [5, 0, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 0, 5]
          (.node 6646160261649736285461506356045414656
            [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0]
            (.node 5342974959019217060742069689830933761
              [4, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
              (.node 5342974959019217060454120788722976001
                [4, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1]
                (.node 5342893830618742493346035667881166081
                  [4, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1]
                  (.node 5342893830618742493346034572664505601
                    [4, 5, 1, 1, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 1]
                    .empty
                    .empty)
                  (.node 5342974959019217060454120788706264321
                    [4, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1]
                    .empty
                    .empty))
                (.node 5342974959019217060670293570769716481
                  [4, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]
                  (.node 5342974959019217060454120788723041536
                    [4, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6646160261649736285461506355961593861
                [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 0, 5]
                (.node 5342974959019217060742351164807578881
                  [4, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                  (.node 5342974959019217060742351164790867201
                    [4, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
                    .empty
                    .empty)
                  (.node 5342974959019217060742351164807644416
                    [4, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty))
                (.node 6646160261649736285461506356028702976
                  [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0]
                  (.node 6646160261649736285461506355961594116
                    [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 4]
                    .empty
                    .empty)
                  .empty)))
            (.node 6646160261649736285749736732130017536
              [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
              (.node 6646160261649736285749735632618455296
                [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 4, 1, 1, 1, 1, 0]
                (.node 6646160261649736285677679138092155136
                  [5, 0, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0]
                  (.node 6646160261649736285461506356045479936
                    [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 1, 0, 0]
                    .empty
                    .empty)
                  (.node 6646160261649736285749455257153372416
                    [5, 0, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6646160261649736285749736732113305856
                  [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0]
                  (.node 6646160261649736285749736727835115776
                    [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6646160657784504227685115680333562116
                [5, 0, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 4]
                (.node 6646160657784504227685115680333561861
                  [5, 0, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 0, 5]
                  (.node 6646160261649736285749736732130082816
                    [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 6646160657784504227973347151701934336
                  [5, 0, 1, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0]
                  (.node 6646160657784504227973346056485273856
                    [5, 0, 1, 5, 1, 0, 5, 1, 5, 5, 0, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))))
          (.node 6651332672233435403859396111036907776
            [5, 1, 0, 5, 1, 0, 5, 1, 4, 5, 1, 1, 5, 1, 1, 0]
            (.node 6646241471749398834788886035520880641
              [5, 0, 5, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 5, 0, 1]
              (.node 6646160657790525245237884447489065216
                [5, 0, 1, 5, 1, 5, 0, 1, 5, 1, 5, 0, 5, 1, 1, 0]
                (.node 6646160657790525245165826857746104576
                  [5, 0, 1, 5, 1, 5, 0, 1, 4, 1, 5, 1, 5, 1, 1, 0]
                  (.node 6646160657790525244949372600655610116
                    [5, 0, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 4]
                    .empty
                    .empty)
                  (.node 6646160657790525245237602976807321856
                    [5, 0, 1, 5, 1, 5, 0, 1, 5, 0, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6646241471749398834788604564839137281
                  [5, 0, 5, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 1]
                  (.node 6646241471749398834716828445777920001
                    [5, 0, 5, 1, 5, 1, 1, 0, 4, 1, 1, 5, 1, 5, 0, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 6651332276098667461707561806231306496
                [5, 1, 0, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                (.node 6651332276098667461419612905039462661
                  [5, 1, 0, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 0, 1, 5]
                  (.node 6646241471749398834788886039815847936
                    [5, 0, 5, 1, 5, 1, 1, 0, 5, 1, 1, 5, 1, 5, 0, 0]
                    .empty
                    .empty)
                  (.node 6651332276098667461419612905123348736
                    [5, 1, 0, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0]
                    .empty
                    .empty))
                (.node 6651332672233435403643222229411430661
                  [5, 1, 0, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 0, 1, 5]
                  (.node 6651332276098667461707843281207951616
                    [5, 1, 0, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 6651352558198786103268691779354951936
              [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0]
              (.node 6651352558198786103196634189611991296
                [5, 1, 1, 0, 0, 5, 5, 1, 0, 5, 5, 1, 5, 1, 1, 0]
                (.node 6651332672233435403931453700779868416
                  [5, 1, 0, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0]
                  (.node 6651332672233435403931172230098125056
                    [5, 1, 0, 5, 1, 0, 5, 1, 5, 4, 1, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651332672239456420907479149733478661
                    [5, 1, 0, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 0, 1, 5]
                    .empty
                    .empty))
                (.node 6651352558198786103268691779271065861
                  [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 0, 0, 1, 1, 5]
                  (.node 6651352558198786103268410308673208576
                    [5, 1, 1, 0, 0, 5, 5, 1, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352558198786103484864565696594176
                [5, 1, 1, 0, 0, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0]
                (.node 6651352558198786103268691783649853696
                  [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0]
                  (.node 6651352558198786103268691783633142016
                    [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 6651352558198786103556922155439554816
                  [5, 1, 1, 0, 0, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0]
                  (.node 6651352558198786103556640684757811456
                    [5, 1, 1, 0, 0, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))))))
    (.node 6651433768607933662417416531850035201
      [5, 1, 5, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 4, 0, 1]
      (.node 6651352558508271113593592287124848896
        [5, 1, 1, 0, 1, 5, 5, 1, 8, 2, 2, 1, 2, 1, 1, 0]
        (.node 6651352558508271094859465560711823616
          [5, 1, 1, 0, 1, 5, 5, 0, 4, 5, 5, 1, 1, 1, 1, 0]
          (.node 6651352558508266390723272507668889861
            [5, 1, 1, 0, 1, 5, 4, 1, 1, 4, 5, 1, 0, 1, 1, 5]
            (.node 6651352558507062187270422223199928576
              [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0]
              (.node 6651352558507062187270422218821140741
                [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 0, 0, 1, 1, 5]
                (.node 6651352558507062187270421123604480261
                  [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 4, 1, 0, 1, 1, 5]
                  (.node 6651352558507062187270140748223283456
                    [5, 1, 1, 0, 1, 4, 5, 1, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352558507062187270421123688366336
                    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 4, 1, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352558507062187270422223183216896
                  [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0]
                  (.node 6651352558507062187270422218905026816
                    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352558507062187558651499772969216
                [5, 1, 1, 0, 1, 4, 5, 1, 5, 5, 4, 1, 1, 1, 1, 0]
                (.node 6651352558507062187486595005246669056
                  [5, 1, 1, 0, 1, 4, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0]
                  (.node 6651352558507062187270422223199993856
                    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 1, 5, 1, 0, 0]
                    .empty
                    .empty)
                  (.node 6651352558507062187558371124307886336
                    [5, 1, 1, 0, 1, 4, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352558507062187558652599284596736
                  [5, 1, 1, 0, 1, 4, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0]
                  (.node 6651352558507062187558652594989629696
                    [5, 1, 1, 0, 1, 4, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 6651352558508271094643011303604551941
              [5, 1, 1, 0, 1, 5, 5, 0, 1, 4, 5, 1, 0, 1, 1, 5]
              (.node 6651352558508266391011784358814023936
                [5, 1, 1, 0, 1, 5, 4, 1, 5, 5, 5, 1, 1, 0, 1, 0]
                (.node 6651352558508266390723553982729421056
                  [5, 1, 1, 0, 1, 5, 4, 1, 1, 5, 5, 1, 5, 0, 1, 0]
                  (.node 6651352558508266390723272507752775936
                    [5, 1, 1, 0, 1, 5, 4, 1, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352558508266391011502883837378816
                    [5, 1, 1, 0, 1, 5, 4, 1, 5, 4, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352558508271094571235184627220736
                  [5, 1, 1, 0, 1, 5, 5, 0, 0, 5, 5, 1, 5, 1, 1, 0]
                  (.node 6651352558508271094571235184543334661
                    [5, 1, 1, 0, 1, 5, 5, 0, 0, 5, 5, 1, 0, 1, 1, 5]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352558508271094643292778581262596
                [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 1, 0, 1, 1, 4]
                (.node 6651352558508271094643292774286295301
                  [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 0, 0, 1, 1, 5]
                  (.node 6651352558508271094643011303688438016
                    [5, 1, 1, 0, 1, 5, 5, 0, 1, 4, 5, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352558508271094643292774370181376
                    [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352558508271094643292778665083136
                  [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 1, 5, 0, 1, 0]
                  (.node 6651352558508271094643292778648371456
                    [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 1, 4, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))))
          (.node 6651352558508271113306209634421309696
            [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 1, 0, 1, 0]
            (.node 6651352558508271113090036852357857536
              [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 4, 0, 1, 0]
              (.node 6651352558508271094931523154749686016
                [5, 1, 1, 0, 1, 5, 5, 0, 5, 5, 5, 1, 1, 0, 1, 0]
                (.node 6651352558508271094931523150454784256
                  [5, 1, 1, 0, 1, 5, 5, 0, 5, 5, 5, 0, 1, 1, 1, 0]
                  (.node 6651352558508271094931241679773040896
                    [5, 1, 1, 0, 1, 5, 5, 0, 5, 4, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352558508271094931523154732974336
                    [5, 1, 1, 0, 1, 5, 5, 0, 5, 5, 5, 1, 0, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352558508271113090036852341145856
                  [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 3, 1, 1, 0]
                  (.node 6651352558508271113090036852290814211
                    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 3]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352558508271113305928159444664576
                [5, 1, 1, 0, 1, 5, 5, 1, 4, 4, 5, 1, 1, 1, 1, 0]
                (.node 6651352558508271113162094446362296576
                  [5, 1, 1, 0, 1, 5, 5, 1, 2, 5, 5, 1, 2, 1, 1, 0]
                  (.node 6651352558508271113090036852374634496
                    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 0, 0]
                    .empty
                    .empty)
                  (.node 6651352558508271113234152040383447296
                    [5, 1, 1, 0, 1, 5, 5, 1, 3, 5, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352558508271113306209634404598016
                  [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 0, 1, 1, 0]
                  (.node 6651352558508271113306209630126407936
                    [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 0, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 6651352558508271113377985753482592256
              [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 0, 0]
              (.node 6651352558508271113377985749187625216
                [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 0, 1, 1, 1, 0]
                (.node 6651352558508271113377704278505881856
                  [5, 1, 1, 0, 1, 5, 5, 1, 5, 3, 5, 1, 1, 1, 1, 0]
                  (.node 6651352558508271113377422803545948416
                    [5, 1, 1, 0, 1, 5, 5, 1, 5, 2, 5, 1, 2, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352558508271113377984653970964736
                    [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 4, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352558508271113377985753482526976
                  [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 0, 1, 0]
                  (.node 6651352558508271113377985753465815296
                    [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 0, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352558508271113378267224164270336
                [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 1, 0, 1, 0]
                (.node 6651352558508271113378267224147558656
                  [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 0, 1, 1, 0]
                  (.node 6651352558508271113378266128947609856
                    [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 4, 1, 1, 0, 1, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 6651352558508271113449480397567099136
                  [5, 1, 1, 0, 1, 5, 5, 1, 6, 2, 5, 1, 1, 1, 1, 0]
                  (.node 6651352558508271113378267228459237376
                    [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 0, 0]
                    .empty
                    .empty)
                  .empty)))))
        (.node 6651352954643039036866902102953230596
          [5, 1, 1, 5, 1, 0, 5, 0, 1, 5, 0, 1, 5, 1, 1, 4]
          (.node 6651352875414876541337540058782171136
            [5, 1, 1, 4, 1, 0, 5, 1, 5, 5, 1, 1, 5, 1, 0, 0]
            (.node 6651352875414876541049308583102054661
              [5, 1, 1, 4, 1, 0, 5, 1, 1, 5, 0, 1, 4, 1, 1, 5]
              (.node 6651352559742584374988630833720525056
                [5, 1, 1, 0, 5, 2, 5, 1, 2, 5, 5, 1, 1, 1, 1, 0]
                (.node 6651352558817756123055497109091451136
                  [5, 1, 1, 0, 2, 5, 5, 1, 3, 5, 5, 1, 0, 1, 1, 0]
                  (.node 6651352558817756122983439515070300416
                    [5, 1, 1, 0, 2, 5, 5, 1, 2, 5, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352558817756123198767872253952256
                    [5, 1, 1, 0, 2, 5, 5, 1, 5, 2, 5, 1, 1, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352559746196985563354469492654336
                  [5, 1, 1, 0, 5, 5, 2, 1, 5, 2, 5, 1, 1, 1, 1, 0]
                  (.node 6651352559742584375204800317299425536
                    [5, 1, 1, 0, 5, 2, 5, 1, 5, 5, 2, 1, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352875414876541337258583805460736
                [5, 1, 1, 4, 1, 0, 5, 1, 5, 4, 1, 1, 5, 1, 1, 0]
                (.node 6651352875414876541049308583118831876
                  [5, 1, 1, 4, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 4]
                  (.node 6651352875414876541049308583118766341
                    [5, 1, 1, 4, 1, 0, 5, 1, 1, 5, 0, 1, 5, 0, 1, 5]
                    .empty
                    .empty)
                  (.node 6651352875414876541265482464744243456
                    [5, 1, 1, 4, 1, 0, 5, 1, 4, 5, 1, 1, 5, 1, 1, 0]
                    .empty
                    .empty))
                (.node 6651352875414876541337540054487204096
                  [5, 1, 1, 4, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0]
                  (.node 6651352875414876541337538959270543616
                    [5, 1, 1, 4, 1, 0, 5, 1, 5, 5, 0, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 6651352954339575062756558023965081861
              [5, 1, 1, 5, 0, 5, 0, 1, 1, 0, 5, 0, 5, 1, 1, 5]
              (.node 6651352875420897558601795879592591616
                [5, 1, 1, 4, 1, 5, 0, 1, 5, 0, 5, 1, 5, 1, 1, 0]
                (.node 6651352875420897558313565503440814341
                  [5, 1, 1, 4, 1, 5, 0, 1, 1, 0, 5, 1, 5, 0, 1, 5]
                  (.node 6651352875420897558313565503424102661
                    [5, 1, 1, 4, 1, 5, 0, 1, 1, 0, 5, 1, 4, 1, 1, 5]
                    .empty
                    .empty)
                  (.node 6651352875420897558313565503440879876
                    [5, 1, 1, 4, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 4]
                    .empty
                    .empty))
                (.node 6651352954333554045492301103643033861
                  [5, 1, 1, 5, 0, 0, 5, 1, 1, 5, 0, 0, 5, 1, 1, 5]
                  (.node 6651352875420897558602077354569236736
                    [5, 1, 1, 4, 1, 5, 0, 1, 5, 1, 5, 1, 5, 0, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352954643039036794844508915302661
                [5, 1, 1, 5, 1, 0, 5, 0, 0, 5, 0, 1, 5, 1, 1, 5]
                (.node 6651352954643034333235394778385940736
                  [5, 1, 1, 5, 1, 0, 4, 1, 5, 5, 1, 0, 5, 1, 1, 0]
                  (.node 6651352954643034332946881832040857861
                    [5, 1, 1, 5, 1, 0, 4, 1, 1, 4, 0, 1, 5, 1, 1, 5]
                    .empty
                    .empty)
                  .empty)
                (.node 6651352954643039036866902098658263301
                  [5, 1, 1, 5, 1, 0, 5, 0, 1, 5, 0, 0, 5, 1, 1, 5]
                  (.node 6651352954643039036866620627976519941
                    [5, 1, 1, 5, 1, 0, 5, 0, 1, 4, 0, 1, 5, 1, 1, 5]
                    .empty
                    .empty)
                  .empty))))
          (.node 6651352954649060054131159018980311301
            [5, 1, 1, 5, 1, 5, 0, 0, 1, 0, 5, 0, 5, 1, 1, 5]
            (.node 6651352954643039055601596173054443776
              [5, 1, 1, 5, 1, 0, 5, 1, 5, 4, 1, 0, 5, 1, 1, 0]
              (.node 6651352954643039055529818958776566016
                [5, 1, 1, 5, 1, 0, 5, 1, 4, 5, 0, 1, 5, 1, 1, 0]
                (.node 6651352954643039037155133574321602816
                  [5, 1, 1, 5, 1, 0, 5, 0, 5, 5, 1, 0, 5, 1, 1, 0]
                  (.node 6651352954643039037155132479104942336
                    [5, 1, 1, 5, 1, 0, 5, 0, 5, 5, 0, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352954643039055313646176662782211
                    [5, 1, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 3]
                    .empty
                    .empty))
                (.node 6651352954643039055601595077837783296
                  [5, 1, 1, 5, 1, 0, 5, 1, 5, 4, 0, 1, 5, 1, 1, 0]
                  (.node 6651352954643039055529820053993226496
                    [5, 1, 1, 5, 1, 0, 5, 1, 4, 5, 1, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6651352954647851146758288463515156741
                [5, 1, 1, 5, 1, 4, 0, 1, 1, 0, 5, 0, 5, 1, 1, 5]
                (.node 6651352954643039055601877648031154176
                  [5, 1, 1, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 0, 0]
                  (.node 6651352954643039055601876548519526656
                    [5, 1, 1, 5, 1, 0, 5, 1, 5, 5, 0, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6651352954647851146758287368298496261
                    [5, 1, 1, 5, 1, 4, 0, 1, 1, 0, 4, 1, 5, 1, 1, 5]
                    .empty
                    .empty))
                (.node 6651352954649060054059101429237350661
                  [5, 1, 1, 5, 1, 5, 0, 0, 0, 0, 5, 1, 5, 1, 1, 5]
                  (.node 6651352954647851147046800314643579136
                    [5, 1, 1, 5, 1, 4, 0, 1, 5, 1, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 6651433689379771148152797467624407041
              [5, 1, 5, 0, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 1]
              (.node 6651352954649060072794075879098614016
                [5, 1, 1, 5, 1, 5, 0, 1, 4, 0, 5, 1, 5, 1, 1, 0]
                (.node 6651352954649060054419389399426990336
                  [5, 1, 1, 5, 1, 5, 0, 0, 5, 0, 5, 1, 5, 1, 1, 0]
                  (.node 6651352954649060054131159023275278596
                    [5, 1, 1, 5, 1, 5, 0, 0, 1, 0, 5, 1, 5, 1, 1, 4]
                    .empty
                    .empty)
                  (.node 6651352954649060072577903096984830211
                    [5, 1, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 3]
                    .empty
                    .empty))
                (.node 6651352954649060072866414943818219776
                  [5, 1, 1, 5, 1, 5, 0, 1, 5, 1, 5, 0, 5, 0, 1, 0]
                  (.node 6651352954649060072866133468841574656
                    [5, 1, 1, 5, 1, 5, 0, 1, 5, 0, 5, 0, 5, 1, 1, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6651433768607933662345077467130429441
                [5, 1, 5, 1, 5, 1, 1, 0, 4, 0, 1, 5, 1, 5, 0, 1]
                (.node 6651433768606724736597801902675394561
                  [5, 1, 5, 1, 5, 0, 1, 0, 5, 1, 1, 4, 1, 5, 0, 1]
                  (.node 6651433689379771148153078942601052161
                    [5, 1, 5, 0, 5, 1, 1, 0, 5, 1, 1, 5, 1, 4, 0, 1]
                    .empty
                    .empty)
                  .empty)
                (.node 6651433768607933662417135061168357376
                  [5, 1, 5, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 0]
                  (.node 6651433768607933662417135056873390081
                    [5, 1, 5, 1, 5, 1, 1, 0, 5, 0, 1, 4, 1, 5, 0, 1]
                    .empty
                    .empty)
                  .empty))))))
      (.node 6672202954494647923536582780278605056
        [5, 5, 5, 1, 0, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0]
        (.node 6672121826403658366177785134123582721
          [5, 5, 1, 1, 5, 1, 1, 0, 4, 1, 1, 4, 1, 0, 5, 1]
          (.node 6667010657945598106017627728758768641
            [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1]
            (.node 6667010657945598105729397352674165761
              [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 4, 1]
              (.node 6666929529545123538621312231832290561
                [5, 4, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1]
                (.node 6656626065466468490045947010999452161
                  [5, 2, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 2, 1]
                  (.node 6656626065466468489758843638628024576
                    [5, 2, 5, 1, 5, 1, 1, 0, 1, 5, 2, 1, 5, 1, 1, 0]
                    .empty
                    .empty)
                  (.node 6666929529545123538621311136615630081
                    [5, 4, 1, 1, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 1]
                    .empty
                    .empty))
                (.node 6667010657945598105729397352674100481
                  [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1]
                  (.node 6667010657945598105729397352657388801
                    [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 6667010657945598106017626629247141121
                [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 0, 0, 1, 5, 5, 1]
                (.node 6667010657945598105945570134720840961
                  [5, 4, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]
                  (.node 6667010657945598105729397352674166016
                    [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0]
                    .empty
                    .empty)
                  (.node 6667010657945598106017346253782058241
                    [5, 4, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty))
                (.node 6667010657945598106017627728758703361
                  [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                  (.node 6667010657945598106017627728741991681
                    [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 6672121747175495851985223663935816961
              [5, 5, 1, 0, 5, 1, 1, 0, 5, 0, 1, 5, 1, 0, 5, 1]
              (.node 6672101543994054714579418780910224641
                [5, 5, 0, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1]
                (.node 6672101543994054714507361191167264001
                  [5, 5, 0, 1, 5, 1, 1, 0, 4, 1, 1, 5, 1, 0, 5, 1]
                  (.node 6667010657945598106017627728758768896
                    [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty)
                  (.node 6672101543994054714579137310228481281
                    [5, 5, 0, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 0, 5, 1]
                    .empty
                    .empty))
                (.node 6672121747175495851913447544874599681
                  [5, 5, 1, 0, 5, 1, 1, 0, 4, 1, 1, 5, 1, 0, 5, 1]
                  (.node 6672101543994054714579418785205191936
                    [5, 5, 0, 1, 5, 1, 1, 0, 5, 1, 1, 5, 1, 0, 5, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6672121747175495851985505138912527616
                [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 1, 5, 1, 0, 5, 0]
                (.node 6672121747175495851985505134617560321
                  [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1]
                  (.node 6672121747175495851985504039400899841
                    [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 1]
                    .empty
                    .empty)
                  (.node 6672121747175495851985505138912527361
                    [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 1, 5, 1, 0, 4, 1]
                    .empty
                    .empty))
                (.node 6672121826403658366177784038906922241
                  [5, 5, 1, 1, 5, 1, 1, 0, 4, 1, 0, 5, 1, 0, 5, 1]
                  (.node 6672121826403653643883359858516296961
                    [5, 5, 1, 1, 5, 1, 0, 0, 5, 1, 1, 4, 1, 0, 5, 1]
                    .empty
                    .empty)
                  .empty))))
          (.node 6672182672394529281975734277836637441
            [5, 5, 4, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
            (.node 6672121826403658366249842728161510656
              [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 0]
              (.node 6672121826403658366249841632944850176
                [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 0]
                (.node 6672121826403658366249561253184800001
                  [5, 5, 1, 1, 5, 1, 1, 0, 5, 0, 1, 4, 1, 0, 5, 1]
                  (.node 6672121826403658366249560157968139521
                    [5, 5, 1, 1, 5, 1, 1, 0, 5, 0, 0, 5, 1, 0, 5, 1]
                    .empty
                    .empty)
                  (.node 6672121826403658366249841628649882881
                    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 0, 4, 1, 0, 5, 1]
                    .empty
                    .empty))
                (.node 6672121826403658366249842728161510401
                  [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 4, 1]
                  (.node 6672121826403658366249842723866543361
                    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 3, 1, 0, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 6672142108813262017920266666822862081
                [5, 5, 2, 1, 5, 1, 1, 0, 5, 1, 1, 2, 1, 0, 5, 1]
                (.node 6672142108813262017632322159466578176
                  [5, 5, 2, 1, 5, 1, 1, 0, 1, 2, 5, 1, 5, 1, 1, 0]
                  (.node 6672121826403658366249843819083203841
                    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 2, 2, 1, 0, 5, 1]
                    .empty
                    .empty)
                  (.node 6672142108813262017920266658233058561
                    [5, 5, 2, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 2, 5, 1]
                    .empty
                    .empty))
                (.node 6672182672394529281975452802859992321
                  [5, 5, 4, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                  (.node 6672182672394529281687503901752034561
                    [5, 5, 4, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 6672202875575970419381820631543973121
              [5, 5, 5, 0, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]
              (.node 6672202875575970419309763037506110721
                [5, 5, 5, 0, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]
                (.node 6672202875575970419093590255459370241
                  [5, 5, 5, 0, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1]
                  (.node 6672202875575970419093590255442658561
                    [5, 5, 5, 0, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1]
                    .empty
                    .empty)
                  (.node 6672202875575970419093590255459435776
                    [5, 5, 5, 0, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0]
                    .empty
                    .empty))
                (.node 6672202875575970419381820631527261441
                  [5, 5, 5, 0, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]
                  (.node 6672202875575970419381539156567328001
                    [5, 5, 5, 0, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 6672202954494647923536301305301894401
                [5, 5, 5, 1, 0, 1, 1, 0, 1, 0, 1, 0, 5, 5, 5, 1]
                (.node 6672202954494647923464525186240677121
                  [5, 5, 5, 1, 0, 1, 1, 0, 0, 1, 1, 0, 5, 5, 5, 1]
                  (.node 6672202875575970419381820631544038656
                    [5, 5, 5, 0, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 6672202954494647923536582780278539521
                  [5, 5, 5, 1, 0, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1]
                  (.node 6672202954494647923536582780261827841
                    [5, 5, 5, 1, 0, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1]
                    .empty
                    .empty)
                  .empty)))))
        (.node 6672202954804132933429985443041117441
          [5, 5, 5, 1, 1, 1, 1, 0, 2, 1, 1, 0, 5, 2, 5, 1]
          (.node 6672202954802924007826543595913282561
            [5, 5, 5, 1, 1, 0, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1]
            (.node 6672202954802924007538313219811902721
              [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1]
              (.node 6672202954802924007466255625790752001
                [5, 5, 5, 1, 1, 0, 1, 0, 0, 1, 1, 0, 5, 5, 5, 1]
                (.node 6672202954494647923824531681386497281
                  [5, 5, 5, 1, 0, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                  (.node 6672202954494647923752755562325280001
                    [5, 5, 5, 1, 0, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty)
                  (.node 6672202954494647923824813156363207936
                    [5, 5, 5, 1, 0, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty))
                (.node 6672202954802924007538312120317052161
                  [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 0, 0, 5, 5, 5, 1]
                  (.node 6672202954802924007538031744851969281
                    [5, 5, 5, 1, 1, 0, 1, 0, 1, 0, 1, 0, 5, 5, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 6672202954802924007754486001875354881
                [5, 5, 5, 1, 1, 0, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]
                (.node 6672202954802924007538313219828679681
                  [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 5, 5, 4, 1]
                  (.node 6672202954802924007538313219828614401
                    [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1]
                    .empty
                    .empty)
                  (.node 6672202954802924007538313219828679936
                    [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0]
                    .empty
                    .empty))
                (.node 6672202954802924007826542496401655041
                  [5, 5, 5, 1, 1, 0, 1, 0, 5, 1, 0, 0, 1, 5, 5, 1]
                  (.node 6672202954802924007826262120936572161
                    [5, 5, 5, 1, 1, 0, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty)
                  .empty)))
            (.node 6672202954804132933357927848986543361
              [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 4, 5, 1]
              (.node 6672202954804128211279393880466064641
                [5, 5, 5, 1, 1, 1, 0, 0, 5, 0, 1, 0, 1, 5, 5, 1]
                (.node 6672202954804128210991163504381461761
                  [5, 5, 5, 1, 1, 1, 0, 0, 1, 0, 1, 0, 5, 5, 5, 1]
                  (.node 6672202954802924007826543595913282816
                    [5, 5, 5, 1, 1, 0, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty)
                  (.node 6672202954804128210991444979358106881
                    [5, 5, 5, 1, 1, 1, 0, 0, 1, 1, 1, 0, 5, 4, 5, 1]
                    .empty
                    .empty))
                (.node 6672202954804132933357927848969831681
                  [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 3, 5, 5, 1]
                  (.node 6672202954804128211279675355442709761
                    [5, 5, 5, 1, 1, 1, 0, 0, 5, 1, 1, 0, 1, 4, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 6672202954804132933357927849003320321
                [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 4, 1]
                (.node 6672202954804132933357927849003255041
                  [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 3, 5, 1]
                  (.node 6672202954804132933357927848986608896
                    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 6672202954804132933429985442990982401
                  [5, 5, 5, 1, 1, 1, 1, 0, 2, 1, 1, 0, 2, 5, 5, 1]
                  (.node 6672202954804132933357927849003320576
                    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 0]
                    .empty
                    .empty)
                  .empty))))
          (.node 6672202954804132933646158225087923456
            [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 0]
            (.node 6672202954804132933645876750094501121
              [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 0, 5, 5, 1]
              (.node 6672202954804132933574100631049995521
                [5, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 4, 5, 1]
                (.node 6672202954804132933573819156073350401
                  [5, 5, 5, 1, 1, 1, 1, 0, 4, 0, 1, 0, 1, 5, 5, 1]
                  (.node 6672202954804132933502043037012133121
                    [5, 5, 5, 1, 1, 1, 1, 0, 3, 1, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty)
                  (.node 6672202954804132933574100631033283841
                    [5, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 0, 5, 5, 1]
                    .empty
                    .empty))
                (.node 6672202954804132933645875650599650561
                  [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 0, 0, 1, 5, 5, 1]
                  (.node 6672202954804132933574100631050061056
                    [5, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty)
                  .empty))
              (.node 6672202954804132933646157125576295681
                [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 0, 0, 1, 4, 5, 1]
                (.node 6672202954804132933645876750111278081
                  [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 4, 1]
                  (.node 6672202954804132933645876750111212801
                    [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 4, 5, 1]
                    .empty
                    .empty)
                  (.node 6672202954804132933645876750111278336
                    [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 0]
                    .empty
                    .empty))
                (.node 6672202954804132933646158225087923201
                  [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 4, 1]
                  (.node 6672202954804132933646158225071211776
                    [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 0]
                    .empty
                    .empty)
                  .empty)))
            (.node 8001430951826988845835345564562161921
              [6, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 1, 1, 1, 1, 1]
              (.node 6672202956042072972931538499986915841
                [5, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 2, 2, 1]
                (.node 6672202954805346600278999797684306176
                  [5, 5, 5, 1, 1, 2, 2, 1, 5, 1, 1, 0, 5, 1, 1, 0]
                  (.node 6672202954804132933646158225154900481
                    [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 5, 2, 2, 1]
                    .empty
                    .empty)
                  (.node 6672202955113617943251330511698986241
                    [5, 5, 5, 1, 2, 1, 1, 0, 2, 1, 1, 0, 1, 5, 5, 1]
                    .empty
                    .empty))
                (.node 8001430950589048806333792503254549761
                  [6, 5, 5, 1, 1, 1, 1, 0, 2, 1, 1, 0, 1, 5, 5, 1]
                  (.node 8001349822188574239153649779851920641
                    [6, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 2, 1, 0, 5, 1]
                    .empty
                    .empty)
                  .empty))
              (.node 10644310051892761079293332985666142721
                [8, 2, 5, 1, 2, 1, 1, 0, 5, 1, 1, 0, 1, 5, 2, 1]
                (.node 10644310051892761079077160203552359681
                  [8, 2, 5, 1, 2, 1, 1, 0, 2, 1, 1, 0, 1, 5, 5, 1]
                  (.node 8001430951826988864282089638271713536
                    [6, 5, 5, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 0]
                    .empty
                    .empty)
                  .empty)
                (.node 10659826095239554644061140780318721281
                  [8, 5, 2, 1, 2, 1, 1, 2, 5, 1, 1, 0, 1, 0, 5, 1]
                  (.node 10659826095239554607167652632899749121
                    [8, 5, 2, 1, 2, 1, 1, 0, 5, 1, 1, 0, 1, 2, 5, 1]
                    .empty
                    .empty)
                  .empty)))))))

private abbrev level4 := tree4.values

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem coversKeys4 : level4.all tree4.contains = true := by

  decide +kernel

private def tree5 : TableTree :=
  .node 457641024144597520519563048796798751248795724364571839071308431174972539136
    [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]
    (.node 1773748916437466586832468094128894959986453665991119470413783746568257536
      [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
      (.node 1773748916437466586736688584326414237247147194927989038678738756442259456
        [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
        (.node 1773748916437466562312540901776310557155819435271005248796977447563165696
          [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
          (.node 1766847170090676023045034799768255265442113057562316627769889899629510656
            [0, 1, 0, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]
            (.node 6901851659082257249172054887613775067080269658868056203726598025773056
              [0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0]
              (.node 6901851659082257249172054887613775067080269658868056203446222560690176
                [0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 1773748916437466562312540901776310555831783736344624203521700883612041216
              [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              .empty
              .empty))
          (.node 1773748916437466586736688584326414235917939481552676817445355643413200896
            [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
            (.node 1773748916437466562312540901776310557161011732129540076425226468915675136
              [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]
              (.node 1773748916437466562312540901776310557161011652901377562161170350348435456
                [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 1773748916437466586736688584326414237241975180479057862720632207364325376
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              .empty
              .empty)))
        (.node 1773748916437466586832095411211375579742311726358776818243771483769798656
          [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
          (.node 1773748916437466586736688584326414237247167477337592690348881228716834816
            [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]
            (.node 1773748916437466586736688584326414237247167477337587967982679834048331776
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              (.node 1773748916437466586736688584326414237247167398109430176084825110149595136
                [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 1773748916437466586736688584326414237247167477337592690349161604181917696
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0]
              .empty
              .empty))
          (.node 1773748916437466586832095411211375579747504023217311645872020505122308096
            [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]
            (.node 1773748916437466586832095411211375579747504023216102720052687350924312576
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              .empty
              .empty)
            (.node 1773748916437466586832468094128894958662417967064738425138507182617133056
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              .empty
              .empty))))
      (.node 1773748916437466586832469555630445178603440109429305562797300869838667776
        [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
        (.node 1773748916437466586832468094128894959991645962849654298042314242880700416
          [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]
          (.node 1773748916437466586832468094128894959991645962848445372222699613722771456
            [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
            (.node 1773748916437466586832468094128894959991645962540169288220969174172696576
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 3, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              (.node 1773748916437466586832468094128894959991645883621491783777976649353527296
                [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 1773748916437466586832468094128894959991645962849654298042032767920766976
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]
              .empty
              .empty))
          (.node 1773748916437466586832469555608231545696033464164788781788347943780089856
            [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
            (.node 1773748916437466586832469555608231545696013260983347644382261590072754176
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0, 1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              (.node 1773748916437466586832469549921541520070724563073180622263015759755083776
                [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 3, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 1773748916437466586832469555608231545696033543392951296052684437812412416
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0]
              .empty
              .empty)))
        (.node 7095022626109516475822186107354529712787330661289004750298849845354496256
          [0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]
          (.node 7095022626109516475822186107354529712787330661289004750226792255611535616
            [0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0]
            (.node 1773748916437466586832469555630532290894564166534487014325051324341682176
              [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
              (.node 1773748916437466586832469555630445178608632406287840390425549891191177216
                [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 7095022626109516475822186107354529712787330661289004750298568374672752896
              [0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]
              .empty
              .empty))
          (.node 457641024144597520519563048796798751248795724364571839071308149704290795776
            [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]
            (.node 457641024144597520519563048796798751248795724364571839071236373585229578496
              [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0]
              .empty
              .empty)
            (.node 457641024144597520519563048796798751248795724364571839071308430079755878656
              [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0]
              .empty
              .empty)))))
    (.node 459407871209375904849050565326237551710975811572250563705453866181128683776
      [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]
      (.node 459407871104063613180589159599623642080952775942552362628880926121954181376
        [1, 4, 4, 1, 3, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]
        (.node 459407844249429237698506551630526582744992534624303035488857274801973166336
          [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]
          (.node 459400969463029114285358911541679392739170757152475287642874874856336261376
            [1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0]
            (.node 459400969463029114285358911541679392739170757152475287642874593381359616256
              [1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]
              (.node 457641024144597520519563048796798751248795724364571839071308431179267506176
                [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 459407844249429237698506551630526582744992534624303035488785498682911949056
              [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0]
              .empty
              .empty))
          (.node 459407844249429237698506551630526582744992534624303035488857556276949811456
            [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0]
            (.node 459407844249429237698506551630526582744992534624303035488857556276933099776
              [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 3, 1, 1, 0]
              (.node 459407844249429237698506551630526582744992534624303035488857556272654909696
                [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]
                .empty
                .empty)
              .empty)
            (.node 459407870788126738272997314121286445970192600706627741337079835694469284096
              [1, 4, 4, 1, 0, 1, 1, 0, 4, 1, 1, 0, 1, 0, 0, 0, 4, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 4, 1, 1, 0]
              .empty
              .empty)))
        (.node 459407871209375904849050565326237551710975791289840960053783442238172365056
          [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0]
          (.node 459407871209374297911102087307266127802530867098844935826435973112748114176
            [1, 4, 4, 1, 4, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]
            (.node 459407871208964528709816044787002927468983870635201774063021642410428006656
              [1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]
              (.node 459407871208964528709816044787002927468983870635201774063021641315211346176
                [1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0]
                .empty
                .empty)
              .empty)
            (.node 459407871209375904849050565326237551710970619275392028877825335689094430976
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0]
              .empty
              .empty))
          (.node 459407871209375904849050565326237551710975811572250563705453584710446940416
            [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]
            (.node 459407871209375904849050565326237551710975811572250563705381808591385723136
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0]
              .empty
              .empty)
            (.node 459407871209375904849050565326237551710975811572250563705453865085912023296
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0]
              .empty
              .empty))))
      (.node 459407871209375904849146346297541669764623208261447458029429755901288448256
        [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 0, 4, 1, 1, 0]
        (.node 459407871209375904849146346291832678993799368737214314151632056830734172416
          [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]
          (.node 459407871209375904849145972153122513053476148118130282660976723986852413696
            [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]
            (.node 459407871209375904849145972153122513053470955821271747833348474965499904256
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0]
              (.node 459407871209375904849050565326237551710975811572250563705453866185423650816
                [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 459407871209375904849145972153122513053476148118130282660977005461829058816
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0]
              .empty
              .empty))
          (.node 459407871209375904849146346297541669764623208261447458029429474430606704896
            [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 2, 4, 1, 4, 1, 1, 0]
            (.node 459407871209375904849146346297541669764623208261447458029357979782227230976
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 0, 4, 1, 1, 0]
              (.node 459407871209375904849146346297541669764623208261447458029357698311545487616
                [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 3, 4, 1, 4, 1, 1, 0]
                .empty
                .empty)
              .empty)
            (.node 459407871209375904849146346297541669764623208261447458029429754806071787776
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 3, 1, 4, 1, 1, 0]
              .empty
              .empty)))
        (.node 459407871209375904849146346297541669765952436257232373902333000015910338816
          [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 4, 1, 4, 1, 1, 0]
          (.node 459407871209375904849146346297541669764623208261447458029430037376248381696
            [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 3, 1, 1, 0]
            (.node 459407871209375904849146346297541669764623208261447458029430036281048432896
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 0, 1, 0]
              (.node 459407871209375904849146346297541669764623208261447458029429755905583415296
                [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 0, 0]
                .empty
                .empty)
              .empty)
            (.node 459407871209375904849146346297541669764623208261447458029430037376265093376
              [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 0, 1, 0]
              .empty
              .empty))
          (.node 1811025143249503020079841767402466738337295823652348806203910298595309387776
            [4, 1, 1, 0, 1, 0, 0, 0, 1, 1, 4, 1, 4, 1, 1, 0, 1, 4, 1, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
            (.node 911720719792642293320550221103145696756710207582365362570221370748031795456
              [2, 4, 4, 1, 4, 1, 1, 0, 4, 1, 1, 0, 1, 0, 0, 0, 4, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0]
              .empty
              .empty)
            (.node 1811025143249503020080127987883121622364781317246641169542605396777292005376
              [4, 1, 1, 0, 1, 0, 0, 0, 1, 4, 1, 1, 4, 1, 1, 0, 1, 1, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
              .empty
              .empty)))))

private abbrev level5 := tree5.values

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem coversKeys5 : level5.all tree5.contains = true := by

  decide +kernel

private def tree6 : TableTree :=
  .empty

private abbrev level6 := tree6.values

private theorem check2 :
    checkGroups 0 108 level1 level2 [[36]] = true := by
  have hgroup : sharedGroup 0 level1 [36] = [
    [25, 11],
    [24, 12],
    [23, 13],
    [22, 14],
    [21, 15],
    [20, 16],
    [19, 17],
    [18, 18]] := by decide +kernel
  unfold checkGroups
  apply all_cons_true
  · unfold checkGroup
    rw [hgroup]
    repeat
      refine all_cons_true ?_ ?_
      · decide +kernel
    rfl
  · rfl

private def base3_0 : List ℕ := [18, 18]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_0 :
    checkTripleGroup 1 108 level2 tree3 base3_0
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_0 = [
    [16, 2, 2, 16],
    [3, 15, 15, 3],
    [2, 16, 16, 2],
    [6, 12, 12, 6],
    [7, 11, 11, 7],
    [11, 7, 7, 11],
    [12, 6, 6, 12],
    [15, 3, 3, 15]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_0) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base3_1 : List ℕ := [19, 17]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_1 :
    checkTripleGroup 1 108 level2 tree3 base3_1
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_1 = [
    [12, 6, 7, 11],
    [3, 16, 16, 1],
    [3, 15, 16, 2],
    [7, 11, 12, 6],
    [7, 12, 12, 5],
    [12, 7, 7, 10],
    [16, 3, 3, 14],
    [16, 2, 3, 15]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_1) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base3_2 : List ℕ := [20, 16]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_2 :
    checkTripleGroup 1 108 level2 tree3 base3_2
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_2 = [
    [7, 12, 13, 4],
    [7, 13, 13, 3],
    [13, 7, 7, 9],
    [16, 3, 4, 13],
    [16, 4, 4, 12]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_2) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base3_3 : List ℕ := [21, 15]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_3 :
    checkTripleGroup 1 108 level2 tree3 base3_3
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_3 = [
    [6, 12, 15, 3],
    [7, 12, 14, 3],
    [7, 13, 14, 2],
    [15, 3, 6, 12],
    [14, 7, 7, 8],
    [16, 3, 5, 12],
    [17, 3, 4, 12]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_3) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base3_4 : List ℕ := [22, 14]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_4 :
    checkTripleGroup 1 108 level2 tree3 base3_4
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_4 = [
    [6, 12, 16, 2],
    [7, 11, 15, 3],
    [7, 12, 15, 2],
    [10, 12, 12, 2],
    [11, 7, 11, 7],
    [13, 7, 9, 7],
    [12, 7, 10, 7],
    [14, 7, 8, 7],
    [15, 6, 7, 8],
    [15, 3, 7, 11],
    [15, 7, 7, 7],
    [16, 3, 6, 11],
    [16, 2, 6, 12],
    [16, 6, 6, 8]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_4) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base3_5 : List ℕ := [23, 13]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_5 :
    checkTripleGroup 1 108 level2 tree3 base3_5
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_5 = [
    [7, 11, 16, 2],
    [7, 12, 16, 1],
    [11, 11, 12, 2],
    [11, 7, 12, 6],
    [11, 12, 12, 1],
    [12, 6, 11, 7],
    [12, 7, 11, 6],
    [12, 11, 11, 2],
    [15, 6, 8, 7],
    [15, 7, 8, 6],
    [16, 2, 7, 11],
    [16, 4, 7, 9],
    [16, 3, 7, 10],
    [16, 5, 7, 8],
    [16, 6, 7, 7],
    [16, 7, 7, 6],
    [17, 6, 6, 7],
    [19, 4, 4, 9]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_5) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base3_6 : List ℕ := [24, 12]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_6 :
    checkTripleGroup 1 108 level2 tree3 base3_6
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_6 = [
    [12, 6, 12, 6],
    [12, 7, 12, 5],
    [12, 11, 12, 1],
    [12, 10, 12, 2],
    [12, 12, 12, 0],
    [17, 5, 7, 7],
    [16, 5, 8, 7],
    [16, 6, 8, 6],
    [16, 7, 8, 5],
    [17, 3, 7, 9],
    [17, 4, 7, 8],
    [18, 4, 6, 8],
    [17, 6, 7, 6],
    [17, 7, 7, 5],
    [18, 5, 6, 7],
    [18, 6, 6, 6],
    [19, 4, 5, 8],
    [19, 5, 5, 7],
    [20, 4, 4, 8]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_6) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base3_7 : List ℕ := [25, 11]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check3_7 :
    checkTripleGroup 1 108 level2 tree3 base3_7
      (keepRemaining 1 tree2) = true := by
  have hgroup : sharedGroup 1 level2 base3_7 = [
    [12, 7, 13, 4],
    [13, 9, 12, 2],
    [13, 7, 12, 4],
    [16, 4, 9, 7],
    [16, 7, 9, 4],
    [16, 9, 9, 2],
    [17, 4, 8, 7],
    [18, 7, 7, 4],
    [17, 7, 8, 4],
    [18, 3, 7, 8],
    [17, 8, 8, 3],
    [18, 5, 7, 6],
    [18, 4, 7, 7],
    [18, 6, 7, 5],
    [19, 5, 6, 6],
    [19, 3, 6, 8],
    [19, 4, 6, 7],
    [20, 4, 5, 7],
    [19, 6, 6, 5],
    [21, 4, 4, 7],
    [20, 5, 5, 6]] := by
    decide +kernel
  have hthird : thirdRows 1 (thirdsAt 1 level2 base3_7) = [
    ((4626, 4626), [16]),
    ((4881, 4626), [11]),
    ((5136, 4881), [4]),
    ((5646, 4626), [2]),
    ((4881, 4881), [1]),
    ((4626, 4626), [3]),
    ((4626, 4626), [2]),
    ((4881, 4626), [2]),
    ((5391, 4626), [3]),
    ((4626, 4626), [6]),
    ((5646, 4626), [3]),
    ((4881, 4626), [6]),
    ((4626, 4626), [7]),
    ((4881, 4881), [5]),
    ((5901, 4626), [2]),
    ((4626, 4626), [11]),
    ((5136, 5136), [3]),
    ((5646, 4881), [2]),
    ((5391, 4881), [3]),
    ((5901, 4881), [1]),
    ((5646, 5646), [2]),
    ((5391, 5136), [2]),
    ((5901, 5646), [2]),
    ((5901, 4626), [6]),
    ((5646, 4626), [7]),
    ((4626, 4626), [12]),
    ((5901, 5901), [1]),
    ((5646, 5136), [7]),
    ((6411, 4881), [4]),
    ((5646, 4881), [7]),
    ((6156, 4626), [6]),
    ((5901, 4626), [7]),
    ((4881, 4881), [10]),
    ((6156, 4881), [5]),
    ((5901, 4881), [6]),
    ((6156, 5901), [1]),
    ((5901, 5901), [2]),
    ((6156, 5646), [2]),
    ((5136, 5136), [9]),
    ((6156, 6156), [0]),
    ((5391, 4626), [12]),
    ((5391, 5391), [8]),
    ((6411, 5646), [2]),
    ((6411, 5136), [4]),
    ((4626, 4626), [15]),
    ((5646, 5391), [7]),
    ((5901, 5391), [7]),
    ((5646, 5391), [8]),
    ((5646, 4626), [11]),
    ((5901, 5646), [6]),
    ((5646, 5646), [7]),
    ((6156, 5646), [7]),
    ((6156, 5391), [7]),
    ((5646, 4881), [11]),
    ((4881, 4881), [14]),
    ((5646, 4626), [12]),
    ((4881, 4626), [15]),
    ((5901, 4626), [11]),
    ((5391, 4881), [12]),
    ((5136, 4881), [13]),
    ((5901, 5136), [9]),
    ((5136, 5136), [12]),
    ((5901, 4881), [10]),
    ((5901, 5391), [8]),
    ((6411, 5136), [7]),
    ((6411, 5901), [4]),
    ((6156, 5646), [6]),
    ((5901, 5646), [7]),
    ((5646, 5646), [8]),
    ((6156, 5901), [5]),
    ((5901, 5901), [6]),
    ((6156, 5136), [9]),
    ((5391, 5136), [12]),
    ((6411, 6411), [2]),
    ((6411, 5391), [7]),
    ((6156, 5391), [8]),
    ((6411, 6411), [4]),
    ((6156, 5646), [8]),
    ((6411, 6156), [4]),
    ((6156, 5901), [6]),
    ((5901, 5901), [7]),
    ((6156, 6156), [5]),
    ((6411, 5391), [8]),
    ((6411, 6411), [3]),
    ((6411, 5901), [6]),
    ((6156, 5901), [7]),
    ((6411, 5646), [7]),
    ((6411, 6156), [5]),
    ((6156, 6156), [6]),
    ((6411, 6156), [6]),
    ((6156, 5901), [8]),
    ((5901, 5901), [9]),
    ((6411, 5646), [8]),
    ((6156, 6156), [7]),
    ((6411, 5901), [7]),
    ((6411, 6156), [7]),
    ((6156, 6156), [8]),
    ((6411, 6411), [5]),
    ((6411, 6411), [7]),
    ((6411, 6411), [6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def bases3 : List (List ℕ) := [
  base3_0, base3_1, base3_2, base3_3, base3_4, base3_5, base3_6, base3_7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem covers3 :
    (level2.map (dropAxis 1 1)).all bases3.contains = true := by
  decide +kernel

private theorem check3 :
    bases3.all (fun base => checkTripleGroup 1 108 level2 tree3 base
      (keepRemaining 1 tree2)) = true := by
  simp only [bases3, List.all_cons, List.all_nil, Bool.and_self,
    check3_0, check3_1, check3_2, check3_3, check3_4, check3_5, check3_6, check3_7]

private def base4_0 : List ℕ := [6, 12, 12, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_0 :
    checkTripleGroup 2 108 level3 tree4 base4_0
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_0 = [
    [0, 6, 6, 6, 6, 6, 6, 0],
    [1, 6, 6, 5, 5, 6, 6, 1],
    [5, 6, 6, 1, 1, 6, 6, 5],
    [6, 6, 6, 0, 0, 6, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_0) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_1 : List ℕ := [7, 11, 11, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_1 :
    checkTripleGroup 2 108 level3 tree4 base4_1
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_1 = [
    [1, 6, 5, 6, 6, 5, 6, 1],
    [1, 5, 6, 6, 6, 6, 5, 1],
    [6, 5, 6, 1, 1, 6, 5, 6],
    [6, 6, 5, 1, 1, 5, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_1) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_2 : List ℕ := [7, 11, 12, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_2 :
    checkTripleGroup 2 108 level3 tree4 base4_2
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_2 = [
    [1, 5, 6, 6, 6, 6, 6, 0],
    [1, 6, 6, 5, 6, 5, 6, 1],
    [6, 5, 6, 1, 1, 6, 6, 5],
    [6, 6, 6, 0, 1, 5, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_2) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_3 : List ℕ := [7, 12, 12, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_3 :
    checkTripleGroup 2 108 level3 tree4 base4_3
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_3 = [
    [1, 6, 6, 5, 6, 6, 6, 0],
    [6, 6, 6, 0, 1, 6, 6, 5],
    [6, 6, 6, 1, 1, 6, 6, 4]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_3) = [
    ((118164486, 118164486), [6, 0]),
    ((118164486, 118164486), [6, 1]),
    ((118230021, 118164486), [6, 0]),
    ((201721611, 201721611), [1, 5]),
    ((201721611, 201721611), [1, 6]),
    ((201787146, 201721611), [1, 5]),
    ((201787146, 201787146), [1, 4]),
    ((201721611, 118164486), [6, 5]),
    ((118164486, 201721611), [6, 5]),
    ((201787146, 118164486), [6, 5]),
    ((201721611, 118164486), [6, 6]),
    ((201787146, 118230021), [6, 4]),
    ((118230021, 201721611), [6, 5]),
    ((118164486, 201721611), [6, 6]),
    ((118230021, 201787146), [6, 4])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_4 : List ℕ := [10, 12, 12, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_4 :
    checkTripleGroup 2 108 level3 tree4 base4_4
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_4 = [
    [0, 10, 10, 2, 10, 2, 2, 0],
    [5, 6, 6, 1, 5, 6, 6, 1],
    [6, 6, 6, 1, 4, 6, 6, 1],
    [7, 6, 6, 1, 3, 6, 6, 1],
    [8, 6, 6, 1, 2, 6, 6, 1],
    [9, 6, 6, 1, 1, 6, 6, 1]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_4) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_5 : List ℕ := [11, 7, 7, 11]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_5 :
    checkTripleGroup 2 108 level3 tree4 base4_5
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_5 = [
    [5, 1, 6, 6, 6, 6, 1, 5],
    [5, 6, 1, 6, 6, 1, 6, 5],
    [6, 1, 6, 5, 5, 6, 1, 6],
    [6, 6, 1, 5, 5, 1, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_5) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_6 : List ℕ := [11, 7, 11, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_6 :
    checkTripleGroup 2 108 level3 tree4 base4_6
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_6 = [
    [1, 1, 10, 6, 10, 6, 1, 1],
    [2, 1, 9, 6, 9, 6, 2, 1],
    [5, 1, 6, 6, 6, 6, 5, 1],
    [5, 6, 6, 1, 6, 1, 5, 6],
    [6, 1, 5, 6, 5, 6, 6, 1],
    [6, 6, 5, 1, 5, 1, 6, 6],
    [9, 6, 2, 1, 2, 1, 9, 6],
    [10, 6, 1, 1, 1, 1, 10, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_6) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_7 : List ℕ := [11, 7, 12, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_7 :
    checkTripleGroup 2 108 level3 tree4 base4_7
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_7 = [
    [1, 1, 10, 6, 10, 6, 2, 0],
    [2, 1, 10, 5, 9, 6, 2, 1],
    [5, 1, 6, 6, 6, 6, 6, 0],
    [5, 6, 6, 1, 6, 1, 6, 5],
    [6, 1, 6, 5, 5, 6, 6, 1],
    [6, 6, 6, 0, 5, 1, 6, 6],
    [9, 6, 2, 1, 2, 1, 10, 5],
    [10, 6, 2, 0, 1, 1, 10, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_7) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_8 : List ℕ := [11, 11, 12, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_8 :
    checkTripleGroup 2 108 level3 tree4 base4_8
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_8 = [
    [1, 9, 10, 2, 10, 2, 2, 0],
    [5, 6, 6, 1, 6, 5, 6, 1],
    [6, 5, 6, 1, 5, 6, 6, 1],
    [6, 6, 6, 1, 5, 5, 6, 1],
    [9, 5, 6, 1, 2, 6, 6, 1],
    [9, 6, 6, 1, 2, 5, 6, 1],
    [10, 5, 6, 1, 1, 6, 6, 1]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_8) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_9 : List ℕ := [11, 12, 12, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_9 :
    checkTripleGroup 2 108 level3 tree4 base4_9
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_9 = [
    [1, 10, 10, 1, 10, 2, 2, 0],
    [2, 10, 10, 1, 9, 2, 2, 0],
    [5, 6, 6, 1, 6, 6, 6, 0],
    [6, 6, 6, 0, 5, 6, 6, 1],
    [6, 6, 6, 1, 5, 6, 6, 0],
    [9, 6, 6, 0, 2, 6, 6, 1],
    [9, 6, 6, 1, 2, 6, 6, 0],
    [10, 6, 6, 0, 1, 6, 6, 1],
    [10, 6, 6, 1, 1, 6, 6, 0]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_9) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_10 : List ℕ := [12, 6, 6, 12]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_10 :
    checkTripleGroup 2 108 level3 tree4 base4_10
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_10 = [
    [6, 0, 6, 6, 6, 6, 0, 6],
    [6, 1, 5, 6, 6, 5, 1, 6],
    [6, 5, 1, 6, 6, 1, 5, 6],
    [6, 6, 0, 6, 6, 0, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_10) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_11 : List ℕ := [12, 6, 7, 11]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_11 :
    checkTripleGroup 2 108 level3 tree4 base4_11
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_11 = [
    [6, 0, 6, 6, 6, 6, 1, 5],
    [6, 1, 6, 5, 6, 5, 1, 6],
    [6, 5, 1, 6, 6, 1, 6, 5],
    [6, 6, 1, 5, 6, 0, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_11) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_12 : List ℕ := [12, 6, 11, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_12 :
    checkTripleGroup 2 108 level3 tree4 base4_12
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_12 = [
    [2, 0, 10, 6, 10, 6, 1, 1],
    [2, 1, 9, 6, 10, 5, 2, 1],
    [6, 0, 6, 6, 6, 6, 5, 1],
    [6, 1, 5, 6, 6, 5, 6, 1],
    [6, 5, 6, 1, 6, 1, 5, 6],
    [6, 6, 5, 1, 6, 0, 6, 6],
    [10, 5, 2, 1, 2, 1, 9, 6],
    [10, 6, 1, 1, 2, 0, 10, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_12) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_13 : List ℕ := [12, 6, 12, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_13 :
    checkTripleGroup 2 108 level3 tree4 base4_13
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_13 = [
    [2, 0, 10, 6, 10, 6, 2, 0],
    [2, 1, 10, 5, 10, 5, 2, 1],
    [6, 0, 6, 6, 6, 6, 6, 0],
    [6, 1, 6, 5, 6, 5, 6, 1],
    [6, 5, 6, 1, 6, 1, 6, 5],
    [6, 6, 6, 0, 6, 0, 6, 6],
    [10, 5, 2, 1, 2, 1, 10, 5],
    [10, 6, 2, 0, 2, 0, 10, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_13) = [
    ((118164231, 101452806), [6, 1]),
    ((101452806, 101452806), [6, 0]),
    ((118164231, 118164231), [5, 1]),
    ((101452806, 118164231), [6, 1]),
    ((185009931, 185009931), [1, 5]),
    ((185009931, 101452806), [6, 5]),
    ((201721356, 201721356), [0, 6]),
    ((101452806, 185009931), [6, 5]),
    ((201721356, 185009931), [1, 6]),
    ((185009931, 201721356), [1, 6]),
    ((201721356, 118164231), [5, 6]),
    ((118164231, 201721356), [5, 6]),
    ((185009931, 118164231), [6, 6]),
    ((201721356, 101452806), [6, 6]),
    ((118164231, 185009931), [6, 6]),
    ((101452806, 201721356), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_14 : List ℕ := [12, 7, 7, 10]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_14 :
    checkTripleGroup 2 108 level3 tree4 base4_14
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_14 = [
    [6, 1, 6, 5, 6, 6, 1, 5],
    [6, 1, 6, 6, 6, 6, 1, 4],
    [6, 6, 1, 5, 6, 1, 6, 5],
    [6, 6, 1, 6, 6, 1, 6, 4]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_14) = [
    ((118164486, 118164486), [6, 0]),
    ((118164486, 118164486), [6, 1]),
    ((118230021, 118164486), [6, 0]),
    ((201721611, 201721611), [1, 5]),
    ((201721611, 201721611), [1, 6]),
    ((201787146, 201721611), [1, 5]),
    ((201787146, 201787146), [1, 4]),
    ((201721611, 118164486), [6, 5]),
    ((118164486, 201721611), [6, 5]),
    ((201787146, 118164486), [6, 5]),
    ((201721611, 118164486), [6, 6]),
    ((201787146, 118230021), [6, 4]),
    ((118230021, 201721611), [6, 5]),
    ((118164486, 201721611), [6, 6]),
    ((118230021, 201787146), [6, 4])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_15 : List ℕ := [12, 7, 10, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_15 :
    checkTripleGroup 2 108 level3 tree4 base4_15
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_15 = [
    [2, 1, 9, 6, 10, 6, 1, 1],
    [2, 1, 10, 6, 10, 6, 0, 1],
    [6, 1, 5, 6, 6, 6, 5, 1],
    [6, 1, 6, 6, 6, 6, 4, 1],
    [6, 6, 5, 1, 6, 1, 5, 6],
    [6, 6, 6, 1, 6, 1, 4, 6],
    [10, 6, 1, 1, 2, 1, 9, 6],
    [10, 6, 2, 1, 2, 1, 8, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_15) = [
    ((118164486, 118164486), [6, 0]),
    ((118164486, 118164486), [6, 1]),
    ((118230021, 118164486), [6, 0]),
    ((201721611, 201721611), [1, 5]),
    ((201721611, 201721611), [1, 6]),
    ((201787146, 201721611), [1, 5]),
    ((201787146, 201787146), [1, 4]),
    ((201721611, 118164486), [6, 5]),
    ((118164486, 201721611), [6, 5]),
    ((201787146, 118164486), [6, 5]),
    ((201721611, 118164486), [6, 6]),
    ((201787146, 118230021), [6, 4]),
    ((118230021, 201721611), [6, 5]),
    ((118164486, 201721611), [6, 6]),
    ((118230021, 201787146), [6, 4])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_16 : List ℕ := [12, 7, 11, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_16 :
    checkTripleGroup 2 108 level3 tree4 base4_16
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_16 = [
    [2, 1, 10, 5, 10, 6, 1, 1],
    [2, 1, 9, 6, 10, 6, 2, 0],
    [2, 1, 10, 6, 10, 6, 1, 0],
    [6, 1, 6, 5, 6, 6, 5, 1],
    [6, 1, 5, 6, 6, 6, 6, 0],
    [6, 1, 6, 6, 6, 6, 5, 0],
    [6, 6, 5, 1, 6, 1, 6, 5],
    [6, 6, 6, 0, 6, 1, 5, 6],
    [6, 6, 6, 1, 6, 1, 5, 5],
    [10, 6, 1, 1, 2, 1, 10, 5],
    [10, 6, 2, 0, 2, 1, 9, 6],
    [10, 6, 2, 1, 2, 1, 9, 5]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_16) = [
    ((118164486, 118164486), [6, 0]),
    ((118164486, 118164486), [6, 1]),
    ((118230021, 118164486), [6, 0]),
    ((201721611, 201721611), [1, 5]),
    ((201721611, 201721611), [1, 6]),
    ((201787146, 201721611), [1, 5]),
    ((201787146, 201787146), [1, 4]),
    ((201721611, 118164486), [6, 5]),
    ((118164486, 201721611), [6, 5]),
    ((201787146, 118164486), [6, 5]),
    ((201721611, 118164486), [6, 6]),
    ((201787146, 118230021), [6, 4]),
    ((118230021, 201721611), [6, 5]),
    ((118164486, 201721611), [6, 6]),
    ((118230021, 201787146), [6, 4])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_17 : List ℕ := [12, 7, 12, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_17 :
    checkTripleGroup 2 108 level3 tree4 base4_17
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_17 = [
    [2, 1, 10, 5, 10, 6, 2, 0],
    [6, 1, 6, 5, 6, 6, 6, 0],
    [6, 6, 6, 0, 6, 1, 6, 5],
    [6, 6, 6, 1, 6, 1, 6, 4],
    [10, 6, 2, 0, 2, 1, 10, 5],
    [10, 6, 2, 1, 2, 1, 10, 4]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_17) = [
    ((118164486, 118164486), [6, 0]),
    ((118164486, 118164486), [6, 1]),
    ((118230021, 118164486), [6, 0]),
    ((201721611, 201721611), [1, 5]),
    ((201721611, 201721611), [1, 6]),
    ((201787146, 201721611), [1, 5]),
    ((201787146, 201787146), [1, 4]),
    ((201721611, 118164486), [6, 5]),
    ((118164486, 201721611), [6, 5]),
    ((201787146, 118164486), [6, 5]),
    ((201721611, 118164486), [6, 6]),
    ((201787146, 118230021), [6, 4]),
    ((118230021, 201721611), [6, 5]),
    ((118164486, 201721611), [6, 6]),
    ((118230021, 201787146), [6, 4])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_18 : List ℕ := [12, 7, 13, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_18 :
    checkTripleGroup 2 108 level3 tree4 base4_18
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_18 = [
    [6, 6, 6, 1, 6, 1, 7, 3]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_18) = [
    ((118164486, 118164486), [6, 0]),
    ((118164486, 118164486), [6, 1]),
    ((118230021, 118164486), [6, 0]),
    ((201721611, 201721611), [1, 5]),
    ((201721611, 201721611), [1, 6]),
    ((201787146, 201721611), [1, 5]),
    ((201787146, 201787146), [1, 4]),
    ((201721611, 118164486), [6, 5]),
    ((118164486, 201721611), [6, 5]),
    ((201787146, 118164486), [6, 5]),
    ((201721611, 118164486), [6, 6]),
    ((201787146, 118230021), [6, 4]),
    ((118230021, 201721611), [6, 5]),
    ((118164486, 201721611), [6, 6]),
    ((118230021, 201787146), [6, 4])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_19 : List ℕ := [12, 10, 12, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_19 :
    checkTripleGroup 2 108 level3 tree4 base4_19
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_19 = [
    [2, 8, 10, 2, 10, 2, 2, 0],
    [6, 5, 6, 1, 6, 5, 6, 1],
    [6, 6, 6, 1, 6, 4, 6, 1],
    [10, 4, 6, 1, 2, 6, 6, 1],
    [10, 5, 6, 1, 2, 5, 6, 1]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_19) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_20 : List ℕ := [12, 11, 11, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_20 :
    checkTripleGroup 2 108 level3 tree4 base4_20
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_20 = [
    [2, 9, 10, 2, 10, 2, 1, 0],
    [2, 9, 9, 2, 10, 2, 2, 0],
    [2, 10, 9, 2, 10, 1, 2, 0],
    [6, 5, 6, 1, 6, 6, 5, 1],
    [6, 6, 5, 1, 6, 5, 6, 1],
    [6, 6, 6, 1, 6, 5, 5, 1],
    [10, 5, 5, 1, 2, 6, 6, 1],
    [10, 5, 6, 1, 2, 6, 5, 1],
    [10, 6, 5, 1, 2, 5, 6, 1],
    [10, 6, 6, 1, 2, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_20) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_21 : List ℕ := [12, 11, 12, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_21 :
    checkTripleGroup 2 108 level3 tree4 base4_21
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_21 = [
    [2, 9, 10, 1, 10, 2, 2, 0],
    [2, 10, 10, 1, 10, 1, 2, 0],
    [6, 5, 6, 1, 6, 6, 6, 0],
    [6, 6, 6, 0, 6, 5, 6, 1],
    [6, 6, 6, 1, 6, 5, 6, 0],
    [10, 5, 6, 0, 2, 6, 6, 1],
    [10, 5, 6, 1, 2, 6, 6, 0],
    [10, 6, 6, 0, 2, 5, 6, 1],
    [10, 6, 6, 1, 2, 5, 6, 0]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_21) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_22 : List ℕ := [12, 12, 12, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_22 :
    checkTripleGroup 2 108 level3 tree4 base4_22
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_22 = [
    [2, 10, 10, 0, 10, 2, 2, 0],
    [6, 6, 6, 0, 6, 6, 6, 0],
    [10, 6, 6, 0, 2, 6, 6, 0]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_22) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_23 : List ℕ := [13, 7, 9, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_23 :
    checkTripleGroup 2 108 level3 tree4 base4_23
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_23 = [
    [6, 1, 6, 6, 7, 6, 3, 1],
    [6, 1, 7, 6, 7, 6, 2, 1],
    [7, 6, 6, 1, 6, 1, 3, 6],
    [10, 6, 3, 1, 3, 1, 6, 6],
    [10, 6, 2, 1, 3, 1, 7, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_23) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_24 : List ℕ := [13, 7, 12, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_24 :
    checkTripleGroup 2 108 level3 tree4 base4_24
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_24 = [
    [6, 1, 10, 3, 7, 6, 2, 1],
    [7, 6, 6, 1, 6, 1, 6, 3],
    [10, 6, 2, 1, 3, 1, 10, 3]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_24) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_25 : List ℕ := [13, 9, 12, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_25 :
    checkTripleGroup 2 108 level3 tree4 base4_25
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_25 = [
    [3, 7, 10, 2, 10, 2, 2, 0],
    [6, 6, 6, 1, 7, 3, 6, 1],
    [7, 6, 6, 1, 6, 3, 6, 1],
    [10, 3, 6, 1, 3, 6, 6, 1],
    [11, 3, 6, 1, 2, 6, 6, 1]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_25) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_26 : List ℕ := [14, 7, 8, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_26 :
    checkTripleGroup 2 108 level3 tree4 base4_26
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_26 = [
    [5, 1, 6, 6, 9, 6, 2, 1],
    [6, 1, 6, 6, 8, 6, 2, 1],
    [6, 1, 7, 6, 8, 6, 1, 1],
    [8, 6, 6, 1, 6, 1, 2, 6],
    [9, 6, 2, 1, 5, 1, 6, 6],
    [10, 6, 2, 1, 4, 1, 6, 6],
    [11, 6, 2, 1, 3, 1, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_26) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_27 : List ℕ := [15, 6, 8, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_27 :
    checkTripleGroup 2 108 level3 tree4 base4_27
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_27 = [
    [5, 1, 6, 6, 10, 5, 2, 1],
    [6, 0, 6, 6, 9, 6, 2, 1],
    [6, 1, 6, 6, 9, 5, 2, 1],
    [9, 5, 6, 1, 6, 1, 2, 6],
    [9, 6, 2, 1, 6, 0, 6, 6],
    [10, 5, 2, 1, 5, 1, 6, 6],
    [10, 6, 2, 1, 5, 0, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_27) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_28 : List ℕ := [15, 7, 7, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_28 :
    checkTripleGroup 2 108 level3 tree4 base4_28
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_28 = [
    [5, 6, 1, 6, 10, 1, 6, 1],
    [5, 1, 6, 6, 10, 6, 1, 1],
    [6, 1, 5, 6, 9, 6, 2, 1],
    [6, 1, 6, 6, 9, 6, 1, 1],
    [6, 5, 1, 6, 9, 2, 6, 1],
    [9, 6, 5, 1, 6, 1, 2, 6],
    [6, 6, 1, 6, 9, 1, 6, 1],
    [9, 1, 6, 6, 6, 6, 1, 1],
    [8, 6, 6, 1, 7, 1, 1, 6],
    [9, 5, 6, 1, 6, 2, 1, 6],
    [9, 2, 6, 1, 6, 5, 1, 6],
    [9, 6, 1, 6, 6, 1, 6, 1],
    [9, 6, 2, 1, 6, 1, 5, 6],
    [9, 6, 6, 1, 6, 1, 1, 6],
    [10, 1, 6, 1, 5, 6, 1, 6],
    [10, 2, 6, 1, 5, 5, 1, 6],
    [10, 5, 6, 1, 5, 2, 1, 6],
    [10, 6, 1, 1, 5, 1, 6, 6],
    [10, 6, 2, 1, 5, 1, 5, 6],
    [10, 6, 5, 1, 5, 1, 2, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_28) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_29 : List ℕ := [15, 7, 8, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_29 :
    checkTripleGroup 2 108 level3 tree4 base4_29
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_29 = [
    [5, 1, 6, 6, 10, 6, 2, 0],
    [6, 1, 6, 5, 9, 6, 2, 1],
    [6, 1, 6, 6, 9, 6, 2, 0],
    [9, 6, 2, 5, 6, 1, 6, 1],
    [9, 6, 2, 1, 6, 1, 6, 5],
    [9, 6, 6, 1, 6, 1, 2, 5],
    [9, 6, 6, 0, 6, 1, 2, 6],
    [10, 6, 2, 0, 5, 1, 6, 6],
    [10, 6, 2, 1, 5, 1, 6, 5],
    [10, 6, 6, 0, 5, 1, 2, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_29) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_30 : List ℕ := [16, 4, 9, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_30 :
    checkTripleGroup 2 108 level3 tree4 base4_30
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_30 = [
    [6, 1, 6, 6, 10, 3, 3, 1],
    [6, 1, 7, 6, 10, 3, 2, 1],
    [10, 3, 6, 1, 6, 1, 3, 6],
    [13, 3, 3, 1, 3, 1, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_30) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_31 : List ℕ := [16, 5, 8, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_31 :
    checkTripleGroup 2 108 level3 tree4 base4_31
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_31 = [
    [6, 0, 6, 6, 10, 5, 2, 1],
    [6, 1, 6, 6, 10, 4, 2, 1],
    [10, 4, 6, 1, 6, 1, 2, 6],
    [10, 5, 2, 1, 6, 0, 6, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_31) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_32 : List ℕ := [16, 6, 6, 8]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_32 :
    checkTripleGroup 2 108 level3 tree4 base4_32
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_32 = [
    [10, 5, 5, 2, 6, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_32) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_33 : List ℕ := [16, 6, 7, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_33 :
    checkTripleGroup 2 108 level3 tree4 base4_33
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_33 = [
    [6, 0, 6, 6, 10, 6, 1, 1],
    [6, 1, 5, 6, 10, 5, 2, 1],
    [6, 1, 6, 6, 10, 5, 1, 1],
    [6, 5, 1, 6, 10, 1, 6, 1],
    [6, 6, 1, 6, 10, 0, 6, 1],
    [10, 0, 6, 6, 6, 6, 1, 1],
    [10, 1, 6, 1, 6, 5, 1, 6],
    [10, 3, 6, 1, 6, 3, 1, 6],
    [10, 2, 6, 1, 6, 4, 1, 6],
    [10, 4, 6, 1, 6, 2, 1, 6],
    [10, 5, 1, 6, 6, 1, 6, 1],
    [10, 5, 2, 1, 6, 1, 5, 6],
    [10, 5, 5, 1, 6, 1, 2, 6],
    [10, 5, 6, 1, 6, 1, 1, 6],
    [10, 6, 1, 1, 6, 0, 6, 6],
    [10, 6, 2, 1, 6, 0, 5, 6],
    [10, 6, 5, 1, 6, 0, 2, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_33) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_34 : List ℕ := [16, 6, 8, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_34 :
    checkTripleGroup 2 108 level3 tree4 base4_34
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_34 = [
    [6, 0, 6, 6, 10, 6, 2, 0],
    [6, 1, 6, 5, 10, 5, 2, 1],
    [6, 1, 6, 6, 10, 5, 2, 0],
    [10, 5, 2, 5, 6, 1, 6, 1],
    [10, 5, 2, 1, 6, 1, 6, 5],
    [10, 5, 6, 0, 6, 1, 2, 6],
    [10, 5, 6, 1, 6, 1, 2, 5],
    [10, 6, 2, 0, 6, 0, 6, 6],
    [10, 6, 2, 1, 6, 0, 6, 5],
    [10, 6, 6, 0, 6, 0, 2, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_34) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_35 : List ℕ := [16, 7, 7, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_35 :
    checkTripleGroup 2 108 level3 tree4 base4_35
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_35 = [
    [10, 6, 1, 1, 6, 1, 6, 5],
    [6, 6, 1, 5, 10, 1, 6, 1],
    [6, 1, 5, 6, 10, 6, 2, 0],
    [6, 1, 6, 5, 10, 6, 1, 1],
    [6, 5, 1, 6, 10, 2, 6, 0],
    [6, 1, 6, 6, 10, 6, 1, 0],
    [6, 6, 1, 6, 10, 1, 6, 0],
    [10, 2, 6, 0, 6, 5, 1, 6],
    [10, 1, 6, 1, 6, 6, 1, 5],
    [10, 1, 6, 6, 6, 6, 1, 0],
    [10, 1, 6, 5, 6, 6, 1, 1],
    [10, 2, 6, 5, 6, 5, 1, 1],
    [10, 2, 6, 1, 6, 5, 1, 5],
    [10, 5, 6, 0, 6, 2, 1, 6],
    [10, 5, 6, 1, 6, 2, 1, 5],
    [10, 6, 1, 6, 6, 1, 6, 0],
    [10, 6, 1, 5, 6, 1, 6, 1],
    [10, 6, 2, 0, 6, 1, 5, 6],
    [10, 6, 2, 1, 6, 1, 5, 5],
    [10, 6, 2, 5, 6, 1, 5, 1],
    [10, 6, 6, 0, 6, 1, 1, 6],
    [10, 6, 5, 0, 6, 1, 2, 6],
    [10, 6, 5, 1, 6, 1, 2, 5],
    [10, 6, 6, 1, 6, 1, 1, 5],
    [11, 6, 6, 0, 5, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_35) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_36 : List ℕ := [16, 7, 8, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_36 :
    checkTripleGroup 2 108 level3 tree4 base4_36
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_36 = [
    [6, 1, 6, 5, 10, 6, 2, 0],
    [10, 6, 2, 0, 6, 1, 6, 5],
    [10, 6, 2, 4, 6, 1, 6, 1],
    [10, 6, 2, 1, 6, 1, 6, 4],
    [10, 6, 2, 5, 6, 1, 6, 0],
    [10, 6, 6, 0, 6, 1, 2, 5],
    [10, 6, 6, 1, 6, 1, 2, 4]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_36) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_37 : List ℕ := [16, 7, 9, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_37 :
    checkTripleGroup 2 108 level3 tree4 base4_37
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_37 = [
    [10, 6, 2, 1, 6, 1, 7, 3],
    [10, 6, 3, 1, 6, 1, 6, 3],
    [10, 6, 3, 3, 6, 1, 6, 1],
    [10, 6, 6, 1, 6, 1, 3, 3],
    [13, 6, 3, 1, 3, 1, 6, 3]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_37) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_38 : List ℕ := [16, 9, 9, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_38 :
    checkTripleGroup 2 108 level3 tree4 base4_38
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_38 = [
    [6, 7, 7, 2, 10, 2, 2, 0],
    [6, 6, 6, 1, 10, 3, 3, 1],
    [10, 3, 6, 1, 6, 6, 3, 1],
    [10, 6, 3, 1, 6, 3, 6, 1],
    [10, 6, 6, 1, 6, 3, 3, 1],
    [13, 3, 3, 1, 3, 6, 6, 1],
    [13, 3, 6, 1, 3, 6, 3, 1],
    [13, 6, 3, 1, 3, 3, 6, 1]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_38) = [
    ((218696706, 218696706), [2, 0]),
    ((268699911, 201788676), [3, 1]),
    ((285476871, 201788676), [2, 1]),
    ((218565636, 268699911), [2, 1]),
    ((268699911, 218565636), [2, 1]),
    ((201788676, 201788676), [7, 3]),
    ((218696706, 201788676), [6, 1]),
    ((269027586, 218696706), [2, 0]),
    ((269027586, 201788676), [3, 1]),
    ((218565636, 218565636), [6, 3]),
    ((218696706, 218565636), [6, 1]),
    ((268699911, 268699911), [3, 6]),
    ((218696706, 268699911), [6, 1]),
    ((269027586, 268699911), [3, 1]),
    ((268699911, 268699911), [6, 6]),
    ((218565636, 201788676), [10, 3]),
    ((268896516, 201788676), [7, 3]),
    ((269027586, 218565636), [6, 1]),
    ((268896516, 218565636), [6, 3]),
    ((268896516, 218696706), [6, 1]),
    ((268896516, 268896516), [3, 3]),
    ((269027586, 268896516), [3, 1]),
    ((285476871, 285476871), [2, 6]),
    ((218696706, 285476871), [6, 1]),
    ((302253831, 285476871), [1, 6]),
    ((285673476, 218696706), [6, 1]),
    ((285673476, 218565636), [6, 3]),
    ((285739011, 285739011), [2, 1]),
    ((285739011, 285673476), [2, 2]),
    ((285673476, 285673476), [2, 3]),
    ((302450436, 285673476), [1, 3]),
    ((302253831, 285476871), [2, 6]),
    ((302253831, 302188296), [1, 6]),
    ((302253831, 302253831), [1, 6]),
    ((302319366, 302188296), [1, 6]),
    ((302319366, 302253831), [1, 5]),
    ((302450436, 302384901), [1, 3]),
    ((302319366, 302253831), [1, 6]),
    ((302319366, 302319366), [1, 5]),
    ((302384901, 302319366), [1, 5]),
    ((302319366, 302319366), [1, 6]),
    ((302384901, 302384901), [1, 4]),
    ((302450436, 302384901), [1, 4]),
    ((302450436, 285673476), [2, 3]),
    ((302384901, 302384901), [1, 5]),
    ((318965256, 302253831), [1, 6]),
    ((319030791, 302188296), [1, 6]),
    ((302450436, 302450436), [1, 3]),
    ((319030791, 318965256), [0, 6]),
    ((302253831, 318965256), [1, 6]),
    ((302450436, 319161861), [1, 4]),
    ((319030791, 285476871), [2, 6]),
    ((319030791, 268699911), [3, 6]),
    ((269027586, 268699911), [6, 1]),
    ((335807751, 285476871), [1, 6]),
    ((319030791, 302253831), [1, 6]),
    ((302253831, 302253831), [2, 6]),
    ((319096326, 302188296), [1, 6]),
    ((319096326, 302253831), [1, 5]),
    ((319030791, 319030791), [0, 6]),
    ((269027586, 319030791), [3, 1]),
    ((302319366, 318965256), [1, 6]),
    ((319030791, 302319366), [1, 5]),
    ((319096326, 318965256), [0, 6]),
    ((302319366, 319030791), [1, 5]),
    ((319096326, 302253831), [1, 6]),
    ((319096326, 319030791), [0, 5]),
    ((319030791, 302319366), [1, 6]),
    ((319161861, 302450436), [1, 3]),
    ((319096326, 319096326), [0, 5]),
    ((302319366, 319030791), [1, 6]),
    ((319096326, 302319366), [1, 5]),
    ((319096326, 319030791), [0, 6]),
    ((319161861, 302319366), [1, 5]),
    ((319096326, 302319366), [1, 6]),
    ((319161861, 302384901), [1, 4]),
    ((319096326, 302384901), [1, 5]),
    ((268896516, 268896516), [6, 3]),
    ((319161861, 319096326), [0, 5]),
    ((302384901, 319096326), [1, 5]),
    ((319096326, 319096326), [0, 6]),
    ((319161861, 319161861), [0, 4]),
    ((302450436, 319161861), [1, 3]),
    ((319161861, 302384901), [1, 5]),
    ((269027586, 268896516), [6, 1]),
    ((319161861, 302450436), [1, 4]),
    ((302450436, 302450436), [2, 3]),
    ((319161861, 319161861), [1, 5]),
    ((319096326, 319096326), [1, 5]),
    ((335873286, 302253831), [1, 6]),
    ((335807751, 302253831), [1, 6]),
    ((335807751, 285476871), [2, 6]),
    ((319161861, 319161861), [0, 5]),
    ((335807751, 319030791), [0, 6]),
    ((319030791, 319030791), [1, 6]),
    ((319096326, 319030791), [1, 6]),
    ((335807751, 302319366), [1, 6]),
    ((335873286, 302319366), [1, 5]),
    ((335873286, 319030791), [0, 6]),
    ((335873286, 302319366), [1, 6]),
    ((335873286, 319096326), [0, 5]),
    ((335807751, 319096326), [0, 6]),
    ((319096326, 335807751), [0, 6]),
    ((335873286, 302384901), [1, 5]),
    ((319161861, 319161861), [1, 4]),
    ((319161861, 319096326), [1, 5]),
    ((319096326, 319096326), [1, 6]),
    ((335873286, 319096326), [0, 6]),
    ((319161861, 335873286), [0, 5]),
    ((335873286, 319161861), [0, 5]),
    ((335873286, 319096326), [1, 6]),
    ((335807751, 335807751), [0, 6]),
    ((335807751, 319030791), [1, 6]),
    ((352584711, 302253831), [1, 6]),
    ((352584711, 319030791), [0, 6]),
    ((335873286, 319030791), [1, 6]),
    ((352584711, 302319366), [1, 6]),
    ((319096326, 335807751), [1, 6]),
    ((335873286, 319096326), [1, 5]),
    ((335807751, 319096326), [1, 6]),
    ((352584711, 319096326), [0, 6]),
    ((335873286, 335873286), [0, 5]),
    ((335873286, 335807751), [0, 6]),
    ((352584711, 319096326), [1, 6]),
    ((352584711, 319030791), [1, 6]),
    ((319161861, 335873286), [1, 5]),
    ((335873286, 319161861), [1, 5]),
    ((335873286, 335873286), [0, 6]),
    ((352584711, 335807751), [0, 6]),
    ((335807751, 335807751), [1, 6]),
    ((352584711, 335873286), [0, 6]),
    ((335873286, 335873286), [1, 5]),
    ((335873286, 335807751), [1, 6]),
    ((335873286, 335873286), [1, 6]),
    ((335873286, 352584711), [0, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_39 : List ℕ := [17, 4, 8, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_39 :
    checkTripleGroup 2 108 level3 tree4 base4_39
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_39 = [
    [6, 1, 6, 6, 11, 3, 2, 1],
    [11, 3, 6, 1, 6, 1, 2, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_39) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_40 : List ℕ := [17, 5, 7, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_40 :
    checkTripleGroup 2 108 level3 tree4 base4_40
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_40 = [
    [10, 4, 6, 1, 7, 1, 1, 6],
    [11, 3, 6, 1, 6, 2, 1, 6],
    [11, 2, 6, 1, 6, 3, 1, 6],
    [11, 4, 6, 1, 6, 1, 1, 6],
    [12, 3, 6, 1, 5, 2, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_40) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_41 : List ℕ := [17, 6, 6, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_41 :
    checkTripleGroup 2 108 level3 tree4 base4_41
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_41 = [
    [11, 5, 5, 1, 6, 1, 1, 6],
    [11, 5, 6, 1, 6, 1, 0, 6],
    [11, 6, 5, 1, 6, 0, 1, 6],
    [12, 5, 5, 1, 5, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_41) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_42 : List ℕ := [17, 6, 7, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_42 :
    checkTripleGroup 2 108 level3 tree4 base4_42
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_42 = [
    [11, 5, 6, 0, 6, 1, 1, 6],
    [11, 5, 6, 1, 6, 1, 1, 5],
    [11, 6, 6, 0, 6, 0, 1, 6],
    [12, 5, 6, 0, 5, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_42) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_43 : List ℕ := [17, 7, 7, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_43 :
    checkTripleGroup 2 108 level3 tree4 base4_43
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_43 = [
    [10, 6, 6, 1, 7, 1, 1, 4],
    [11, 6, 6, 1, 6, 1, 1, 4],
    [11, 6, 6, 0, 6, 1, 1, 5],
    [12, 6, 6, 0, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_43) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_44 : List ℕ := [17, 7, 8, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_44 :
    checkTripleGroup 2 108 level3 tree4 base4_44
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_44 = [
    [11, 6, 2, 3, 6, 1, 6, 1],
    [11, 6, 2, 1, 6, 1, 6, 3],
    [11, 6, 6, 1, 6, 1, 2, 3]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_44) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_45 : List ℕ := [17, 8, 8, 3]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_45 :
    checkTripleGroup 2 108 level3 tree4 base4_45
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_45 = [
    [11, 6, 6, 2, 6, 2, 2, 1],
    [11, 6, 6, 1, 6, 2, 2, 2]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_45) = [
    ((218696706, 218696706), [2, 0]),
    ((268699911, 201788676), [3, 1]),
    ((285476871, 201788676), [2, 1]),
    ((218565636, 268699911), [2, 1]),
    ((268699911, 218565636), [2, 1]),
    ((201788676, 201788676), [7, 3]),
    ((218696706, 201788676), [6, 1]),
    ((269027586, 218696706), [2, 0]),
    ((269027586, 201788676), [3, 1]),
    ((218565636, 218565636), [6, 3]),
    ((218696706, 218565636), [6, 1]),
    ((268699911, 268699911), [3, 6]),
    ((218696706, 268699911), [6, 1]),
    ((269027586, 268699911), [3, 1]),
    ((268699911, 268699911), [6, 6]),
    ((218565636, 201788676), [10, 3]),
    ((268896516, 201788676), [7, 3]),
    ((269027586, 218565636), [6, 1]),
    ((268896516, 218565636), [6, 3]),
    ((268896516, 218696706), [6, 1]),
    ((268896516, 268896516), [3, 3]),
    ((269027586, 268896516), [3, 1]),
    ((285476871, 285476871), [2, 6]),
    ((218696706, 285476871), [6, 1]),
    ((302253831, 285476871), [1, 6]),
    ((285673476, 218696706), [6, 1]),
    ((285673476, 218565636), [6, 3]),
    ((285739011, 285739011), [2, 1]),
    ((285739011, 285673476), [2, 2]),
    ((285673476, 285673476), [2, 3]),
    ((302450436, 285673476), [1, 3]),
    ((302253831, 285476871), [2, 6]),
    ((302253831, 302188296), [1, 6]),
    ((302253831, 302253831), [1, 6]),
    ((302319366, 302188296), [1, 6]),
    ((302319366, 302253831), [1, 5]),
    ((302450436, 302384901), [1, 3]),
    ((302319366, 302253831), [1, 6]),
    ((302319366, 302319366), [1, 5]),
    ((302384901, 302319366), [1, 5]),
    ((302319366, 302319366), [1, 6]),
    ((302384901, 302384901), [1, 4]),
    ((302450436, 302384901), [1, 4]),
    ((302450436, 285673476), [2, 3]),
    ((302384901, 302384901), [1, 5]),
    ((318965256, 302253831), [1, 6]),
    ((319030791, 302188296), [1, 6]),
    ((302450436, 302450436), [1, 3]),
    ((319030791, 318965256), [0, 6]),
    ((302253831, 318965256), [1, 6]),
    ((302450436, 319161861), [1, 4]),
    ((319030791, 285476871), [2, 6]),
    ((319030791, 268699911), [3, 6]),
    ((269027586, 268699911), [6, 1]),
    ((335807751, 285476871), [1, 6]),
    ((319030791, 302253831), [1, 6]),
    ((302253831, 302253831), [2, 6]),
    ((319096326, 302188296), [1, 6]),
    ((319096326, 302253831), [1, 5]),
    ((319030791, 319030791), [0, 6]),
    ((269027586, 319030791), [3, 1]),
    ((302319366, 318965256), [1, 6]),
    ((319030791, 302319366), [1, 5]),
    ((319096326, 318965256), [0, 6]),
    ((302319366, 319030791), [1, 5]),
    ((319096326, 302253831), [1, 6]),
    ((319096326, 319030791), [0, 5]),
    ((319030791, 302319366), [1, 6]),
    ((319161861, 302450436), [1, 3]),
    ((319096326, 319096326), [0, 5]),
    ((302319366, 319030791), [1, 6]),
    ((319096326, 302319366), [1, 5]),
    ((319096326, 319030791), [0, 6]),
    ((319161861, 302319366), [1, 5]),
    ((319096326, 302319366), [1, 6]),
    ((319161861, 302384901), [1, 4]),
    ((319096326, 302384901), [1, 5]),
    ((268896516, 268896516), [6, 3]),
    ((319161861, 319096326), [0, 5]),
    ((302384901, 319096326), [1, 5]),
    ((319096326, 319096326), [0, 6]),
    ((319161861, 319161861), [0, 4]),
    ((302450436, 319161861), [1, 3]),
    ((319161861, 302384901), [1, 5]),
    ((269027586, 268896516), [6, 1]),
    ((319161861, 302450436), [1, 4]),
    ((302450436, 302450436), [2, 3]),
    ((319161861, 319161861), [1, 5]),
    ((319096326, 319096326), [1, 5]),
    ((335873286, 302253831), [1, 6]),
    ((335807751, 302253831), [1, 6]),
    ((335807751, 285476871), [2, 6]),
    ((319161861, 319161861), [0, 5]),
    ((335807751, 319030791), [0, 6]),
    ((319030791, 319030791), [1, 6]),
    ((319096326, 319030791), [1, 6]),
    ((335807751, 302319366), [1, 6]),
    ((335873286, 302319366), [1, 5]),
    ((335873286, 319030791), [0, 6]),
    ((335873286, 302319366), [1, 6]),
    ((335873286, 319096326), [0, 5]),
    ((335807751, 319096326), [0, 6]),
    ((319096326, 335807751), [0, 6]),
    ((335873286, 302384901), [1, 5]),
    ((319161861, 319161861), [1, 4]),
    ((319161861, 319096326), [1, 5]),
    ((319096326, 319096326), [1, 6]),
    ((335873286, 319096326), [0, 6]),
    ((319161861, 335873286), [0, 5]),
    ((335873286, 319161861), [0, 5]),
    ((335873286, 319096326), [1, 6]),
    ((335807751, 335807751), [0, 6]),
    ((335807751, 319030791), [1, 6]),
    ((352584711, 302253831), [1, 6]),
    ((352584711, 319030791), [0, 6]),
    ((335873286, 319030791), [1, 6]),
    ((352584711, 302319366), [1, 6]),
    ((319096326, 335807751), [1, 6]),
    ((335873286, 319096326), [1, 5]),
    ((335807751, 319096326), [1, 6]),
    ((352584711, 319096326), [0, 6]),
    ((335873286, 335873286), [0, 5]),
    ((335873286, 335807751), [0, 6]),
    ((352584711, 319096326), [1, 6]),
    ((352584711, 319030791), [1, 6]),
    ((319161861, 335873286), [1, 5]),
    ((335873286, 319161861), [1, 5]),
    ((335873286, 335873286), [0, 6]),
    ((352584711, 335807751), [0, 6]),
    ((335807751, 335807751), [1, 6]),
    ((352584711, 335873286), [0, 6]),
    ((335873286, 335873286), [1, 5]),
    ((335873286, 335807751), [1, 6]),
    ((335873286, 335873286), [1, 6]),
    ((335873286, 352584711), [0, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_46 : List ℕ := [18, 4, 6, 8]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_46 :
    checkTripleGroup 2 108 level3 tree4 base4_46
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_46 = [
    [12, 3, 5, 2, 6, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_46) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_47 : List ℕ := [18, 4, 7, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_47 :
    checkTripleGroup 2 108 level3 tree4 base4_47
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_47 = [
    [11, 3, 6, 1, 7, 1, 1, 6],
    [12, 3, 5, 1, 6, 1, 2, 6],
    [12, 2, 6, 1, 6, 2, 1, 6],
    [12, 3, 6, 1, 6, 1, 1, 6],
    [13, 2, 6, 1, 5, 2, 1, 6],
    [13, 3, 5, 1, 5, 1, 2, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_47) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_48 : List ℕ := [18, 5, 6, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_48 :
    checkTripleGroup 2 108 level3 tree4 base4_48
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_48 = [
    [12, 4, 5, 1, 6, 1, 1, 6],
    [12, 3, 5, 1, 6, 2, 1, 6],
    [12, 3, 6, 1, 6, 2, 0, 6],
    [12, 4, 6, 1, 6, 1, 0, 6],
    [12, 5, 5, 1, 6, 0, 1, 6],
    [13, 3, 5, 1, 5, 2, 1, 6],
    [13, 3, 6, 1, 5, 2, 0, 6],
    [13, 4, 5, 1, 5, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_48) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_49 : List ℕ := [18, 5, 7, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_49 :
    checkTripleGroup 2 108 level3 tree4 base4_49
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_49 = [
    [12, 3, 6, 0, 6, 2, 1, 6],
    [12, 3, 6, 1, 6, 2, 1, 5],
    [12, 4, 6, 0, 6, 1, 1, 6],
    [12, 4, 6, 1, 6, 1, 1, 5],
    [12, 5, 6, 0, 6, 0, 1, 6],
    [13, 3, 6, 0, 5, 2, 1, 6],
    [13, 3, 6, 1, 5, 2, 1, 5],
    [13, 4, 6, 0, 5, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_49) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_50 : List ℕ := [18, 6, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_50 :
    checkTripleGroup 2 108 level3 tree4 base4_50
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_50 = [
    [12, 5, 5, 1, 6, 1, 1, 5],
    [12, 5, 5, 0, 6, 1, 1, 6],
    [12, 5, 6, 0, 6, 1, 0, 6],
    [12, 5, 6, 1, 6, 1, 0, 5],
    [12, 6, 5, 1, 6, 0, 1, 5],
    [12, 6, 5, 0, 6, 0, 1, 6],
    [12, 6, 6, 0, 6, 0, 0, 6],
    [13, 5, 5, 0, 5, 1, 1, 6],
    [13, 5, 5, 1, 5, 1, 1, 5],
    [13, 5, 6, 0, 5, 1, 0, 6],
    [13, 6, 5, 0, 5, 0, 1, 6],
    [14, 5, 5, 0, 4, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_50) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_51 : List ℕ := [18, 6, 7, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_51 :
    checkTripleGroup 2 108 level3 tree4 base4_51
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_51 = [
    [12, 5, 6, 0, 6, 1, 1, 5],
    [12, 5, 6, 1, 6, 1, 1, 4],
    [12, 6, 6, 0, 6, 0, 1, 5],
    [13, 5, 6, 0, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_51) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_52 : List ℕ := [18, 7, 7, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_52 :
    checkTripleGroup 2 108 level3 tree4 base4_52
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_52 = [
    [11, 6, 6, 1, 7, 1, 1, 3],
    [12, 5, 6, 1, 6, 2, 1, 3],
    [12, 6, 6, 0, 6, 1, 1, 4],
    [12, 6, 5, 1, 6, 1, 2, 3],
    [12, 6, 6, 1, 6, 1, 1, 3],
    [13, 6, 6, 0, 5, 1, 1, 4],
    [13, 5, 6, 1, 5, 2, 1, 3],
    [13, 6, 5, 1, 5, 1, 2, 3]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_52) = [
    ((218696706, 218696706), [2, 0]),
    ((268699911, 201788676), [3, 1]),
    ((285476871, 201788676), [2, 1]),
    ((218565636, 268699911), [2, 1]),
    ((268699911, 218565636), [2, 1]),
    ((201788676, 201788676), [7, 3]),
    ((218696706, 201788676), [6, 1]),
    ((269027586, 218696706), [2, 0]),
    ((269027586, 201788676), [3, 1]),
    ((218565636, 218565636), [6, 3]),
    ((218696706, 218565636), [6, 1]),
    ((268699911, 268699911), [3, 6]),
    ((218696706, 268699911), [6, 1]),
    ((269027586, 268699911), [3, 1]),
    ((268699911, 268699911), [6, 6]),
    ((218565636, 201788676), [10, 3]),
    ((268896516, 201788676), [7, 3]),
    ((269027586, 218565636), [6, 1]),
    ((268896516, 218565636), [6, 3]),
    ((268896516, 218696706), [6, 1]),
    ((268896516, 268896516), [3, 3]),
    ((269027586, 268896516), [3, 1]),
    ((285476871, 285476871), [2, 6]),
    ((218696706, 285476871), [6, 1]),
    ((302253831, 285476871), [1, 6]),
    ((285673476, 218696706), [6, 1]),
    ((285673476, 218565636), [6, 3]),
    ((285739011, 285739011), [2, 1]),
    ((285739011, 285673476), [2, 2]),
    ((285673476, 285673476), [2, 3]),
    ((302450436, 285673476), [1, 3]),
    ((302253831, 285476871), [2, 6]),
    ((302253831, 302188296), [1, 6]),
    ((302253831, 302253831), [1, 6]),
    ((302319366, 302188296), [1, 6]),
    ((302319366, 302253831), [1, 5]),
    ((302450436, 302384901), [1, 3]),
    ((302319366, 302253831), [1, 6]),
    ((302319366, 302319366), [1, 5]),
    ((302384901, 302319366), [1, 5]),
    ((302319366, 302319366), [1, 6]),
    ((302384901, 302384901), [1, 4]),
    ((302450436, 302384901), [1, 4]),
    ((302450436, 285673476), [2, 3]),
    ((302384901, 302384901), [1, 5]),
    ((318965256, 302253831), [1, 6]),
    ((319030791, 302188296), [1, 6]),
    ((302450436, 302450436), [1, 3]),
    ((319030791, 318965256), [0, 6]),
    ((302253831, 318965256), [1, 6]),
    ((302450436, 319161861), [1, 4]),
    ((319030791, 285476871), [2, 6]),
    ((319030791, 268699911), [3, 6]),
    ((269027586, 268699911), [6, 1]),
    ((335807751, 285476871), [1, 6]),
    ((319030791, 302253831), [1, 6]),
    ((302253831, 302253831), [2, 6]),
    ((319096326, 302188296), [1, 6]),
    ((319096326, 302253831), [1, 5]),
    ((319030791, 319030791), [0, 6]),
    ((269027586, 319030791), [3, 1]),
    ((302319366, 318965256), [1, 6]),
    ((319030791, 302319366), [1, 5]),
    ((319096326, 318965256), [0, 6]),
    ((302319366, 319030791), [1, 5]),
    ((319096326, 302253831), [1, 6]),
    ((319096326, 319030791), [0, 5]),
    ((319030791, 302319366), [1, 6]),
    ((319161861, 302450436), [1, 3]),
    ((319096326, 319096326), [0, 5]),
    ((302319366, 319030791), [1, 6]),
    ((319096326, 302319366), [1, 5]),
    ((319096326, 319030791), [0, 6]),
    ((319161861, 302319366), [1, 5]),
    ((319096326, 302319366), [1, 6]),
    ((319161861, 302384901), [1, 4]),
    ((319096326, 302384901), [1, 5]),
    ((268896516, 268896516), [6, 3]),
    ((319161861, 319096326), [0, 5]),
    ((302384901, 319096326), [1, 5]),
    ((319096326, 319096326), [0, 6]),
    ((319161861, 319161861), [0, 4]),
    ((302450436, 319161861), [1, 3]),
    ((319161861, 302384901), [1, 5]),
    ((269027586, 268896516), [6, 1]),
    ((319161861, 302450436), [1, 4]),
    ((302450436, 302450436), [2, 3]),
    ((319161861, 319161861), [1, 5]),
    ((319096326, 319096326), [1, 5]),
    ((335873286, 302253831), [1, 6]),
    ((335807751, 302253831), [1, 6]),
    ((335807751, 285476871), [2, 6]),
    ((319161861, 319161861), [0, 5]),
    ((335807751, 319030791), [0, 6]),
    ((319030791, 319030791), [1, 6]),
    ((319096326, 319030791), [1, 6]),
    ((335807751, 302319366), [1, 6]),
    ((335873286, 302319366), [1, 5]),
    ((335873286, 319030791), [0, 6]),
    ((335873286, 302319366), [1, 6]),
    ((335873286, 319096326), [0, 5]),
    ((335807751, 319096326), [0, 6]),
    ((319096326, 335807751), [0, 6]),
    ((335873286, 302384901), [1, 5]),
    ((319161861, 319161861), [1, 4]),
    ((319161861, 319096326), [1, 5]),
    ((319096326, 319096326), [1, 6]),
    ((335873286, 319096326), [0, 6]),
    ((319161861, 335873286), [0, 5]),
    ((335873286, 319161861), [0, 5]),
    ((335873286, 319096326), [1, 6]),
    ((335807751, 335807751), [0, 6]),
    ((335807751, 319030791), [1, 6]),
    ((352584711, 302253831), [1, 6]),
    ((352584711, 319030791), [0, 6]),
    ((335873286, 319030791), [1, 6]),
    ((352584711, 302319366), [1, 6]),
    ((319096326, 335807751), [1, 6]),
    ((335873286, 319096326), [1, 5]),
    ((335807751, 319096326), [1, 6]),
    ((352584711, 319096326), [0, 6]),
    ((335873286, 335873286), [0, 5]),
    ((335873286, 335807751), [0, 6]),
    ((352584711, 319096326), [1, 6]),
    ((352584711, 319030791), [1, 6]),
    ((319161861, 335873286), [1, 5]),
    ((335873286, 319161861), [1, 5]),
    ((335873286, 335873286), [0, 6]),
    ((352584711, 335807751), [0, 6]),
    ((335807751, 335807751), [1, 6]),
    ((352584711, 335873286), [0, 6]),
    ((335873286, 335873286), [1, 5]),
    ((335873286, 335807751), [1, 6]),
    ((335873286, 335873286), [1, 6]),
    ((335873286, 352584711), [0, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_53 : List ℕ := [19, 3, 6, 8]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_53 :
    checkTripleGroup 2 108 level3 tree4 base4_53
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_53 = [
    [13, 2, 5, 2, 6, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_53) = [
    ((168561666, 168561666), [2, 0]),
    ((185010951, 185010951), [1, 1]),
    ((185010951, 185010951), [2, 1]),
    ((201787911, 185010951), [1, 1]),
    ((201787911, 201787911), [0, 1]),
    ((252118791, 101453826), [6, 1]),
    ((185010951, 185010951), [5, 1]),
    ((252118791, 185010951), [1, 1]),
    ((235341831, 185010951), [2, 1]),
    ((168561666, 185010951), [6, 1]),
    ((185010951, 185010951), [5, 6]),
    ((201787911, 185010951), [5, 1]),
    ((185010951, 185010951), [6, 1]),
    ((252118791, 185010951), [2, 1]),
    ((201787911, 201787911), [4, 1]),
    ((218564871, 201787911), [3, 1]),
    ((235341831, 201787911), [2, 1]),
    ((252118791, 201787911), [1, 1]),
    ((235341831, 218564871), [1, 1]),
    ((218564871, 218564871), [2, 1]),
    ((252118791, 118165251), [6, 1]),
    ((252118791, 235341831), [2, 6]),
    ((252118791, 118230786), [6, 1]),
    ((185010951, 185010951), [6, 6]),
    ((201787911, 185010951), [5, 6]),
    ((201787911, 201787911), [4, 6]),
    ((168561666, 201787911), [6, 1]),
    ((252118791, 252118791), [1, 1]),
    ((168561666, 218564871), [6, 1]),
    ((168561666, 235341831), [6, 1]),
    ((218564871, 218564871), [3, 6]),
    ((252118791, 235341831), [1, 6]),
    ((235341831, 235341831), [2, 6]),
    ((252118791, 252053256), [1, 6]),
    ((252118791, 251856651), [1, 6]),
    ((185010951, 185010951), [9, 6]),
    ((252118791, 168561666), [6, 1]),
    ((252118791, 185010951), [5, 6]),
    ((235341831, 185010951), [6, 6]),
    ((168561666, 252118791), [6, 1]),
    ((252118791, 252118791), [1, 6]),
    ((252118791, 268568076), [1, 6]),
    ((252118791, 268633611), [1, 6]),
    ((268830216, 252118791), [1, 6]),
    ((185010951, 185010951), [10, 6]),
    ((252118791, 268830216), [1, 6]),
    ((201787911, 185010951), [9, 6]),
    ((252118791, 185010951), [6, 6]),
    ((218564871, 218564871), [6, 6]),
    ((218564871, 201787911), [7, 6]),
    ((201787911, 201787911), [8, 6]),
    ((252118791, 201787911), [5, 6]),
    ((235341831, 201787911), [6, 6]),
    ((252118791, 252118791), [2, 6]),
    ((235341831, 218564871), [6, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_54 : List ℕ := [19, 4, 4, 9]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_54 :
    checkTripleGroup 2 108 level3 tree4 base4_54
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_54 = [
    [13, 3, 3, 3, 6, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_54) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_55 : List ℕ := [19, 4, 5, 8]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_55 :
    checkTripleGroup 2 108 level3 tree4 base4_55
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_55 = [
    [13, 3, 5, 2, 6, 1, 0, 6],
    [13, 3, 4, 2, 6, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_55) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_56 : List ℕ := [19, 4, 6, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_56 :
    checkTripleGroup 2 108 level3 tree4 base4_56
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_56 = [
    [13, 2, 5, 1, 6, 2, 1, 6],
    [13, 2, 6, 1, 6, 2, 0, 6],
    [13, 3, 4, 1, 6, 1, 2, 6],
    [13, 3, 3, 1, 6, 1, 3, 6],
    [13, 3, 5, 1, 6, 1, 1, 6],
    [13, 3, 6, 1, 6, 1, 0, 6],
    [13, 3, 5, 2, 6, 1, 1, 5],
    [13, 4, 5, 1, 6, 0, 1, 6],
    [14, 3, 5, 1, 5, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_56) = [
    ((268896006, 185011206), [6, 5]),
    ((268896006, 118165506), [6, 1]),
    ((202050306, 202050306), [1, 0]),
    ((185011206, 185011206), [2, 0]),
    ((185273346, 185273346), [2, 0]),
    ((201722631, 201722631), [1, 1]),
    ((185338881, 185273346), [2, 0]),
    ((201788166, 201722631), [1, 1]),
    ((201788166, 185011206), [2, 0]),
    ((201722631, 185011206), [2, 1]),
    ((185011206, 201722631), [2, 1]),
    ((201788166, 201788166), [1, 0]),
    ((202050306, 185273346), [2, 0]),
    ((202050306, 185338881), [2, 0]),
    ((185338881, 202050306), [2, 0]),
    ((185011206, 185011206), [6, 0]),
    ((252053511, 185011206), [2, 1]),
    ((252119046, 185011206), [2, 0]),
    ((185011206, 185011206), [6, 5]),
    ((185338881, 185011206), [6, 0]),
    ((185273346, 185011206), [6, 1]),
    ((252053511, 201722631), [2, 1]),
    ((201722631, 201722631), [5, 1]),
    ((268830471, 201722631), [1, 1]),
    ((201788166, 201722631), [5, 1]),
    ((268830471, 185011206), [2, 1]),
    ((201722631, 185011206), [6, 1]),
    ((201788166, 185011206), [6, 0]),
    ((268896006, 185011206), [2, 0]),
    ((185011206, 201722631), [6, 1]),
    ((268896006, 201722631), [1, 1]),
    ((252119046, 201722631), [2, 1]),
    ((252053511, 201788166), [2, 1]),
    ((201788166, 201788166), [5, 0]),
    ((252119046, 201788166), [2, 0]),
    ((268896006, 118165506), [6, 0]),
    ((268896006, 201788166), [1, 0]),
    ((268830471, 201788166), [1, 1]),
    ((268830471, 118165506), [6, 1]),
    ((202050306, 201722631), [5, 1]),
    ((201722631, 201722631), [5, 6]),
    ((185273346, 201722631), [6, 1]),
    ((185011206, 201722631), [6, 6]),
    ((201722631, 185011206), [6, 6]),
    ((268896006, 118231041), [6, 0]),
    ((268830471, 118231041), [6, 1]),
    ((201788166, 185011206), [6, 5]),
    ((202050306, 185011206), [6, 1]),
    ((185338881, 201722631), [6, 1]),
    ((201788166, 201722631), [5, 6]),
    ((185273346, 201788166), [6, 1]),
    ((185338881, 201788166), [6, 0]),
    ((201788166, 201788166), [5, 5]),
    ((202050306, 201788166), [5, 1]),
    ((185011206, 185011206), [10, 5]),
    ((185273346, 252053511), [6, 1]),
    ((252053511, 252053511), [2, 6]),
    ((252053511, 185011206), [6, 6]),
    ((252119046, 185273346), [6, 1]),
    ((252119046, 185011206), [6, 5]),
    ((201722631, 201722631), [9, 6]),
    ((268896006, 268568331), [1, 6]),
    ((252119046, 252119046), [2, 5]),
    ((185273346, 252119046), [6, 1]),
    ((252119046, 252053511), [2, 6]),
    ((185338881, 252053511), [6, 1]),
    ((185338881, 252119046), [6, 0]),
    ((268896006, 268568331), [1, 5]),
    ((268830471, 268830471), [1, 1]),
    ((268830471, 268568331), [1, 6]),
    ((268896006, 268896006), [1, 0]),
    ((268896006, 268830471), [1, 1]),
    ((268830471, 268699401), [1, 6]),
    ((268896006, 268896006), [1, 1]),
    ((268830471, 268633866), [1, 6]),
    ((268896006, 268633866), [1, 5]),
    ((268830471, 268764936), [1, 6]),
    ((268830471, 185273346), [6, 1]),
    ((202050306, 252053511), [6, 1]),
    ((268830471, 201722631), [5, 6]),
    ((252053511, 201722631), [6, 6]),
    ((268830471, 252053511), [2, 6]),
    ((185273346, 268830471), [6, 1]),
    ((268896006, 268764936), [1, 6]),
    ((268830471, 268830471), [1, 6]),
    ((202050306, 268830471), [5, 1]),
    ((268896006, 268830471), [1, 5]),
    ((201788166, 185011206), [10, 5]),
    ((201722631, 185011206), [10, 6]),
    ((268830471, 185011206), [6, 6]),
    ((252119046, 201722631), [6, 6]),
    ((268896006, 185338881), [6, 0]),
    ((268896006, 185273346), [6, 1]),
    ((185011206, 201722631), [10, 6]),
    ((201788166, 201722631), [9, 6]),
    ((268896006, 201722631), [5, 6]),
    ((201788166, 201788166), [9, 5]),
    ((252053511, 201788166), [6, 6]),
    ((268830471, 201788166), [5, 6]),
    ((252119046, 201788166), [6, 5]),
    ((268896006, 201788166), [5, 5]),
    ((268896006, 202050306), [5, 1]),
    ((268896006, 268830471), [1, 6]),
    ((268830471, 252119046), [2, 6]),
    ((268896006, 252053511), [2, 6]),
    ((202050306, 252119046), [6, 1]),
    ((185338881, 268830471), [6, 1]),
    ((268896006, 252119046), [2, 5]),
    ((252119046, 268830471), [2, 6]),
    ((185338881, 268896006), [6, 0]),
    ((202050306, 268896006), [5, 1]),
    ((268896006, 268896006), [1, 5]),
    ((285607431, 268830471), [1, 6]),
    ((285607431, 285607431), [0, 6]),
    ((268896006, 285607431), [1, 6]),
    ((285607431, 268896006), [1, 6]),
    ((285607431, 285607431), [1, 6]),
    ((319030281, 268830471), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_57 : List ℕ := [19, 5, 5, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_57 :
    checkTripleGroup 2 108 level3 tree4 base4_57
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_57 = [
    [13, 4, 5, 1, 6, 1, 0, 6],
    [13, 3, 4, 1, 6, 2, 1, 6],
    [13, 3, 5, 1, 6, 2, 0, 6],
    [13, 4, 3, 1, 6, 1, 2, 6],
    [13, 4, 4, 1, 6, 1, 1, 6],
    [13, 5, 4, 1, 6, 0, 1, 6],
    [13, 5, 3, 1, 6, 0, 2, 6],
    [13, 5, 5, 1, 6, 0, 0, 6],
    [14, 4, 4, 1, 5, 1, 1, 6],
    [14, 4, 5, 1, 5, 1, 0, 6],
    [14, 5, 4, 1, 5, 0, 1, 6],
    [15, 4, 4, 1, 4, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_57) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_58 : List ℕ := [19, 5, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_58 :
    checkTripleGroup 2 108 level3 tree4 base4_58
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_58 = [
    [13, 3, 5, 0, 6, 2, 1, 6],
    [13, 3, 5, 1, 6, 2, 1, 5],
    [13, 3, 6, 0, 6, 2, 0, 6],
    [13, 4, 5, 0, 6, 1, 1, 6],
    [13, 3, 6, 1, 6, 2, 0, 5],
    [13, 4, 6, 1, 6, 1, 0, 5],
    [13, 4, 5, 1, 6, 1, 1, 5],
    [13, 4, 6, 0, 6, 1, 0, 6],
    [13, 5, 5, 0, 6, 0, 1, 6],
    [13, 5, 5, 1, 6, 0, 1, 5],
    [13, 5, 6, 0, 6, 0, 0, 6],
    [14, 4, 5, 1, 5, 1, 1, 5],
    [14, 4, 5, 0, 5, 1, 1, 6],
    [14, 4, 6, 0, 5, 1, 0, 6],
    [14, 5, 5, 0, 5, 0, 1, 6],
    [15, 4, 5, 0, 4, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_58) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_59 : List ℕ := [19, 6, 6, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_59 :
    checkTripleGroup 2 108 level3 tree4 base4_59
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_59 = [
    [13, 5, 5, 2, 6, 1, 1, 3],
    [13, 5, 5, 0, 6, 1, 1, 5],
    [13, 5, 5, 1, 6, 1, 1, 4],
    [13, 5, 6, 0, 6, 1, 0, 5],
    [13, 5, 6, 1, 6, 1, 0, 4],
    [13, 6, 5, 0, 6, 0, 1, 5],
    [13, 6, 5, 1, 6, 0, 1, 4],
    [14, 6, 5, 0, 5, 0, 1, 5],
    [13, 6, 6, 0, 6, 0, 0, 5],
    [14, 5, 5, 1, 5, 1, 1, 4],
    [14, 5, 5, 0, 5, 1, 1, 5],
    [14, 5, 6, 0, 5, 1, 0, 5],
    [15, 5, 5, 0, 4, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_59) = [
    ((218696706, 218696706), [2, 0]),
    ((268699911, 201788676), [3, 1]),
    ((285476871, 201788676), [2, 1]),
    ((218565636, 268699911), [2, 1]),
    ((268699911, 218565636), [2, 1]),
    ((201788676, 201788676), [7, 3]),
    ((218696706, 201788676), [6, 1]),
    ((269027586, 218696706), [2, 0]),
    ((269027586, 201788676), [3, 1]),
    ((218565636, 218565636), [6, 3]),
    ((218696706, 218565636), [6, 1]),
    ((268699911, 268699911), [3, 6]),
    ((218696706, 268699911), [6, 1]),
    ((269027586, 268699911), [3, 1]),
    ((268699911, 268699911), [6, 6]),
    ((218565636, 201788676), [10, 3]),
    ((268896516, 201788676), [7, 3]),
    ((269027586, 218565636), [6, 1]),
    ((268896516, 218565636), [6, 3]),
    ((268896516, 218696706), [6, 1]),
    ((268896516, 268896516), [3, 3]),
    ((269027586, 268896516), [3, 1]),
    ((285476871, 285476871), [2, 6]),
    ((218696706, 285476871), [6, 1]),
    ((302253831, 285476871), [1, 6]),
    ((285673476, 218696706), [6, 1]),
    ((285673476, 218565636), [6, 3]),
    ((285739011, 285739011), [2, 1]),
    ((285739011, 285673476), [2, 2]),
    ((285673476, 285673476), [2, 3]),
    ((302450436, 285673476), [1, 3]),
    ((302253831, 285476871), [2, 6]),
    ((302253831, 302188296), [1, 6]),
    ((302253831, 302253831), [1, 6]),
    ((302319366, 302188296), [1, 6]),
    ((302319366, 302253831), [1, 5]),
    ((302450436, 302384901), [1, 3]),
    ((302319366, 302253831), [1, 6]),
    ((302319366, 302319366), [1, 5]),
    ((302384901, 302319366), [1, 5]),
    ((302319366, 302319366), [1, 6]),
    ((302384901, 302384901), [1, 4]),
    ((302450436, 302384901), [1, 4]),
    ((302450436, 285673476), [2, 3]),
    ((302384901, 302384901), [1, 5]),
    ((318965256, 302253831), [1, 6]),
    ((319030791, 302188296), [1, 6]),
    ((302450436, 302450436), [1, 3]),
    ((319030791, 318965256), [0, 6]),
    ((302253831, 318965256), [1, 6]),
    ((302450436, 319161861), [1, 4]),
    ((319030791, 285476871), [2, 6]),
    ((319030791, 268699911), [3, 6]),
    ((269027586, 268699911), [6, 1]),
    ((335807751, 285476871), [1, 6]),
    ((319030791, 302253831), [1, 6]),
    ((302253831, 302253831), [2, 6]),
    ((319096326, 302188296), [1, 6]),
    ((319096326, 302253831), [1, 5]),
    ((319030791, 319030791), [0, 6]),
    ((269027586, 319030791), [3, 1]),
    ((302319366, 318965256), [1, 6]),
    ((319030791, 302319366), [1, 5]),
    ((319096326, 318965256), [0, 6]),
    ((302319366, 319030791), [1, 5]),
    ((319096326, 302253831), [1, 6]),
    ((319096326, 319030791), [0, 5]),
    ((319030791, 302319366), [1, 6]),
    ((319161861, 302450436), [1, 3]),
    ((319096326, 319096326), [0, 5]),
    ((302319366, 319030791), [1, 6]),
    ((319096326, 302319366), [1, 5]),
    ((319096326, 319030791), [0, 6]),
    ((319161861, 302319366), [1, 5]),
    ((319096326, 302319366), [1, 6]),
    ((319161861, 302384901), [1, 4]),
    ((319096326, 302384901), [1, 5]),
    ((268896516, 268896516), [6, 3]),
    ((319161861, 319096326), [0, 5]),
    ((302384901, 319096326), [1, 5]),
    ((319096326, 319096326), [0, 6]),
    ((319161861, 319161861), [0, 4]),
    ((302450436, 319161861), [1, 3]),
    ((319161861, 302384901), [1, 5]),
    ((269027586, 268896516), [6, 1]),
    ((319161861, 302450436), [1, 4]),
    ((302450436, 302450436), [2, 3]),
    ((319161861, 319161861), [1, 5]),
    ((319096326, 319096326), [1, 5]),
    ((335873286, 302253831), [1, 6]),
    ((335807751, 302253831), [1, 6]),
    ((335807751, 285476871), [2, 6]),
    ((319161861, 319161861), [0, 5]),
    ((335807751, 319030791), [0, 6]),
    ((319030791, 319030791), [1, 6]),
    ((319096326, 319030791), [1, 6]),
    ((335807751, 302319366), [1, 6]),
    ((335873286, 302319366), [1, 5]),
    ((335873286, 319030791), [0, 6]),
    ((335873286, 302319366), [1, 6]),
    ((335873286, 319096326), [0, 5]),
    ((335807751, 319096326), [0, 6]),
    ((319096326, 335807751), [0, 6]),
    ((335873286, 302384901), [1, 5]),
    ((319161861, 319161861), [1, 4]),
    ((319161861, 319096326), [1, 5]),
    ((319096326, 319096326), [1, 6]),
    ((335873286, 319096326), [0, 6]),
    ((319161861, 335873286), [0, 5]),
    ((335873286, 319161861), [0, 5]),
    ((335873286, 319096326), [1, 6]),
    ((335807751, 335807751), [0, 6]),
    ((335807751, 319030791), [1, 6]),
    ((352584711, 302253831), [1, 6]),
    ((352584711, 319030791), [0, 6]),
    ((335873286, 319030791), [1, 6]),
    ((352584711, 302319366), [1, 6]),
    ((319096326, 335807751), [1, 6]),
    ((335873286, 319096326), [1, 5]),
    ((335807751, 319096326), [1, 6]),
    ((352584711, 319096326), [0, 6]),
    ((335873286, 335873286), [0, 5]),
    ((335873286, 335807751), [0, 6]),
    ((352584711, 319096326), [1, 6]),
    ((352584711, 319030791), [1, 6]),
    ((319161861, 335873286), [1, 5]),
    ((335873286, 319161861), [1, 5]),
    ((335873286, 335873286), [0, 6]),
    ((352584711, 335807751), [0, 6]),
    ((335807751, 335807751), [1, 6]),
    ((352584711, 335873286), [0, 6]),
    ((335873286, 335873286), [1, 5]),
    ((335873286, 335807751), [1, 6]),
    ((335873286, 335873286), [1, 6]),
    ((335873286, 352584711), [0, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_60 : List ℕ := [20, 4, 4, 8]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_60 :
    checkTripleGroup 2 108 level3 tree4 base4_60
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_60 = [
    [14, 3, 3, 2, 6, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_60) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_61 : List ℕ := [20, 4, 5, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_61 :
    checkTripleGroup 2 108 level3 tree4 base4_61
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_61 = [
    [13, 3, 4, 1, 7, 1, 1, 6],
    [14, 3, 4, 1, 6, 1, 1, 6],
    [14, 3, 3, 1, 6, 1, 2, 6],
    [14, 3, 5, 1, 6, 1, 0, 6],
    [14, 4, 4, 1, 6, 0, 1, 6],
    [14, 4, 5, 1, 6, 0, 0, 6],
    [15, 3, 5, 1, 5, 1, 0, 6],
    [15, 3, 4, 1, 5, 1, 1, 6],
    [15, 4, 4, 1, 5, 0, 1, 6],
    [16, 3, 4, 1, 4, 1, 1, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_61) = [
    ((268830726, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 0]),
    ((201722886, 201722886), [2, 1]),
    ((201985026, 201985026), [2, 0]),
    ((201788421, 201722886), [2, 0]),
    ((202050561, 201985026), [2, 0]),
    ((202050561, 202050561), [2, 0]),
    ((202116096, 201985026), [2, 0]),
    ((201722886, 201722886), [6, 0]),
    ((268765191, 201722886), [2, 1]),
    ((201722886, 201722886), [6, 1]),
    ((201788421, 201722886), [6, 0]),
    ((268830726, 201722886), [2, 1]),
    ((268896261, 201722886), [2, 0]),
    ((268765191, 201788421), [2, 1]),
    ((268830726, 201788421), [2, 0]),
    ((201985026, 201722886), [6, 1]),
    ((201722886, 201722886), [6, 5]),
    ((202050561, 201722886), [6, 0]),
    ((201788421, 201722886), [6, 5]),
    ((201722886, 201722886), [6, 6]),
    ((202116096, 201722886), [6, 0]),
    ((202050561, 201722886), [6, 1]),
    ((201788421, 201788421), [6, 4]),
    ((201985026, 201788421), [6, 1]),
    ((202050561, 201788421), [6, 0]),
    ((201985026, 268765191), [6, 1]),
    ((268765191, 268765191), [2, 6]),
    ((285542151, 268765191), [1, 6]),
    ((201985026, 268830726), [6, 1]),
    ((201722886, 201722886), [10, 5]),
    ((268765191, 201722886), [6, 6]),
    ((268830726, 201985026), [6, 1]),
    ((268830726, 201722886), [6, 5]),
    ((268830726, 268765191), [2, 6]),
    ((202050561, 268765191), [6, 1]),
    ((202050561, 268830726), [6, 0]),
    ((268830726, 268830726), [2, 5]),
    ((285542151, 285476616), [1, 6]),
    ((201722886, 201722886), [10, 6]),
    ((201788421, 201722886), [10, 5]),
    ((268830726, 201722886), [6, 6]),
    ((268896261, 201722886), [6, 5]),
    ((201788421, 201788421), [10, 4]),
    ((268830726, 201788421), [6, 5]),
    ((268896261, 201985026), [6, 1]),
    ((268896261, 201788421), [6, 4]),
    ((268896261, 202050561), [6, 0]),
    ((202116096, 268830726), [6, 0]),
    ((202050561, 268830726), [6, 1]),
    ((268830726, 268830726), [2, 6]),
    ((202050561, 268896261), [6, 0]),
    ((268896261, 268830726), [2, 5]),
    ((268896261, 268896261), [2, 4]),
    ((285542151, 285411081), [1, 6]),
    ((285673221, 268896261), [1, 4]),
    ((302319111, 285542151), [1, 6]),
    ((285673221, 285673221), [1, 4]),
    ((285607686, 285542151), [1, 6]),
    ((285542151, 285542151), [1, 6]),
    ((285607686, 285607686), [1, 5]),
    ((285673221, 285607686), [1, 5]),
    ((285607686, 285607686), [1, 6]),
    ((302319111, 285476616), [1, 6]),
    ((302253576, 285542151), [1, 6]),
    ((285542151, 302253576), [1, 6]),
    ((302319111, 302253576), [0, 6]),
    ((302384646, 285607686), [1, 5]),
    ((302384646, 285542151), [1, 6]),
    ((302319111, 302319111), [0, 6]),
    ((302319111, 285607686), [1, 6]),
    ((285607686, 302319111), [1, 6]),
    ((302384646, 302319111), [0, 6]),
    ((302384646, 302384646), [0, 5]),
    ((285673221, 302384646), [1, 5]),
    ((302384646, 285673221), [1, 5]),
    ((302384646, 285607686), [1, 6]),
    ((302384646, 302384646), [0, 6]),
    ((319096071, 302319111), [0, 6]),
    ((319030536, 302319111), [0, 6]),
    ((319030536, 285542151), [1, 6]),
    ((319096071, 285476616), [1, 6]),
    ((302319111, 302253576), [1, 6]),
    ((319096071, 302253576), [0, 6]),
    ((302319111, 319030536), [0, 6]),
    ((319096071, 268765191), [2, 6]),
    ((319096071, 285542151), [1, 6]),
    ((302319111, 302319111), [1, 6]),
    ((302384646, 302319111), [1, 6]),
    ((319096071, 285607686), [1, 6]),
    ((319096071, 268830726), [2, 6]),
    ((319096071, 302384646), [0, 6]),
    ((302384646, 302384646), [1, 5]),
    ((302384646, 319096071), [0, 6]),
    ((302384646, 302384646), [1, 6]),
    ((335807496, 285542151), [1, 6]),
    ((319096071, 302319111), [1, 6]),
    ((319096071, 319096071), [0, 6]),
    ((302384646, 319096071), [1, 6]),
    ((319096071, 302384646), [1, 6]),
    ((319096071, 319096071), [1, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_62 : List ℕ := [20, 5, 5, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_62 :
    checkTripleGroup 2 108 level3 tree4 base4_62
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_62 = [
    [14, 4, 4, 0, 6, 1, 1, 6],
    [14, 4, 4, 1, 6, 1, 1, 5],
    [14, 4, 5, 0, 6, 1, 0, 6],
    [14, 5, 4, 0, 6, 0, 1, 6],
    [14, 4, 5, 1, 6, 1, 0, 5],
    [14, 5, 4, 1, 6, 0, 1, 5],
    [14, 5, 5, 0, 6, 0, 0, 6],
    [14, 5, 5, 1, 6, 0, 0, 5],
    [15, 5, 4, 0, 5, 0, 1, 6],
    [15, 4, 4, 0, 5, 1, 1, 6],
    [15, 4, 4, 1, 5, 1, 1, 5],
    [15, 4, 5, 1, 5, 1, 0, 5],
    [15, 4, 5, 0, 5, 1, 0, 6],
    [15, 5, 4, 1, 5, 0, 1, 5],
    [15, 5, 5, 0, 5, 0, 0, 6],
    [16, 4, 4, 1, 4, 1, 1, 5],
    [16, 4, 4, 0, 4, 1, 1, 6],
    [16, 5, 4, 0, 4, 0, 1, 6],
    [16, 4, 5, 0, 4, 1, 0, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_62) = [
    ((218696706, 218696706), [2, 0]),
    ((268699911, 201788676), [3, 1]),
    ((285476871, 201788676), [2, 1]),
    ((218565636, 268699911), [2, 1]),
    ((268699911, 218565636), [2, 1]),
    ((201788676, 201788676), [7, 3]),
    ((218696706, 201788676), [6, 1]),
    ((269027586, 218696706), [2, 0]),
    ((269027586, 201788676), [3, 1]),
    ((218565636, 218565636), [6, 3]),
    ((218696706, 218565636), [6, 1]),
    ((268699911, 268699911), [3, 6]),
    ((218696706, 268699911), [6, 1]),
    ((269027586, 268699911), [3, 1]),
    ((268699911, 268699911), [6, 6]),
    ((218565636, 201788676), [10, 3]),
    ((268896516, 201788676), [7, 3]),
    ((269027586, 218565636), [6, 1]),
    ((268896516, 218565636), [6, 3]),
    ((268896516, 218696706), [6, 1]),
    ((268896516, 268896516), [3, 3]),
    ((269027586, 268896516), [3, 1]),
    ((285476871, 285476871), [2, 6]),
    ((218696706, 285476871), [6, 1]),
    ((302253831, 285476871), [1, 6]),
    ((285673476, 218696706), [6, 1]),
    ((285673476, 218565636), [6, 3]),
    ((285739011, 285739011), [2, 1]),
    ((285739011, 285673476), [2, 2]),
    ((285673476, 285673476), [2, 3]),
    ((302450436, 285673476), [1, 3]),
    ((302253831, 285476871), [2, 6]),
    ((302253831, 302188296), [1, 6]),
    ((302253831, 302253831), [1, 6]),
    ((302319366, 302188296), [1, 6]),
    ((302319366, 302253831), [1, 5]),
    ((302450436, 302384901), [1, 3]),
    ((302319366, 302253831), [1, 6]),
    ((302319366, 302319366), [1, 5]),
    ((302384901, 302319366), [1, 5]),
    ((302319366, 302319366), [1, 6]),
    ((302384901, 302384901), [1, 4]),
    ((302450436, 302384901), [1, 4]),
    ((302450436, 285673476), [2, 3]),
    ((302384901, 302384901), [1, 5]),
    ((318965256, 302253831), [1, 6]),
    ((319030791, 302188296), [1, 6]),
    ((302450436, 302450436), [1, 3]),
    ((319030791, 318965256), [0, 6]),
    ((302253831, 318965256), [1, 6]),
    ((302450436, 319161861), [1, 4]),
    ((319030791, 285476871), [2, 6]),
    ((319030791, 268699911), [3, 6]),
    ((269027586, 268699911), [6, 1]),
    ((335807751, 285476871), [1, 6]),
    ((319030791, 302253831), [1, 6]),
    ((302253831, 302253831), [2, 6]),
    ((319096326, 302188296), [1, 6]),
    ((319096326, 302253831), [1, 5]),
    ((319030791, 319030791), [0, 6]),
    ((269027586, 319030791), [3, 1]),
    ((302319366, 318965256), [1, 6]),
    ((319030791, 302319366), [1, 5]),
    ((319096326, 318965256), [0, 6]),
    ((302319366, 319030791), [1, 5]),
    ((319096326, 302253831), [1, 6]),
    ((319096326, 319030791), [0, 5]),
    ((319030791, 302319366), [1, 6]),
    ((319161861, 302450436), [1, 3]),
    ((319096326, 319096326), [0, 5]),
    ((302319366, 319030791), [1, 6]),
    ((319096326, 302319366), [1, 5]),
    ((319096326, 319030791), [0, 6]),
    ((319161861, 302319366), [1, 5]),
    ((319096326, 302319366), [1, 6]),
    ((319161861, 302384901), [1, 4]),
    ((319096326, 302384901), [1, 5]),
    ((268896516, 268896516), [6, 3]),
    ((319161861, 319096326), [0, 5]),
    ((302384901, 319096326), [1, 5]),
    ((319096326, 319096326), [0, 6]),
    ((319161861, 319161861), [0, 4]),
    ((302450436, 319161861), [1, 3]),
    ((319161861, 302384901), [1, 5]),
    ((269027586, 268896516), [6, 1]),
    ((319161861, 302450436), [1, 4]),
    ((302450436, 302450436), [2, 3]),
    ((319161861, 319161861), [1, 5]),
    ((319096326, 319096326), [1, 5]),
    ((335873286, 302253831), [1, 6]),
    ((335807751, 302253831), [1, 6]),
    ((335807751, 285476871), [2, 6]),
    ((319161861, 319161861), [0, 5]),
    ((335807751, 319030791), [0, 6]),
    ((319030791, 319030791), [1, 6]),
    ((319096326, 319030791), [1, 6]),
    ((335807751, 302319366), [1, 6]),
    ((335873286, 302319366), [1, 5]),
    ((335873286, 319030791), [0, 6]),
    ((335873286, 302319366), [1, 6]),
    ((335873286, 319096326), [0, 5]),
    ((335807751, 319096326), [0, 6]),
    ((319096326, 335807751), [0, 6]),
    ((335873286, 302384901), [1, 5]),
    ((319161861, 319161861), [1, 4]),
    ((319161861, 319096326), [1, 5]),
    ((319096326, 319096326), [1, 6]),
    ((335873286, 319096326), [0, 6]),
    ((319161861, 335873286), [0, 5]),
    ((335873286, 319161861), [0, 5]),
    ((335873286, 319096326), [1, 6]),
    ((335807751, 335807751), [0, 6]),
    ((335807751, 319030791), [1, 6]),
    ((352584711, 302253831), [1, 6]),
    ((352584711, 319030791), [0, 6]),
    ((335873286, 319030791), [1, 6]),
    ((352584711, 302319366), [1, 6]),
    ((319096326, 335807751), [1, 6]),
    ((335873286, 319096326), [1, 5]),
    ((335807751, 319096326), [1, 6]),
    ((352584711, 319096326), [0, 6]),
    ((335873286, 335873286), [0, 5]),
    ((335873286, 335807751), [0, 6]),
    ((352584711, 319096326), [1, 6]),
    ((352584711, 319030791), [1, 6]),
    ((319161861, 335873286), [1, 5]),
    ((335873286, 319161861), [1, 5]),
    ((335873286, 335873286), [0, 6]),
    ((352584711, 335807751), [0, 6]),
    ((335807751, 335807751), [1, 6]),
    ((352584711, 335873286), [0, 6]),
    ((335873286, 335873286), [1, 5]),
    ((335873286, 335807751), [1, 6]),
    ((335873286, 335873286), [1, 6]),
    ((335873286, 352584711), [0, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base4_63 : List ℕ := [21, 4, 4, 7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check4_63 :
    checkTripleGroup 2 108 level3 tree4 base4_63
      (keepRemaining 2 tree3) = true := by
  have hgroup : sharedGroup 2 level3 base4_63 = [
    [15, 3, 3, 1, 6, 1, 1, 6],
    [15, 3, 4, 1, 6, 1, 0, 6],
    [15, 4, 3, 1, 6, 0, 1, 6],
    [15, 4, 4, 1, 6, 0, 0, 6],
    [16, 4, 3, 1, 5, 0, 1, 6],
    [16, 3, 3, 1, 5, 1, 1, 6],
    [16, 3, 4, 1, 5, 1, 0, 6],
    [16, 4, 4, 1, 5, 0, 0, 6]] := by
    decide +kernel
  have hthird : thirdRows 2 (thirdsAt 2 level3 base4_63) = [
    ((218696706, 218696706), [2, 0]),
    ((268699911, 201788676), [3, 1]),
    ((285476871, 201788676), [2, 1]),
    ((218565636, 268699911), [2, 1]),
    ((268699911, 218565636), [2, 1]),
    ((201788676, 201788676), [7, 3]),
    ((218696706, 201788676), [6, 1]),
    ((269027586, 218696706), [2, 0]),
    ((269027586, 201788676), [3, 1]),
    ((218565636, 218565636), [6, 3]),
    ((218696706, 218565636), [6, 1]),
    ((268699911, 268699911), [3, 6]),
    ((218696706, 268699911), [6, 1]),
    ((269027586, 268699911), [3, 1]),
    ((268699911, 268699911), [6, 6]),
    ((218565636, 201788676), [10, 3]),
    ((268896516, 201788676), [7, 3]),
    ((269027586, 218565636), [6, 1]),
    ((268896516, 218565636), [6, 3]),
    ((268896516, 218696706), [6, 1]),
    ((268896516, 268896516), [3, 3]),
    ((269027586, 268896516), [3, 1]),
    ((285476871, 285476871), [2, 6]),
    ((218696706, 285476871), [6, 1]),
    ((302253831, 285476871), [1, 6]),
    ((285673476, 218696706), [6, 1]),
    ((285673476, 218565636), [6, 3]),
    ((285739011, 285739011), [2, 1]),
    ((285739011, 285673476), [2, 2]),
    ((285673476, 285673476), [2, 3]),
    ((302450436, 285673476), [1, 3]),
    ((302253831, 285476871), [2, 6]),
    ((302253831, 302188296), [1, 6]),
    ((302253831, 302253831), [1, 6]),
    ((302319366, 302188296), [1, 6]),
    ((302319366, 302253831), [1, 5]),
    ((302450436, 302384901), [1, 3]),
    ((302319366, 302253831), [1, 6]),
    ((302319366, 302319366), [1, 5]),
    ((302384901, 302319366), [1, 5]),
    ((302319366, 302319366), [1, 6]),
    ((302384901, 302384901), [1, 4]),
    ((302450436, 302384901), [1, 4]),
    ((302450436, 285673476), [2, 3]),
    ((302384901, 302384901), [1, 5]),
    ((318965256, 302253831), [1, 6]),
    ((319030791, 302188296), [1, 6]),
    ((302450436, 302450436), [1, 3]),
    ((319030791, 318965256), [0, 6]),
    ((302253831, 318965256), [1, 6]),
    ((302450436, 319161861), [1, 4]),
    ((319030791, 285476871), [2, 6]),
    ((319030791, 268699911), [3, 6]),
    ((269027586, 268699911), [6, 1]),
    ((335807751, 285476871), [1, 6]),
    ((319030791, 302253831), [1, 6]),
    ((302253831, 302253831), [2, 6]),
    ((319096326, 302188296), [1, 6]),
    ((319096326, 302253831), [1, 5]),
    ((319030791, 319030791), [0, 6]),
    ((269027586, 319030791), [3, 1]),
    ((302319366, 318965256), [1, 6]),
    ((319030791, 302319366), [1, 5]),
    ((319096326, 318965256), [0, 6]),
    ((302319366, 319030791), [1, 5]),
    ((319096326, 302253831), [1, 6]),
    ((319096326, 319030791), [0, 5]),
    ((319030791, 302319366), [1, 6]),
    ((319161861, 302450436), [1, 3]),
    ((319096326, 319096326), [0, 5]),
    ((302319366, 319030791), [1, 6]),
    ((319096326, 302319366), [1, 5]),
    ((319096326, 319030791), [0, 6]),
    ((319161861, 302319366), [1, 5]),
    ((319096326, 302319366), [1, 6]),
    ((319161861, 302384901), [1, 4]),
    ((319096326, 302384901), [1, 5]),
    ((268896516, 268896516), [6, 3]),
    ((319161861, 319096326), [0, 5]),
    ((302384901, 319096326), [1, 5]),
    ((319096326, 319096326), [0, 6]),
    ((319161861, 319161861), [0, 4]),
    ((302450436, 319161861), [1, 3]),
    ((319161861, 302384901), [1, 5]),
    ((269027586, 268896516), [6, 1]),
    ((319161861, 302450436), [1, 4]),
    ((302450436, 302450436), [2, 3]),
    ((319161861, 319161861), [1, 5]),
    ((319096326, 319096326), [1, 5]),
    ((335873286, 302253831), [1, 6]),
    ((335807751, 302253831), [1, 6]),
    ((335807751, 285476871), [2, 6]),
    ((319161861, 319161861), [0, 5]),
    ((335807751, 319030791), [0, 6]),
    ((319030791, 319030791), [1, 6]),
    ((319096326, 319030791), [1, 6]),
    ((335807751, 302319366), [1, 6]),
    ((335873286, 302319366), [1, 5]),
    ((335873286, 319030791), [0, 6]),
    ((335873286, 302319366), [1, 6]),
    ((335873286, 319096326), [0, 5]),
    ((335807751, 319096326), [0, 6]),
    ((319096326, 335807751), [0, 6]),
    ((335873286, 302384901), [1, 5]),
    ((319161861, 319161861), [1, 4]),
    ((319161861, 319096326), [1, 5]),
    ((319096326, 319096326), [1, 6]),
    ((335873286, 319096326), [0, 6]),
    ((319161861, 335873286), [0, 5]),
    ((335873286, 319161861), [0, 5]),
    ((335873286, 319096326), [1, 6]),
    ((335807751, 335807751), [0, 6]),
    ((335807751, 319030791), [1, 6]),
    ((352584711, 302253831), [1, 6]),
    ((352584711, 319030791), [0, 6]),
    ((335873286, 319030791), [1, 6]),
    ((352584711, 302319366), [1, 6]),
    ((319096326, 335807751), [1, 6]),
    ((335873286, 319096326), [1, 5]),
    ((335807751, 319096326), [1, 6]),
    ((352584711, 319096326), [0, 6]),
    ((335873286, 335873286), [0, 5]),
    ((335873286, 335807751), [0, 6]),
    ((352584711, 319096326), [1, 6]),
    ((352584711, 319030791), [1, 6]),
    ((319161861, 335873286), [1, 5]),
    ((335873286, 319161861), [1, 5]),
    ((335873286, 335873286), [0, 6]),
    ((352584711, 335807751), [0, 6]),
    ((335807751, 335807751), [1, 6]),
    ((352584711, 335873286), [0, 6]),
    ((335873286, 335873286), [1, 5]),
    ((335873286, 335807751), [1, 6]),
    ((335873286, 335873286), [1, 6]),
    ((335873286, 352584711), [0, 6])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def bases4 : List (List ℕ) := [
  base4_0, base4_1, base4_2, base4_3, base4_4, base4_5, base4_6, base4_7, base4_8, base4_9,
  base4_10, base4_11, base4_12, base4_13, base4_14, base4_15, base4_16, base4_17, base4_18,
  base4_19, base4_20, base4_21, base4_22, base4_23, base4_24, base4_25, base4_26, base4_27,
  base4_28, base4_29, base4_30, base4_31, base4_32, base4_33, base4_34, base4_35, base4_36,
  base4_37, base4_38, base4_39, base4_40, base4_41, base4_42, base4_43, base4_44, base4_45,
  base4_46, base4_47, base4_48, base4_49, base4_50, base4_51, base4_52, base4_53, base4_54,
  base4_55, base4_56, base4_57, base4_58, base4_59, base4_60, base4_61, base4_62, base4_63]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem covers4 :
    (level3.map (dropAxis 2 2)).all bases4.contains = true := by
  decide +kernel

private theorem check4 :
    bases4.all (fun base => checkTripleGroup 2 108 level3 tree4 base
      (keepRemaining 2 tree3)) = true := by
  simp only [bases4, List.all_cons, List.all_nil, Bool.and_self,
    check4_0, check4_1, check4_2, check4_3, check4_4, check4_5, check4_6, check4_7, check4_8,
    check4_9, check4_10, check4_11, check4_12, check4_13, check4_14, check4_15, check4_16,
    check4_17, check4_18, check4_19, check4_20, check4_21, check4_22, check4_23, check4_24,
    check4_25, check4_26, check4_27, check4_28, check4_29, check4_30, check4_31, check4_32,
    check4_33, check4_34, check4_35, check4_36, check4_37, check4_38, check4_39, check4_40,
    check4_41, check4_42, check4_43, check4_44, check4_45, check4_46, check4_47, check4_48,
    check4_49, check4_50, check4_51, check4_52, check4_53, check4_54, check4_55, check4_56,
    check4_57, check4_58, check4_59, check4_60, check4_61, check4_62, check4_63]

private def base5_0 : List ℕ := [0, 6, 6, 6, 6, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_0 :
    checkTripleGroup 3 108 level4 tree5 base5_0
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_0 = [
    [0, 1, 1, 5, 1, 5, 5, 0, 0, 5, 5, 1, 5, 1, 1, 0],
    [0, 5, 5, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_0) = [
    ((73753062527075841, 361983421431809541), [1, 5, 5, 1]),
    ((73753062527075841, 73753062527075841), [4, 1, 1, 0]),
    ((73753062527075841, 1695472800892416), [5, 1, 1, 0]),
    ((1695472800892416, 73753062527075841), [5, 1, 1, 0]),
    ((361983421431809541, 1695472800892416), [1, 5, 5, 0]),
    ((1695472800892416, 361983421431809541), [1, 5, 5, 0]),
    ((73753062527075841, 434041011157992966), [0, 5, 5, 1]),
    ((434041011157992966, 73753062527075841), [0, 5, 5, 1]),
    ((361983421431809541, 73753062527075841), [1, 5, 5, 1]),
    ((361983421431809541, 361983421431809541), [0, 1, 1, 4]),
    ((434041011157992966, 361983421431809541), [0, 1, 1, 5]),
    ((361983421431809541, 434041011157992966), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_1 : List ℕ := [0, 10, 10, 2, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_1 :
    checkTripleGroup 3 108 level4 tree5 base5_1
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_1 = [
    [0, 5, 5, 1, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_1) = [
    ((361983421498918401, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [0, 5, 5, 1]),
    ((2825753641222656, 361983421498918401), [5, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [1, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [4, 1, 1, 0]),
    ((578156203562370561, 361983421498918401), [1, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [4, 5, 5, 1]),
    ((578156203562370561, 361983421498918401), [1, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [5, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [4, 1, 1, 0]),
    ((434041015520069121, 434041015520069121), [3, 1, 1, 0]),
    ((506098609541219841, 434041015520069121), [2, 1, 1, 0]),
    ((578156203562370561, 434041015520069121), [1, 1, 1, 0]),
    ((650213797583521281, 434041015520069121), [0, 1, 1, 0]),
    ((578156203562370561, 506098609541219841), [0, 1, 1, 0]),
    ((506098609541219841, 506098609541219841), [1, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [5, 5, 5, 1]),
    ((434041015520069121, 361983421498918401), [4, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [1, 5, 5, 1]),
    ((434041015520069121, 434041015520069121), [3, 5, 5, 1]),
    ((506098609541219841, 434041015520069121), [2, 5, 5, 1]),
    ((578156203562370561, 434041015520069121), [1, 5, 5, 1]),
    ((650213797583521281, 434041015520069121), [0, 5, 5, 1]),
    ((506098609541219841, 506098609541219841), [1, 5, 5, 1]),
    ((578156203562370561, 506098609541219841), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_2 : List ℕ := [1, 5, 6, 6, 6, 6, 5, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_2 :
    checkTripleGroup 3 108 level4 tree5 base5_2
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_2 = [
    [0, 0, 1, 5, 1, 5, 5, 1, 1, 5, 5, 1, 5, 1, 0, 0],
    [0, 1, 1, 5, 1, 5, 4, 1, 1, 4, 5, 1, 5, 1, 1, 0],
    [1, 4, 5, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 4, 1],
    [1, 5, 5, 1, 5, 1, 0, 0, 0, 0, 1, 5, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_2) = [
    ((73753062527075841, 361983421431809541), [1, 5, 5, 1]),
    ((73753062527075841, 73753062527075841), [4, 1, 1, 0]),
    ((73753062527075841, 1695472800892416), [5, 1, 1, 0]),
    ((1695472800892416, 73753062527075841), [5, 1, 1, 0]),
    ((361983421431809541, 1695472800892416), [1, 5, 5, 0]),
    ((1695472800892416, 361983421431809541), [1, 5, 5, 0]),
    ((73753062527075841, 434041011157992966), [0, 5, 5, 1]),
    ((434041011157992966, 73753062527075841), [0, 5, 5, 1]),
    ((361983421431809541, 73753062527075841), [1, 5, 5, 1]),
    ((361983421431809541, 361983421431809541), [0, 1, 1, 4]),
    ((434041011157992966, 361983421431809541), [0, 1, 1, 5]),
    ((361983421431809541, 434041011157992966), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_3 : List ℕ := [1, 5, 6, 6, 6, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_3 :
    checkTripleGroup 3 108 level4 tree5 base5_3
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_3 = [
    [0, 1, 1, 5, 1, 5, 5, 0, 1, 4, 5, 1, 5, 1, 1, 0],
    [1, 4, 5, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_3) = [
    ((73753062527075841, 361983421431809541), [1, 5, 5, 1]),
    ((73753062527075841, 73753062527075841), [4, 1, 1, 0]),
    ((73753062527075841, 1695472800892416), [5, 1, 1, 0]),
    ((1695472800892416, 73753062527075841), [5, 1, 1, 0]),
    ((361983421431809541, 1695472800892416), [1, 5, 5, 0]),
    ((1695472800892416, 361983421431809541), [1, 5, 5, 0]),
    ((73753062527075841, 434041011157992966), [0, 5, 5, 1]),
    ((434041011157992966, 73753062527075841), [0, 5, 5, 1]),
    ((361983421431809541, 73753062527075841), [1, 5, 5, 1]),
    ((361983421431809541, 361983421431809541), [0, 1, 1, 4]),
    ((434041011157992966, 361983421431809541), [0, 1, 1, 5]),
    ((361983421431809541, 434041011157992966), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_4 : List ℕ := [1, 6, 5, 6, 6, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_4 :
    checkTripleGroup 3 108 level4 tree5 base5_4
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_4 = [
    [0, 1, 0, 5, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [0, 1, 1, 5, 1, 4, 5, 1, 1, 5, 4, 1, 5, 1, 1, 0],
    [1, 5, 4, 1, 5, 1, 1, 0, 0, 1, 1, 5, 1, 4, 5, 1],
    [1, 5, 5, 1, 5, 0, 1, 0, 0, 1, 0, 5, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_4) = [
    ((73471591862109441, 73471591862109441), [5, 1, 0, 0]),
    ((73751967327127041, 73751967327127041), [5, 0, 1, 0]),
    ((73471591862109441, 73751967327127041), [5, 1, 1, 0]),
    ((73751967327127041, 73471591862109441), [5, 1, 1, 0]),
    ((433759540493026566, 73471591862109441), [1, 5, 4, 1]),
    ((73471591862109441, 433759540493026566), [1, 5, 4, 1]),
    ((73751967327127041, 434039915958044166), [1, 4, 5, 1]),
    ((434039915958044166, 73751967327127041), [1, 4, 5, 1]),
    ((433759540493026566, 73751967327127041), [1, 5, 5, 1]),
    ((434039915958044166, 73471591862109441), [1, 5, 5, 1]),
    ((73751967327127041, 433759540493026566), [1, 5, 5, 1]),
    ((73471591862109441, 434039915958044166), [1, 5, 5, 1]),
    ((433759540493026566, 433759540493026566), [0, 1, 0, 5]),
    ((434039915958044166, 434039915958044166), [0, 0, 1, 5]),
    ((433759540493026566, 434039915958044166), [0, 1, 1, 5]),
    ((434039915958044166, 433759540493026566), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_5 : List ℕ := [1, 6, 6, 5, 5, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_5 :
    checkTripleGroup 3 108 level4 tree5 base5_5
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_5 = [
    [1, 5, 5, 1, 4, 1, 1, 0, 0, 1, 1, 4, 1, 5, 5, 1],
    [0, 1, 1, 4, 1, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0],
    [0, 1, 1, 5, 0, 5, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 0, 1, 1, 5, 0, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_5) = [
    ((73471591862109441, 73471591862109441), [5, 1, 0, 0]),
    ((73751967327127041, 73751967327127041), [5, 0, 1, 0]),
    ((73471591862109441, 73751967327127041), [5, 1, 1, 0]),
    ((73751967327127041, 73471591862109441), [5, 1, 1, 0]),
    ((433759540493026566, 73471591862109441), [1, 5, 4, 1]),
    ((73471591862109441, 433759540493026566), [1, 5, 4, 1]),
    ((73751967327127041, 434039915958044166), [1, 4, 5, 1]),
    ((434039915958044166, 73751967327127041), [1, 4, 5, 1]),
    ((433759540493026566, 73751967327127041), [1, 5, 5, 1]),
    ((434039915958044166, 73471591862109441), [1, 5, 5, 1]),
    ((73751967327127041, 433759540493026566), [1, 5, 5, 1]),
    ((73471591862109441, 434039915958044166), [1, 5, 5, 1]),
    ((433759540493026566, 433759540493026566), [0, 1, 0, 5]),
    ((434039915958044166, 434039915958044166), [0, 0, 1, 5]),
    ((433759540493026566, 434039915958044166), [0, 1, 1, 5]),
    ((434039915958044166, 433759540493026566), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_6 : List ℕ := [1, 6, 6, 5, 6, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_6 :
    checkTripleGroup 3 108 level4 tree5 base5_6
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_6 = [
    [0, 1, 1, 4, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [0, 1, 1, 5, 1, 4, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 0, 1, 1, 5, 1, 4, 5, 1],
    [1, 5, 5, 1, 5, 0, 1, 0, 0, 1, 1, 4, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_6) = [
    ((73471591862109441, 73471591862109441), [5, 1, 0, 0]),
    ((73751967327127041, 73751967327127041), [5, 0, 1, 0]),
    ((73471591862109441, 73751967327127041), [5, 1, 1, 0]),
    ((73751967327127041, 73471591862109441), [5, 1, 1, 0]),
    ((433759540493026566, 73471591862109441), [1, 5, 4, 1]),
    ((73471591862109441, 433759540493026566), [1, 5, 4, 1]),
    ((73751967327127041, 434039915958044166), [1, 4, 5, 1]),
    ((434039915958044166, 73751967327127041), [1, 4, 5, 1]),
    ((433759540493026566, 73751967327127041), [1, 5, 5, 1]),
    ((434039915958044166, 73471591862109441), [1, 5, 5, 1]),
    ((73751967327127041, 433759540493026566), [1, 5, 5, 1]),
    ((73471591862109441, 434039915958044166), [1, 5, 5, 1]),
    ((433759540493026566, 433759540493026566), [0, 1, 0, 5]),
    ((434039915958044166, 434039915958044166), [0, 0, 1, 5]),
    ((433759540493026566, 434039915958044166), [0, 1, 1, 5]),
    ((434039915958044166, 433759540493026566), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_7 : List ℕ := [1, 6, 6, 5, 6, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_7 :
    checkTripleGroup 3 108 level4 tree5 base5_7
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_7 = [
    [0, 1, 1, 5, 1, 5, 5, 0, 1, 5, 5, 0, 5, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 0, 1, 1, 5, 1, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_7) = [
    ((73753062543787521, 73753062543787521), [5, 0, 1, 0]),
    ((73753062543787521, 73471591862109696), [5, 1, 1, 0]),
    ((73471591862109696, 73753062543787521), [5, 1, 1, 0]),
    ((73471591862109696, 433759540493026821), [1, 5, 5, 0]),
    ((433759540493026821, 73471591862109696), [1, 5, 5, 0]),
    ((434041011174704646, 73753062543787521), [1, 4, 5, 1]),
    ((73753062543787521, 434041011174704646), [1, 4, 5, 1]),
    ((433759540493026821, 73753062543787521), [1, 5, 5, 1]),
    ((73753062543787521, 433759540493026821), [1, 5, 5, 1]),
    ((433759540493026821, 433759540493026821), [0, 1, 1, 4]),
    ((434041011174704646, 433759540493026821), [0, 1, 1, 5]),
    ((433759540493026821, 434041011174704646), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_8 : List ℕ := [1, 9, 10, 2, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_8 :
    checkTripleGroup 3 108 level4 tree5 base5_8
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_8 = [
    [0, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0],
    [1, 4, 5, 1, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 0, 4, 5, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_8) = [
    ((361983421498918401, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [0, 5, 5, 1]),
    ((2825753641222656, 361983421498918401), [5, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [1, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [4, 1, 1, 0]),
    ((578156203562370561, 361983421498918401), [1, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [4, 5, 5, 1]),
    ((578156203562370561, 361983421498918401), [1, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [5, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [4, 1, 1, 0]),
    ((434041015520069121, 434041015520069121), [3, 1, 1, 0]),
    ((506098609541219841, 434041015520069121), [2, 1, 1, 0]),
    ((578156203562370561, 434041015520069121), [1, 1, 1, 0]),
    ((650213797583521281, 434041015520069121), [0, 1, 1, 0]),
    ((578156203562370561, 506098609541219841), [0, 1, 1, 0]),
    ((506098609541219841, 506098609541219841), [1, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [5, 5, 5, 1]),
    ((434041015520069121, 361983421498918401), [4, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [1, 5, 5, 1]),
    ((434041015520069121, 434041015520069121), [3, 5, 5, 1]),
    ((506098609541219841, 434041015520069121), [2, 5, 5, 1]),
    ((578156203562370561, 434041015520069121), [1, 5, 5, 1]),
    ((650213797583521281, 434041015520069121), [0, 5, 5, 1]),
    ((506098609541219841, 506098609541219841), [1, 5, 5, 1]),
    ((578156203562370561, 506098609541219841), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_9 : List ℕ := [1, 10, 10, 1, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_9 :
    checkTripleGroup 3 108 level4 tree5 base5_9
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_9 = [
    [0, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 0, 5, 5, 0, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_9) = [
    ((361983421515630081, 433759540560135681), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 0, 1, 0]),
    ((74601872702439936, 361983421515630081), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [0, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [1, 0, 1, 0]),
    ((361983421515630081, 433759540560135681), [1, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 0, 1, 0]),
    ((74601872702439936, 433759540560135681), [5, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [0, 5, 5, 1]),
    ((434041015536780801, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [1, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [1, 4, 5, 1]),
    ((361983421515630081, 433759540560135681), [1, 5, 5, 1]),
    ((74601872702439936, 434041015536780801), [5, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [5, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 5, 5, 1]),
    ((361983421515630081, 361983421515630081), [5, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [4, 1, 1, 0]),
    ((649932322623587841, 433759540560135681), [1, 1, 1, 0]),
    ((721989916644738561, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [5, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [5, 0, 1, 0]),
    ((721989916644738561, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [4, 1, 1, 0]),
    ((650213797600232961, 433759540560135681), [1, 1, 1, 0]),
    ((650213797600232961, 434041015536780801), [1, 0, 1, 0]),
    ((434041015536780801, 434041015536780801), [4, 0, 1, 0]),
    ((649932322623587841, 434041015536780801), [1, 1, 1, 0]),
    ((721989916644738561, 434041015536780801), [0, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [4, 5, 5, 1]),
    ((649932322623587841, 433759540560135681), [1, 5, 5, 1]),
    ((721989916644738561, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [5, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [5, 4, 5, 1]),
    ((434041015536780801, 433759540560135681), [4, 5, 5, 1]),
    ((361983421515630081, 433759540560135681), [5, 5, 5, 1]),
    ((721989916644738561, 361983421515630081), [1, 5, 5, 1]),
    ((650213797600232961, 433759540560135681), [1, 5, 5, 1]),
    ((434041015536780801, 434041015536780801), [4, 4, 5, 1]),
    ((721989916644738561, 434041015536780801), [0, 5, 5, 1]),
    ((650213797600232961, 434041015536780801), [1, 4, 5, 1]),
    ((649932322623587841, 434041015536780801), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_10 : List ℕ := [2, 8, 10, 2, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_10 :
    checkTripleGroup 3 108 level4 tree5 base5_10
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_10 = [
    [1, 4, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 3, 5, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_10) = [
    ((361983421498918401, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [0, 5, 5, 1]),
    ((2825753641222656, 361983421498918401), [5, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [1, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [4, 1, 1, 0]),
    ((578156203562370561, 361983421498918401), [1, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [4, 5, 5, 1]),
    ((578156203562370561, 361983421498918401), [1, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [5, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [4, 1, 1, 0]),
    ((434041015520069121, 434041015520069121), [3, 1, 1, 0]),
    ((506098609541219841, 434041015520069121), [2, 1, 1, 0]),
    ((578156203562370561, 434041015520069121), [1, 1, 1, 0]),
    ((650213797583521281, 434041015520069121), [0, 1, 1, 0]),
    ((578156203562370561, 506098609541219841), [0, 1, 1, 0]),
    ((506098609541219841, 506098609541219841), [1, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [5, 5, 5, 1]),
    ((434041015520069121, 361983421498918401), [4, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [1, 5, 5, 1]),
    ((434041015520069121, 434041015520069121), [3, 5, 5, 1]),
    ((506098609541219841, 434041015520069121), [2, 5, 5, 1]),
    ((578156203562370561, 434041015520069121), [1, 5, 5, 1]),
    ((650213797583521281, 434041015520069121), [0, 5, 5, 1]),
    ((506098609541219841, 506098609541219841), [1, 5, 5, 1]),
    ((578156203562370561, 506098609541219841), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_11 : List ℕ := [2, 9, 9, 2, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_11 :
    checkTripleGroup 3 108 level4 tree5 base5_11
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_11 = [
    [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 4, 1, 5, 1, 1, 0],
    [1, 5, 4, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 4, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_11) = [
    ((361983421515630081, 433759540560135681), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 0, 1, 0]),
    ((74601872702439936, 361983421515630081), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [0, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [1, 0, 1, 0]),
    ((361983421515630081, 433759540560135681), [1, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 0, 1, 0]),
    ((74601872702439936, 433759540560135681), [5, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [0, 5, 5, 1]),
    ((434041015536780801, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [1, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [1, 4, 5, 1]),
    ((361983421515630081, 433759540560135681), [1, 5, 5, 1]),
    ((74601872702439936, 434041015536780801), [5, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [5, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 5, 5, 1]),
    ((361983421515630081, 361983421515630081), [5, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [4, 1, 1, 0]),
    ((649932322623587841, 433759540560135681), [1, 1, 1, 0]),
    ((721989916644738561, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [5, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [5, 0, 1, 0]),
    ((721989916644738561, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [4, 1, 1, 0]),
    ((650213797600232961, 433759540560135681), [1, 1, 1, 0]),
    ((650213797600232961, 434041015536780801), [1, 0, 1, 0]),
    ((434041015536780801, 434041015536780801), [4, 0, 1, 0]),
    ((649932322623587841, 434041015536780801), [1, 1, 1, 0]),
    ((721989916644738561, 434041015536780801), [0, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [4, 5, 5, 1]),
    ((649932322623587841, 433759540560135681), [1, 5, 5, 1]),
    ((721989916644738561, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [5, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [5, 4, 5, 1]),
    ((434041015536780801, 433759540560135681), [4, 5, 5, 1]),
    ((361983421515630081, 433759540560135681), [5, 5, 5, 1]),
    ((721989916644738561, 361983421515630081), [1, 5, 5, 1]),
    ((650213797600232961, 433759540560135681), [1, 5, 5, 1]),
    ((434041015536780801, 434041015536780801), [4, 4, 5, 1]),
    ((721989916644738561, 434041015536780801), [0, 5, 5, 1]),
    ((650213797600232961, 434041015536780801), [1, 4, 5, 1]),
    ((649932322623587841, 434041015536780801), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_12 : List ℕ := [2, 9, 10, 1, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_12 :
    checkTripleGroup 3 108 level4 tree5 base5_12
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_12 = [
    [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 0, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_12) = [
    ((361983421515630081, 433759540560135681), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 0, 1, 0]),
    ((74601872702439936, 361983421515630081), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [0, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [1, 0, 1, 0]),
    ((361983421515630081, 433759540560135681), [1, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 0, 1, 0]),
    ((74601872702439936, 433759540560135681), [5, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [0, 5, 5, 1]),
    ((434041015536780801, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [1, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [1, 4, 5, 1]),
    ((361983421515630081, 433759540560135681), [1, 5, 5, 1]),
    ((74601872702439936, 434041015536780801), [5, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [5, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 5, 5, 1]),
    ((361983421515630081, 361983421515630081), [5, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [4, 1, 1, 0]),
    ((649932322623587841, 433759540560135681), [1, 1, 1, 0]),
    ((721989916644738561, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [5, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [5, 0, 1, 0]),
    ((721989916644738561, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [4, 1, 1, 0]),
    ((650213797600232961, 433759540560135681), [1, 1, 1, 0]),
    ((650213797600232961, 434041015536780801), [1, 0, 1, 0]),
    ((434041015536780801, 434041015536780801), [4, 0, 1, 0]),
    ((649932322623587841, 434041015536780801), [1, 1, 1, 0]),
    ((721989916644738561, 434041015536780801), [0, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [4, 5, 5, 1]),
    ((649932322623587841, 433759540560135681), [1, 5, 5, 1]),
    ((721989916644738561, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [5, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [5, 4, 5, 1]),
    ((434041015536780801, 433759540560135681), [4, 5, 5, 1]),
    ((361983421515630081, 433759540560135681), [5, 5, 5, 1]),
    ((721989916644738561, 361983421515630081), [1, 5, 5, 1]),
    ((650213797600232961, 433759540560135681), [1, 5, 5, 1]),
    ((434041015536780801, 434041015536780801), [4, 4, 5, 1]),
    ((721989916644738561, 434041015536780801), [0, 5, 5, 1]),
    ((650213797600232961, 434041015536780801), [1, 4, 5, 1]),
    ((649932322623587841, 434041015536780801), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_13 : List ℕ := [2, 9, 10, 2, 10, 2, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_13 :
    checkTripleGroup 3 108 level4 tree5 base5_13
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_13 = [
    [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 5, 1, 5, 1, 0, 0],
    [1, 5, 5, 1, 5, 1, 0, 0, 1, 4, 5, 1, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 0, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_13) = [
    ((74883343384183296, 361983421515695616), [5, 1, 1, 0]),
    ((361983421515695616, 361983421515695616), [1, 5, 5, 0]),
    ((434041011241879041, 361983421515695616), [1, 1, 1, 0]),
    ((361983421515695616, 434041011241879041), [1, 1, 1, 0]),
    ((434041015536846336, 434041011241879041), [0, 1, 1, 0]),
    ((74883343384183296, 434041011241879041), [5, 1, 1, 0]),
    ((146940937405334016, 434041011241879041), [4, 1, 1, 0]),
    ((434041011241879041, 434041011241879041), [0, 5, 5, 1]),
    ((146940937405334016, 361983421515695616), [5, 1, 1, 0]),
    ((434041015536846336, 361983421515695616), [1, 5, 5, 0]),
    ((74883343384183296, 434041015536846336), [5, 1, 1, 0]),
    ((146940937405334016, 434041015536846336), [4, 1, 1, 0]),
    ((434041015536846336, 434041015536846336), [0, 5, 5, 0]),
    ((650213793305331201, 361983421515695616), [1, 1, 1, 0]),
    ((361983421515695616, 361983421515695616), [5, 5, 5, 0]),
    ((650213797600298496, 361983421515695616), [1, 5, 5, 0]),
    ((434041011241879041, 361983421515695616), [5, 1, 1, 0]),
    ((722271387326481921, 361983421515695616), [1, 1, 1, 0]),
    ((650213797600298496, 434041011241879041), [1, 1, 1, 0]),
    ((361983421515695616, 434041011241879041), [5, 1, 1, 0]),
    ((434041015536846336, 434041011241879041), [4, 1, 1, 0]),
    ((722271391621449216, 434041011241879041), [0, 1, 1, 0]),
    ((650213793305331201, 434041015536846336), [1, 1, 1, 0]),
    ((722271387326481921, 434041015536846336), [0, 1, 1, 0]),
    ((434041015536846336, 361983421515695616), [5, 5, 5, 0]),
    ((650213793305331201, 434041011241879041), [1, 5, 5, 1]),
    ((434041011241879041, 434041011241879041), [4, 5, 5, 1]),
    ((722271387326481921, 434041011241879041), [0, 5, 5, 1]),
    ((722271391621449216, 361983421515695616), [1, 5, 5, 0]),
    ((434041015536846336, 434041015536846336), [4, 5, 5, 0]),
    ((650213797600298496, 434041015536846336), [1, 5, 5, 0]),
    ((722271391621449216, 434041015536846336), [0, 5, 5, 0])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_14 : List ℕ := [2, 10, 9, 2, 10, 1, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_14 :
    checkTripleGroup 3 108 level4 tree5 base5_14
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_14 = [
    [1, 5, 4, 1, 5, 1, 1, 0, 1, 5, 5, 1, 5, 0, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 4, 1, 5, 0, 1, 0],
    [1, 5, 5, 1, 5, 0, 1, 0, 1, 5, 4, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_14) = [
    ((433759540576912641, 433759540576912641), [1, 1, 0, 0]),
    ((434039916041930241, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [1, 1, 0, 0]),
    ((434041015553557761, 434039916041930241), [1, 0, 1, 0]),
    ((146658367228740096, 433759540576912641), [5, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [1, 0, 0, 0]),
    ((146659466740367616, 433759540576912641), [5, 1, 0, 0]),
    ((433759540576912641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 434039916041930241), [1, 4, 5, 1]),
    ((146939842205385216, 434039916041930241), [5, 0, 1, 0]),
    ((146658367228740096, 434039916041930241), [5, 1, 1, 0]),
    ((146939842205385216, 434041015553557761), [5, 0, 1, 0]),
    ((146939842205385216, 433759540576912641), [5, 1, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 434039916041930241), [1, 5, 5, 1]),
    ((146659466740367616, 434039916041930241), [5, 1, 1, 0]),
    ((146658367228740096, 434041015553557761), [5, 1, 1, 0]),
    ((146659466740367616, 434041015553557761), [5, 1, 0, 0]),
    ((434041015553557761, 434041015553557761), [1, 4, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 433759540576912641), [5, 1, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 1, 0, 0]),
    ((721988817149888001, 434039916041930241), [1, 1, 1, 0]),
    ((434039916041930241, 434039916041930241), [5, 0, 1, 0]),
    ((722270292126533121, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [5, 1, 1, 0]),
    ((722270292126533121, 433759540576912641), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [5, 1, 0, 0]),
    ((722271391638160641, 433759540576912641), [1, 1, 0, 0]),
    ((722271391638160641, 434039916041930241), [1, 0, 1, 0]),
    ((434041015553557761, 434039916041930241), [5, 0, 1, 0]),
    ((433759540576912641, 434039916041930241), [5, 1, 1, 0]),
    ((721989916661515521, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [5, 0, 0, 0]),
    ((721989916661515521, 434041015553557761), [1, 1, 0, 0]),
    ((721988817149888001, 434041015553557761), [1, 1, 1, 0]),
    ((722270292126533121, 434041015553557761), [1, 0, 1, 0]),
    ((722271391638160641, 434041015553557761), [1, 0, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 433759540576912641), [5, 5, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 5, 5, 1]),
    ((722270292126533121, 434039916041930241), [1, 4, 5, 1]),
    ((721988817149888001, 434039916041930241), [1, 5, 5, 1]),
    ((434039916041930241, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 433759540576912641), [5, 5, 5, 1]),
    ((434041015553557761, 433759540576912641), [5, 5, 4, 1]),
    ((722270292126533121, 433759540576912641), [1, 5, 5, 1]),
    ((721989916661515521, 434039916041930241), [1, 5, 5, 1]),
    ((433759540576912641, 434039916041930241), [5, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 434041015553557761), [5, 4, 4, 1]),
    ((721988817149888001, 434041015553557761), [1, 5, 5, 1]),
    ((722270292126533121, 434041015553557761), [1, 4, 5, 1]),
    ((721989916661515521, 434041015553557761), [1, 5, 4, 1]),
    ((722271391638160641, 434041015553557761), [1, 4, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_15 : List ℕ := [2, 10, 10, 0, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_15 :
    checkTripleGroup 3 108 level4 tree5 base5_15
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_15 = [
    [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_15) = [
    ((433759540576847361, 433759540576847361), [1, 0, 1, 0]),
    ((433759540576847361, 433759540576847361), [1, 1, 1, 0]),
    ((434041015553492481, 433759540576847361), [1, 0, 1, 0]),
    ((146377991763657216, 433759540576847361), [5, 1, 1, 0]),
    ((433759540576847361, 433759540576847361), [1, 4, 5, 1]),
    ((433759540576847361, 433759540576847361), [1, 5, 5, 1]),
    ((434041015553492481, 433759540576847361), [1, 4, 5, 1]),
    ((146377991763657216, 434041015553492481), [5, 1, 1, 0]),
    ((434041015553492481, 434041015553492481), [1, 3, 5, 1]),
    ((433759540576847361, 433759540576847361), [5, 0, 1, 0]),
    ((721989916661450241, 433759540576847361), [1, 0, 1, 0]),
    ((721708441684805121, 433759540576847361), [1, 1, 1, 0]),
    ((434041015553492481, 433759540576847361), [5, 0, 1, 0]),
    ((433759540576847361, 433759540576847361), [5, 1, 1, 0]),
    ((721989916661450241, 433759540576847361), [1, 1, 1, 0]),
    ((721708441684805121, 434041015553492481), [1, 1, 1, 0]),
    ((721989916661450241, 434041015553492481), [1, 0, 1, 0]),
    ((433759540576847361, 433759540576847361), [5, 4, 5, 1]),
    ((721708441684805121, 433759540576847361), [1, 5, 5, 1]),
    ((721989916661450241, 433759540576847361), [1, 4, 5, 1]),
    ((433759540576847361, 433759540576847361), [5, 5, 5, 1]),
    ((434041015553492481, 433759540576847361), [5, 4, 5, 1]),
    ((721989916661450241, 433759540576847361), [1, 5, 5, 1]),
    ((434041015553492481, 434041015553492481), [5, 3, 5, 1]),
    ((721989916661450241, 434041015553492481), [1, 4, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_16 : List ℕ := [2, 10, 10, 1, 9, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_16 :
    checkTripleGroup 3 108 level4 tree5 base5_16
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_16 = [
    [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 1, 4, 1, 1, 0],
    [1, 5, 5, 1, 4, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_16) = [
    ((433759540576912641, 433759540576912641), [1, 1, 0, 0]),
    ((434039916041930241, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [1, 1, 0, 0]),
    ((434041015553557761, 434039916041930241), [1, 0, 1, 0]),
    ((146658367228740096, 433759540576912641), [5, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [1, 0, 0, 0]),
    ((146659466740367616, 433759540576912641), [5, 1, 0, 0]),
    ((433759540576912641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 434039916041930241), [1, 4, 5, 1]),
    ((146939842205385216, 434039916041930241), [5, 0, 1, 0]),
    ((146658367228740096, 434039916041930241), [5, 1, 1, 0]),
    ((146939842205385216, 434041015553557761), [5, 0, 1, 0]),
    ((146939842205385216, 433759540576912641), [5, 1, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 434039916041930241), [1, 5, 5, 1]),
    ((146659466740367616, 434039916041930241), [5, 1, 1, 0]),
    ((146658367228740096, 434041015553557761), [5, 1, 1, 0]),
    ((146659466740367616, 434041015553557761), [5, 1, 0, 0]),
    ((434041015553557761, 434041015553557761), [1, 4, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 433759540576912641), [5, 1, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 1, 0, 0]),
    ((721988817149888001, 434039916041930241), [1, 1, 1, 0]),
    ((434039916041930241, 434039916041930241), [5, 0, 1, 0]),
    ((722270292126533121, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [5, 1, 1, 0]),
    ((722270292126533121, 433759540576912641), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [5, 1, 0, 0]),
    ((722271391638160641, 433759540576912641), [1, 1, 0, 0]),
    ((722271391638160641, 434039916041930241), [1, 0, 1, 0]),
    ((434041015553557761, 434039916041930241), [5, 0, 1, 0]),
    ((433759540576912641, 434039916041930241), [5, 1, 1, 0]),
    ((721989916661515521, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [5, 0, 0, 0]),
    ((721989916661515521, 434041015553557761), [1, 1, 0, 0]),
    ((721988817149888001, 434041015553557761), [1, 1, 1, 0]),
    ((722270292126533121, 434041015553557761), [1, 0, 1, 0]),
    ((722271391638160641, 434041015553557761), [1, 0, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 433759540576912641), [5, 5, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 5, 5, 1]),
    ((722270292126533121, 434039916041930241), [1, 4, 5, 1]),
    ((721988817149888001, 434039916041930241), [1, 5, 5, 1]),
    ((434039916041930241, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 433759540576912641), [5, 5, 5, 1]),
    ((434041015553557761, 433759540576912641), [5, 5, 4, 1]),
    ((722270292126533121, 433759540576912641), [1, 5, 5, 1]),
    ((721989916661515521, 434039916041930241), [1, 5, 5, 1]),
    ((433759540576912641, 434039916041930241), [5, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 434041015553557761), [5, 4, 4, 1]),
    ((721988817149888001, 434041015553557761), [1, 5, 5, 1]),
    ((722270292126533121, 434041015553557761), [1, 4, 5, 1]),
    ((721989916661515521, 434041015553557761), [1, 5, 4, 1]),
    ((722271391638160641, 434041015553557761), [1, 4, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_17 : List ℕ := [2, 10, 10, 1, 10, 1, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_17 :
    checkTripleGroup 3 108 level4 tree5 base5_17
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_17 = [
    [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 1, 5, 0, 1, 0],
    [1, 5, 5, 1, 5, 0, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 0, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_17) = [
    ((433759540576912641, 433759540576912641), [1, 1, 0, 0]),
    ((434039916041930241, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [1, 1, 0, 0]),
    ((434041015553557761, 434039916041930241), [1, 0, 1, 0]),
    ((146658367228740096, 433759540576912641), [5, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [1, 0, 0, 0]),
    ((146659466740367616, 433759540576912641), [5, 1, 0, 0]),
    ((433759540576912641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 434039916041930241), [1, 4, 5, 1]),
    ((146939842205385216, 434039916041930241), [5, 0, 1, 0]),
    ((146658367228740096, 434039916041930241), [5, 1, 1, 0]),
    ((146939842205385216, 434041015553557761), [5, 0, 1, 0]),
    ((146939842205385216, 433759540576912641), [5, 1, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 434039916041930241), [1, 5, 5, 1]),
    ((146659466740367616, 434039916041930241), [5, 1, 1, 0]),
    ((146658367228740096, 434041015553557761), [5, 1, 1, 0]),
    ((146659466740367616, 434041015553557761), [5, 1, 0, 0]),
    ((434041015553557761, 434041015553557761), [1, 4, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 433759540576912641), [5, 1, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 1, 0, 0]),
    ((721988817149888001, 434039916041930241), [1, 1, 1, 0]),
    ((434039916041930241, 434039916041930241), [5, 0, 1, 0]),
    ((722270292126533121, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [5, 1, 1, 0]),
    ((722270292126533121, 433759540576912641), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [5, 1, 0, 0]),
    ((722271391638160641, 433759540576912641), [1, 1, 0, 0]),
    ((722271391638160641, 434039916041930241), [1, 0, 1, 0]),
    ((434041015553557761, 434039916041930241), [5, 0, 1, 0]),
    ((433759540576912641, 434039916041930241), [5, 1, 1, 0]),
    ((721989916661515521, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [5, 0, 0, 0]),
    ((721989916661515521, 434041015553557761), [1, 1, 0, 0]),
    ((721988817149888001, 434041015553557761), [1, 1, 1, 0]),
    ((722270292126533121, 434041015553557761), [1, 0, 1, 0]),
    ((722271391638160641, 434041015553557761), [1, 0, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 433759540576912641), [5, 5, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 5, 5, 1]),
    ((722270292126533121, 434039916041930241), [1, 4, 5, 1]),
    ((721988817149888001, 434039916041930241), [1, 5, 5, 1]),
    ((434039916041930241, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 433759540576912641), [5, 5, 5, 1]),
    ((434041015553557761, 433759540576912641), [5, 5, 4, 1]),
    ((722270292126533121, 433759540576912641), [1, 5, 5, 1]),
    ((721989916661515521, 434039916041930241), [1, 5, 5, 1]),
    ((433759540576912641, 434039916041930241), [5, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 434041015553557761), [5, 4, 4, 1]),
    ((721988817149888001, 434041015553557761), [1, 5, 5, 1]),
    ((722270292126533121, 434041015553557761), [1, 4, 5, 1]),
    ((721989916661515521, 434041015553557761), [1, 5, 4, 1]),
    ((722271391638160641, 434041015553557761), [1, 4, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_18 : List ℕ := [3, 7, 10, 2, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_18 :
    checkTripleGroup 3 108 level4 tree5 base5_18
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_18 = [
    [1, 5, 5, 1, 5, 1, 1, 0, 2, 2, 5, 1, 5, 1, 1, 0],
    [2, 5, 5, 1, 5, 1, 1, 0, 1, 2, 5, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_18) = [
    ((361983421498918401, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [0, 5, 5, 1]),
    ((2825753641222656, 361983421498918401), [5, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [1, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [4, 1, 1, 0]),
    ((578156203562370561, 361983421498918401), [1, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [4, 5, 5, 1]),
    ((578156203562370561, 361983421498918401), [1, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [5, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [4, 1, 1, 0]),
    ((434041015520069121, 434041015520069121), [3, 1, 1, 0]),
    ((506098609541219841, 434041015520069121), [2, 1, 1, 0]),
    ((578156203562370561, 434041015520069121), [1, 1, 1, 0]),
    ((650213797583521281, 434041015520069121), [0, 1, 1, 0]),
    ((578156203562370561, 506098609541219841), [0, 1, 1, 0]),
    ((506098609541219841, 506098609541219841), [1, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [5, 5, 5, 1]),
    ((434041015520069121, 361983421498918401), [4, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [1, 5, 5, 1]),
    ((434041015520069121, 434041015520069121), [3, 5, 5, 1]),
    ((506098609541219841, 434041015520069121), [2, 5, 5, 1]),
    ((578156203562370561, 434041015520069121), [1, 5, 5, 1]),
    ((650213797583521281, 434041015520069121), [0, 5, 5, 1]),
    ((506098609541219841, 506098609541219841), [1, 5, 5, 1]),
    ((578156203562370561, 506098609541219841), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_19 : List ℕ := [5, 1, 6, 6, 6, 6, 1, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_19 :
    checkTripleGroup 3 108 level4 tree5 base5_19
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_19 = [
    [0, 0, 5, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 5, 0, 0],
    [1, 0, 5, 1, 5, 1, 1, 4, 4, 1, 1, 5, 1, 5, 0, 1],
    [4, 1, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 4],
    [5, 1, 1, 5, 1, 5, 0, 0, 0, 0, 5, 1, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_19) = [
    ((73753062527075841, 361983421431809541), [1, 5, 5, 1]),
    ((73753062527075841, 73753062527075841), [4, 1, 1, 0]),
    ((73753062527075841, 1695472800892416), [5, 1, 1, 0]),
    ((1695472800892416, 73753062527075841), [5, 1, 1, 0]),
    ((361983421431809541, 1695472800892416), [1, 5, 5, 0]),
    ((1695472800892416, 361983421431809541), [1, 5, 5, 0]),
    ((73753062527075841, 434041011157992966), [0, 5, 5, 1]),
    ((434041011157992966, 73753062527075841), [0, 5, 5, 1]),
    ((361983421431809541, 73753062527075841), [1, 5, 5, 1]),
    ((361983421431809541, 361983421431809541), [0, 1, 1, 4]),
    ((434041011157992966, 361983421431809541), [0, 1, 1, 5]),
    ((361983421431809541, 434041011157992966), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_20 : List ℕ := [5, 6, 1, 6, 6, 1, 6, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_20 :
    checkTripleGroup 3 108 level4 tree5 base5_20
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_20 = [
    [0, 5, 0, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 5, 0],
    [1, 5, 0, 1, 5, 1, 1, 4, 4, 1, 1, 5, 1, 0, 5, 1],
    [4, 1, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 4],
    [5, 1, 1, 5, 1, 0, 5, 0, 0, 5, 0, 1, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_20) = [
    ((432633657833160966, 432633657833160966), [0, 5, 0, 1]),
    ((360576068106977541, 360576068106977541), [1, 5, 0, 0]),
    ((361977945432065541, 361977945432065541), [1, 0, 5, 0]),
    ((360576068106977541, 432633657833160966), [1, 5, 0, 1]),
    ((432633657833160966, 360576068106977541), [1, 5, 0, 1]),
    ((434035535158248966, 434035535158248966), [0, 0, 5, 1]),
    ((434035535158248966, 361977945432065541), [1, 0, 5, 1]),
    ((361977945432065541, 434035535158248966), [1, 0, 5, 1]),
    ((361977945432065541, 360576068106977541), [5, 1, 1, 4]),
    ((360576068106977541, 361977945432065541), [5, 1, 1, 4]),
    ((434035535158248966, 432633657833160966), [4, 1, 1, 5]),
    ((432633657833160966, 361977945432065541), [5, 1, 1, 5]),
    ((432633657833160966, 434035535158248966), [4, 1, 1, 5]),
    ((434035535158248966, 360576068106977541), [5, 1, 1, 5]),
    ((361977945432065541, 432633657833160966), [5, 1, 1, 5]),
    ((360576068106977541, 434035535158248966), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_21 : List ℕ := [5, 6, 6, 1, 1, 6, 6, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_21 :
    checkTripleGroup 3 108 level4 tree5 base5_21
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_21 = [
    [0, 5, 5, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 5, 0],
    [1, 5, 5, 1, 0, 1, 1, 4, 4, 1, 1, 0, 1, 5, 5, 1],
    [4, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 4],
    [5, 1, 1, 0, 1, 5, 5, 0, 0, 5, 5, 1, 0, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_21) = [
    ((432633657833160966, 432633657833160966), [0, 5, 0, 1]),
    ((360576068106977541, 360576068106977541), [1, 5, 0, 0]),
    ((361977945432065541, 361977945432065541), [1, 0, 5, 0]),
    ((360576068106977541, 432633657833160966), [1, 5, 0, 1]),
    ((432633657833160966, 360576068106977541), [1, 5, 0, 1]),
    ((434035535158248966, 434035535158248966), [0, 0, 5, 1]),
    ((434035535158248966, 361977945432065541), [1, 0, 5, 1]),
    ((361977945432065541, 434035535158248966), [1, 0, 5, 1]),
    ((361977945432065541, 360576068106977541), [5, 1, 1, 4]),
    ((360576068106977541, 361977945432065541), [5, 1, 1, 4]),
    ((434035535158248966, 432633657833160966), [4, 1, 1, 5]),
    ((432633657833160966, 361977945432065541), [5, 1, 1, 5]),
    ((432633657833160966, 434035535158248966), [4, 1, 1, 5]),
    ((434035535158248966, 360576068106977541), [5, 1, 1, 5]),
    ((361977945432065541, 432633657833160966), [5, 1, 1, 5]),
    ((360576068106977541, 434035535158248966), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_22 : List ℕ := [5, 6, 6, 1, 5, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_22 :
    checkTripleGroup 3 108 level4 tree5 base5_22
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_22 = [
    [0, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0],
    [0, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1],
    [1, 1, 1, 0, 4, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0],
    [1, 5, 5, 1, 4, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1],
    [4, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0],
    [4, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1],
    [5, 1, 1, 0, 0, 5, 5, 1, 0, 5, 5, 1, 5, 1, 1, 0],
    [5, 5, 5, 1, 0, 1, 1, 0, 0, 1, 1, 0, 5, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_22) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_23 : List ℕ := [5, 6, 6, 1, 6, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_23 :
    checkTripleGroup 3 108 level4 tree5 base5_23
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_23 = [
    [5, 1, 1, 0, 1, 4, 5, 1, 0, 5, 5, 1, 5, 1, 1, 0],
    [0, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [0, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [1, 1, 1, 0, 5, 4, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0],
    [1, 5, 5, 1, 5, 0, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1],
    [4, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [4, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1],
    [5, 5, 5, 1, 1, 0, 1, 0, 0, 1, 1, 0, 5, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_23) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_24 : List ℕ := [5, 6, 6, 1, 6, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_24 :
    checkTripleGroup 3 108 level4 tree5 base5_24
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_24 = [
    [0, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [1, 1, 1, 0, 5, 5, 5, 0, 4, 5, 5, 1, 1, 1, 1, 0],
    [4, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 0, 5, 5, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_24) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_25 : List ℕ := [6, 0, 6, 6, 6, 6, 0, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_25 :
    checkTripleGroup 3 108 level4 tree5 base5_25
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_25 = [
    [1, 0, 5, 1, 5, 1, 0, 5, 5, 0, 1, 5, 1, 5, 0, 1],
    [5, 0, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 0, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_25) = [
    ((73753062527075841, 361983421431809541), [1, 5, 5, 1]),
    ((73753062527075841, 73753062527075841), [4, 1, 1, 0]),
    ((73753062527075841, 1695472800892416), [5, 1, 1, 0]),
    ((1695472800892416, 73753062527075841), [5, 1, 1, 0]),
    ((361983421431809541, 1695472800892416), [1, 5, 5, 0]),
    ((1695472800892416, 361983421431809541), [1, 5, 5, 0]),
    ((73753062527075841, 434041011157992966), [0, 5, 5, 1]),
    ((434041011157992966, 73753062527075841), [0, 5, 5, 1]),
    ((361983421431809541, 73753062527075841), [1, 5, 5, 1]),
    ((361983421431809541, 361983421431809541), [0, 1, 1, 4]),
    ((434041011157992966, 361983421431809541), [0, 1, 1, 5]),
    ((361983421431809541, 434041011157992966), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_26 : List ℕ := [6, 0, 6, 6, 6, 6, 1, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_26 :
    checkTripleGroup 3 108 level4 tree5 base5_26
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_26 = [
    [1, 0, 5, 1, 5, 1, 1, 4, 5, 0, 1, 5, 1, 5, 0, 1],
    [5, 0, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 4]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_26) = [
    ((73753062527075841, 361983421431809541), [1, 5, 5, 1]),
    ((73753062527075841, 73753062527075841), [4, 1, 1, 0]),
    ((73753062527075841, 1695472800892416), [5, 1, 1, 0]),
    ((1695472800892416, 73753062527075841), [5, 1, 1, 0]),
    ((361983421431809541, 1695472800892416), [1, 5, 5, 0]),
    ((1695472800892416, 361983421431809541), [1, 5, 5, 0]),
    ((73753062527075841, 434041011157992966), [0, 5, 5, 1]),
    ((434041011157992966, 73753062527075841), [0, 5, 5, 1]),
    ((361983421431809541, 73753062527075841), [1, 5, 5, 1]),
    ((361983421431809541, 361983421431809541), [0, 1, 1, 4]),
    ((434041011157992966, 361983421431809541), [0, 1, 1, 5]),
    ((361983421431809541, 434041011157992966), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_27 : List ℕ := [6, 1, 5, 6, 6, 5, 1, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_27 :
    checkTripleGroup 3 108 level4 tree5 base5_27
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_27 = [
    [1, 0, 4, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 4, 0, 1],
    [1, 0, 5, 1, 5, 0, 1, 5, 5, 1, 0, 5, 1, 5, 0, 1],
    [5, 1, 0, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 0, 1, 5],
    [5, 1, 1, 5, 1, 4, 0, 1, 1, 0, 4, 1, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_27) = [
    ((73471591862109441, 73471591862109441), [5, 1, 0, 0]),
    ((73751967327127041, 73751967327127041), [5, 0, 1, 0]),
    ((73471591862109441, 73751967327127041), [5, 1, 1, 0]),
    ((73751967327127041, 73471591862109441), [5, 1, 1, 0]),
    ((433759540493026566, 73471591862109441), [1, 5, 4, 1]),
    ((73471591862109441, 433759540493026566), [1, 5, 4, 1]),
    ((73751967327127041, 434039915958044166), [1, 4, 5, 1]),
    ((434039915958044166, 73751967327127041), [1, 4, 5, 1]),
    ((433759540493026566, 73751967327127041), [1, 5, 5, 1]),
    ((434039915958044166, 73471591862109441), [1, 5, 5, 1]),
    ((73751967327127041, 433759540493026566), [1, 5, 5, 1]),
    ((73471591862109441, 434039915958044166), [1, 5, 5, 1]),
    ((433759540493026566, 433759540493026566), [0, 1, 0, 5]),
    ((434039915958044166, 434039915958044166), [0, 0, 1, 5]),
    ((433759540493026566, 434039915958044166), [0, 1, 1, 5]),
    ((434039915958044166, 433759540493026566), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_28 : List ℕ := [6, 1, 6, 5, 5, 6, 1, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_28 :
    checkTripleGroup 3 108 level4 tree5 base5_28
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_28 = [
    [1, 0, 5, 0, 5, 1, 1, 5, 5, 1, 1, 5, 0, 5, 0, 1],
    [1, 0, 5, 1, 4, 1, 1, 5, 5, 1, 1, 4, 1, 5, 0, 1],
    [5, 1, 1, 5, 0, 5, 0, 1, 1, 0, 5, 0, 5, 1, 1, 5],
    [5, 1, 1, 4, 1, 5, 0, 1, 1, 0, 5, 1, 4, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_28) = [
    ((73471591862109441, 73471591862109441), [5, 1, 0, 0]),
    ((73751967327127041, 73751967327127041), [5, 0, 1, 0]),
    ((73471591862109441, 73751967327127041), [5, 1, 1, 0]),
    ((73751967327127041, 73471591862109441), [5, 1, 1, 0]),
    ((433759540493026566, 73471591862109441), [1, 5, 4, 1]),
    ((73471591862109441, 433759540493026566), [1, 5, 4, 1]),
    ((73751967327127041, 434039915958044166), [1, 4, 5, 1]),
    ((434039915958044166, 73751967327127041), [1, 4, 5, 1]),
    ((433759540493026566, 73751967327127041), [1, 5, 5, 1]),
    ((434039915958044166, 73471591862109441), [1, 5, 5, 1]),
    ((73751967327127041, 433759540493026566), [1, 5, 5, 1]),
    ((73471591862109441, 434039915958044166), [1, 5, 5, 1]),
    ((433759540493026566, 433759540493026566), [0, 1, 0, 5]),
    ((434039915958044166, 434039915958044166), [0, 0, 1, 5]),
    ((433759540493026566, 434039915958044166), [0, 1, 1, 5]),
    ((434039915958044166, 433759540493026566), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_29 : List ℕ := [6, 1, 6, 5, 6, 5, 1, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_29 :
    checkTripleGroup 3 108 level4 tree5 base5_29
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_29 = [
    [1, 0, 5, 0, 5, 1, 1, 5, 5, 1, 1, 5, 1, 4, 0, 1],
    [1, 0, 5, 1, 5, 0, 1, 5, 5, 1, 1, 4, 1, 5, 0, 1],
    [5, 1, 1, 4, 1, 5, 0, 1, 1, 0, 5, 1, 5, 0, 1, 5],
    [5, 1, 1, 5, 1, 4, 0, 1, 1, 0, 5, 0, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_29) = [
    ((73471591862109441, 73471591862109441), [5, 1, 0, 0]),
    ((73751967327127041, 73751967327127041), [5, 0, 1, 0]),
    ((73471591862109441, 73751967327127041), [5, 1, 1, 0]),
    ((73751967327127041, 73471591862109441), [5, 1, 1, 0]),
    ((433759540493026566, 73471591862109441), [1, 5, 4, 1]),
    ((73471591862109441, 433759540493026566), [1, 5, 4, 1]),
    ((73751967327127041, 434039915958044166), [1, 4, 5, 1]),
    ((434039915958044166, 73751967327127041), [1, 4, 5, 1]),
    ((433759540493026566, 73751967327127041), [1, 5, 5, 1]),
    ((434039915958044166, 73471591862109441), [1, 5, 5, 1]),
    ((73751967327127041, 433759540493026566), [1, 5, 5, 1]),
    ((73471591862109441, 434039915958044166), [1, 5, 5, 1]),
    ((433759540493026566, 433759540493026566), [0, 1, 0, 5]),
    ((434039915958044166, 434039915958044166), [0, 0, 1, 5]),
    ((433759540493026566, 434039915958044166), [0, 1, 1, 5]),
    ((434039915958044166, 433759540493026566), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_30 : List ℕ := [6, 1, 6, 5, 6, 6, 1, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_30 :
    checkTripleGroup 3 108 level4 tree5 base5_30
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_30 = [
    [1, 0, 5, 0, 5, 1, 1, 5, 5, 1, 1, 5, 1, 5, 0, 0],
    [1, 0, 5, 1, 5, 1, 1, 4, 5, 1, 1, 4, 1, 5, 0, 1],
    [5, 1, 1, 4, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 4],
    [5, 1, 1, 5, 1, 5, 0, 0, 1, 0, 5, 0, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_30) = [
    ((73753062543787521, 73753062543787521), [5, 0, 1, 0]),
    ((73753062543787521, 73471591862109696), [5, 1, 1, 0]),
    ((73471591862109696, 73753062543787521), [5, 1, 1, 0]),
    ((73471591862109696, 433759540493026821), [1, 5, 5, 0]),
    ((433759540493026821, 73471591862109696), [1, 5, 5, 0]),
    ((434041011174704646, 73753062543787521), [1, 4, 5, 1]),
    ((73753062543787521, 434041011174704646), [1, 4, 5, 1]),
    ((433759540493026821, 73753062543787521), [1, 5, 5, 1]),
    ((73753062543787521, 433759540493026821), [1, 5, 5, 1]),
    ((433759540493026821, 433759540493026821), [0, 1, 1, 4]),
    ((434041011174704646, 433759540493026821), [0, 1, 1, 5]),
    ((433759540493026821, 434041011174704646), [0, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_31 : List ℕ := [6, 1, 6, 6, 6, 6, 1, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_31 :
    checkTripleGroup 3 108 level4 tree5 base5_31
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_31 = [
    [1, 0, 5, 1, 5, 1, 1, 4, 5, 1, 1, 5, 1, 5, 0, 0],
    [5, 1, 1, 5, 1, 5, 0, 0, 1, 0, 5, 1, 5, 1, 1, 4],
    [5, 1, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 3]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_31) = [
    ((73753062543853056, 73753062543853056), [5, 1, 1, 0]),
    ((434041011174770181, 73753062543853056), [1, 5, 5, 0]),
    ((73753062543853056, 434041011174770181), [1, 5, 5, 0]),
    ((434041015469737476, 73753062543853056), [1, 5, 5, 0]),
    ((434041015469737476, 434041011174770181), [0, 1, 1, 4]),
    ((434041011174770181, 434041011174770181), [0, 1, 1, 5]),
    ((434041015469737476, 434041015469737476), [0, 1, 1, 3])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_32 : List ℕ := [6, 5, 1, 6, 6, 1, 5, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_32 :
    checkTripleGroup 3 108 level4 tree5 base5_32
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_32 = [
    [1, 4, 0, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 4, 1],
    [1, 5, 0, 1, 5, 1, 0, 5, 5, 0, 1, 5, 1, 0, 5, 1],
    [5, 0, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 0, 5],
    [5, 1, 1, 5, 1, 0, 4, 1, 1, 4, 0, 1, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_32) = [
    ((432633657833160966, 432633657833160966), [0, 5, 0, 1]),
    ((360576068106977541, 360576068106977541), [1, 5, 0, 0]),
    ((361977945432065541, 361977945432065541), [1, 0, 5, 0]),
    ((360576068106977541, 432633657833160966), [1, 5, 0, 1]),
    ((432633657833160966, 360576068106977541), [1, 5, 0, 1]),
    ((434035535158248966, 434035535158248966), [0, 0, 5, 1]),
    ((434035535158248966, 361977945432065541), [1, 0, 5, 1]),
    ((361977945432065541, 434035535158248966), [1, 0, 5, 1]),
    ((361977945432065541, 360576068106977541), [5, 1, 1, 4]),
    ((360576068106977541, 361977945432065541), [5, 1, 1, 4]),
    ((434035535158248966, 432633657833160966), [4, 1, 1, 5]),
    ((432633657833160966, 361977945432065541), [5, 1, 1, 5]),
    ((432633657833160966, 434035535158248966), [4, 1, 1, 5]),
    ((434035535158248966, 360576068106977541), [5, 1, 1, 5]),
    ((361977945432065541, 432633657833160966), [5, 1, 1, 5]),
    ((360576068106977541, 434035535158248966), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_33 : List ℕ := [6, 5, 1, 6, 6, 1, 6, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_33 :
    checkTripleGroup 3 108 level4 tree5 base5_33
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_33 = [
    [1, 5, 0, 1, 5, 1, 1, 4, 5, 0, 1, 5, 1, 0, 5, 1],
    [1, 4, 0, 1, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 5, 0],
    [5, 0, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 4],
    [5, 1, 1, 5, 1, 0, 5, 0, 1, 4, 0, 1, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_33) = [
    ((432633657833160966, 432633657833160966), [0, 5, 0, 1]),
    ((360576068106977541, 360576068106977541), [1, 5, 0, 0]),
    ((361977945432065541, 361977945432065541), [1, 0, 5, 0]),
    ((360576068106977541, 432633657833160966), [1, 5, 0, 1]),
    ((432633657833160966, 360576068106977541), [1, 5, 0, 1]),
    ((434035535158248966, 434035535158248966), [0, 0, 5, 1]),
    ((434035535158248966, 361977945432065541), [1, 0, 5, 1]),
    ((361977945432065541, 434035535158248966), [1, 0, 5, 1]),
    ((361977945432065541, 360576068106977541), [5, 1, 1, 4]),
    ((360576068106977541, 361977945432065541), [5, 1, 1, 4]),
    ((434035535158248966, 432633657833160966), [4, 1, 1, 5]),
    ((432633657833160966, 361977945432065541), [5, 1, 1, 5]),
    ((432633657833160966, 434035535158248966), [4, 1, 1, 5]),
    ((434035535158248966, 360576068106977541), [5, 1, 1, 5]),
    ((361977945432065541, 432633657833160966), [5, 1, 1, 5]),
    ((360576068106977541, 434035535158248966), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_34 : List ℕ := [6, 5, 6, 1, 1, 6, 5, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_34 :
    checkTripleGroup 3 108 level4 tree5 base5_34
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_34 = [
    [1, 4, 5, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 4, 1],
    [1, 5, 5, 1, 0, 1, 0, 5, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 0, 5],
    [5, 1, 1, 0, 1, 5, 4, 1, 1, 4, 5, 1, 0, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_34) = [
    ((432633657833160966, 432633657833160966), [0, 5, 0, 1]),
    ((360576068106977541, 360576068106977541), [1, 5, 0, 0]),
    ((361977945432065541, 361977945432065541), [1, 0, 5, 0]),
    ((360576068106977541, 432633657833160966), [1, 5, 0, 1]),
    ((432633657833160966, 360576068106977541), [1, 5, 0, 1]),
    ((434035535158248966, 434035535158248966), [0, 0, 5, 1]),
    ((434035535158248966, 361977945432065541), [1, 0, 5, 1]),
    ((361977945432065541, 434035535158248966), [1, 0, 5, 1]),
    ((361977945432065541, 360576068106977541), [5, 1, 1, 4]),
    ((360576068106977541, 361977945432065541), [5, 1, 1, 4]),
    ((434035535158248966, 432633657833160966), [4, 1, 1, 5]),
    ((432633657833160966, 361977945432065541), [5, 1, 1, 5]),
    ((432633657833160966, 434035535158248966), [4, 1, 1, 5]),
    ((434035535158248966, 360576068106977541), [5, 1, 1, 5]),
    ((361977945432065541, 432633657833160966), [5, 1, 1, 5]),
    ((360576068106977541, 434035535158248966), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_35 : List ℕ := [6, 5, 6, 1, 1, 6, 6, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_35 :
    checkTripleGroup 3 108 level4 tree5 base5_35
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_35 = [
    [1, 4, 5, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 5, 0],
    [1, 5, 5, 1, 0, 1, 1, 4, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 4],
    [5, 1, 1, 0, 1, 5, 5, 0, 1, 4, 5, 1, 0, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_35) = [
    ((432633657833160966, 432633657833160966), [0, 5, 0, 1]),
    ((360576068106977541, 360576068106977541), [1, 5, 0, 0]),
    ((361977945432065541, 361977945432065541), [1, 0, 5, 0]),
    ((360576068106977541, 432633657833160966), [1, 5, 0, 1]),
    ((432633657833160966, 360576068106977541), [1, 5, 0, 1]),
    ((434035535158248966, 434035535158248966), [0, 0, 5, 1]),
    ((434035535158248966, 361977945432065541), [1, 0, 5, 1]),
    ((361977945432065541, 434035535158248966), [1, 0, 5, 1]),
    ((361977945432065541, 360576068106977541), [5, 1, 1, 4]),
    ((360576068106977541, 361977945432065541), [5, 1, 1, 4]),
    ((434035535158248966, 432633657833160966), [4, 1, 1, 5]),
    ((432633657833160966, 361977945432065541), [5, 1, 1, 5]),
    ((432633657833160966, 434035535158248966), [4, 1, 1, 5]),
    ((434035535158248966, 360576068106977541), [5, 1, 1, 5]),
    ((361977945432065541, 432633657833160966), [5, 1, 1, 5]),
    ((360576068106977541, 434035535158248966), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_36 : List ℕ := [6, 5, 6, 1, 5, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_36 :
    checkTripleGroup 3 108 level4 tree5 base5_36
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_36 = [
    [1, 0, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 4, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1],
    [1, 5, 5, 1, 4, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0],
    [5, 1, 1, 0, 0, 5, 5, 1, 1, 4, 5, 1, 5, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1],
    [5, 5, 5, 1, 0, 1, 1, 0, 1, 0, 1, 0, 5, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_36) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_37 : List ℕ := [6, 5, 6, 1, 6, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_37 :
    checkTripleGroup 3 108 level4 tree5 base5_37
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_37 = [
    [1, 0, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 5, 4, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [1, 5, 5, 1, 5, 0, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 4, 5, 1, 5, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1],
    [5, 5, 5, 1, 1, 0, 1, 0, 1, 0, 1, 0, 5, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_37) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_38 : List ℕ := [6, 5, 6, 1, 6, 6, 5, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_38 :
    checkTripleGroup 3 108 level4 tree5 base5_38
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_38 = [
    [1, 0, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0],
    [1, 1, 1, 0, 5, 5, 4, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1],
    [1, 5, 5, 1, 5, 1, 0, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 0, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 1, 0, 0],
    [5, 1, 1, 0, 1, 5, 4, 1, 1, 4, 5, 1, 5, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 4, 1],
    [5, 5, 5, 1, 1, 1, 0, 0, 1, 0, 1, 0, 5, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_38) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_39 : List ℕ := [6, 5, 6, 1, 6, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_39 :
    checkTripleGroup 3 108 level4 tree5 base5_39
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_39 = [
    [1, 1, 1, 0, 5, 5, 5, 0, 5, 4, 5, 1, 1, 1, 1, 0],
    [1, 4, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 1, 4, 5, 1, 5, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_39) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_40 : List ℕ := [6, 6, 0, 6, 6, 0, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_40 :
    checkTripleGroup 3 108 level4 tree5 base5_40
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_40 = [
    [1, 5, 0, 1, 5, 0, 1, 5, 5, 1, 0, 5, 1, 0, 5, 1],
    [5, 1, 0, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 0, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_40) = [
    ((432632562633212166, 432632562633212166), [1, 4, 0, 1]),
    ((432632562633212166, 432352187168194566), [1, 5, 0, 1]),
    ((432352187168194566, 432632562633212166), [1, 5, 0, 1]),
    ((433754064493282566, 433754064493282566), [1, 0, 4, 1]),
    ((434034439958300166, 433754064493282566), [1, 0, 5, 1]),
    ((433754064493282566, 434034439958300166), [1, 0, 5, 1]),
    ((432352187168194566, 433754064493282566), [5, 1, 0, 5]),
    ((433754064493282566, 432352187168194566), [5, 1, 0, 5]),
    ((434034439958300166, 432632562633212166), [5, 0, 1, 5]),
    ((432632562633212166, 434034439958300166), [5, 0, 1, 5]),
    ((433754064493282566, 432632562633212166), [5, 1, 1, 5]),
    ((432632562633212166, 433754064493282566), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_41 : List ℕ := [6, 6, 1, 5, 5, 1, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_41 :
    checkTripleGroup 3 108 level4 tree5 base5_41
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_41 = [
    [1, 5, 0, 0, 5, 1, 1, 5, 5, 1, 1, 5, 0, 0, 5, 1],
    [1, 5, 0, 1, 4, 1, 1, 5, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 1, 1, 4, 1, 0, 5, 1, 1, 5, 0, 1, 4, 1, 1, 5],
    [5, 1, 1, 5, 0, 0, 5, 1, 1, 5, 0, 0, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_41) = [
    ((432632562633212166, 432632562633212166), [1, 4, 0, 1]),
    ((432632562633212166, 432352187168194566), [1, 5, 0, 1]),
    ((432352187168194566, 432632562633212166), [1, 5, 0, 1]),
    ((433754064493282566, 433754064493282566), [1, 0, 4, 1]),
    ((434034439958300166, 433754064493282566), [1, 0, 5, 1]),
    ((433754064493282566, 434034439958300166), [1, 0, 5, 1]),
    ((432352187168194566, 433754064493282566), [5, 1, 0, 5]),
    ((433754064493282566, 432352187168194566), [5, 1, 0, 5]),
    ((434034439958300166, 432632562633212166), [5, 0, 1, 5]),
    ((432632562633212166, 434034439958300166), [5, 0, 1, 5]),
    ((433754064493282566, 432632562633212166), [5, 1, 1, 5]),
    ((432632562633212166, 433754064493282566), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_42 : List ℕ := [6, 6, 1, 5, 6, 0, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_42 :
    checkTripleGroup 3 108 level4 tree5 base5_42
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_42 = [
    [1, 5, 0, 1, 5, 0, 1, 5, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 1, 1, 4, 1, 0, 5, 1, 1, 5, 0, 1, 5, 0, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_42) = [
    ((432632562633212166, 432632562633212166), [1, 4, 0, 1]),
    ((432632562633212166, 432352187168194566), [1, 5, 0, 1]),
    ((432352187168194566, 432632562633212166), [1, 5, 0, 1]),
    ((433754064493282566, 433754064493282566), [1, 0, 4, 1]),
    ((434034439958300166, 433754064493282566), [1, 0, 5, 1]),
    ((433754064493282566, 434034439958300166), [1, 0, 5, 1]),
    ((432352187168194566, 433754064493282566), [5, 1, 0, 5]),
    ((433754064493282566, 432352187168194566), [5, 1, 0, 5]),
    ((434034439958300166, 432632562633212166), [5, 0, 1, 5]),
    ((432632562633212166, 434034439958300166), [5, 0, 1, 5]),
    ((433754064493282566, 432632562633212166), [5, 1, 1, 5]),
    ((432632562633212166, 433754064493282566), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_43 : List ℕ := [6, 6, 1, 5, 6, 1, 6, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_43 :
    checkTripleGroup 3 108 level4 tree5 base5_43
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_43 = [
    [1, 5, 0, 0, 5, 1, 1, 5, 5, 1, 1, 5, 1, 0, 5, 0],
    [1, 5, 0, 1, 5, 1, 1, 4, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 1, 1, 4, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 4],
    [5, 1, 1, 5, 1, 0, 5, 0, 1, 5, 0, 0, 5, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_43) = [
    ((432633657849872646, 432633657849872646), [1, 4, 0, 1]),
    ((432633657849872646, 432352187168194821), [1, 5, 0, 1]),
    ((432352187168194821, 432633657849872646), [1, 5, 0, 1]),
    ((433754064493282821, 434035535174960646), [1, 0, 5, 1]),
    ((433754064493282821, 433754064493282821), [1, 0, 5, 0]),
    ((434035535174960646, 433754064493282821), [1, 0, 5, 1]),
    ((433754064493282821, 432352187168194821), [5, 1, 1, 4]),
    ((432352187168194821, 433754064493282821), [5, 1, 1, 4]),
    ((434035535174960646, 432633657849872646), [5, 0, 1, 5]),
    ((432633657849872646, 434035535174960646), [5, 0, 1, 5]),
    ((433754064493282821, 432633657849872646), [5, 1, 1, 5]),
    ((432633657849872646, 433754064493282821), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_44 : List ℕ := [6, 6, 1, 6, 6, 1, 6, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_44 :
    checkTripleGroup 3 108 level4 tree5 base5_44
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_44 = [
    [1, 5, 0, 1, 5, 1, 1, 4, 5, 1, 1, 5, 1, 0, 5, 0],
    [5, 1, 1, 5, 1, 0, 5, 0, 1, 5, 0, 1, 5, 1, 1, 4],
    [5, 1, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 3]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_44) = [
    ((432633657849938181, 432633657849938181), [1, 5, 0, 0]),
    ((432633657849938181, 432633657849938181), [1, 5, 0, 1]),
    ((432633662144905476, 432633657849938181), [1, 5, 0, 0]),
    ((434035535175026181, 434035535175026181), [1, 0, 5, 0]),
    ((434035539469993476, 434035535175026181), [1, 0, 5, 0]),
    ((434035535175026181, 434035535175026181), [1, 0, 5, 1]),
    ((434035539469993476, 432633657849938181), [5, 1, 1, 4]),
    ((434035535175026181, 432633657849938181), [5, 1, 1, 4]),
    ((432633657849938181, 434035535175026181), [5, 1, 1, 4]),
    ((434035535175026181, 432633657849938181), [5, 1, 1, 5]),
    ((432633657849938181, 434035535175026181), [5, 1, 1, 5]),
    ((434035539469993476, 432633662144905476), [5, 1, 1, 3]),
    ((432633662144905476, 434035535175026181), [5, 1, 1, 4]),
    ((432633662144905476, 434035539469993476), [5, 1, 1, 3])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_45 : List ℕ := [6, 6, 5, 1, 1, 5, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_45 :
    checkTripleGroup 3 108 level4 tree5 base5_45
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_45 = [
    [1, 5, 4, 1, 0, 1, 1, 5, 5, 1, 1, 0, 1, 4, 5, 1],
    [1, 5, 5, 1, 0, 0, 1, 5, 5, 1, 0, 0, 1, 5, 5, 1],
    [5, 1, 0, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 0, 1, 5],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 4, 1, 0, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_45) = [
    ((432632562633212166, 432632562633212166), [1, 4, 0, 1]),
    ((432632562633212166, 432352187168194566), [1, 5, 0, 1]),
    ((432352187168194566, 432632562633212166), [1, 5, 0, 1]),
    ((433754064493282566, 433754064493282566), [1, 0, 4, 1]),
    ((434034439958300166, 433754064493282566), [1, 0, 5, 1]),
    ((433754064493282566, 434034439958300166), [1, 0, 5, 1]),
    ((432352187168194566, 433754064493282566), [5, 1, 0, 5]),
    ((433754064493282566, 432352187168194566), [5, 1, 0, 5]),
    ((434034439958300166, 432632562633212166), [5, 0, 1, 5]),
    ((432632562633212166, 434034439958300166), [5, 0, 1, 5]),
    ((433754064493282566, 432632562633212166), [5, 1, 1, 5]),
    ((432632562633212166, 433754064493282566), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_46 : List ℕ := [6, 6, 5, 1, 6, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_46 :
    checkTripleGroup 3 108 level4 tree5 base5_46
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_46 = [
    [1, 1, 0, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 4, 1, 1, 1, 1, 0],
    [1, 5, 4, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 0, 0, 1, 5, 5, 1],
    [5, 1, 0, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 4, 1, 5, 1, 1, 0],
    [5, 5, 4, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1],
    [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 0, 0, 5, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_46) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_47 : List ℕ := [6, 6, 6, 0, 0, 6, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_47 :
    checkTripleGroup 3 108 level4 tree5 base5_47
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_47 = [
    [1, 5, 5, 0, 0, 1, 1, 5, 5, 1, 1, 0, 0, 5, 5, 1],
    [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 0, 0, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_47) = [
    ((432632562633212166, 432632562633212166), [1, 4, 0, 1]),
    ((432632562633212166, 432352187168194566), [1, 5, 0, 1]),
    ((432352187168194566, 432632562633212166), [1, 5, 0, 1]),
    ((433754064493282566, 433754064493282566), [1, 0, 4, 1]),
    ((434034439958300166, 433754064493282566), [1, 0, 5, 1]),
    ((433754064493282566, 434034439958300166), [1, 0, 5, 1]),
    ((432352187168194566, 433754064493282566), [5, 1, 0, 5]),
    ((433754064493282566, 432352187168194566), [5, 1, 0, 5]),
    ((434034439958300166, 432632562633212166), [5, 0, 1, 5]),
    ((432632562633212166, 434034439958300166), [5, 0, 1, 5]),
    ((433754064493282566, 432632562633212166), [5, 1, 1, 5]),
    ((432632562633212166, 433754064493282566), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_48 : List ℕ := [6, 6, 6, 0, 1, 5, 6, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_48 :
    checkTripleGroup 3 108 level4 tree5 base5_48
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_48 = [
    [1, 5, 5, 0, 0, 1, 1, 5, 5, 1, 1, 0, 1, 4, 5, 1],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 0, 0, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_48) = [
    ((432632562633212166, 432632562633212166), [1, 4, 0, 1]),
    ((432632562633212166, 432352187168194566), [1, 5, 0, 1]),
    ((432352187168194566, 432632562633212166), [1, 5, 0, 1]),
    ((433754064493282566, 433754064493282566), [1, 0, 4, 1]),
    ((434034439958300166, 433754064493282566), [1, 0, 5, 1]),
    ((433754064493282566, 434034439958300166), [1, 0, 5, 1]),
    ((432352187168194566, 433754064493282566), [5, 1, 0, 5]),
    ((433754064493282566, 432352187168194566), [5, 1, 0, 5]),
    ((434034439958300166, 432632562633212166), [5, 0, 1, 5]),
    ((432632562633212166, 434034439958300166), [5, 0, 1, 5]),
    ((433754064493282566, 432632562633212166), [5, 1, 1, 5]),
    ((432632562633212166, 433754064493282566), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_49 : List ℕ := [6, 6, 6, 0, 1, 6, 6, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_49 :
    checkTripleGroup 3 108 level4 tree5 base5_49
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_49 = [
    [1, 5, 5, 0, 0, 1, 1, 5, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 0, 0, 1, 1, 5]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_49) = [
    ((432633657849872646, 432633657849872646), [1, 4, 0, 1]),
    ((432633657849872646, 432352187168194821), [1, 5, 0, 1]),
    ((432352187168194821, 432633657849872646), [1, 5, 0, 1]),
    ((433754064493282821, 434035535174960646), [1, 0, 5, 1]),
    ((433754064493282821, 433754064493282821), [1, 0, 5, 0]),
    ((434035535174960646, 433754064493282821), [1, 0, 5, 1]),
    ((433754064493282821, 432352187168194821), [5, 1, 1, 4]),
    ((432352187168194821, 433754064493282821), [5, 1, 1, 4]),
    ((434035535174960646, 432633657849872646), [5, 0, 1, 5]),
    ((432633657849872646, 434035535174960646), [5, 0, 1, 5]),
    ((433754064493282821, 432633657849872646), [5, 1, 1, 5]),
    ((432633657849872646, 433754064493282821), [5, 1, 1, 5])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_50 : List ℕ := [6, 6, 6, 0, 5, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_50 :
    checkTripleGroup 3 108 level4 tree5 base5_50
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_50 = [
    [1, 1, 1, 0, 4, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1],
    [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_50) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_51 : List ℕ := [6, 6, 6, 0, 6, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_51 :
    checkTripleGroup 3 108 level4 tree5 base5_51
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_51 = [
    [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 0, 5, 1, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_51) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_52 : List ℕ := [6, 6, 6, 0, 6, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_52 :
    checkTripleGroup 3 108 level4 tree5 base5_52
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_52 = [
    [1, 1, 1, 0, 5, 5, 5, 0, 5, 5, 5, 0, 1, 1, 1, 0],
    [1, 5, 5, 0, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 0, 5, 1, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_52) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_53 : List ℕ := [6, 6, 6, 1, 1, 6, 6, 4]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_53 :
    checkTripleGroup 3 108 level4 tree5 base5_53
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_53 = [
    [1, 5, 5, 1, 0, 1, 1, 4, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 1, 0, 1, 1, 4],
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 3]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_53) = [
    ((432633657849938181, 432633657849938181), [1, 5, 0, 0]),
    ((432633657849938181, 432633657849938181), [1, 5, 0, 1]),
    ((432633662144905476, 432633657849938181), [1, 5, 0, 0]),
    ((434035535175026181, 434035535175026181), [1, 0, 5, 0]),
    ((434035539469993476, 434035535175026181), [1, 0, 5, 0]),
    ((434035535175026181, 434035535175026181), [1, 0, 5, 1]),
    ((434035539469993476, 432633657849938181), [5, 1, 1, 4]),
    ((434035535175026181, 432633657849938181), [5, 1, 1, 4]),
    ((432633657849938181, 434035535175026181), [5, 1, 1, 4]),
    ((434035535175026181, 432633657849938181), [5, 1, 1, 5]),
    ((432633657849938181, 434035535175026181), [5, 1, 1, 5]),
    ((434035539469993476, 432633662144905476), [5, 1, 1, 3]),
    ((432633662144905476, 434035535175026181), [5, 1, 1, 4]),
    ((432633662144905476, 434035539469993476), [5, 1, 1, 3])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_54 : List ℕ := [6, 6, 6, 1, 4, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_54 :
    checkTripleGroup 3 108 level4 tree5 base5_54
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_54 = [
    [1, 1, 1, 0, 4, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0],
    [1, 5, 5, 1, 4, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1],
    [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 3, 1, 1, 0],
    [5, 5, 5, 1, 0, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 3, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_54) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_55 : List ℕ := [6, 6, 6, 1, 5, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_55 :
    checkTripleGroup 3 108 level4 tree5 base5_55
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_55 = [
    [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 4, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 0, 0, 1, 0],
    [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1],
    [1, 5, 5, 1, 4, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 4, 5, 1],
    [5, 1, 1, 0, 0, 5, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 1, 4, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 4, 0, 1, 0],
    [5, 5, 5, 1, 0, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1],
    [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 4, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 4, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_55) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_56 : List ℕ := [6, 6, 6, 1, 5, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_56 :
    checkTripleGroup 3 108 level4 tree5 base5_56
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_56 = [
    [1, 1, 1, 0, 5, 5, 5, 0, 5, 5, 5, 1, 0, 1, 1, 0],
    [1, 5, 5, 1, 4, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 1, 4, 1, 1, 0],
    [5, 5, 5, 1, 0, 1, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 4, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_56) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_57 : List ℕ := [6, 6, 6, 1, 6, 4, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_57 :
    checkTripleGroup 3 108 level4 tree5 base5_57
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_57 = [
    [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 3, 5, 1],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 5, 4, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 3, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_57) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_58 : List ℕ := [6, 6, 6, 1, 6, 5, 5, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_58 :
    checkTripleGroup 3 108 level4 tree5 base5_58
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_58 = [
    [1, 1, 1, 0, 5, 4, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0],
    [1, 1, 1, 0, 5, 5, 4, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 5, 5, 5, 1, 5, 5, 5, 1, 1, 0, 0, 0],
    [1, 5, 5, 1, 5, 1, 0, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1],
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 4, 1],
    [5, 1, 1, 0, 1, 4, 5, 1, 1, 5, 5, 1, 5, 1, 0, 0],
    [5, 1, 1, 0, 1, 5, 4, 1, 1, 5, 5, 1, 5, 0, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 5, 0, 0, 0],
    [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 5, 5, 4, 1],
    [5, 5, 5, 1, 1, 1, 0, 0, 1, 1, 1, 0, 5, 4, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 4, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_58) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_59 : List ℕ := [6, 6, 6, 1, 6, 5, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_59 :
    checkTripleGroup 3 108 level4 tree5 base5_59
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_59 = [
    [1, 1, 1, 0, 5, 5, 5, 0, 5, 5, 5, 1, 1, 0, 1, 0],
    [1, 5, 5, 1, 5, 0, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 1, 5, 5, 1, 5, 0, 1, 0],
    [5, 5, 5, 1, 1, 0, 1, 0, 1, 1, 1, 0, 5, 5, 5, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 4, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_59) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_60 : List ℕ := [6, 6, 6, 1, 7, 3, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_60 :
    checkTripleGroup 3 108 level4 tree5 base5_60
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_60 = [
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 2, 2, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_60) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_61 : List ℕ := [6, 6, 6, 1, 10, 3, 3, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_61 :
    checkTripleGroup 3 108 level4 tree5 base5_61
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_61 = [
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 5, 2, 2, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_61) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_62 : List ℕ := [6, 7, 7, 2, 10, 2, 2, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_62 :
    checkTripleGroup 3 108 level4 tree5 base5_62
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_62 = [
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 2, 2, 1, 5, 1, 1, 0],
    [5, 2, 5, 1, 5, 1, 1, 0, 1, 5, 2, 1, 5, 1, 1, 0],
    [5, 5, 2, 1, 5, 1, 1, 0, 1, 2, 5, 1, 5, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_62) = [
    ((218154110824874496, 434041015570204161), [5, 1, 1, 0]),
    ((434041015570204161, 434041015570204161), [2, 2, 5, 1]),
    ((506098609591354881, 506098609591354881), [1, 2, 5, 1]),
    ((218154110824874496, 506098609591354881), [5, 1, 1, 0]),
    ((721426966724871681, 434041015570204161), [2, 1, 1, 0]),
    ((793484560746022401, 434041015570204161), [1, 1, 1, 0]),
    ((506098609591354881, 721426966724871681), [1, 1, 1, 0]),
    ((721426966724871681, 506098609591354881), [1, 1, 1, 0]),
    ((506098609591354881, 434041015570204161), [5, 2, 5, 1]),
    ((721426966724871681, 721426966724871681), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_63 : List ℕ := [7, 6, 6, 1, 3, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_63 :
    checkTripleGroup 3 108 level4 tree5 base5_63
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_63 = [
    [5, 1, 1, 0, 1, 5, 5, 1, 2, 5, 5, 1, 2, 1, 1, 0],
    [5, 1, 1, 0, 2, 5, 5, 1, 2, 5, 5, 1, 1, 1, 1, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 2, 1, 1, 0, 2, 5, 5, 1],
    [5, 5, 5, 1, 2, 1, 1, 0, 2, 1, 1, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_63) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_64 : List ℕ := [7, 6, 6, 1, 6, 3, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_64 :
    checkTripleGroup 3 108 level4 tree5 base5_64
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_64 = [
    [2, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 2, 5, 1],
    [5, 1, 1, 0, 5, 2, 5, 1, 2, 5, 5, 1, 1, 1, 1, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 2, 1, 1, 0, 5, 2, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_64) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_65 : List ℕ := [8, 6, 6, 1, 2, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_65 :
    checkTripleGroup 3 108 level4 tree5 base5_65
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_65 = [
    [4, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0],
    [4, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1],
    [5, 1, 1, 0, 1, 5, 5, 1, 3, 5, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 2, 5, 5, 1, 3, 5, 5, 1, 0, 1, 1, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 3, 1, 1, 0, 1, 5, 5, 1],
    [6, 5, 5, 1, 1, 1, 1, 0, 2, 1, 1, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_65) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_66 : List ℕ := [9, 1, 6, 6, 6, 6, 1, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_66 :
    checkTripleGroup 3 108 level4 tree5 base5_66
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_66 = [
    [4, 1, 5, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 1],
    [4, 1, 1, 5, 1, 5, 0, 1, 5, 0, 5, 1, 5, 1, 1, 0],
    [5, 0, 1, 5, 1, 5, 0, 1, 4, 1, 5, 1, 5, 1, 1, 0],
    [5, 0, 5, 1, 5, 1, 1, 0, 4, 1, 1, 5, 1, 5, 0, 1],
    [5, 1, 1, 5, 1, 5, 0, 1, 4, 0, 5, 1, 5, 1, 1, 0],
    [5, 1, 5, 1, 5, 1, 1, 0, 4, 0, 1, 5, 1, 5, 0, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_66) = [
    ((361983421498918401, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [0, 5, 5, 1]),
    ((2825753641222656, 361983421498918401), [5, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [1, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [4, 1, 1, 0]),
    ((578156203562370561, 361983421498918401), [1, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [4, 5, 5, 1]),
    ((578156203562370561, 361983421498918401), [1, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [5, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [4, 1, 1, 0]),
    ((434041015520069121, 434041015520069121), [3, 1, 1, 0]),
    ((506098609541219841, 434041015520069121), [2, 1, 1, 0]),
    ((578156203562370561, 434041015520069121), [1, 1, 1, 0]),
    ((650213797583521281, 434041015520069121), [0, 1, 1, 0]),
    ((578156203562370561, 506098609541219841), [0, 1, 1, 0]),
    ((506098609541219841, 506098609541219841), [1, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [5, 5, 5, 1]),
    ((434041015520069121, 361983421498918401), [4, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [1, 5, 5, 1]),
    ((434041015520069121, 434041015520069121), [3, 5, 5, 1]),
    ((506098609541219841, 434041015520069121), [2, 5, 5, 1]),
    ((578156203562370561, 434041015520069121), [1, 5, 5, 1]),
    ((650213797583521281, 434041015520069121), [0, 5, 5, 1]),
    ((506098609541219841, 506098609541219841), [1, 5, 5, 1]),
    ((578156203562370561, 506098609541219841), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_67 : List ℕ := [9, 5, 6, 1, 2, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_67 :
    checkTripleGroup 3 108 level4 tree5 base5_67
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_67 = [
    [4, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [4, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 0, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 4, 4, 5, 1, 1, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 4, 0, 1, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_67) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_68 : List ℕ := [9, 6, 1, 6, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_68 :
    checkTripleGroup 3 108 level4 tree5 base5_68
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_68 = [
    [4, 1, 1, 5, 1, 0, 5, 1, 5, 5, 0, 1, 5, 1, 1, 0],
    [4, 5, 1, 1, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 1],
    [5, 1, 0, 5, 1, 0, 5, 1, 4, 5, 1, 1, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 0, 5, 1, 4, 5, 0, 1, 5, 1, 1, 0],
    [5, 5, 0, 1, 5, 1, 1, 0, 4, 1, 1, 5, 1, 0, 5, 1],
    [5, 5, 1, 1, 5, 1, 1, 0, 4, 1, 0, 5, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_68) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_69 : List ℕ := [9, 6, 2, 5, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_69 :
    checkTripleGroup 3 108 level4 tree5 base5_69
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_69 = [
    [4, 1, 1, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0],
    [4, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 1, 1, 4, 1, 0, 5, 1, 4, 5, 1, 1, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 0, 5, 1, 4, 5, 1, 0, 5, 1, 1, 0],
    [5, 5, 1, 1, 5, 1, 1, 0, 4, 1, 1, 4, 1, 0, 5, 1],
    [5, 5, 1, 0, 5, 1, 1, 0, 4, 1, 1, 5, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_69) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_70 : List ℕ := [9, 6, 6, 0, 2, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_70 :
    checkTripleGroup 3 108 level4 tree5 base5_70
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_70 = [
    [4, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 0, 1, 1, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_70) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_71 : List ℕ := [9, 6, 6, 1, 1, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_71 :
    checkTripleGroup 3 108 level4 tree5 base5_71
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_71 = [
    [4, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0],
    [4, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1],
    [5, 1, 1, 0, 0, 5, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 0, 1, 1, 0],
    [5, 5, 5, 1, 0, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 0, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_71) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_72 : List ℕ := [9, 6, 6, 1, 2, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_72 :
    checkTripleGroup 3 108 level4 tree5 base5_72
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_72 = [
    [4, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [4, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [5, 1, 1, 0, 1, 4, 5, 1, 4, 5, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 1, 0, 1, 0],
    [5, 5, 5, 1, 1, 0, 1, 0, 4, 1, 1, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 4, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_72) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_73 : List ℕ := [9, 6, 6, 1, 2, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_73 :
    checkTripleGroup 3 108 level4 tree5 base5_73
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_73 = [
    [4, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 1, 1, 0, 1, 5, 5, 0, 4, 5, 5, 1, 1, 1, 1, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 4, 1, 1, 0, 1, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_73) = [
    ((650209416800437761, 360576068174086656), [5, 1, 1, 0]),
    ((650209416800437761, 650209399620568581), [1, 0, 5, 1]),
    ((650209416800437761, 432633657900270081), [5, 1, 1, 0]),
    ((650209416800437761, 432633662195237376), [5, 1, 1, 0]),
    ((650209416800437761, 722266993641719301), [1, 0, 5, 1]),
    ((650209416800437761, 722266989346752006), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_74 : List ℕ := [10, 0, 6, 6, 6, 6, 1, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_74 :
    checkTripleGroup 3 108 level4 tree5 base5_74
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_74 = [
    [5, 0, 1, 5, 1, 5, 0, 1, 5, 0, 5, 1, 5, 1, 1, 0],
    [5, 0, 5, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_74) = [
    ((361983421498918401, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [0, 5, 5, 1]),
    ((2825753641222656, 361983421498918401), [5, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [1, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [4, 1, 1, 0]),
    ((578156203562370561, 361983421498918401), [1, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [0, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [4, 5, 5, 1]),
    ((578156203562370561, 361983421498918401), [1, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [0, 5, 5, 1]),
    ((361983421498918401, 361983421498918401), [5, 1, 1, 0]),
    ((650213797583521281, 361983421498918401), [1, 1, 1, 0]),
    ((434041015520069121, 361983421498918401), [4, 1, 1, 0]),
    ((434041015520069121, 434041015520069121), [3, 1, 1, 0]),
    ((506098609541219841, 434041015520069121), [2, 1, 1, 0]),
    ((578156203562370561, 434041015520069121), [1, 1, 1, 0]),
    ((650213797583521281, 434041015520069121), [0, 1, 1, 0]),
    ((578156203562370561, 506098609541219841), [0, 1, 1, 0]),
    ((506098609541219841, 506098609541219841), [1, 1, 1, 0]),
    ((361983421498918401, 361983421498918401), [5, 5, 5, 1]),
    ((434041015520069121, 361983421498918401), [4, 5, 5, 1]),
    ((650213797583521281, 361983421498918401), [1, 5, 5, 1]),
    ((434041015520069121, 434041015520069121), [3, 5, 5, 1]),
    ((506098609541219841, 434041015520069121), [2, 5, 5, 1]),
    ((578156203562370561, 434041015520069121), [1, 5, 5, 1]),
    ((650213797583521281, 434041015520069121), [0, 5, 5, 1]),
    ((506098609541219841, 506098609541219841), [1, 5, 5, 1]),
    ((578156203562370561, 506098609541219841), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_75 : List ℕ := [10, 1, 6, 5, 6, 6, 1, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_75 :
    checkTripleGroup 3 108 level4 tree5 base5_75
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_75 = [
    [5, 0, 5, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 5, 0, 1],
    [5, 0, 1, 5, 1, 5, 0, 1, 5, 1, 5, 0, 5, 1, 1, 0],
    [5, 1, 1, 4, 1, 5, 0, 1, 5, 0, 5, 1, 5, 1, 1, 0],
    [5, 1, 5, 0, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 1],
    [5, 1, 1, 5, 1, 5, 0, 1, 5, 0, 5, 0, 5, 1, 1, 0],
    [5, 1, 5, 1, 5, 1, 1, 0, 5, 0, 1, 4, 1, 5, 0, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_75) = [
    ((361983421515630081, 433759540560135681), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 0, 1, 0]),
    ((74601872702439936, 361983421515630081), [5, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [0, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [1, 0, 1, 0]),
    ((361983421515630081, 433759540560135681), [1, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 0, 1, 0]),
    ((74601872702439936, 433759540560135681), [5, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [0, 5, 5, 1]),
    ((434041015536780801, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [1, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [1, 4, 5, 1]),
    ((361983421515630081, 433759540560135681), [1, 5, 5, 1]),
    ((74601872702439936, 434041015536780801), [5, 1, 1, 0]),
    ((434041015536780801, 434041015536780801), [0, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 1, 1, 0]),
    ((361983421515630081, 361983421515630081), [5, 0, 1, 0]),
    ((649932322623587841, 361983421515630081), [1, 5, 5, 1]),
    ((361983421515630081, 361983421515630081), [5, 4, 5, 1]),
    ((650213797600232961, 361983421515630081), [1, 4, 5, 1]),
    ((433759540560135681, 433759540560135681), [4, 1, 1, 0]),
    ((649932322623587841, 433759540560135681), [1, 1, 1, 0]),
    ((721989916644738561, 433759540560135681), [0, 1, 1, 0]),
    ((433759540560135681, 361983421515630081), [5, 1, 1, 0]),
    ((434041015536780801, 361983421515630081), [5, 0, 1, 0]),
    ((721989916644738561, 361983421515630081), [1, 1, 1, 0]),
    ((434041015536780801, 433759540560135681), [4, 1, 1, 0]),
    ((650213797600232961, 433759540560135681), [1, 1, 1, 0]),
    ((650213797600232961, 434041015536780801), [1, 0, 1, 0]),
    ((434041015536780801, 434041015536780801), [4, 0, 1, 0]),
    ((649932322623587841, 434041015536780801), [1, 1, 1, 0]),
    ((721989916644738561, 434041015536780801), [0, 1, 1, 0]),
    ((433759540560135681, 433759540560135681), [4, 5, 5, 1]),
    ((649932322623587841, 433759540560135681), [1, 5, 5, 1]),
    ((721989916644738561, 433759540560135681), [0, 5, 5, 1]),
    ((433759540560135681, 361983421515630081), [5, 5, 5, 1]),
    ((434041015536780801, 361983421515630081), [5, 4, 5, 1]),
    ((434041015536780801, 433759540560135681), [4, 5, 5, 1]),
    ((361983421515630081, 433759540560135681), [5, 5, 5, 1]),
    ((721989916644738561, 361983421515630081), [1, 5, 5, 1]),
    ((650213797600232961, 433759540560135681), [1, 5, 5, 1]),
    ((434041015536780801, 434041015536780801), [4, 4, 5, 1]),
    ((721989916644738561, 434041015536780801), [0, 5, 5, 1]),
    ((650213797600232961, 434041015536780801), [1, 4, 5, 1]),
    ((649932322623587841, 434041015536780801), [1, 5, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_76 : List ℕ := [10, 1, 6, 6, 6, 6, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_76 :
    checkTripleGroup 3 108 level4 tree5 base5_76
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_76 = [
    [5, 0, 5, 1, 5, 1, 1, 0, 5, 1, 1, 5, 1, 5, 0, 0],
    [5, 1, 1, 5, 1, 5, 0, 0, 5, 0, 5, 1, 5, 1, 1, 0],
    [5, 1, 5, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 5, 0, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_76) = [
    ((74883343384183296, 361983421515695616), [5, 1, 1, 0]),
    ((361983421515695616, 361983421515695616), [1, 5, 5, 0]),
    ((434041011241879041, 361983421515695616), [1, 1, 1, 0]),
    ((361983421515695616, 434041011241879041), [1, 1, 1, 0]),
    ((434041015536846336, 434041011241879041), [0, 1, 1, 0]),
    ((74883343384183296, 434041011241879041), [5, 1, 1, 0]),
    ((146940937405334016, 434041011241879041), [4, 1, 1, 0]),
    ((434041011241879041, 434041011241879041), [0, 5, 5, 1]),
    ((146940937405334016, 361983421515695616), [5, 1, 1, 0]),
    ((434041015536846336, 361983421515695616), [1, 5, 5, 0]),
    ((74883343384183296, 434041015536846336), [5, 1, 1, 0]),
    ((146940937405334016, 434041015536846336), [4, 1, 1, 0]),
    ((434041015536846336, 434041015536846336), [0, 5, 5, 0]),
    ((650213793305331201, 361983421515695616), [1, 1, 1, 0]),
    ((361983421515695616, 361983421515695616), [5, 5, 5, 0]),
    ((650213797600298496, 361983421515695616), [1, 5, 5, 0]),
    ((434041011241879041, 361983421515695616), [5, 1, 1, 0]),
    ((722271387326481921, 361983421515695616), [1, 1, 1, 0]),
    ((650213797600298496, 434041011241879041), [1, 1, 1, 0]),
    ((361983421515695616, 434041011241879041), [5, 1, 1, 0]),
    ((434041015536846336, 434041011241879041), [4, 1, 1, 0]),
    ((722271391621449216, 434041011241879041), [0, 1, 1, 0]),
    ((650213793305331201, 434041015536846336), [1, 1, 1, 0]),
    ((722271387326481921, 434041015536846336), [0, 1, 1, 0]),
    ((434041015536846336, 361983421515695616), [5, 5, 5, 0]),
    ((650213793305331201, 434041011241879041), [1, 5, 5, 1]),
    ((434041011241879041, 434041011241879041), [4, 5, 5, 1]),
    ((722271387326481921, 434041011241879041), [0, 5, 5, 1]),
    ((722271391621449216, 361983421515695616), [1, 5, 5, 0]),
    ((434041015536846336, 434041015536846336), [4, 5, 5, 0]),
    ((650213797600298496, 434041015536846336), [1, 5, 5, 0]),
    ((722271391621449216, 434041015536846336), [0, 5, 5, 0])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_77 : List ℕ := [10, 2, 6, 5, 6, 5, 1, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_77 :
    checkTripleGroup 3 108 level4 tree5 base5_77
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_77 = [
    [5, 1, 5, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 4, 0, 1],
    [5, 1, 1, 4, 1, 5, 0, 1, 5, 1, 5, 1, 5, 0, 1, 0],
    [5, 1, 1, 5, 1, 4, 0, 1, 5, 1, 5, 0, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 5, 0, 1, 5, 1, 5, 0, 5, 0, 1, 0],
    [5, 1, 5, 1, 5, 0, 1, 0, 5, 1, 1, 4, 1, 5, 0, 1],
    [5, 1, 5, 0, 5, 1, 1, 0, 5, 1, 1, 5, 1, 4, 0, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_77) = [
    ((433759540576912641, 433759540576912641), [1, 1, 0, 0]),
    ((434039916041930241, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [1, 1, 0, 0]),
    ((434041015553557761, 434039916041930241), [1, 0, 1, 0]),
    ((146658367228740096, 433759540576912641), [5, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [1, 0, 0, 0]),
    ((146659466740367616, 433759540576912641), [5, 1, 0, 0]),
    ((433759540576912641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 434039916041930241), [1, 4, 5, 1]),
    ((146939842205385216, 434039916041930241), [5, 0, 1, 0]),
    ((146658367228740096, 434039916041930241), [5, 1, 1, 0]),
    ((146939842205385216, 434041015553557761), [5, 0, 1, 0]),
    ((146939842205385216, 433759540576912641), [5, 1, 1, 0]),
    ((434039916041930241, 433759540576912641), [1, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 434039916041930241), [1, 5, 5, 1]),
    ((146659466740367616, 434039916041930241), [5, 1, 1, 0]),
    ((146658367228740096, 434041015553557761), [5, 1, 1, 0]),
    ((146659466740367616, 434041015553557761), [5, 1, 0, 0]),
    ((434041015553557761, 434041015553557761), [1, 4, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 1, 1, 0]),
    ((433759540576912641, 433759540576912641), [5, 1, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 1, 0, 0]),
    ((721988817149888001, 434039916041930241), [1, 1, 1, 0]),
    ((434039916041930241, 434039916041930241), [5, 0, 1, 0]),
    ((722270292126533121, 434039916041930241), [1, 0, 1, 0]),
    ((434039916041930241, 433759540576912641), [5, 1, 1, 0]),
    ((722270292126533121, 433759540576912641), [1, 1, 1, 0]),
    ((434041015553557761, 433759540576912641), [5, 1, 0, 0]),
    ((722271391638160641, 433759540576912641), [1, 1, 0, 0]),
    ((722271391638160641, 434039916041930241), [1, 0, 1, 0]),
    ((434041015553557761, 434039916041930241), [5, 0, 1, 0]),
    ((433759540576912641, 434039916041930241), [5, 1, 1, 0]),
    ((721989916661515521, 434039916041930241), [1, 1, 1, 0]),
    ((434041015553557761, 434041015553557761), [5, 0, 0, 0]),
    ((721989916661515521, 434041015553557761), [1, 1, 0, 0]),
    ((721988817149888001, 434041015553557761), [1, 1, 1, 0]),
    ((722270292126533121, 434041015553557761), [1, 0, 1, 0]),
    ((722271391638160641, 434041015553557761), [1, 0, 0, 0]),
    ((721989916661515521, 433759540576912641), [1, 5, 4, 1]),
    ((433759540576912641, 433759540576912641), [5, 5, 4, 1]),
    ((721988817149888001, 433759540576912641), [1, 5, 5, 1]),
    ((722270292126533121, 434039916041930241), [1, 4, 5, 1]),
    ((721988817149888001, 434039916041930241), [1, 5, 5, 1]),
    ((434039916041930241, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 433759540576912641), [1, 5, 4, 1]),
    ((434039916041930241, 433759540576912641), [5, 5, 5, 1]),
    ((434041015553557761, 433759540576912641), [5, 5, 4, 1]),
    ((722270292126533121, 433759540576912641), [1, 5, 5, 1]),
    ((721989916661515521, 434039916041930241), [1, 5, 5, 1]),
    ((433759540576912641, 434039916041930241), [5, 5, 5, 1]),
    ((434041015553557761, 434039916041930241), [5, 4, 5, 1]),
    ((722271391638160641, 434039916041930241), [1, 4, 5, 1]),
    ((434041015553557761, 434041015553557761), [5, 4, 4, 1]),
    ((721988817149888001, 434041015553557761), [1, 5, 5, 1]),
    ((722270292126533121, 434041015553557761), [1, 4, 5, 1]),
    ((721989916661515521, 434041015553557761), [1, 5, 4, 1]),
    ((722271391638160641, 434041015553557761), [1, 4, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_78 : List ℕ := [10, 3, 6, 1, 3, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_78 :
    checkTripleGroup 3 108 level4 tree5 base5_78
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_78 = [
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 2, 5, 1, 2, 1, 1, 0],
    [5, 1, 1, 0, 2, 5, 5, 1, 5, 2, 5, 1, 1, 1, 1, 0],
    [8, 2, 5, 1, 2, 1, 1, 0, 2, 1, 1, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_78) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_79 : List ℕ := [10, 3, 6, 1, 6, 6, 3, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_79 :
    checkTripleGroup 3 108 level4 tree5 base5_79
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_79 = [
    [5, 1, 1, 0, 5, 5, 2, 1, 5, 2, 5, 1, 1, 1, 1, 0],
    [5, 2, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 5, 2, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_79) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_80 : List ℕ := [10, 4, 6, 1, 2, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_80 :
    checkTripleGroup 3 108 level4 tree5 base5_80
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_80 = [
    [5, 0, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 3, 5, 1, 1, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_80) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_81 : List ℕ := [10, 5, 1, 6, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_81 :
    checkTripleGroup 3 108 level4 tree5 base5_81
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_81 = [
    [5, 0, 1, 5, 1, 0, 5, 1, 5, 5, 0, 1, 5, 1, 1, 0],
    [5, 1, 0, 5, 1, 0, 5, 1, 5, 4, 1, 1, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 0, 5, 1, 5, 4, 0, 1, 5, 1, 1, 0],
    [5, 4, 1, 1, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 1],
    [5, 5, 0, 1, 5, 1, 1, 0, 5, 0, 1, 5, 1, 0, 5, 1],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 0, 0, 5, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_81) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_82 : List ℕ := [10, 5, 2, 5, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_82 :
    checkTripleGroup 3 108 level4 tree5 base5_82
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_82 = [
    [5, 0, 1, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0],
    [5, 1, 1, 4, 1, 0, 5, 1, 5, 4, 1, 1, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 0, 5, 1, 5, 4, 1, 0, 5, 1, 1, 0],
    [5, 4, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 5, 1, 0, 5, 1, 1, 0, 5, 0, 1, 5, 1, 0, 5, 1],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 0, 1, 4, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_82) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_83 : List ℕ := [10, 5, 5, 1, 2, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_83 :
    checkTripleGroup 3 108 level4 tree5 base5_83
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_83 = [
    [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 4, 1, 1, 1, 1, 0],
    [5, 1, 0, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 4, 1, 1, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 0, 0, 1, 5, 5, 1],
    [5, 5, 4, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 0, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_83) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_84 : List ℕ := [10, 5, 6, 0, 2, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_84 :
    checkTripleGroup 3 108 level4 tree5 base5_84
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_84 = [
    [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 0, 1, 1, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_84) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_85 : List ℕ := [10, 5, 6, 1, 1, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_85 :
    checkTripleGroup 3 108 level4 tree5 base5_85
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_85 = [
    [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 0, 1, 1, 0],
    [5, 1, 1, 0, 0, 5, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 0, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1],
    [5, 5, 5, 1, 0, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 0, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_85) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_86 : List ℕ := [10, 5, 6, 1, 2, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_86 :
    checkTripleGroup 3 108 level4 tree5 base5_86
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_86 = [
    [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [5, 1, 1, 0, 1, 4, 5, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 0, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [5, 5, 5, 1, 1, 0, 1, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 4, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_86) = [
    ((648806444258689281, 649087897760497926), [1, 5, 0, 1]),
    ((650208321583777281, 360576068174086401), [5, 1, 1, 0]),
    ((648806444258689281, 361977945499174401), [5, 1, 1, 0]),
    ((650208321583777281, 650209399620568326), [1, 0, 5, 1]),
    ((650208321583777281, 432632562683609601), [5, 1, 1, 0]),
    ((648806444258689281, 433754064543680001), [5, 1, 1, 0]),
    ((648806444258689281, 720864016805003526), [1, 5, 0, 1]),
    ((650208321583777281, 432633662195237121), [5, 1, 1, 0]),
    ((648806444258689281, 434035539520325121), [5, 1, 1, 0]),
    ((648806444258689281, 721145491781648646), [1, 5, 0, 1]),
    ((650208321583777281, 722265894130091526), [1, 0, 5, 1]),
    ((650208321583777281, 722266993641719046), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_87 : List ℕ := [10, 5, 6, 1, 2, 6, 5, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_87 :
    checkTripleGroup 3 108 level4 tree5 base5_87
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_87 = [
    [5, 0, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0],
    [5, 1, 1, 0, 1, 5, 4, 1, 5, 4, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 4, 5, 1, 1, 1, 0, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1],
    [5, 5, 5, 1, 1, 1, 0, 0, 5, 0, 1, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 4, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_87) = [
    ((650209416800437761, 360576068174086656), [5, 1, 1, 0]),
    ((650209416800437761, 650209399620568581), [1, 0, 5, 1]),
    ((650209416800437761, 432633657900270081), [5, 1, 1, 0]),
    ((650209416800437761, 432633662195237376), [5, 1, 1, 0]),
    ((650209416800437761, 722266993641719301), [1, 0, 5, 1]),
    ((650209416800437761, 722266989346752006), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_88 : List ℕ := [10, 5, 6, 1, 2, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_88 :
    checkTripleGroup 3 108 level4 tree5 base5_88
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_88 = [
    [5, 1, 1, 0, 1, 5, 5, 0, 5, 4, 5, 1, 1, 1, 1, 0],
    [5, 4, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 0, 1, 0, 1, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_88) = [
    ((650209416800437761, 360576068174086656), [5, 1, 1, 0]),
    ((650209416800437761, 650209399620568581), [1, 0, 5, 1]),
    ((650209416800437761, 432633657900270081), [5, 1, 1, 0]),
    ((650209416800437761, 432633662195237376), [5, 1, 1, 0]),
    ((650209416800437761, 722266993641719301), [1, 0, 5, 1]),
    ((650209416800437761, 722266989346752006), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_89 : List ℕ := [10, 6, 1, 5, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_89 :
    checkTripleGroup 3 108 level4 tree5 base5_89
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_89 = [
    [5, 1, 0, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0],
    [5, 1, 1, 4, 1, 0, 5, 1, 5, 5, 0, 1, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 0, 5, 1, 5, 5, 0, 0, 5, 1, 1, 0],
    [5, 5, 0, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 1],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 0, 4, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_89) = [
    ((721984440644994561, 432352187235303681), [5, 1, 1, 0]),
    ((720582563319906561, 433754064560391681), [5, 1, 1, 0]),
    ((720582563319906561, 720864016821715206), [1, 5, 0, 1]),
    ((721984440644994561, 432632562700321281), [5, 1, 1, 0]),
    ((721984440644994561, 432633662211948801), [5, 1, 1, 0]),
    ((721984440644994561, 721985518681785606), [1, 0, 5, 1]),
    ((721984440644994561, 722265894146803206), [1, 0, 5, 1]),
    ((721984440644994561, 722266993658430726), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_90 : List ℕ := [10, 6, 1, 6, 6, 1, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_90 :
    checkTripleGroup 3 108 level4 tree5 base5_90
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_90 = [
    [5, 1, 1, 5, 1, 0, 5, 0, 5, 5, 0, 1, 5, 1, 1, 0],
    [5, 5, 0, 1, 5, 1, 1, 0, 5, 1, 1, 5, 1, 0, 5, 0],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 0, 5, 1, 0, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_90) = [
    ((720864034001649921, 720864016821780741), [1, 5, 0, 1]),
    ((720864034001649921, 433754064560457216), [5, 1, 1, 0]),
    ((720864038296617216, 720864016821780741), [1, 5, 0, 0]),
    ((722265911326737921, 432632562700386816), [5, 1, 1, 0]),
    ((721145508978295041, 721145491798425861), [1, 4, 0, 1]),
    ((722267010838365441, 432633657917047041), [5, 1, 0, 0]),
    ((722265911326737921, 432633657917047041), [5, 1, 1, 0]),
    ((720864034001649921, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035535242135041), [5, 0, 1, 0]),
    ((722267010838365441, 432632562700386816), [5, 1, 1, 0]),
    ((722265915621705216, 432633657917047041), [5, 1, 1, 0]),
    ((722267010838365441, 432633662212014336), [5, 1, 0, 0]),
    ((722265911326737921, 432633662212014336), [5, 1, 1, 0]),
    ((721145508978295041, 433754064560457216), [5, 1, 1, 0]),
    ((720864034001649921, 721145487503458566), [1, 5, 0, 1]),
    ((720864038296617216, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035539537102336), [5, 0, 1, 0]),
    ((720864034001649921, 434035539537102336), [5, 1, 1, 0]),
    ((721145508978295041, 720864016821780741), [1, 5, 0, 1]),
    ((721145508978295041, 721145487503458566), [1, 4, 0, 1]),
    ((720864038296617216, 721145491798425861), [1, 5, 0, 0]),
    ((720864034001649921, 721145491798425861), [1, 5, 0, 1]),
    ((722265911326737921, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722265894146868741), [1, 0, 5, 0]),
    ((722265911326737921, 722266989363528966), [1, 0, 5, 1]),
    ((722267010838365441, 722266989363528966), [1, 0, 4, 1]),
    ((722267010838365441, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722266993658496261), [1, 0, 5, 0]),
    ((722265911326737921, 722266993658496261), [1, 0, 5, 1]),
    ((722267010838365441, 722266993658496261), [1, 0, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_91 : List ℕ := [10, 6, 2, 4, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_91 :
    checkTripleGroup 3 108 level4 tree5 base5_91
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_91 = [
    [5, 1, 1, 4, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 1, 0],
    [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 3, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_91) = [
    ((721984440644994561, 432352187235303681), [5, 1, 1, 0]),
    ((720582563319906561, 433754064560391681), [5, 1, 1, 0]),
    ((720582563319906561, 720864016821715206), [1, 5, 0, 1]),
    ((721984440644994561, 432632562700321281), [5, 1, 1, 0]),
    ((721984440644994561, 432633662211948801), [5, 1, 1, 0]),
    ((721984440644994561, 721985518681785606), [1, 0, 5, 1]),
    ((721984440644994561, 722265894146803206), [1, 0, 5, 1]),
    ((721984440644994561, 722266993658430726), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_92 : List ℕ := [10, 6, 2, 5, 6, 1, 5, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_92 :
    checkTripleGroup 3 108 level4 tree5 base5_92
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_92 = [
    [5, 1, 1, 4, 1, 0, 5, 1, 5, 5, 1, 1, 5, 1, 0, 0],
    [5, 1, 1, 5, 1, 0, 4, 1, 5, 5, 1, 0, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 0, 5, 1, 5, 5, 1, 0, 5, 1, 0, 0],
    [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 1, 5, 1, 0, 4, 1],
    [5, 5, 1, 1, 5, 1, 0, 0, 5, 1, 1, 4, 1, 0, 5, 1],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 4, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_92) = [
    ((720864034001649921, 720864016821780741), [1, 5, 0, 1]),
    ((720864034001649921, 433754064560457216), [5, 1, 1, 0]),
    ((720864038296617216, 720864016821780741), [1, 5, 0, 0]),
    ((722265911326737921, 432632562700386816), [5, 1, 1, 0]),
    ((721145508978295041, 721145491798425861), [1, 4, 0, 1]),
    ((722267010838365441, 432633657917047041), [5, 1, 0, 0]),
    ((722265911326737921, 432633657917047041), [5, 1, 1, 0]),
    ((720864034001649921, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035535242135041), [5, 0, 1, 0]),
    ((722267010838365441, 432632562700386816), [5, 1, 1, 0]),
    ((722265915621705216, 432633657917047041), [5, 1, 1, 0]),
    ((722267010838365441, 432633662212014336), [5, 1, 0, 0]),
    ((722265911326737921, 432633662212014336), [5, 1, 1, 0]),
    ((721145508978295041, 433754064560457216), [5, 1, 1, 0]),
    ((720864034001649921, 721145487503458566), [1, 5, 0, 1]),
    ((720864038296617216, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035539537102336), [5, 0, 1, 0]),
    ((720864034001649921, 434035539537102336), [5, 1, 1, 0]),
    ((721145508978295041, 720864016821780741), [1, 5, 0, 1]),
    ((721145508978295041, 721145487503458566), [1, 4, 0, 1]),
    ((720864038296617216, 721145491798425861), [1, 5, 0, 0]),
    ((720864034001649921, 721145491798425861), [1, 5, 0, 1]),
    ((722265911326737921, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722265894146868741), [1, 0, 5, 0]),
    ((722265911326737921, 722266989363528966), [1, 0, 5, 1]),
    ((722267010838365441, 722266989363528966), [1, 0, 4, 1]),
    ((722267010838365441, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722266993658496261), [1, 0, 5, 0]),
    ((722265911326737921, 722266993658496261), [1, 0, 5, 1]),
    ((722267010838365441, 722266993658496261), [1, 0, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_93 : List ℕ := [10, 6, 2, 5, 6, 1, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_93 :
    checkTripleGroup 3 108 level4 tree5 base5_93
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_93 = [
    [5, 1, 1, 5, 1, 0, 5, 0, 5, 5, 1, 0, 5, 1, 1, 0],
    [5, 5, 1, 0, 5, 1, 1, 0, 5, 1, 1, 5, 1, 0, 5, 0],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 4, 1, 0, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_93) = [
    ((720864034001649921, 720864016821780741), [1, 5, 0, 1]),
    ((720864034001649921, 433754064560457216), [5, 1, 1, 0]),
    ((720864038296617216, 720864016821780741), [1, 5, 0, 0]),
    ((722265911326737921, 432632562700386816), [5, 1, 1, 0]),
    ((721145508978295041, 721145491798425861), [1, 4, 0, 1]),
    ((722267010838365441, 432633657917047041), [5, 1, 0, 0]),
    ((722265911326737921, 432633657917047041), [5, 1, 1, 0]),
    ((720864034001649921, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035535242135041), [5, 0, 1, 0]),
    ((722267010838365441, 432632562700386816), [5, 1, 1, 0]),
    ((722265915621705216, 432633657917047041), [5, 1, 1, 0]),
    ((722267010838365441, 432633662212014336), [5, 1, 0, 0]),
    ((722265911326737921, 432633662212014336), [5, 1, 1, 0]),
    ((721145508978295041, 433754064560457216), [5, 1, 1, 0]),
    ((720864034001649921, 721145487503458566), [1, 5, 0, 1]),
    ((720864038296617216, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035539537102336), [5, 0, 1, 0]),
    ((720864034001649921, 434035539537102336), [5, 1, 1, 0]),
    ((721145508978295041, 720864016821780741), [1, 5, 0, 1]),
    ((721145508978295041, 721145487503458566), [1, 4, 0, 1]),
    ((720864038296617216, 721145491798425861), [1, 5, 0, 0]),
    ((720864034001649921, 721145491798425861), [1, 5, 0, 1]),
    ((722265911326737921, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722265894146868741), [1, 0, 5, 0]),
    ((722265911326737921, 722266989363528966), [1, 0, 5, 1]),
    ((722267010838365441, 722266989363528966), [1, 0, 4, 1]),
    ((722267010838365441, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722266993658496261), [1, 0, 5, 0]),
    ((722265911326737921, 722266993658496261), [1, 0, 5, 1]),
    ((722267010838365441, 722266993658496261), [1, 0, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_94 : List ℕ := [10, 6, 3, 1, 6, 3, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_94 :
    checkTripleGroup 3 108 level4 tree5 base5_94
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_94 = [
    [5, 1, 1, 0, 5, 2, 5, 1, 5, 5, 2, 1, 1, 1, 1, 0],
    [5, 5, 2, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 2, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_94) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_95 : List ℕ := [10, 6, 3, 3, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_95 :
    checkTripleGroup 3 108 level4 tree5 base5_95
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_95 = [
    [5, 5, 2, 1, 5, 1, 1, 0, 5, 1, 1, 2, 1, 0, 5, 1],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 2, 2, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_95) = [
    ((721984440644994561, 432352187235303681), [5, 1, 1, 0]),
    ((720582563319906561, 433754064560391681), [5, 1, 1, 0]),
    ((720582563319906561, 720864016821715206), [1, 5, 0, 1]),
    ((721984440644994561, 432632562700321281), [5, 1, 1, 0]),
    ((721984440644994561, 432633662211948801), [5, 1, 1, 0]),
    ((721984440644994561, 721985518681785606), [1, 0, 5, 1]),
    ((721984440644994561, 722265894146803206), [1, 0, 5, 1]),
    ((721984440644994561, 722266993658430726), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_96 : List ℕ := [10, 6, 5, 1, 2, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_96 :
    checkTripleGroup 3 108 level4 tree5 base5_96
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_96 = [
    [5, 1, 0, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [5, 1, 1, 0, 1, 4, 5, 1, 5, 5, 4, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 4, 1, 1, 0, 1, 0],
    [5, 5, 4, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [5, 5, 5, 1, 1, 0, 1, 0, 5, 1, 0, 0, 1, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 0, 0, 1, 4, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_96) = [
    ((721984440644994561, 432352187235303681), [5, 1, 1, 0]),
    ((720582563319906561, 433754064560391681), [5, 1, 1, 0]),
    ((720582563319906561, 720864016821715206), [1, 5, 0, 1]),
    ((721984440644994561, 432632562700321281), [5, 1, 1, 0]),
    ((721984440644994561, 432633662211948801), [5, 1, 1, 0]),
    ((721984440644994561, 721985518681785606), [1, 0, 5, 1]),
    ((721984440644994561, 722265894146803206), [1, 0, 5, 1]),
    ((721984440644994561, 722266993658430726), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_97 : List ℕ := [10, 6, 6, 0, 1, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_97 :
    checkTripleGroup 3 108 level4 tree5 base5_97
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_97 = [
    [5, 1, 1, 0, 0, 5, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 0, 1, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_97) = [
    ((721984440644994561, 432352187235303681), [5, 1, 1, 0]),
    ((720582563319906561, 433754064560391681), [5, 1, 1, 0]),
    ((720582563319906561, 720864016821715206), [1, 5, 0, 1]),
    ((721984440644994561, 432632562700321281), [5, 1, 1, 0]),
    ((721984440644994561, 432633662211948801), [5, 1, 1, 0]),
    ((721984440644994561, 721985518681785606), [1, 0, 5, 1]),
    ((721984440644994561, 722265894146803206), [1, 0, 5, 1]),
    ((721984440644994561, 722266993658430726), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_98 : List ℕ := [10, 6, 6, 0, 2, 5, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_98 :
    checkTripleGroup 3 108 level4 tree5 base5_98
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_98 = [
    [5, 1, 1, 0, 1, 4, 5, 1, 5, 5, 5, 0, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 0, 1, 0, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_98) = [
    ((721984440644994561, 432352187235303681), [5, 1, 1, 0]),
    ((720582563319906561, 433754064560391681), [5, 1, 1, 0]),
    ((720582563319906561, 720864016821715206), [1, 5, 0, 1]),
    ((721984440644994561, 432632562700321281), [5, 1, 1, 0]),
    ((721984440644994561, 432633662211948801), [5, 1, 1, 0]),
    ((721984440644994561, 721985518681785606), [1, 0, 5, 1]),
    ((721984440644994561, 722265894146803206), [1, 0, 5, 1]),
    ((721984440644994561, 722266993658430726), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_99 : List ℕ := [10, 6, 6, 0, 2, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_99 :
    checkTripleGroup 3 108 level4 tree5 base5_99
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_99 = [
    [5, 1, 1, 0, 1, 5, 5, 0, 5, 5, 5, 0, 1, 1, 1, 0],
    [5, 5, 5, 0, 1, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_99) = [
    ((721985535861655041, 432352187235303936), [5, 1, 1, 0]),
    ((721985535861655041, 432633657916981761), [5, 1, 1, 0]),
    ((721985535861655041, 432633662211949056), [5, 1, 1, 0]),
    ((721985535861655041, 721985518681785861), [1, 0, 5, 1]),
    ((721985535861655041, 722266989363463686), [1, 0, 5, 1]),
    ((721985535861655041, 722266993658430981), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_100 : List ℕ := [10, 6, 6, 1, 1, 6, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_100 :
    checkTripleGroup 3 108 level4 tree5 base5_100
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_100 = [
    [5, 1, 1, 0, 1, 5, 5, 0, 5, 5, 5, 1, 0, 1, 1, 0],
    [5, 5, 5, 1, 0, 1, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 0, 5, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_100) = [
    ((720864034001649921, 720864016821780741), [1, 5, 0, 1]),
    ((720864034001649921, 433754064560457216), [5, 1, 1, 0]),
    ((720864038296617216, 720864016821780741), [1, 5, 0, 0]),
    ((722265911326737921, 432632562700386816), [5, 1, 1, 0]),
    ((721145508978295041, 721145491798425861), [1, 4, 0, 1]),
    ((722267010838365441, 432633657917047041), [5, 1, 0, 0]),
    ((722265911326737921, 432633657917047041), [5, 1, 1, 0]),
    ((720864034001649921, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035535242135041), [5, 0, 1, 0]),
    ((722267010838365441, 432632562700386816), [5, 1, 1, 0]),
    ((722265915621705216, 432633657917047041), [5, 1, 1, 0]),
    ((722267010838365441, 432633662212014336), [5, 1, 0, 0]),
    ((722265911326737921, 432633662212014336), [5, 1, 1, 0]),
    ((721145508978295041, 433754064560457216), [5, 1, 1, 0]),
    ((720864034001649921, 721145487503458566), [1, 5, 0, 1]),
    ((720864038296617216, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035539537102336), [5, 0, 1, 0]),
    ((720864034001649921, 434035539537102336), [5, 1, 1, 0]),
    ((721145508978295041, 720864016821780741), [1, 5, 0, 1]),
    ((721145508978295041, 721145487503458566), [1, 4, 0, 1]),
    ((720864038296617216, 721145491798425861), [1, 5, 0, 0]),
    ((720864034001649921, 721145491798425861), [1, 5, 0, 1]),
    ((722265911326737921, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722265894146868741), [1, 0, 5, 0]),
    ((722265911326737921, 722266989363528966), [1, 0, 5, 1]),
    ((722267010838365441, 722266989363528966), [1, 0, 4, 1]),
    ((722267010838365441, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722266993658496261), [1, 0, 5, 0]),
    ((722265911326737921, 722266993658496261), [1, 0, 5, 1]),
    ((722267010838365441, 722266993658496261), [1, 0, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_101 : List ℕ := [10, 6, 6, 1, 2, 5, 5, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_101 :
    checkTripleGroup 3 108 level4 tree5 base5_101
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_101 = [
    [5, 1, 1, 0, 1, 4, 5, 1, 5, 5, 5, 1, 1, 1, 0, 0],
    [5, 1, 1, 0, 1, 5, 4, 1, 5, 5, 5, 1, 1, 0, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 5, 5, 1, 1, 0, 0, 0],
    [5, 5, 5, 1, 1, 0, 1, 0, 5, 1, 1, 0, 1, 5, 4, 1],
    [5, 5, 5, 1, 1, 1, 0, 0, 5, 1, 1, 0, 1, 4, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 4, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_101) = [
    ((720864034001649921, 720864016821780741), [1, 5, 0, 1]),
    ((720864034001649921, 433754064560457216), [5, 1, 1, 0]),
    ((720864038296617216, 720864016821780741), [1, 5, 0, 0]),
    ((722265911326737921, 432632562700386816), [5, 1, 1, 0]),
    ((721145508978295041, 721145491798425861), [1, 4, 0, 1]),
    ((722267010838365441, 432633657917047041), [5, 1, 0, 0]),
    ((722265911326737921, 432633657917047041), [5, 1, 1, 0]),
    ((720864034001649921, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035535242135041), [5, 0, 1, 0]),
    ((722267010838365441, 432632562700386816), [5, 1, 1, 0]),
    ((722265915621705216, 432633657917047041), [5, 1, 1, 0]),
    ((722267010838365441, 432633662212014336), [5, 1, 0, 0]),
    ((722265911326737921, 432633662212014336), [5, 1, 1, 0]),
    ((721145508978295041, 433754064560457216), [5, 1, 1, 0]),
    ((720864034001649921, 721145487503458566), [1, 5, 0, 1]),
    ((720864038296617216, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035539537102336), [5, 0, 1, 0]),
    ((720864034001649921, 434035539537102336), [5, 1, 1, 0]),
    ((721145508978295041, 720864016821780741), [1, 5, 0, 1]),
    ((721145508978295041, 721145487503458566), [1, 4, 0, 1]),
    ((720864038296617216, 721145491798425861), [1, 5, 0, 0]),
    ((720864034001649921, 721145491798425861), [1, 5, 0, 1]),
    ((722265911326737921, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722265894146868741), [1, 0, 5, 0]),
    ((722265911326737921, 722266989363528966), [1, 0, 5, 1]),
    ((722267010838365441, 722266989363528966), [1, 0, 4, 1]),
    ((722267010838365441, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722266993658496261), [1, 0, 5, 0]),
    ((722265911326737921, 722266993658496261), [1, 0, 5, 1]),
    ((722267010838365441, 722266993658496261), [1, 0, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_102 : List ℕ := [10, 6, 6, 1, 2, 5, 6, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_102 :
    checkTripleGroup 3 108 level4 tree5 base5_102
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_102 = [
    [5, 1, 1, 0, 1, 5, 5, 0, 5, 5, 5, 1, 1, 0, 1, 0],
    [5, 5, 5, 1, 1, 0, 1, 0, 5, 1, 1, 0, 1, 5, 5, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 1, 4, 5, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_102) = [
    ((720864034001649921, 720864016821780741), [1, 5, 0, 1]),
    ((720864034001649921, 433754064560457216), [5, 1, 1, 0]),
    ((720864038296617216, 720864016821780741), [1, 5, 0, 0]),
    ((722265911326737921, 432632562700386816), [5, 1, 1, 0]),
    ((721145508978295041, 721145491798425861), [1, 4, 0, 1]),
    ((722267010838365441, 432633657917047041), [5, 1, 0, 0]),
    ((722265911326737921, 432633657917047041), [5, 1, 1, 0]),
    ((720864034001649921, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035535242135041), [5, 0, 1, 0]),
    ((722267010838365441, 432632562700386816), [5, 1, 1, 0]),
    ((722265915621705216, 432633657917047041), [5, 1, 1, 0]),
    ((722267010838365441, 432633662212014336), [5, 1, 0, 0]),
    ((722265911326737921, 432633662212014336), [5, 1, 1, 0]),
    ((721145508978295041, 433754064560457216), [5, 1, 1, 0]),
    ((720864034001649921, 721145487503458566), [1, 5, 0, 1]),
    ((720864038296617216, 434035535242135041), [5, 1, 1, 0]),
    ((721145508978295041, 434035539537102336), [5, 0, 1, 0]),
    ((720864034001649921, 434035539537102336), [5, 1, 1, 0]),
    ((721145508978295041, 720864016821780741), [1, 5, 0, 1]),
    ((721145508978295041, 721145487503458566), [1, 4, 0, 1]),
    ((720864038296617216, 721145491798425861), [1, 5, 0, 0]),
    ((720864034001649921, 721145491798425861), [1, 5, 0, 1]),
    ((722265911326737921, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722265894146868741), [1, 0, 5, 0]),
    ((722265911326737921, 722266989363528966), [1, 0, 5, 1]),
    ((722267010838365441, 722266989363528966), [1, 0, 4, 1]),
    ((722267010838365441, 722265894146868741), [1, 0, 5, 1]),
    ((722265915621705216, 722266993658496261), [1, 0, 5, 0]),
    ((722265911326737921, 722266993658496261), [1, 0, 5, 1]),
    ((722267010838365441, 722266993658496261), [1, 0, 4, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_103 : List ℕ := [10, 6, 6, 1, 6, 3, 3, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_103 :
    checkTripleGroup 3 108 level4 tree5 base5_103
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_103 = [
    [5, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 2, 2, 1],
    [5, 5, 5, 1, 1, 2, 2, 1, 5, 1, 1, 0, 5, 1, 1, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 5, 1, 1, 0, 5, 2, 2, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_103) = [
    ((722268101760058881, 722268093170124291), [1, 0, 5, 1]),
    ((722268101760058881, 722266993658496771), [1, 0, 5, 1]),
    ((938440875233576451, 722268101760058881), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_104 : List ℕ := [11, 3, 6, 1, 2, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_104 :
    checkTripleGroup 3 108 level4 tree5 base5_104
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_104 = [
    [5, 1, 1, 0, 1, 5, 5, 1, 6, 2, 5, 1, 1, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_104) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_105 : List ℕ := [11, 6, 2, 3, 6, 1, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_105 :
    checkTripleGroup 3 108 level4 tree5 base5_105
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_105 = [
    [6, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 2, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_105) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_106 : List ℕ := [11, 6, 6, 2, 6, 2, 2, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_106 :
    checkTripleGroup 3 108 level4 tree5 base5_106
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_106 = [
    [6, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 1, 1, 1, 1, 1],
    [6, 5, 5, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_106) = [
    ((794328990037967361, 794328985743000066), [1, 1, 1, 1]),
    ((794328990037967361, 794328990037967361), [1, 1, 1, 0])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_107 : List ℕ := [13, 3, 3, 1, 3, 6, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_107 :
    checkTripleGroup 3 108 level4 tree5 base5_107
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_107 = [
    [5, 1, 1, 0, 1, 5, 5, 1, 8, 2, 2, 1, 2, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_107) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_108 : List ℕ := [13, 3, 6, 1, 3, 6, 3, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_108 :
    checkTripleGroup 3 108 level4 tree5 base5_108
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_108 = [
    [8, 2, 5, 1, 2, 1, 1, 0, 5, 1, 1, 0, 1, 5, 2, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_108) = [
    ((722268101760058881, 722268093170124291), [1, 0, 5, 1]),
    ((722268101760058881, 722266993658496771), [1, 0, 5, 1]),
    ((938440875233576451, 722268101760058881), [1, 0, 5, 1])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_109 : List ℕ := [13, 6, 3, 1, 3, 1, 6, 3]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_109 :
    checkTripleGroup 3 108 level4 tree5 base5_109
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_109 = [
    [8, 5, 2, 1, 2, 1, 1, 2, 5, 1, 1, 0, 1, 0, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_109) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base5_110 : List ℕ := [13, 6, 3, 1, 3, 3, 6, 1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check5_110 :
    checkTripleGroup 3 108 level4 tree5 base5_110
      (keepRemaining 3 tree4) = true := by
  have hgroup : sharedGroup 3 level4 base5_110 = [
    [8, 5, 2, 1, 2, 1, 1, 0, 5, 1, 1, 0, 1, 2, 5, 1]] := by
    decide +kernel
  have hthird : thirdRows 3 (thirdsAt 3 level4 base5_110) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def bases5 : List (List ℕ) := [
  base5_0, base5_1, base5_2, base5_3, base5_4, base5_5, base5_6, base5_7, base5_8, base5_9,
  base5_10, base5_11, base5_12, base5_13, base5_14, base5_15, base5_16, base5_17, base5_18,
  base5_19, base5_20, base5_21, base5_22, base5_23, base5_24, base5_25, base5_26, base5_27,
  base5_28, base5_29, base5_30, base5_31, base5_32, base5_33, base5_34, base5_35, base5_36,
  base5_37, base5_38, base5_39, base5_40, base5_41, base5_42, base5_43, base5_44, base5_45,
  base5_46, base5_47, base5_48, base5_49, base5_50, base5_51, base5_52, base5_53, base5_54,
  base5_55, base5_56, base5_57, base5_58, base5_59, base5_60, base5_61, base5_62, base5_63,
  base5_64, base5_65, base5_66, base5_67, base5_68, base5_69, base5_70, base5_71, base5_72,
  base5_73, base5_74, base5_75, base5_76, base5_77, base5_78, base5_79, base5_80, base5_81,
  base5_82, base5_83, base5_84, base5_85, base5_86, base5_87, base5_88, base5_89, base5_90,
  base5_91, base5_92, base5_93, base5_94, base5_95, base5_96, base5_97, base5_98, base5_99,
  base5_100, base5_101, base5_102, base5_103, base5_104, base5_105, base5_106, base5_107,
  base5_108, base5_109, base5_110]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem covers5 :
    (level4.map (dropAxis 3 3)).all bases5.contains = true := by
  decide +kernel

private theorem check5 :
    bases5.all (fun base => checkTripleGroup 3 108 level4 tree5 base
      (keepRemaining 3 tree4)) = true := by
  simp only [bases5, List.all_cons, List.all_nil, Bool.and_self,
    check5_0, check5_1, check5_2, check5_3, check5_4, check5_5, check5_6, check5_7, check5_8,
    check5_9, check5_10, check5_11, check5_12, check5_13, check5_14, check5_15, check5_16,
    check5_17, check5_18, check5_19, check5_20, check5_21, check5_22, check5_23, check5_24,
    check5_25, check5_26, check5_27, check5_28, check5_29, check5_30, check5_31, check5_32,
    check5_33, check5_34, check5_35, check5_36, check5_37, check5_38, check5_39, check5_40,
    check5_41, check5_42, check5_43, check5_44, check5_45, check5_46, check5_47, check5_48,
    check5_49, check5_50, check5_51, check5_52, check5_53, check5_54, check5_55, check5_56,
    check5_57, check5_58, check5_59, check5_60, check5_61, check5_62, check5_63, check5_64,
    check5_65, check5_66, check5_67, check5_68, check5_69, check5_70, check5_71, check5_72,
    check5_73, check5_74, check5_75, check5_76, check5_77, check5_78, check5_79, check5_80,
    check5_81, check5_82, check5_83, check5_84, check5_85, check5_86, check5_87, check5_88,
    check5_89, check5_90, check5_91, check5_92, check5_93, check5_94, check5_95, check5_96,
    check5_97, check5_98, check5_99, check5_100, check5_101, check5_102, check5_103,
    check5_104, check5_105, check5_106, check5_107, check5_108, check5_109, check5_110]

private def base6_0 : List ℕ := [0, 5, 5, 1, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_0 :
    checkTripleGroup 4 108 level5 tree6 base6_0
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_0 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_0) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_1 : List ℕ := [0, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_1 :
    checkTripleGroup 4 108 level5 tree6 base6_1
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_1 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_1) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_2 : List ℕ := [0, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_2 :
    checkTripleGroup 4 108 level5 tree6 base6_2
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_2 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_2) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_3 : List ℕ := [1, 4, 5, 1, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_3 :
    checkTripleGroup 4 108 level5 tree6 base6_3
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_3 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_3) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_4 : List ℕ := [1, 4, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_4 :
    checkTripleGroup 4 108 level5 tree6 base6_4
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_4 = [
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_4) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_5 : List ℕ := [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 4, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_5 :
    checkTripleGroup 4 108 level5 tree6 base6_5
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_5 = [
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_5) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_6 : List ℕ := [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_6 :
    checkTripleGroup 4 108 level5 tree6 base6_6
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_6 = [
    [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_6) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_7 : List ℕ := [1, 4, 5, 1, 5, 1, 1, 0, 1, 5, 5, 1, 5, 1, 0, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_7 :
    checkTripleGroup 4 108 level5 tree6 base6_7
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_7 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 3, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_7) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_8 : List ℕ := [1, 5, 4, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_8 :
    checkTripleGroup 4 108 level5 tree6 base6_8
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_8 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_8) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_9 : List ℕ := [1, 5, 4, 1, 5, 1, 1, 0, 1, 5, 5, 1, 5, 0, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_9 :
    checkTripleGroup 4 108 level5 tree6 base6_9
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_9 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0, 1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 3, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_9) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_10 : List ℕ := [1, 5, 5, 0, 5, 1, 1, 0, 0, 5, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_10 :
    checkTripleGroup 4 108 level5 tree6 base6_10
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_10 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_10) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_11 : List ℕ := [1, 5, 5, 0, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_11 :
    checkTripleGroup 4 108 level5 tree6 base6_11
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_11 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_11) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_12 : List ℕ := [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_12 :
    checkTripleGroup 4 108 level5 tree6 base6_12
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_12 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_12) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_13 : List ℕ := [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 1, 4, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_13 :
    checkTripleGroup 4 108 level5 tree6 base6_13
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_13 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 3, 1, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 3, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_13) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_14 : List ℕ := [1, 5, 5, 0, 5, 1, 1, 0, 1, 5, 5, 1, 5, 0, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_14 :
    checkTripleGroup 4 108 level5 tree6 base6_14
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_14 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0, 1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 0, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_14) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_15 : List ℕ := [1, 5, 5, 1, 4, 1, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_15 :
    checkTripleGroup 4 108 level5 tree6 base6_15
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_15 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 3, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 3, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_15) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_16 : List ℕ := [1, 5, 5, 1, 5, 0, 1, 0, 1, 5, 4, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_16 :
    checkTripleGroup 4 108 level5 tree6 base6_16
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_16 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_16) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_17 : List ℕ := [1, 5, 5, 1, 5, 0, 1, 0, 1, 5, 5, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_17 :
    checkTripleGroup 4 108 level5 tree6 base6_17
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_17 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_17) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_18 : List ℕ := [1, 5, 5, 1, 5, 1, 0, 0, 1, 4, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_18 :
    checkTripleGroup 4 108 level5 tree6 base6_18
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_18 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_18) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_19 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 0, 4, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_19 :
    checkTripleGroup 4 108 level5 tree6 base6_19
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_19 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 1, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 3, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_19) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_20 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 0, 5, 5, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_20 :
    checkTripleGroup 4 108 level5 tree6 base6_20
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_20 = [
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_20) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_21 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 3, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_21 :
    checkTripleGroup 4 108 level5 tree6 base6_21
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_21 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 2, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_21) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_22 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 4, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_22 :
    checkTripleGroup 4 108 level5 tree6 base6_22
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_22 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 3, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_22) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_23 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_23 :
    checkTripleGroup 4 108 level5 tree6 base6_23
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_23 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_23) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_24 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 4, 5, 1, 5, 1, 0, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_24 :
    checkTripleGroup 4 108 level5 tree6 base6_24
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_24 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 1, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 3, 4, 1, 4, 1, 0, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_24) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_25 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 4, 1, 5, 0, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_25 :
    checkTripleGroup 4 108 level5 tree6 base6_25
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_25 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 1, 4, 0, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 3, 1, 4, 0, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_25) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_26 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 4, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_26 :
    checkTripleGroup 4 108 level5 tree6 base6_26
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_26 = [
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0, 1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 1, 1, 0],
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 3, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_26) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_27 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 5, 5, 0, 5, 0, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_27 :
    checkTripleGroup 4 108 level5 tree6 base6_27
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_27 = [
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 4, 4, 0, 4, 0, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_27) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_28 : List ℕ := [2, 5, 5, 1, 5, 1, 1, 0, 1, 2, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_28 :
    checkTripleGroup 4 108 level5 tree6 base6_28
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_28 = [
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 4, 1, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_28) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_29 : List ℕ := [5, 2, 5, 1, 5, 1, 1, 0, 1, 5, 2, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_29 :
    checkTripleGroup 4 108 level5 tree6 base6_29
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_29 = [
    [4, 1, 1, 0, 1, 0, 0, 0, 1, 4, 1, 1, 4, 1, 1, 0, 1, 1, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_29) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_30 : List ℕ := [5, 5, 2, 1, 5, 1, 1, 0, 1, 2, 5, 1, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_30 :
    checkTripleGroup 4 108 level5 tree6 base6_30
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_30 = [
    [4, 1, 1, 0, 1, 0, 0, 0, 1, 1, 4, 1, 4, 1, 1, 0, 1, 4, 1, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_30) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_31 : List ℕ := [5, 5, 5, 1, 1, 2, 2, 1, 5, 1, 1, 0, 5, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_31 :
    checkTripleGroup 4 108 level5 tree6 base6_31
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_31 = [
    [1, 4, 4, 1, 0, 1, 1, 0, 4, 1, 1, 0, 1, 0, 0, 0, 4, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 4, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_31) = [] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def base6_32 : List ℕ := [6, 5, 5, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem check6_32 :
    checkTripleGroup 4 108 level5 tree6 base6_32
      (keepRemaining 4 tree5) = true := by
  have hgroup : sharedGroup 4 level5 base6_32 = [
    [2, 4, 4, 1, 4, 1, 1, 0, 4, 1, 1, 0, 1, 0, 0, 0, 4, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0]] := by
    decide +kernel
  have hthird : thirdRows 4 (thirdsAt 4 level5 base6_32) = [
    ((8001430951826988864282089638271713536, 8001430951826988845835345564562161921), [1, 0, 0, 1, 0, 1, 1, 0])] := by
    decide +kernel
  unfold checkTripleGroup
  rw [hgroup, hthird]
  repeat
    refine all_cons_true ?_ ?_
    · decide +kernel
  rfl

private def bases6 : List (List ℕ) := [
  base6_0, base6_1, base6_2, base6_3, base6_4, base6_5, base6_6, base6_7, base6_8, base6_9,
  base6_10, base6_11, base6_12, base6_13, base6_14, base6_15, base6_16, base6_17, base6_18,
  base6_19, base6_20, base6_21, base6_22, base6_23, base6_24, base6_25, base6_26, base6_27,
  base6_28, base6_29, base6_30, base6_31, base6_32]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem covers6 :
    (level5.map (dropAxis 4 4)).all bases6.contains = true := by
  decide +kernel

private theorem check6 :
    bases6.all (fun base => checkTripleGroup 4 108 level5 tree6 base
      (keepRemaining 4 tree5)) = true := by
  simp only [bases6, List.all_cons, List.all_nil, Bool.and_self,
    check6_0, check6_1, check6_2, check6_3, check6_4, check6_5, check6_6, check6_7, check6_8,
    check6_9, check6_10, check6_11, check6_12, check6_13, check6_14, check6_15, check6_16,
    check6_17, check6_18, check6_19, check6_20, check6_21, check6_22, check6_23, check6_24,
    check6_25, check6_26, check6_27, check6_28, check6_29, check6_30, check6_31, check6_32]

private theorem covers2 :
    (level1.map (dropAxis 0 0)).all ([[36]] : List (List ℕ)).contains = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- The ordered six-axis projection constraints at closed neighborhood cap 108
have no 36-vertex table. -/
theorem excludeOrdered36 (counts : List ℕ) (hlen : counts.length = 2 ^ 6)
    (hsum : counts.sum = 36) (hcap : ∀ x ∈ counts, x ≤ 2 ^ (8 - 6))
    (hproj : ProjectionConstraints 36 108 6 counts) (horder : OrderedProjections 6 counts) :
    False := by
  have h1 : ∀ t : List ℕ, t.length = 2 ^ 1 → t.sum = 36 →
      (∀ x ∈ t, x ≤ 2 ^ (8 - 1)) → ProjectionConstraints 36 108 1 t →
      OrderedProjections 1 t → t ∈ level1 :=
    fun t hl hs hc hp _ => singles_complete _ _ t hl hs hc hp
  have h2 := complete_of_step (cap := 108) 0 (by decide) level1 level2 h1
    (checkedStep (covers_bases covers2) check2)
  have h3 := complete_of_step (cap := 108) 1 (by decide) level2 level3 h2
    (checkedTripleStep (by decide) (covers_bases covers3) check3
      (fun _ hc => keepRemaining_of_children coversKeys2 hc))
  have h4 := complete_of_step (cap := 108) 2 (by decide) level3 level4 h3
    (checkedTripleStep (by decide) (covers_bases covers4) check4
      (fun _ hc => keepRemaining_of_children coversKeys3 hc))
  have h5 := complete_of_step (cap := 108) 3 (by decide) level4 level5 h4
    (checkedTripleStep (by decide) (covers_bases covers5) check5
      (fun _ hc => keepRemaining_of_children coversKeys4 hc))
  have h6 := complete_of_step (cap := 108) 4 (by decide) level5 level6 h5
    (checkedTripleStep (by decide) (covers_bases covers6) check6
      (fun _ hc => keepRemaining_of_children coversKeys5 hc))
  exact List.not_mem_nil (h6 counts hlen hsum hcap hproj horder)

#print axioms excludeOrdered36

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrderedFiberCapacity108
