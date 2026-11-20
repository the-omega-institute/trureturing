/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q8FourFiberCapacityCertificate
   generality: I
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Four projected fibre count tables force a larger Q8 neighbourhood at sizes 36 and 39. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeClosedNeighborhoodRecurrence

/-! Tables are in increasing binary pattern order, with axis zero the least
significant bit. The search joins two projections along their common marginal.
For each common pattern it enumerates the possible counts in the intersection of
the two 1-sides. -/

set_option autoImplicit false

open private table table_eq_h from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeClosedNeighborhoodRecurrence

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q8FourFiberCapacityCertificate

open CubeClosedNeighborhoodRecurrence (h)

/-- Delete an axis and add the two counts above every remaining bit pattern.
The argument `d` is the number of remaining axes. -/
def dropAxis : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, counts => List.zipWith (· + ·) (counts.take 1) (counts.drop 1)
  | d + 1, axis, counts =>
      let low := counts.take (2 ^ (d + 1))
      let high := counts.drop (2 ^ (d + 1))
      if axis = d + 1 then List.zipWith (· + ·) low high
      else dropAxis d axis low ++ dropAxis d axis high

private def costWith (floor : ℕ → ℕ) (d : ℕ) (counts : List ℕ) : ℕ :=
  let values := counts.toArray
  ((List.range (2 ^ d)).map fun p =>
    (List.range d).foldl (fun bound i => max bound values[p ^^^ (2 ^ i)]!)
      (floor values[p]!)).sum

/-- The sum of the recurrence bound and adjacent-fibre bounds, taking their
maximum separately at each pattern. -/
def neighborhoodCost (d : ℕ) (counts : List ℕ) : ℕ :=
  costWith (h (8 - d)) d counts

/-- Every nonempty projection meets the cost cap. At each one-axis leaf, the
count on the 1-side lies between 11 and half the total. The root is included. -/
def ProjectionConstraints (total cap : ℕ) : ℕ → List ℕ → Prop
  | 0, _ => True
  | d + 1, counts =>
      neighborhoodCost (d + 1) counts ≤ cap ∧
      (if d = 0 then 11 ≤ counts[1]! ∧ counts[1]! ≤ total / 2 else True) ∧
      ∀ axis : Fin (d + 1), ProjectionConstraints total cap d (dropAxis d axis counts)

private theorem dropAxis_last (d : ℕ) (counts : List ℕ) :
    dropAxis d d counts = List.zipWith (· + ·) (counts.take (2 ^ d)) (counts.drop (2 ^ d)) := by
  cases d <;> simp [dropAxis]

private theorem zipWith_add_spec (a b : List ℕ) (hlen : a.length = b.length) :
    (List.zipWith (· + ·) a b).sum = a.sum + b.sum ∧
      ∀ cap, (∀ x ∈ a, x ≤ cap) → (∀ x ∈ b, x ≤ cap) →
        ∀ x ∈ List.zipWith (· + ·) a b, x ≤ cap + cap := by
  induction a generalizing b with
  | nil =>
      have hb : b = [] := List.eq_nil_of_length_eq_zero hlen.symm
      simp [hb]
  | cons x a ih =>
      cases b with
      | nil => simp at hlen
      | cons y b =>
          have htail := ih b (by simpa using hlen)
          constructor
          · simp only [List.zipWith_cons_cons, List.sum_cons, htail.1]
            omega
          · intro cap ha hb z hz
            simp only [List.zipWith_cons_cons, List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact Nat.add_le_add (ha x (by simp)) (hb y (by simp))
            · exact htail.2 cap (fun w hw => ha w (by simp [hw]))
                (fun w hw => hb w (by simp [hw])) z hz

private theorem dropAxis_spec (d axis : ℕ) (counts : List ℕ)
    (hlen : counts.length = 2 ^ (d + 1)) :
    (dropAxis d axis counts).length = 2 ^ d ∧
    (dropAxis d axis counts).sum = counts.sum ∧
    ∀ cap, (∀ x ∈ counts, x ≤ cap) → ∀ x ∈ dropAxis d axis counts, x ≤ cap + cap := by
  have halfLengths (d : ℕ) (counts : List ℕ) (hlen : counts.length = 2 ^ (d + 1)) :
      (counts.take (2 ^ d)).length = 2 ^ d ∧ (counts.drop (2 ^ d)).length = 2 ^ d := by
    simp only [List.length_take, List.length_drop, hlen, pow_succ]
    omega
  have last (d : ℕ) (counts : List ℕ) (hlen : counts.length = 2 ^ (d + 1))
      (he : dropAxis d axis counts =
        List.zipWith (· + ·) (counts.take (2 ^ d)) (counts.drop (2 ^ d))) :
      (dropAxis d axis counts).length = 2 ^ d ∧
      (dropAxis d axis counts).sum = counts.sum ∧
      ∀ cap, (∀ x ∈ counts, x ≤ cap) → ∀ x ∈ dropAxis d axis counts, x ≤ cap + cap := by
    rw [he]
    obtain ⟨takeLen, dropLen⟩ := halfLengths d counts hlen
    have z := zipWith_add_spec _ _ (takeLen.trans dropLen.symm)
    refine ⟨by simp [List.length_zipWith, takeLen, dropLen], ?_, ?_⟩
    · rw [z.1, ← List.sum_append, List.take_append_drop]
    · exact fun cap hc => z.2 cap (fun x hx => hc x (List.mem_of_mem_take hx))
        (fun x hx => hc x (List.mem_of_mem_drop hx))
  induction d generalizing counts with
  | zero => exact last 0 counts hlen rfl
  | succ d ih =>
      by_cases ha : axis = d + 1
      · exact last _ counts hlen (by simp [dropAxis, ha])
      · dsimp only [dropAxis]
        rw [ite_eq_right ha]
        obtain ⟨takeLen, dropLen⟩ := halfLengths (d + 1) counts hlen
        obtain ⟨ll, ls, lc⟩ := ih _ takeLen
        obtain ⟨rl, rs, rc⟩ := ih _ dropLen
        refine ⟨by rw [List.length_append, ll, rl, pow_succ, Nat.mul_two], ?_, ?_⟩
        · rw [List.sum_append, ls, rs, ← List.sum_append, List.take_append_drop]
        · intro cap hc x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact lc cap (fun y hy => hc y (List.mem_of_mem_take hy)) x hx
          · exact rc cap (fun y hy => hc y (List.mem_of_mem_drop hy)) x hx

private def lookupCost (d : ℕ) (counts : List ℕ) : ℕ :=
  costWith (table (8 - d)) d counts

-- Unroll the fixed-width costs used in closed decisions. The fallback also
-- makes the equality valid for arbitrary dimensions and list lengths.
private def fastCost : ℕ → List ℕ → ℕ
  | 1, [c0, c1] =>
      max (table 7 c0) c1 + (
      max (table 7 c1) c0 + 0)
  | 2, [c0, c1, c2, c3] =>
      max (max (table 6 c0) c1) c2 + (
      max (max (table 6 c1) c0) c3 + (
      max (max (table 6 c2) c3) c0 + (
      max (max (table 6 c3) c2) c1 + 0)))
  | 3, [c0, c1, c2, c3, c4, c5, c6, c7] =>
      max (max (max (table 5 c0) c1) c2) c4 + (
      max (max (max (table 5 c1) c0) c3) c5 + (
      max (max (max (table 5 c2) c3) c0) c6 + (
      max (max (max (table 5 c3) c2) c1) c7 + (
      max (max (max (table 5 c4) c5) c6) c0 + (
      max (max (max (table 5 c5) c4) c7) c1 + (
      max (max (max (table 5 c6) c7) c4) c2 + (
      max (max (max (table 5 c7) c6) c5) c3 + 0)))))))
  | 4, [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] =>
      max (max (max (max (table 4 c0) c1) c2) c4) c8 + (
      max (max (max (max (table 4 c1) c0) c3) c5) c9 + (
      max (max (max (max (table 4 c2) c3) c0) c6) c10 + (
      max (max (max (max (table 4 c3) c2) c1) c7) c11 + (
      max (max (max (max (table 4 c4) c5) c6) c0) c12 + (
      max (max (max (max (table 4 c5) c4) c7) c1) c13 + (
      max (max (max (max (table 4 c6) c7) c4) c2) c14 + (
      max (max (max (max (table 4 c7) c6) c5) c3) c15 + (
      max (max (max (max (table 4 c8) c9) c10) c12) c0 + (
      max (max (max (max (table 4 c9) c8) c11) c13) c1 + (
      max (max (max (max (table 4 c10) c11) c8) c14) c2 + (
      max (max (max (max (table 4 c11) c10) c9) c15) c3 + (
      max (max (max (max (table 4 c12) c13) c14) c8) c4 + (
      max (max (max (max (table 4 c13) c12) c15) c9) c5 + (
      max (max (max (max (table 4 c14) c15) c12) c10) c6 + (
      max (max (max (max (table 4 c15) c14) c13) c11) c7 + 0)))))))))))))))
  | d, counts => lookupCost d counts

private theorem fastCost_eq (d : ℕ) (counts : List ℕ) :
    fastCost d counts = lookupCost d counts := by
  unfold fastCost
  split <;> rfl

private theorem lookupCost_eq (d : ℕ) (counts : List ℕ) (hd : 1 ≤ d)
    (hc : ∀ x ∈ counts, x ≤ 2 ^ (8 - d)) :
    fastCost d counts = neighborhoodCost d counts := by
  rw [fastCost_eq]
  dsimp only [lookupCost, neighborhoodCost, costWith]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  have hp : counts.toArray[p]! ≤ 2 ^ (8 - d) := by
    by_cases hi : p < counts.length
    · rw [getElem!_pos _ _ (by simpa using hi)]
      exact hc _ (List.getElem_mem hi)
    · rw [getElem!_neg _ _ (by simpa using hi)]
      exact Nat.zero_le _
  rw [table_eq_h (by omega) hp]

private abbrev Blocks := List ℕ × List ℕ × List ℕ × List ℕ

private def overlap (base left right : ℕ) : List ℕ :=
  let low := left + right - base
  List.range' low (min left right + 1 - low)

private theorem overlap_complete (a b c e : ℕ) :
    e ∈ overlap ((a + b) + (c + e)) (b + e) (c + e) := by
  simp only [overlap, List.mem_range'_1]
  omega

-- Work one common pattern at a time so a fibre exceeding capacity kills
-- the branch before a full table is constructed.
private def glue (capacity : ℕ) : List ℕ → List ℕ → List ℕ → List Blocks
  | [], [], [] => [([], [], [], [])]
  | base :: bases, left :: lefts, right :: rights =>
      (overlap base left right).flatMap fun both =>
        let neither := base + both - (left + right)
        let onlyLeft := left - both
        let onlyRight := right - both
        if max (max neither onlyLeft) (max onlyRight both) ≤ capacity then
          (glue capacity bases lefts rights).map fun (a, b, c, e) =>
            (neither :: a, onlyLeft :: b, onlyRight :: c, both :: e)
        else []
  | _, _, _ => []

private theorem glue_complete (capacity : ℕ) (a b c e : List ℕ)
    (hb : b.length = a.length) (hc : c.length = a.length) (he : e.length = a.length)
    (hcap : ∀ x ∈ a ++ b ++ c ++ e, x ≤ capacity) :
    (a, b, c, e) ∈ glue capacity
      (List.zipWith (· + ·) (List.zipWith (· + ·) a b) (List.zipWith (· + ·) c e))
      (List.zipWith (· + ·) b e) (List.zipWith (· + ·) c e) := by
  induction a generalizing b c e with
  | nil =>
      have hb' : b = [] := List.eq_nil_of_length_eq_zero hb
      have hc' : c = [] := List.eq_nil_of_length_eq_zero hc
      have he' : e = [] := List.eq_nil_of_length_eq_zero he
      simp [hb', hc', he', glue]
  | cons x a ih =>
      cases b with
      | nil => simp at hb
      | cons y b =>
        cases c with
        | nil => simp at hc
        | cons z c =>
          cases e with
          | nil => simp at he
          | cons w e =>
            simp only [List.zipWith_cons_cons, glue]
            apply List.mem_flatMap.mpr
            refine ⟨w, overlap_complete x y z w, ?_⟩
            rw [show (x + y + (z + w)) + w - ((y + w) + (z + w)) = x by omega,
              Nat.add_sub_cancel, Nat.add_sub_cancel, ite_eq_left]
            · exact List.mem_map.mpr ⟨(a, b, c, e),
                ih _ _ _ (by simpa using hb) (by simpa using hc) (by simpa using he)
                  (fun u hu => hcap u (by simpa using
                    (show u ∈ (x :: a) ++ (y :: b) ++ (z :: c) ++ (w :: e) by
                      simp only [List.mem_append, List.mem_cons] at hu ⊢
                      tauto))), rfl⟩
            · simp only [max_le_iff]
              exact ⟨⟨hcap x (by simp), hcap y (by simp)⟩,
                hcap z (by simp), hcap w (by simp)⟩

private def joinPair (d cap : ℕ) (left right : List ℕ) : List (List ℕ) :=
  let width := 2 ^ d
  let base := dropAxis d d left
  if base = dropAxis d d right then
    (glue (2 ^ (8 - (d + 2))) base (left.drop width) (right.drop width)).filterMap
      fun (a, b, c, e) =>
        let counts := a ++ b ++ c ++ e
        if fastCost (d + 2) counts ≤ cap then some counts else none
  else []

private def extend (d cap : ℕ) (previous : List (List ℕ)) : List (List ℕ) :=
  previous.flatMap fun left => previous.flatMap fun right => joinPair d cap left right

private def singles (total cap : ℕ) : List (List ℕ) :=
  (List.range' 11 (total / 2 + 1 - 11)).filterMap fun side =>
    let counts := [total - side, side]
    if fastCost 1 counts ≤ cap then some counts else none

private theorem singles_complete (total cap : ℕ) (counts : List ℕ)
    (hlen : counts.length = 2) (hsum : counts.sum = total)
    (hcap : ∀ x ∈ counts, x ≤ 128) (hcost : ProjectionConstraints total cap 1 counts) :
    counts ∈ singles total cap := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℕ, counts = [x, y] := by
    cases counts with
    | nil => simp at hlen
    | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
        cases ys with
        | nil => exact ⟨x, y, rfl⟩
        | cons z zs => simp at hlen
  have hm : 11 ≤ y ∧ y ≤ total / 2 := hcost.2.1
  have hlookup : fastCost 1 [x, y] ≤ cap := by
    rw [lookupCost_eq _ _ (by decide) hcap]
    exact hcost.1
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
  have hx : total - y = x := by omega
  apply List.mem_filterMap.mpr
  refine ⟨y, ?_, ?_⟩
  · simp only [List.mem_range'_1]
    omega
  · simp [hx, hlookup]

private theorem zipWith_add_cross (a b c e : List ℕ) :
    List.zipWith (· + ·) (List.zipWith (· + ·) a c) (List.zipWith (· + ·) b e) =
    List.zipWith (· + ·) (List.zipWith (· + ·) a b) (List.zipWith (· + ·) c e) := by
  induction a generalizing b c e with
  | nil => simp
  | cons x a ih =>
      cases b <;> cases c <;> cases e <;> simp [ih, add_left_comm, add_comm]

private theorem joinPair_complete (d cap : ℕ) (counts : List ℕ)
    (hlen : counts.length = 2 ^ (d + 2)) (hcost : neighborhoodCost (d + 2) counts ≤ cap)
    (hcount : ∀ x ∈ counts, x ≤ 2 ^ (8 - (d + 2))) :
    counts ∈ joinPair d cap (dropAxis (d + 1) (d + 1) counts) (dropAxis (d + 1) d counts) := by
  let w := 2 ^ d
  let low := counts.take (w + w)
  let high := counts.drop (w + w)
  let a := low.take w
  let b := low.drop w
  let c := high.take w
  let e := high.drop w
  have hlen' : counts.length = w + w + (w + w) := by
    rw [hlen, show d + 2 = (d + 1) + 1 by rfl, pow_succ, pow_succ]
    simp [w, Nat.mul_two]
  have hl : low.length = w + w := by simp [low, hlen']
  have hh : high.length = w + w := by simp [high, hlen']
  have ha : a.length = 2 ^ d := by change a.length = w; simp [a, hl]
  have hb : b.length = 2 ^ d := by change b.length = w; simp [b, hl]
  have hc : c.length = 2 ^ d := by change c.length = w; simp [c, hh]
  have he : e.length = 2 ^ d := by change e.length = w; simp [e, hh]
  have hlow : a ++ b = low := List.take_append_drop w low
  have hhigh : c ++ e = high := List.take_append_drop w high
  have hsplit : (a ++ b) ++ (c ++ e) = counts := by
    rw [hlow, hhigh]
    exact List.take_append_drop _ _
  let add : List ℕ → List ℕ → List ℕ := List.zipWith (· + ·)
  have htake : counts.take (2 ^ (d + 1)) = a ++ b := by
    rw [hlow, pow_succ, Nat.mul_two]
  have hdrop : counts.drop (2 ^ (d + 1)) = c ++ e := by
    rw [hhigh, pow_succ, Nat.mul_two]
  have hleft : dropAxis (d + 1) (d + 1) counts = add a c ++ add b e := by
    rw [dropAxis_last, htake, hdrop, List.zipWith_append (ha.trans hc.symm)]
  have hright : dropAxis (d + 1) d counts = add a b ++ add c e := by
    simp [dropAxis, htake, hdrop, dropAxis_last, List.take_left' ha, List.drop_left' ha,
      List.take_left' hc, List.drop_left' hc, add]
  have addLen (u v : List ℕ) (hu : u.length = w) (hv : v.length = w) :
      (add u v).length = 2 ^ d := by
    change (add u v).length = w
    simp [add, List.length_zipWith, hu, hv]
  have hlenAC := addLen a c ha hc
  have hlenAB := addLen a b ha hb
  have hbase : add (add a c) (add b e) = add (add a b) (add c e) := zipWith_add_cross _ _ _ _
  have hcounts : a ++ b ++ c ++ e = counts := by simpa only [List.append_assoc] using hsplit
  simp only [hleft, hright, joinPair, dropAxis_last, List.take_left' hlenAC,
    List.drop_left' hlenAC, List.take_left' hlenAB, List.drop_left' hlenAB]
  change counts ∈ (if add (add a c) (add b e) = add (add a b) (add c e) then _ else [])
  rw [ite_eq_left hbase]
  apply List.mem_filterMap.mpr
  refine ⟨(a, b, c, e), ?_, ?_⟩
  · dsimp only [add] at hbase
    rw [hbase]
    exact glue_complete _ _ _ _ _ (hb.trans ha.symm) (hc.trans ha.symm) (he.trans ha.symm)
      (hcounts.symm ▸ hcount)
  · have hlookup : fastCost (d + 2) counts ≤ cap := by
      rw [lookupCost_eq _ _ (by omega) hcount]
      exact hcost
    have hassoc : a ++ (b ++ (c ++ e)) = counts := by
      simpa only [List.append_assoc] using hcounts
    simp [hassoc, hlookup]

private def candidates (total cap : ℕ) : ℕ → List (List ℕ)
  | 0 => []
  | 1 => singles total cap
  | d + 2 => extend d cap (candidates total cap (d + 1))

private theorem candidates_complete (total cap d : ℕ) (counts : List ℕ)
    (hd : 1 ≤ d) (hd' : d ≤ 4)
    (hlen : counts.length = 2 ^ d) (hsum : counts.sum = total)
    (hcount : ∀ x ∈ counts, x ≤ 2 ^ (8 - d))
    (hcost : ProjectionConstraints total cap d counts) :
    counts ∈ candidates total cap d := by
  induction d generalizing counts with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero => exact singles_complete _ _ _ hlen hsum hcount hcost
    | succ k =>
      have powDouble : 2 ^ (8 - (k + 1)) =
          2 ^ (8 - (k + 2)) + 2 ^ (8 - (k + 2)) := by
        rw [show 8 - (k + 1) = (8 - (k + 2)) + 1 by omega, pow_succ, Nat.mul_two]
      have child (axis : Fin (k + 2)) :
          dropAxis (k + 1) axis counts ∈ candidates total cap (k + 1) := by
        obtain ⟨hl', hs', hc'⟩ := dropAxis_spec (k + 1) axis counts hlen
        exact ih _ (by omega) (by omega) hl' (hs'.trans hsum)
          (powDouble.symm ▸ hc' _ hcount) (hcost.2.2 axis)
      change counts ∈ extend k cap (candidates total cap (k + 1))
      exact List.mem_flatMap.mpr ⟨_, child ⟨k + 1, by omega⟩,
        List.mem_flatMap.mpr ⟨_, child ⟨k, by omega⟩,
          joinPair_complete k cap counts hlen hcost.1 hcount⟩⟩

-- Splitting the closed decisions by a shared marginal keeps the kernel's
-- reduction cache bounded. Each literal is checked against the same join.
private def extendLeft (d cap : ℕ) (previous : List (List ℕ)) (left : List ℕ) :
    List (List ℕ) :=
  previous.flatMap fun right => joinPair d cap left right

private theorem flatMap_eq_of_forall₂ {α β : Type} {f : α → List β}
    {xs : List α} {ys : List (List β)}
    (h : List.Forall₂ (fun x y => f x = y) xs ys) : xs.flatMap f = ys.flatten := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

private def extendOn (d cap : ℕ) (previous : List (List ℕ)) (base : List ℕ) :
    List (List ℕ) :=
  extend d cap (previous.filter fun t => dropAxis d d t == base)

private theorem extend_eq_nil_of_shared (d cap : ℕ) (previous bases : List (List ℕ))
    (hbase : ∀ t ∈ previous, dropAxis d d t ∈ bases)
    (hexclude : ∀ base ∈ bases, extendOn d cap previous base = []) :
    extend d cap previous = [] := by
  by_contra h
  obtain ⟨counts, hcounts⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨left, hl, right, hr, hjoin⟩ := by
    simpa only [extend, List.mem_flatMap] using hcounts
  have heq : dropAxis d d left = dropAxis d d right := by
    by_contra hn
    simp [joinPair, hn] at hjoin
  have hgroup := hexclude _ (hbase _ hl)
  have hmem : counts ∈ extendOn d cap previous (dropAxis d d left) := by
    exact List.mem_flatMap.mpr ⟨left, by simp [hl],
      List.mem_flatMap.mpr ⟨right, by simp [hr, ← heq], hjoin⟩⟩
  rw [hgroup] at hmem
  exact List.not_mem_nil hmem

private theorem forall_mem_cons {α : Type} {P : α → Prop} {a : α} {rest : List α}
    (ha : P a) (hrest : ∀ x ∈ rest, P x) : ∀ x ∈ a :: rest, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact hrest x hx

private def second36 : List (List ℕ) := [
   [18, 7, 7, 4], [19, 6, 6, 5], [20, 5, 5, 6], [21, 4, 4, 7], [18, 6, 7, 5],
   [19, 5, 6, 6], [20, 4, 5, 7], [18, 5, 7, 6], [19, 4, 6, 7], [18, 4, 7, 7],
   [18, 7, 6, 5], [19, 6, 5, 6], [20, 5, 4, 7], [17, 7, 7, 5], [19, 5, 5, 7],
   [17, 6, 7, 6], [18, 5, 6, 7], [17, 5, 7, 7], [18, 7, 5, 6], [19, 6, 4, 7],
   [17, 7, 6, 6], [18, 6, 5, 7], [16, 7, 7, 6], [17, 6, 6, 7], [16, 6, 7, 7],
   [18, 7, 4, 7], [17, 7, 5, 7], [16, 7, 6, 7], [15, 7, 7, 7]]

private def third36 : List (List (List ℕ)) := [
  [[12, 6, 6, 1, 6, 1, 1, 3], [13, 6, 6, 0, 5, 1, 1, 4], [12, 6, 6, 0, 6, 1, 1, 4]],
  [[13, 6, 5, 1, 6, 0, 1, 4], [13, 5, 6, 1, 6, 1, 0, 4], [15, 5, 5, 0, 4, 1, 1, 5],
    [13, 5, 5, 1, 6, 1, 1, 4], [13, 5, 5, 0, 6, 1, 1, 5]],
  [[15, 5, 4, 1, 5, 0, 1, 5], [15, 4, 5, 1, 5, 1, 0, 5], [15, 4, 4, 1, 5, 1, 1, 5],
    [14, 4, 4, 1, 6, 1, 1, 5], [15, 4, 4, 0, 5, 1, 1, 6], [14, 4, 4, 0, 6, 1, 1, 6]],
  [[15, 4, 4, 1, 6, 0, 0, 6], [15, 4, 3, 1, 6, 0, 1, 6], [15, 3, 4, 1, 6, 1, 0, 6],
    [15, 3, 3, 1, 6, 1, 1, 6]],
  [[12, 6, 6, 1, 6, 0, 1, 4], [13, 5, 6, 1, 5, 1, 1, 4], [12, 5, 6, 1, 6, 1, 1, 4]],
  [[15, 4, 5, 1, 4, 1, 1, 5], [15, 4, 6, 0, 4, 1, 0, 6], [13, 4, 6, 1, 6, 1, 0, 5],
    [15, 4, 5, 0, 4, 1, 1, 6], [13, 4, 5, 1, 6, 1, 1, 5], [13, 4, 6, 0, 6, 1, 0, 6],
    [13, 4, 5, 0, 6, 1, 1, 6]],
  [[15, 4, 4, 1, 5, 0, 1, 6], [14, 4, 4, 1, 6, 0, 1, 6], [14, 3, 5, 1, 6, 1, 0, 6],
    [15, 3, 4, 1, 5, 1, 1, 6], [14, 3, 4, 1, 6, 1, 1, 6]],
  [[13, 5, 6, 1, 5, 0, 1, 5], [14, 4, 6, 1, 4, 1, 1, 5], [15, 4, 6, 0, 3, 1, 1, 6],
    [13, 4, 6, 1, 5, 1, 1, 5], [14, 4, 6, 0, 4, 1, 1, 6], [12, 4, 6, 1, 6, 1, 1, 5],
    [13, 4, 6, 0, 5, 1, 1, 6], [12, 4, 6, 0, 6, 1, 1, 6]],
  [[15, 4, 5, 1, 4, 0, 1, 6], [15, 3, 6, 1, 4, 1, 0, 6], [13, 4, 6, 1, 6, 0, 0, 6],
    [14, 3, 6, 1, 5, 1, 0, 6], [15, 3, 5, 1, 4, 1, 1, 6], [13, 4, 5, 1, 6, 0, 1, 6],
    [13, 3, 6, 1, 6, 1, 0, 6], [14, 3, 5, 1, 5, 1, 1, 6], [13, 3, 5, 1, 6, 1, 1, 6]],
  [[14, 4, 6, 1, 4, 0, 1, 6], [15, 3, 6, 1, 3, 1, 1, 6], [13, 4, 6, 1, 5, 0, 1, 6],
    [14, 3, 6, 1, 4, 1, 1, 6], [12, 4, 6, 1, 6, 0, 1, 6], [13, 3, 6, 1, 5, 1, 1, 6],
    [12, 3, 6, 1, 6, 1, 1, 6]],
  [[12, 6, 6, 1, 6, 1, 0, 4], [13, 6, 5, 1, 5, 1, 1, 4], [12, 6, 5, 1, 6, 1, 1, 4]],
  [[15, 5, 4, 1, 4, 1, 1, 5], [15, 6, 4, 0, 4, 0, 1, 6], [13, 6, 4, 1, 6, 0, 1, 5],
    [15, 5, 4, 0, 4, 1, 1, 6], [13, 5, 4, 1, 6, 1, 1, 5], [13, 6, 4, 0, 6, 0, 1, 6],
    [13, 5, 4, 0, 6, 1, 1, 6]],
  [[15, 4, 4, 1, 5, 1, 0, 6], [14, 5, 3, 1, 6, 0, 1, 6], [14, 4, 4, 1, 6, 1, 0, 6],
    [15, 4, 3, 1, 5, 1, 1, 6], [14, 4, 3, 1, 6, 1, 1, 6]],
  [[12, 6, 6, 1, 5, 1, 1, 4], [13, 6, 6, 0, 4, 1, 1, 5], [11, 6, 6, 1, 6, 1, 1, 4],
    [11, 6, 6, 0, 6, 1, 1, 5]],
  [[15, 5, 4, 1, 4, 0, 1, 6], [15, 4, 5, 1, 4, 1, 0, 6], [15, 4, 4, 1, 4, 1, 1, 6],
    [13, 5, 4, 1, 6, 0, 1, 6], [13, 4, 5, 1, 6, 1, 0, 6], [14, 4, 4, 1, 5, 1, 1, 6],
    [13, 4, 4, 1, 6, 1, 1, 6]],
  [[13, 5, 6, 1, 4, 1, 1, 5], [13, 6, 6, 0, 4, 0, 1, 6], [14, 5, 6, 0, 3, 1, 1, 6],
    [11, 6, 6, 1, 6, 0, 1, 5], [13, 5, 6, 0, 4, 1, 1, 6], [11, 5, 6, 1, 6, 1, 1, 5],
    [11, 6, 6, 0, 6, 0, 1, 6], [11, 5, 6, 0, 6, 1, 1, 6]],
  [[14, 4, 6, 1, 4, 1, 0, 6], [15, 4, 5, 1, 3, 1, 1, 6], [13, 4, 6, 1, 5, 1, 0, 6],
    [14, 4, 5, 1, 4, 1, 1, 6], [12, 4, 6, 1, 6, 1, 0, 6], [13, 4, 5, 1, 5, 1, 1, 6],
    [12, 4, 5, 1, 6, 1, 1, 6]],
  [[13, 5, 6, 1, 4, 0, 1, 6], [14, 4, 6, 1, 3, 1, 1, 6], [13, 4, 6, 1, 4, 1, 1, 6],
    [11, 5, 6, 1, 6, 0, 1, 6], [12, 4, 6, 1, 5, 1, 1, 6], [11, 4, 6, 1, 6, 1, 1, 6]],
  [[13, 6, 5, 1, 5, 1, 0, 5], [14, 6, 4, 1, 4, 1, 1, 5], [15, 6, 4, 0, 3, 1, 1, 6],
    [13, 6, 4, 1, 5, 1, 1, 5], [14, 6, 4, 0, 4, 1, 1, 6], [12, 6, 4, 1, 6, 1, 1, 5],
    [13, 6, 4, 0, 5, 1, 1, 6], [12, 6, 4, 0, 6, 1, 1, 6]],
  [[15, 6, 3, 1, 4, 0, 1, 6], [15, 5, 4, 1, 4, 1, 0, 6], [13, 6, 4, 1, 6, 0, 0, 6],
    [14, 6, 3, 1, 5, 0, 1, 6], [15, 5, 3, 1, 4, 1, 1, 6], [13, 6, 3, 1, 6, 0, 1, 6],
    [13, 5, 4, 1, 6, 1, 0, 6], [14, 5, 3, 1, 5, 1, 1, 6], [13, 5, 3, 1, 6, 1, 1, 6]],
  [[13, 6, 5, 1, 4, 1, 1, 5], [13, 6, 6, 0, 4, 1, 0, 6], [14, 6, 5, 0, 3, 1, 1, 6],
    [11, 6, 6, 1, 6, 1, 0, 5], [13, 6, 5, 0, 4, 1, 1, 6], [11, 6, 5, 1, 6, 1, 1, 5],
    [11, 6, 6, 0, 6, 1, 0, 6], [11, 6, 5, 0, 6, 1, 1, 6]],
  [[14, 6, 4, 1, 4, 0, 1, 6], [15, 5, 4, 1, 3, 1, 1, 6], [13, 6, 4, 1, 5, 0, 1, 6],
    [14, 5, 4, 1, 4, 1, 1, 6], [12, 6, 4, 1, 6, 0, 1, 6], [13, 5, 4, 1, 5, 1, 1, 6],
    [12, 5, 4, 1, 6, 1, 1, 6]],
  [[12, 6, 6, 1, 4, 1, 1, 5], [13, 6, 6, 0, 3, 1, 1, 6], [11, 6, 6, 1, 5, 1, 1, 5],
    [12, 6, 6, 0, 4, 1, 1, 6], [10, 6, 6, 1, 6, 1, 1, 5], [11, 6, 6, 0, 5, 1, 1, 6],
    [10, 6, 6, 0, 6, 1, 1, 6]],
  [[13, 6, 5, 1, 4, 0, 1, 6], [13, 5, 6, 1, 4, 1, 0, 6], [14, 5, 5, 1, 3, 1, 1, 6],
    [11, 6, 6, 1, 6, 0, 0, 6], [13, 5, 5, 1, 4, 1, 1, 6], [11, 6, 5, 1, 6, 0, 1, 6],
    [11, 5, 6, 1, 6, 1, 0, 6], [11, 5, 5, 1, 6, 1, 1, 6]],
  [[12, 6, 6, 1, 4, 0, 1, 6], [13, 5, 6, 1, 3, 1, 1, 6], [11, 6, 6, 1, 5, 0, 1, 6],
    [12, 5, 6, 1, 4, 1, 1, 6], [10, 6, 6, 1, 6, 0, 1, 6], [11, 5, 6, 1, 5, 1, 1, 6],
    [10, 5, 6, 1, 6, 1, 1, 6]],
  [[14, 6, 4, 1, 4, 1, 0, 6], [15, 6, 3, 1, 3, 1, 1, 6], [13, 6, 4, 1, 5, 1, 0, 6],
    [14, 6, 3, 1, 4, 1, 1, 6], [12, 6, 4, 1, 6, 1, 0, 6], [13, 6, 3, 1, 5, 1, 1, 6],
    [12, 6, 3, 1, 6, 1, 1, 6]],
  [[13, 6, 5, 1, 4, 1, 0, 6], [14, 6, 4, 1, 3, 1, 1, 6], [13, 6, 4, 1, 4, 1, 1, 6],
    [11, 6, 5, 1, 6, 1, 0, 6], [12, 6, 4, 1, 5, 1, 1, 6], [11, 6, 4, 1, 6, 1, 1, 6]],
  [[12, 6, 6, 1, 4, 1, 0, 6], [13, 6, 5, 1, 3, 1, 1, 6], [11, 6, 6, 1, 5, 1, 0, 6],
    [12, 6, 5, 1, 4, 1, 1, 6], [10, 6, 6, 1, 6, 1, 0, 6], [11, 6, 5, 1, 5, 1, 1, 6],
    [10, 6, 5, 1, 6, 1, 1, 6]],
  [[12, 6, 6, 1, 3, 1, 1, 6], [11, 6, 6, 1, 4, 1, 1, 6], [10, 6, 6, 1, 5, 1, 1, 6],
    [9, 6, 6, 1, 6, 1, 1, 6]]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
-- Check all feasible joins of one-axis projections.
private theorem candidates_36_two : candidates 36 106 2 = second36 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check each group of three-axis tables against the two-axis joins.
private theorem candidates_36_three : candidates 36 106 3 = third36.flatten := by
  rw [candidates, candidates_36_two]
  apply flatMap_eq_of_forall₂ (f := extendLeft 1 106 second36)
  repeat' first
    | exact List.Forall₂.nil
    | refine List.Forall₂.cons ?_ ?_
      · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check all joins within each shared two-axis marginal.
private theorem candidates_36 : candidates 36 106 4 = [] := by
  rw [candidates, candidates_36_three]
  apply extend_eq_nil_of_shared _ _ _ second36
  · intro t ht
    have hall : (third36.flatten.all fun t => second36.contains (dropAxis 2 2 t)) = true := by
      decide +kernel
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hall t ht)
  · repeat' first
      | exact fun _ h => False.elim (List.not_mem_nil h)
      | refine forall_mem_cons ?_ ?_
        · decide +kernel

private def second39 : List (List ℕ) := [
   [21, 7, 7, 4], [22, 6, 6, 5], [20, 7, 8, 4], [21, 6, 7, 5], [22, 5, 6, 6],
   [21, 5, 7, 6], [22, 4, 6, 7], [21, 4, 7, 7], [20, 8, 7, 4], [21, 7, 6, 5],
   [22, 6, 5, 6], [20, 7, 7, 5], [21, 6, 6, 6], [22, 5, 5, 7], [20, 6, 7, 6],
   [21, 5, 6, 7], [20, 5, 7, 7], [21, 7, 5, 6], [22, 6, 4, 7], [20, 7, 6, 6],
   [21, 6, 5, 7], [19, 7, 7, 6], [20, 6, 6, 7], [19, 6, 7, 7], [21, 7, 4, 7],
   [20, 7, 5, 7], [19, 7, 6, 7], [18, 7, 7, 7]]

private def third39 : List (List (List ℕ)) := [
  [[15, 6, 6, 1, 6, 1, 1, 3], [16, 6, 5, 1, 5, 1, 2, 3], [16, 5, 6, 1, 5, 2, 1, 3],
    [16, 6, 6, 0, 5, 1, 1, 4], [15, 6, 5, 1, 6, 1, 2, 3], [15, 5, 6, 1, 6, 2, 1, 3],
    [15, 6, 6, 0, 6, 1, 1, 4]],
  [[16, 5, 5, 2, 6, 1, 1, 3], [16, 6, 5, 1, 6, 0, 1, 4], [16, 5, 6, 1, 6, 1, 0, 4],
    [16, 6, 6, 0, 6, 0, 0, 5], [16, 5, 5, 1, 6, 1, 1, 4], [16, 6, 5, 0, 6, 0, 1, 5],
    [16, 5, 6, 0, 6, 1, 0, 5], [16, 5, 5, 0, 6, 1, 1, 5]],
  [[15, 6, 6, 1, 5, 1, 2, 3], [14, 6, 6, 1, 6, 1, 2, 3]],
  [[15, 5, 6, 2, 6, 1, 1, 3], [15, 6, 6, 1, 6, 0, 1, 4], [16, 5, 6, 1, 5, 1, 1, 4],
    [16, 6, 6, 0, 5, 0, 1, 5], [15, 5, 6, 1, 6, 1, 1, 4], [15, 6, 6, 0, 6, 0, 1, 5],
    [16, 5, 6, 0, 5, 1, 1, 5], [15, 5, 6, 0, 6, 1, 1, 5]],
  [[16, 5, 6, 1, 6, 0, 0, 5], [16, 5, 5, 1, 6, 0, 1, 5], [16, 4, 6, 1, 6, 1, 0, 5],
    [16, 5, 6, 0, 6, 0, 0, 6], [16, 4, 5, 1, 6, 1, 1, 5], [16, 5, 5, 0, 6, 0, 1, 6],
    [16, 4, 6, 0, 6, 1, 0, 6], [16, 4, 5, 0, 6, 1, 1, 6]],
  [[16, 5, 6, 1, 5, 0, 1, 5], [15, 5, 6, 1, 6, 0, 1, 5], [16, 4, 6, 1, 5, 1, 1, 5],
    [16, 5, 6, 0, 5, 0, 1, 6], [15, 4, 6, 1, 6, 1, 1, 5], [15, 5, 6, 0, 6, 0, 1, 6],
    [16, 4, 6, 0, 5, 1, 1, 6], [15, 4, 6, 0, 6, 1, 1, 6]],
  [[16, 4, 6, 1, 6, 0, 0, 6], [16, 4, 5, 1, 6, 0, 1, 6], [16, 3, 6, 1, 6, 1, 0, 6],
    [16, 3, 5, 1, 6, 1, 1, 6]],
  [[16, 4, 6, 1, 5, 0, 1, 6], [15, 4, 6, 1, 6, 0, 1, 6], [16, 3, 6, 1, 5, 1, 1, 6],
    [15, 3, 6, 1, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 5, 2, 1, 3], [14, 6, 6, 1, 6, 2, 1, 3]],
  [[15, 6, 5, 2, 6, 1, 1, 3], [15, 6, 6, 1, 6, 1, 0, 4], [16, 6, 5, 1, 5, 1, 1, 4],
    [16, 6, 6, 0, 5, 1, 0, 5], [15, 6, 5, 1, 6, 1, 1, 4], [15, 6, 6, 0, 6, 1, 0, 5],
    [16, 6, 5, 0, 5, 1, 1, 5], [15, 6, 5, 0, 6, 1, 1, 5]],
  [[16, 6, 5, 1, 6, 0, 0, 5], [16, 6, 4, 1, 6, 0, 1, 5], [16, 5, 5, 1, 6, 1, 0, 5],
    [16, 6, 5, 0, 6, 0, 0, 6], [16, 5, 4, 1, 6, 1, 1, 5], [16, 6, 4, 0, 6, 0, 1, 6],
    [16, 5, 5, 0, 6, 1, 0, 6], [16, 5, 4, 0, 6, 1, 1, 6]],
  [[14, 6, 6, 2, 6, 1, 1, 3], [15, 6, 6, 1, 5, 1, 1, 4], [16, 6, 6, 0, 4, 1, 1, 5],
    [14, 6, 6, 1, 6, 1, 1, 4], [15, 6, 6, 0, 5, 1, 1, 5], [14, 6, 6, 0, 6, 1, 1, 5]],
  [[15, 6, 6, 1, 6, 0, 0, 5], [16, 6, 5, 1, 5, 0, 1, 5], [16, 5, 6, 1, 5, 1, 0, 5],
    [16, 6, 6, 0, 5, 0, 0, 6], [15, 6, 5, 1, 6, 0, 1, 5], [15, 5, 6, 1, 6, 1, 0, 5],
    [15, 6, 6, 0, 6, 0, 0, 6], [16, 5, 5, 1, 5, 1, 1, 5], [16, 6, 5, 0, 5, 0, 1, 6],
    [16, 5, 6, 0, 5, 1, 0, 6], [15, 5, 5, 1, 6, 1, 1, 5], [15, 6, 5, 0, 6, 0, 1, 6],
    [15, 5, 6, 0, 6, 1, 0, 6], [16, 5, 5, 0, 5, 1, 1, 6], [15, 5, 5, 0, 6, 1, 1, 6]],
  [[16, 5, 5, 1, 6, 0, 0, 6], [16, 5, 4, 1, 6, 0, 1, 6], [16, 4, 5, 1, 6, 1, 0, 6],
    [16, 4, 4, 1, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 5, 0, 1, 5], [16, 5, 6, 1, 4, 1, 1, 5], [16, 6, 6, 0, 4, 0, 1, 6],
    [14, 6, 6, 1, 6, 0, 1, 5], [15, 5, 6, 1, 5, 1, 1, 5], [15, 6, 6, 0, 5, 0, 1, 6],
    [16, 5, 6, 0, 4, 1, 1, 6], [14, 5, 6, 1, 6, 1, 1, 5], [14, 6, 6, 0, 6, 0, 1, 6],
    [15, 5, 6, 0, 5, 1, 1, 6], [14, 5, 6, 0, 6, 1, 1, 6]],
  [[16, 5, 6, 1, 5, 0, 0, 6], [15, 5, 6, 1, 6, 0, 0, 6], [16, 5, 5, 1, 5, 0, 1, 6],
    [16, 4, 6, 1, 5, 1, 0, 6], [15, 5, 5, 1, 6, 0, 1, 6], [15, 4, 6, 1, 6, 1, 0, 6],
    [16, 4, 5, 1, 5, 1, 1, 6], [15, 4, 5, 1, 6, 1, 1, 6]],
  [[16, 5, 6, 1, 4, 0, 1, 6], [15, 5, 6, 1, 5, 0, 1, 6], [16, 4, 6, 1, 4, 1, 1, 6],
    [14, 5, 6, 1, 6, 0, 1, 6], [15, 4, 6, 1, 5, 1, 1, 6], [14, 4, 6, 1, 6, 1, 1, 6]],
  [[16, 6, 5, 1, 5, 1, 0, 5], [15, 6, 5, 1, 6, 1, 0, 5], [16, 6, 4, 1, 5, 1, 1, 5],
    [16, 6, 5, 0, 5, 1, 0, 6], [15, 6, 4, 1, 6, 1, 1, 5], [15, 6, 5, 0, 6, 1, 0, 6],
    [16, 6, 4, 0, 5, 1, 1, 6], [15, 6, 4, 0, 6, 1, 1, 6]],
  [[16, 6, 4, 1, 6, 0, 0, 6], [16, 6, 3, 1, 6, 0, 1, 6], [16, 5, 4, 1, 6, 1, 0, 6],
    [16, 5, 3, 1, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 5, 1, 0, 5], [16, 6, 5, 1, 4, 1, 1, 5], [16, 6, 6, 0, 4, 1, 0, 6],
    [14, 6, 6, 1, 6, 1, 0, 5], [15, 6, 5, 1, 5, 1, 1, 5], [15, 6, 6, 0, 5, 1, 0, 6],
    [16, 6, 5, 0, 4, 1, 1, 6], [14, 6, 5, 1, 6, 1, 1, 5], [14, 6, 6, 0, 6, 1, 0, 6],
    [15, 6, 5, 0, 5, 1, 1, 6], [14, 6, 5, 0, 6, 1, 1, 6]],
  [[16, 6, 5, 1, 5, 0, 0, 6], [15, 6, 5, 1, 6, 0, 0, 6], [16, 6, 4, 1, 5, 0, 1, 6],
    [16, 5, 5, 1, 5, 1, 0, 6], [15, 6, 4, 1, 6, 0, 1, 6], [15, 5, 5, 1, 6, 1, 0, 6],
    [16, 5, 4, 1, 5, 1, 1, 6], [15, 5, 4, 1, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 4, 1, 1, 5], [16, 6, 6, 0, 3, 1, 1, 6], [14, 6, 6, 1, 5, 1, 1, 5],
    [15, 6, 6, 0, 4, 1, 1, 6], [13, 6, 6, 1, 6, 1, 1, 5], [14, 6, 6, 0, 5, 1, 1, 6],
    [13, 6, 6, 0, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 5, 0, 0, 6], [16, 6, 5, 1, 4, 0, 1, 6], [16, 5, 6, 1, 4, 1, 0, 6],
    [14, 6, 6, 1, 6, 0, 0, 6], [15, 6, 5, 1, 5, 0, 1, 6], [15, 5, 6, 1, 5, 1, 0, 6],
    [16, 5, 5, 1, 4, 1, 1, 6], [14, 6, 5, 1, 6, 0, 1, 6], [14, 5, 6, 1, 6, 1, 0, 6],
    [15, 5, 5, 1, 5, 1, 1, 6], [14, 5, 5, 1, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 4, 0, 1, 6], [16, 5, 6, 1, 3, 1, 1, 6], [14, 6, 6, 1, 5, 0, 1, 6],
    [15, 5, 6, 1, 4, 1, 1, 6], [13, 6, 6, 1, 6, 0, 1, 6], [14, 5, 6, 1, 5, 1, 1, 6],
    [13, 5, 6, 1, 6, 1, 1, 6]],
  [[16, 6, 4, 1, 5, 1, 0, 6], [15, 6, 4, 1, 6, 1, 0, 6], [16, 6, 3, 1, 5, 1, 1, 6],
    [15, 6, 3, 1, 6, 1, 1, 6]],
  [[16, 6, 5, 1, 4, 1, 0, 6], [15, 6, 5, 1, 5, 1, 0, 6], [16, 6, 4, 1, 4, 1, 1, 6],
    [14, 6, 5, 1, 6, 1, 0, 6], [15, 6, 4, 1, 5, 1, 1, 6], [14, 6, 4, 1, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 4, 1, 0, 6], [16, 6, 5, 1, 3, 1, 1, 6], [14, 6, 6, 1, 5, 1, 0, 6],
    [15, 6, 5, 1, 4, 1, 1, 6], [13, 6, 6, 1, 6, 1, 0, 6], [14, 6, 5, 1, 5, 1, 1, 6],
    [13, 6, 5, 1, 6, 1, 1, 6]],
  [[15, 6, 6, 1, 3, 1, 1, 6], [14, 6, 6, 1, 4, 1, 1, 6], [13, 6, 6, 1, 5, 1, 1, 6],
    [12, 6, 6, 1, 6, 1, 1, 6]]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
-- Check all feasible joins of one-axis projections.
private theorem candidates_39_two : candidates 39 109 2 = second39 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check each group of three-axis tables against the two-axis joins.
private theorem candidates_39_three : candidates 39 109 3 = third39.flatten := by
  rw [candidates, candidates_39_two]
  apply flatMap_eq_of_forall₂ (f := extendLeft 1 109 second39)
  repeat' first
    | exact List.Forall₂.nil
    | refine List.Forall₂.cons ?_ ?_
      · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check all joins within each shared two-axis marginal.
private theorem candidates_39 : candidates 39 109 4 = [] := by
  rw [candidates, candidates_39_three]
  apply extend_eq_nil_of_shared _ _ _ second39
  · intro t ht
    have hall : (third39.flatten.all fun t => second39.contains (dropAxis 2 2 t)) = true := by
      decide +kernel
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hall t ht)
  · repeat' first
      | exact fun _ h => False.elim (List.not_mem_nil h)
      | refine forall_mem_cons ?_ ?_
        · decide +kernel

/-- At total 36, the oriented margins and the cost cap of 106 cannot both
hold for the nonempty projections of the four axes. -/
theorem exclude36 (counts : List ℕ) (hlen : counts.length = 16) (hsum : counts.sum = 36)
    (hcount : ∀ x ∈ counts, x ≤ 16) :
    ¬ ProjectionConstraints 36 106 4 counts := by
  intro hcost
  have hmem := candidates_complete 36 106 4 counts (by decide) (by decide) hlen hsum hcount hcost
  rw [candidates_36] at hmem
  exact List.not_mem_nil hmem

/-- At total 39, the oriented margins and the cost cap of 109 cannot both
hold for the nonempty projections of the four axes. -/
theorem exclude39 (counts : List ℕ) (hlen : counts.length = 16) (hsum : counts.sum = 39)
    (hcount : ∀ x ∈ counts, x ≤ 16) :
    ¬ ProjectionConstraints 39 109 4 counts := by
  intro hcost
  have hmem := candidates_complete 39 109 4 counts (by decide) (by decide) hlen hsum hcount hcost
  rw [candidates_39] at hmem
  exact List.not_mem_nil hmem

#print axioms exclude36
#print axioms exclude39

end Q8FourFiberCapacityCertificate
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
