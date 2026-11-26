/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ProjectedHeightCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: none
   digest: A common height fixes the centers of overlapping boxes and excludes mixed splits in connected threefold projections. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

/-! Integer height on the six-axis projection fixes the center along overlaps
of boxes. The two splits are normalized by a permutation of the six axes. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9ProjectedHeightCompatibility

abbrev Point := BitVec 6
abbrev Mask := BitVec 64

private def partition (p : Bool) : List (Fin 6) × List (Fin 6) :=
  if p then ([0, 1, 3], [2, 4, 5]) else ([0, 1, 2], [3, 4, 5])

def hasPoint (m : Mask) (x : Point) : Bool := m.getLsbD x.toNat

private def axisBit (i : Fin 6) : Point := (1 : Point) <<< i.val

private def boxAtZero (p : Bool) : Mask :=
  let (left, right) := partition p
  left.foldl (fun m i =>
    right.foldl (fun n j =>
      n ||| ((1 : Mask) <<< (axisBit i ^^^ axisBit j).toNat)) m) 0

/-- The XOR translate of the pairs that cross the selected split. -/
def inBox (p : Bool) (c x : Point) : Bool := hasPoint (boxAtZero p) (x ^^^ c)

/-- Height on a projected box is a translate of the indicator of the two
flipped axes, with all other coordinates zero. -/
def HasBoxHeight (height : Point → Fin 6 → ℤ) (p : Bool) (c : Point) : Prop :=
  ∃ offset : Fin 6 → ℤ, ∀ x : Point, inBox p c x = true → ∀ i : Fin 6,
    height x i = offset i + ((x ^^^ c).getLsbD i.val).toNat

private def common (p : Bool) (c : Point) (q : Bool) (d : Point) (x : Point) : Bool :=
  inBox p c x && inBox q d x

private def conflict (p : Bool) (c : Point) (q : Bool) (d : Point) : Bool :=
  let points := (List.finRange 64).map BitVec.ofFin
  (List.finRange 6).any fun i =>
    (c ^^^ d).getLsbD i.val &&
      (points.any fun x => common p c q d x && !x.getLsbD i.val) &&
      (points.any fun y => common p c q d y && y.getLsbD i.val)

private theorem no_conflict {height : Point → Fin 6 → ℤ} {p q : Bool} {c d : Point}
    (hp : HasBoxHeight height p c) (hq : HasBoxHeight height q d) :
    conflict p c q d = false := by
  rcases hp with ⟨offP, hP⟩
  rcases hq with ⟨offQ, hQ⟩
  apply Bool.eq_false_of_not_eq_true
  intro h
  unfold conflict at h
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hi
  obtain ⟨⟨hc, hlow⟩, hhigh⟩ := hi
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp hlow
  obtain ⟨y, _, hy⟩ := List.any_eq_true.mp hhigh
  simp only [common, Bool.and_eq_true, Bool.not_eq_true'] at hx hy
  have hx' := (hP x hx.1.1 i).symm.trans (hQ x hx.1.2 i)
  have hy' := (hP y hy.1.1 i).symm.trans (hQ y hy.1.2 i)
  simp only [BitVec.getLsbD_xor, hx.2, hy.2, Bool.false_xor, Bool.true_xor] at hx' hy' hc
  cases hci : c.getLsbD i.val <;> cases hdi : d.getLsbD i.val <;>
    simp_all <;> omega

private def modelCheck (p q : Bool) (d : Point) : Bool :=
  if d = 0#6 then true else
    let points := (List.finRange 64).map BitVec.ofFin
    !(points.any (common p 0#6 q d)) || conflict p 0#6 q d

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check four split pairs against the 64 relative center offsets.
private theorem model_check_all (p q : Bool) :
    ∀ d : Fin 64, modelCheck p q (BitVec.ofFin d) = true := by
  cases p <;> cases q <;> decide +kernel

private theorem equal_center_at_zero {height : Point → Fin 6 → ℤ} {p q : Bool} {d x : Point}
    (hp : HasBoxHeight height p 0#6) (hq : HasBoxHeight height q d)
    (hx : inBox p 0#6 x = true) (hy : inBox q d x = true) : d = 0#6 := by
  by_contra hne
  have h := model_check_all p q d.toFin
  change modelCheck p q d = true at h
  have hcommon : ((List.finRange 64).map BitVec.ofFin).any (common p 0#6 q d) = true := by
    apply List.any_eq_true.mpr
    refine ⟨x, List.mem_map.mpr ⟨x.toFin, List.mem_finRange _, rfl⟩, ?_⟩
    rw [common, hx, hy]
    rfl
  rw [modelCheck, ite_eq_right hne] at h
  change (!(List.any ((List.finRange 64).map BitVec.ofFin) (common p 0#6 q d)) ||
    conflict p 0#6 q d) = true at h
  rw [hcommon, no_conflict hp hq] at h
  contradiction

private theorem xor_right_cancel (a c : Point) : (a ^^^ c) ^^^ c = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem xor_translate (a c d : Point) : (a ^^^ c) ^^^ (d ^^^ c) = a ^^^ d := by
  rw [BitVec.xor_comm d c, ← BitVec.xor_assoc, xor_right_cancel]

/-- Two boxes admitting one integer height and sharing a point must have
identical centers. The XOR action reduces the finite check to relative centers. -/
theorem equal_center_of_overlap {height : Point → Fin 6 → ℤ} {p q : Bool} {c d x : Point}
    (hp : HasBoxHeight height p c) (hq : HasBoxHeight height q d)
    (hx : inBox p c x = true) (hy : inBox q d x = true) : c = d := by
  let g : Point → Fin 6 → ℤ := fun y => height (y ^^^ c)
  have liftHeight {r : Bool} {e : Point} (h : HasBoxHeight height r e) :
      HasBoxHeight g r (e ^^^ c) := by
    obtain ⟨k, hk⟩ := h
    refine ⟨k, fun y hmem i => ?_⟩
    have heq : (y ^^^ c) ^^^ e = y ^^^ (e ^^^ c) := by
      rw [BitVec.xor_assoc, BitVec.xor_comm c e]
    have hmem' : inBox r e (y ^^^ c) = true := by simpa only [inBox, heq] using hmem
    simpa only [g, heq] using hk (y ^^^ c) hmem' i
  have hp' : HasBoxHeight g p 0#6 := by simpa only [BitVec.xor_self] using liftHeight hp
  have hx' : inBox p 0#6 (x ^^^ c) = true := by simpa only [inBox, BitVec.xor_zero] using hx
  have hy' : inBox q (d ^^^ c) (x ^^^ c) = true := by
    simpa only [inBox, xor_translate] using hy
  have h := equal_center_at_zero hp' (liftHeight hq) hx' hy'
  have h' := congrArg (fun u : Point => u ^^^ c) h
  rw [xor_right_cancel, BitVec.zero_xor] at h'
  exact h'.symm

/-- Two projected vertices are related when one box contains both. -/
def sameBox (family : Finset (Bool × Point)) (x y : Point) : Prop :=
  ∃ t ∈ family, inBox t.1 t.2 x = true ∧ inBox t.1 t.2 y = true

/-- The center is invariant along paths that move within boxes. -/
theorem equal_center_of_box_path {family : Finset (Bool × Point)}
    {height : Point → Fin 6 → ℤ} {p q : Bool} {c d x y : Point}
    (hp : (p, c) ∈ family) (hq : (q, d) ∈ family)
    (hheight : ∀ t ∈ family, HasBoxHeight height t.1 t.2)
    (hx : inBox p c x = true) (hy : inBox q d y = true)
    (hpath : Relation.ReflTransGen (sameBox family) x y) : c = d := by
  have atEnd : ∃ r : Bool, (r, c) ∈ family ∧ inBox r c y = true := by
    clear hq hy
    induction hpath with
    | refl => exact ⟨p, hp, hx⟩
    | tail _ hstep ih =>
      obtain ⟨r, hr, hz⟩ := ih
      obtain ⟨⟨s, e⟩, hs, hz', hw⟩ := hstep
      have he : c = e := equal_center_of_overlap (hheight (r, c) hr) (hheight (s, e) hs) hz hz'
      subst e
      exact ⟨s, hs, hw⟩
  obtain ⟨r, hr, hy'⟩ := atEnd
  exact equal_center_of_overlap (hheight (r, c) hr) (hheight (q, d) hq) hy' hy

private theorem exclusive_point (p : Bool) : ∃ x : Point,
    inBox p 0#6 x = true ∧ inBox (!p) 0#6 x = false := by
  cases p
  · exact ⟨9, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩

/-- The slice indices containing a projected point. -/
def projectedFiber (labels : Fin 4 → Option Bool) (c x : Point) : Finset (Fin 4) :=
  Finset.univ.filter fun i => ((labels i).map fun p => inBox p c x) = some true

/-- Four one-box slices with the same center and threefold fibers cannot
use both complementary splits. Empty slices carry no label. -/
theorem unique_split_of_threefold_fibers (labels : Fin 4 → Option Bool) (c : Point)
    (hthree : ∀ x : Point, (projectedFiber labels c x).Nonempty →
      (projectedFiber labels c x).card = 3) :
    ¬ ((∃ i, labels i = some false) ∧ (∃ i, labels i = some true)) := by
  have hcount (p : Bool) (hp : ∃ i, labels i = some p) :
      (Finset.univ.filter fun i => labels i = some p).card = 3 := by
    obtain ⟨x, hx, hn⟩ := exclusive_point p
    have hleft : inBox p c (x ^^^ c) = true := by
      simpa only [inBox, BitVec.xor_zero, xor_right_cancel] using hx
    have hright : inBox (!p) c (x ^^^ c) = false := by
      simpa only [inBox, BitVec.xor_zero, xor_right_cancel] using hn
    have hset : projectedFiber labels c (x ^^^ c) =
        Finset.univ.filter (fun i => labels i = some p) := by
      ext i
      simp only [projectedFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : labels i with
      | none => simp
      | some q =>
        have hq : q = p ∨ q = !p := by cases p <;> cases q <;> simp
        rcases hq with rfl | rfl
        · simp [hleft]
        · change some (inBox (!p) c (x ^^^ c)) = some true ↔ some (!p) = some p
          rw [hright]
          cases p <;> decide
    rw [← hset]
    apply hthree
    rw [hset]
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  rintro ⟨hfalse, htrue⟩
  have hd : Disjoint (Finset.univ.filter fun i => labels i = some false)
      (Finset.univ.filter fun i => labels i = some true) := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hj
    have hf := (Finset.mem_filter.mp hi).2
    have ht := (Finset.mem_filter.mp hj).2
    simp [hf] at ht
  have hcard := Finset.card_union_of_disjoint hd
  rw [hcount false hfalse, hcount true htrue] at hcard
  have hle := Finset.card_le_univ ((Finset.univ.filter fun i => labels i = some false) ∪
    (Finset.univ.filter fun i => labels i = some true))
  rw [Fintype.card_fin] at hle
  omega

/-- The slice indices in which some box contains the input point. -/
noncomputable def occupiedSlices (slices : Fin 4 → Finset (Bool × Point)) (x : Point) :
    Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun i => ∃ t ∈ slices i, inBox t.1 t.2 x = true

/-- A connected four-slice projection with a common height and threefold
fibers uses at most one complementary split. Boxes on one slice are disjoint. -/
theorem no_mixed_splits_of_connected_projection (slices : Fin 4 → Finset (Bool × Point))
    (height : Point → Fin 6 → ℤ)
    (hheight : ∀ i t, t ∈ slices i → HasBoxHeight height t.1 t.2)
    (hdisjoint : ∀ i t u, t ∈ slices i → u ∈ slices i → t ≠ u →
      ∀ x, inBox t.1 t.2 x = true → inBox u.1 u.2 x = false)
    (hconnected : ∀ x y, (occupiedSlices slices x).Nonempty →
      (occupiedSlices slices y).Nonempty →
      Relation.ReflTransGen (sameBox (Finset.univ.biUnion slices)) x y)
    (hthree : ∀ x, (occupiedSlices slices x).Nonempty → (occupiedSlices slices x).card = 3) :
    ¬ ((∃ i c, (false, c) ∈ slices i) ∧ (∃ i c, (true, c) ∈ slices i)) := by
  classical
  rintro ⟨⟨i, c, hic⟩, ⟨j, d, hjd⟩⟩
  let boxes := Finset.univ.biUnion slices
  have hmember (k : Fin 4) (t : Bool × Point) (ht : t ∈ slices k) : t ∈ boxes :=
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, ht⟩
  have hH : ∀ t ∈ boxes, HasBoxHeight height t.1 t.2 := by
    intro t ht
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp ht
    exact hheight k t hk
  have hadj (p : Bool) (a : Point) : inBox p a (17#6 ^^^ a) = true := by
    have h : inBox p 0#6 17#6 = true := by cases p <;> decide
    simpa only [inBox, BitVec.xor_zero, xor_right_cancel] using h
  have hoccupied (k : Fin 4) (t : Bool × Point) (ht : t ∈ slices k) :
      (occupiedSlices slices (17#6 ^^^ t.2)).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hadj t.1 t.2⟩⟩
  have hcenter (k : Fin 4) (t : Bool × Point) (ht : t ∈ slices k) : t.2 = c :=
    (equal_center_of_box_path (hmember i (false, c) hic) (hmember k t ht) hH
      (hadj false c) (hadj t.1 t.2)
      (hconnected _ _ (hoccupied i (false, c) hic) (hoccupied k t ht))).symm
  have heq (k : Fin 4) {t u : Bool × Point} (ht : t ∈ slices k) (hu : u ∈ slices k) : t = u := by
    by_contra hne
    have h := hdisjoint k t u ht hu hne (17#6 ^^^ c)
    rw [hcenter k t ht, hcenter k u hu] at h
    have h' := h (hadj t.1 c)
    rw [hadj u.1 c] at h'
    contradiction
  let labels (k : Fin 4) : Option Bool :=
    if hk : (slices k).Nonempty then some hk.choose.1 else none
  have hlabel (k : Fin 4) (t : Bool × Point) (ht : t ∈ slices k) : labels k = some t.1 := by
    have hk : (slices k).Nonempty := ⟨t, ht⟩
    simp only [labels, dite_eq_left hk, heq k hk.choose_spec ht]
  have hsame (x : Point) : projectedFiber labels c x = occupiedSlices slices x := by
    ext k
    simp only [projectedFiber, occupiedSlices, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hk : (slices k).Nonempty
    · simp only [hlabel k _ hk.choose_spec, Option.map_some, Option.some.injEq]
      constructor
      · intro hx
        exact ⟨hk.choose, hk.choose_spec, by rwa [hcenter k _ hk.choose_spec]⟩
      · rintro ⟨t, ht, hx⟩
        rw [heq k hk.choose_spec ht]
        rwa [← hcenter k t ht]
    · simp only [labels, dite_eq_right hk, Option.map_none, reduceCtorEq, false_iff]
      rintro ⟨t, ht, _⟩
      exact hk ⟨t, ht⟩
  exact unique_split_of_threefold_fibers labels c (by simpa only [hsame] using hthree)
    ⟨⟨i, hlabel i (false, c) hic⟩, ⟨j, hlabel j (true, d) hjd⟩⟩

#print axioms equal_center_of_overlap
#print axioms equal_center_of_box_path
#print axioms unique_split_of_threefold_fibers
#print axioms no_mixed_splits_of_connected_projection

end Q9ProjectedHeightCompatibility
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
