/- GID: D5/S3/Combinatorics/PatternMatchings/P13Orders
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Orders
   mirror-E: none(waiver:survivor-order-transport)
   anchors: []
   utility: none
   digest: Normalized future orders are transported through every actual indexed deletion. -/

import D5.S3.Combinatorics.PatternMatchings.P13Decoder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

/-- A closing-time function respects the old base, without constraining pending openers. -/
def Respects {α : Type} (q : List α) (f : α → ℕ) (s : Base) : Prop :=
  ∀ x y : Fin q.length, x.val < s.size → y.val < s.size →
    Before s.cut x.val y.val → f (q.get x) < f (q.get y)

/-- The total future order imposed by closing rank r. -/
def ClosureRespects {α : Type} (q : List α) (f : α → ℕ) (r : ℕ) : Prop :=
  ∀ x y : Fin q.length, x.val ≠ r → y.val ≠ r →
    Before r x.val y.val → f (q.get x) < f (q.get y)

private theorem before_reverse (a x y : ℕ) :
    ¬ Before a x y ↔ x = y ∨ Before a y x := by
  unfold Before
  omega

/-- A realized total survivor order determines every comparison, in both directions. -/
theorem closure_comparison {α : Type} (q : List α) (f : α → ℕ) (r : ℕ)
    (h : ClosureRespects q f r) (x y : Fin q.length)
    (hx : x.val ≠ r) (hy : y.val ≠ r) :
    f (q.get x) < f (q.get y) ↔ Before r x.val y.val := by
  constructor
  · intro hf
    by_contra hb
    rcases (before_reverse r x.val y.val).mp hb with he | he
    · have hxy : x = y := Fin.ext he
      subst y
      exact lt_irrefl _ hf
    · exact (not_lt_of_ge (h y x hy hx he).le) hf
  · exact h x y hx hy

private theorem lower_spec {α : Type} (q : List α) (r : ℕ) (hr : r < q.length)
    (x : Fin q.length) (hx : x.val ≠ r) :
    let j := if x.val < r then x.val else x.val - 1
    j < (q.eraseIdx r).length ∧ liftRank r j = x.val := by
  have hl := List.length_eraseIdx_add_one hr
  dsimp
  unfold liftRank
  split_ifs <;> omega

/-- Actual queue deletion realizes exactly the new normalized base order. -/
theorem deletion_order {α : Type} (q : List α) (f : α → ℕ)
    (s : Base) (k r : ℕ) (hlen : q.length = s.size + k)
    (hr : r < q.length) :
    Respects (q.eraseIdx r) f (afterClose s k r) ↔ ClosureRespects q f r := by
  have hb := blocks_spec r (s.size + k - r - 1)
  have hl := List.length_eraseIdx_add_one hr
  have hsz : (afterClose s k r).size = (q.eraseIdx r).length := by
    change (blocks r (s.size + k - r - 1)).size = _
    have hh := hb.1
    omega
  have getlift (j : Fin (q.eraseIdx r).length) :
      (q.eraseIdx r).get j = q.get ⟨liftRank r j.val, by
        unfold liftRank
        split_ifs <;> omega⟩ := by
    change (q.eraseIdx r)[j.val] = q[liftRank r j.val]'(by
      unfold liftRank
      split_ifs <;> have hh := j.isLt <;> omega)
    rw [List.getElem_eraseIdx]
    unfold liftRank
    split_ifs <;> rfl
  constructor
  · intro h x y hx hy hxy
    let j : Fin (q.eraseIdx r).length :=
      ⟨if x.val < r then x.val else x.val - 1, (lower_spec q r hr x hx).1⟩
    let l : Fin (q.eraseIdx r).length :=
      ⟨if y.val < r then y.val else y.val - 1, (lower_spec q r hr y hy).1⟩
    have hj : liftRank r j.val = x.val := (lower_spec q r hr x hx).2
    have hl' : liftRank r l.val = y.val := (lower_spec q r hr y hy).2
    have ho : Before (afterClose s k r).cut j.val l.val := by
      apply (hb.2.2 j.val l.val (by have := j.isLt; omega)
        (by have := l.isLt; omega)).mpr
      apply (before_lift r j.val l.val).mp
      simpa only [hj, hl'] using hxy
    have hh := h j l (by rw [hsz]; exact j.isLt) (by rw [hsz]; exact l.isLt) ho
    rw [getlift, getlift] at hh
    simpa only [hj, hl', Fin.eta] using hh
  · intro h x y hx hy hxy
    have ho : Before r (liftRank r x.val) (liftRank r y.val) := by
      apply (before_lift r x.val y.val).mpr
      exact (hb.2.2 x.val y.val (by change _ < (blocks _ _).size at hx; omega)
        (by change _ < (blocks _ _).size at hy; omega)).mp hxy
    rw [getlift, getlift]
    apply h _ _ (by change liftRank r x.val ≠ r; unfold liftRank; split_ifs <;> omega)
      (by change liftRank r y.val ≠ r; unfold liftRank; split_ifs <;> omega) ho

/-- Compatibility is necessary when the current closure and both base orders
are realized by one and the same closing-time function. -/
theorem compatible_of_orders {α : Type} (q : List α) (f : α → ℕ)
    (s : Base) (k r : ℕ) (hlen : q.length = s.size + k) (hr : r < q.length)
    (hold : Respects q f s) (hnew : ClosureRespects q f r)
    (hfirst : ∀ j : Fin q.length, j.val ≠ r → f (q[r]) < f (q.get j)) :
    Compatible s k r := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hrold j hj hne
    let x : Fin q.length := ⟨r, hr⟩
    let y : Fin q.length := ⟨j, by omega⟩
    by_contra hb
    rcases (before_reverse s.cut r j).mp hb with he | he
    · exact hne he.symm
    · have hh := hold y x hj hrold he
      have hf := hfirst y hne
      change f (q[j]) < f (q[r]) at hh
      exact (not_lt_of_ge hh.le) hf
  · intro x y hx hy hxr hyr hxy
    exact (closure_comparison q f r hnew ⟨x, by omega⟩ ⟨y, by omega⟩ hxr hyr).mp
      (hold _ _ hx hy hxy)

/-- Conversely, compatibility and the next realized total order recover every
old comparison, including constraints involving the just-closed opener. -/
theorem respects_of_compatible {α : Type} (q : List α) (f : α → ℕ)
    (s : Base) (k r : ℕ) (hr : r < q.length)
    (hc : Compatible s k r) (hnew : ClosureRespects q f r)
    (hfirst : ∀ j : Fin q.length, j.val ≠ r → f (q[r]) < f (q.get j)) :
    Respects q f s := by
  intro x y hx hy hxy
  by_cases hxr : x.val = r
  · have hne : y.val ≠ r := by
      unfold Before at hxy
      omega
    have hh := hfirst y hne
    have he : q.get x = q[r] := by cases x; simp_all
    simpa only [he] using hh
  · by_cases hyr : y.val = r
    · have ho := hc.2.1 (by omega) x.val hx hxr
      unfold Before at ho hxy
      omega
    · exact hnew x y hxr hyr (hc.2.2 x.val y.val hx hy hxr hyr hxy)

open TripleAvoidingMatchingsDefs

/-- The sequence of exact total orders imposed at closures. -/
def OrderedRun {n : ℕ} (m : Matching n) :
    List (Fin (2 * n)) → List (Fin (2 * n)) → List Step → Prop
  | _, [], [] => True
  | q, v :: vs, .opening :: w => OrderedRun m (q ++ [v]) vs w
  | q, _ :: vs, .closing r :: w =>
      ClosureRespects q (fun x => (m.1 x).val) r ∧ OrderedRun m (q.eraseIdx r) vs w
  | _, _, _ => False

private theorem realizes_queued {n : ℕ} (m : Matching n)
    {q vs : List (Fin (2 * n))} {w : List Step} (h : Realizes m q vs w) :
    ∀ x ∈ q, ∃ b ∈ vs, m.1 x = b := by
  induction h with
  | nil => simp
  | @opening q vs w v ho h ih =>
    intro x hx
    obtain ⟨b, hb, he⟩ := ih x (by simp [hx])
    exact ⟨b, by simp [hb], he⟩
  | @closing q vs w v r hr he h ih =>
    intro x hx
    by_cases hsel : x = q[r]
    · refine ⟨v, by simp, ?_⟩
      rw [hsel, ← he]
      exact (m.2 v).1
    · have hx' : x ∈ q.eraseIdx r := by
        have hh := (List.getElem_cons_eraseIdx_perm hr).mem_iff.mpr hx
        simpa only [List.mem_cons, hsel, false_or] using hh
      obtain ⟨b, hb, he⟩ := ih x hx'
      exact ⟨b, by simp [hb], he⟩

/-- The independently defined transition system is equivalent to realization
of the old base and of every subsequent closure order. -/
theorem normalized_run {n : ℕ} (m : Matching n)
    {q vs : List (Fin (2 * n))} {w : List Step} (h : Realizes m q vs w)
    (hq : q.Pairwise (· < ·)) (hv : vs.Pairwise (· < ·))
    (hb : ∀ x ∈ q, ∀ v ∈ vs, x < v) :
    ∀ (s : Base) (k : ℕ), s.Valid → q.length = s.size + k →
      (AcceptFrom s k w ↔
        Respects q (fun x => (m.1 x).val) s ∧ OrderedRun m q vs w) := by
  revert hq hv hb
  induction h with
  | nil =>
    intro hq hv hb s k hs hlen
    simp only [List.length_nil] at hlen
    simp only [AcceptFrom, Respects, OrderedRun]
    constructor
    · intro _
      exact ⟨fun x => Fin.elim0 x, trivial⟩
    · intro _
      omega
  | @opening q vs w v ho h ih =>
    intro hq hv hb s k hs hlen
    obtain ⟨hvfirst, hvsort⟩ := List.pairwise_cons.mp hv
    have hbefore : ∀ x ∈ q, x < v := fun x hx => hb x hx v (by simp)
    have hq' : (q ++ [v]).Pairwise (· < ·) :=
      List.pairwise_append.mpr ⟨hq, by simp, by
        intro x hx y hy
        have hy' : y = v := by simpa using hy
        subst y
        exact hbefore x hx⟩
    have hb' : ∀ x ∈ q ++ [v], ∀ y ∈ vs, x < y := by
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact hb x hx y (by simp [hy])
      · have hx' : x = v := by simpa using hx
        subst x
        exact hvfirst y hy
    have hi := ih hq' hvsort hb' s (k + 1) hs (by simp; omega)
    change AcceptFrom s (k + 1) w ↔ Respects q _ s ∧ OrderedRun m (q ++ [v]) vs w
    rw [hi]
    apply and_congr_left
    intro _
    unfold Respects
    constructor
    · intro hh x y hx hy hxy
      have h1 := hh ⟨x.val, by simpa using x.isLt⟩ ⟨y.val, by simpa using y.isLt⟩ hx hy hxy
      simpa only [List.get_eq_getElem, List.getElem_append_left x.isLt,
        List.getElem_append_left y.isLt] using h1
    · intro hh x y hx hy hxy
      have hx' : x.val < q.length := by omega
      have hy' : y.val < q.length := by omega
      have h1 := hh ⟨x.val, hx'⟩ ⟨y.val, hy'⟩ hx hy hxy
      simpa only [List.get_eq_getElem, List.getElem_append_left hx',
        List.getElem_append_left hy'] using h1
  | @closing q vs w v r hr he h ih =>
    intro hq hv hb s k hs hlen
    have hq' := hq.sublist (List.eraseIdx_sublist q r)
    have hb' : ∀ x ∈ q.eraseIdx r, ∀ y ∈ vs, x < y :=
      fun x hx y hy => hb x (List.mem_of_mem_eraseIdx hx) y (by simp [hy])
    obtain ⟨hvfirst, hvsort⟩ := List.pairwise_cons.mp hv
    have hfirst : ∀ j : Fin q.length, j.val ≠ r →
        (m.1 q[r]).val < (m.1 (q.get j)).val := by
      intro j hj
      have hjmem : q.get j ∈ q.eraseIdx r :=
        List.mem_eraseIdx_iff_getElem.mpr ⟨j.val, j.isLt, hj, rfl⟩
      obtain ⟨b, hb, hmb⟩ := realizes_queued m h (q.get j) hjmem
      have hsel : m.1 q[r] = v := by rw [← he]; exact (m.2 v).1
      rw [hsel, hmb]
      exact hvfirst b hb
    change (Permitted s k r ∧ AcceptFrom (afterClose s k r) 0 w) ↔
      Respects q _ s ∧ (ClosureRespects q _ r ∧ OrderedRun m (q.eraseIdx r) vs w)
    constructor
    · rintro ⟨hp, ha⟩
      have ht := transition_spec s k r hs hp
      have hl := List.length_eraseIdx_add_one hr
      have hi := (ih hq' hvsort hb' (afterClose s k r) 0 ht.2.1 (by omega)).mp ha
      have hc := (deletion_order q _ s k r hlen hr).mp hi.1
      exact ⟨respects_of_compatible q _ s k r hr ht.2.2.2 hc hfirst, hc, hi.2⟩
    · rintro ⟨ho, hc, hw⟩
      have hp := (compatible_iff s k r hs).mp
        (compatible_of_orders q _ s k r hlen hr ho hc hfirst)
      have ht := transition_spec s k r hs hp
      have hl := List.length_eraseIdx_add_one hr
      refine ⟨hp, (ih hq' hvsort hb' (afterClose s k r) 0 ht.2.1 (by omega)).mpr ?_⟩
      exact ⟨(deletion_order q _ s k r hlen hr).mpr hc, hw⟩

end D5.S3.Combinatorics.PatternMatchings.P13
