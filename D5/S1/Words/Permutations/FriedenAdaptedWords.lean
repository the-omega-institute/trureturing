/- GID: D5/S1/Words/Permutations/FriedenAdaptedWords
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/FriedenAdaptedWords
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Four-wire avoidance characterizes source-flip adaptedness for reduced reversal words. -/

import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import D5.S1.Words.Permutations.FriedenSortingNetwork

namespace D5.S1.Words.Permutations.Frieden

def edgeVisit {n : Nat} (e : Fin (n - 2)) (i : Fin (n - 1)) : Option Bool :=
  if i.val = e.val then some true
  else if i.val = e.val + 1 then some false
  else none

def SourceAt {n : Nat} (o : Orientation n) (i : Fin (n - 1)) : Prop :=
  ∀ (e : Fin (n - 2)) (tail : Bool), edgeVisit e i = some tail → o e = tail

def flip {n : Nat} (o : Orientation n) (i : Fin (n - 1)) : Orientation n :=
  fun e => if (edgeVisit e i).isSome then !(o e) else o e

def Legal {n : Nat} (o : Orientation n) : Word n → Prop
  | [] => True
  | i :: rest => SourceAt o i ∧ Legal (flip o i) rest

def Adapted {n : Nat} (w : Word n) : Prop :=
  ∃ o : Orientation n, Legal o w

private def projection {n : Nat} (w : Word n) (e : Fin (n - 2)) : List Bool :=
  w.filterMap (edgeVisit e)

private def EdgeLegal (tail : Bool) : List Bool → Prop
  | [] => True
  | a :: rest => tail = a ∧ EdgeLegal (!tail) rest

private def Alternating : List Bool → Prop
  | a :: b :: rest => a ≠ b ∧ Alternating (b :: rest)
  | _ => True

private theorem legal_iff_edges {n : Nat} (w : Word n) (o : Orientation n) :
    Legal o w ↔ ∀ e, EdgeLegal (o e) (projection w e) := by
  induction w generalizing o with
  | nil => simp [Legal, projection, EdgeLegal]
  | cons i rest ih =>
    simp only [Legal, ih, SourceAt, projection, List.filterMap_cons]
    constructor
    · rintro ⟨hsource, hrest⟩ e
      cases hv : edgeVisit e i with
      | none =>
        simpa [hv, flip] using hrest e
      | some tail =>
        exact ⟨hsource e tail hv, by simpa [flip, hv] using hrest e⟩
    · intro h
      constructor
      · intro e tail hv
        have hstep : EdgeLegal (o e) (tail :: List.filterMap (edgeVisit e) rest) := by
          simpa [hv] using h e
        exact hstep.1
      · intro e
        cases hv : edgeVisit e i with
        | none =>
          simpa [hv, flip] using h e
        | some tail =>
          have hstep : EdgeLegal (o e) (tail :: List.filterMap (edgeVisit e) rest) := by
            simpa [hv] using h e
          simpa [flip, hv] using hstep.2

private theorem edgeLegal_iff_alternating (tail : Bool) (xs : List Bool) :
    EdgeLegal tail xs ↔
      (∀ a, xs.head? = some a → tail = a) ∧ Alternating xs := by
  induction xs generalizing tail with
  | nil => simp [EdgeLegal, Alternating]
  | cons a rest ih =>
    rw [EdgeLegal, ih]
    cases rest with
    | nil => simp [Alternating]
    | cons b rest =>
      simp only [List.head?_cons, Option.some.injEq, forall_eq', Alternating]
      cases tail <;> cases a <;> cases b <;> simp

private theorem adapted_iff_alternating {n : Nat} (w : Word n) :
    Adapted w ↔ ∀ e, Alternating (projection w e) := by
  simp only [Adapted, legal_iff_edges, edgeLegal_iff_alternating]
  constructor
  · rintro ⟨o, ho⟩ e
    exact (ho e).2
  · intro h
    refine ⟨fun e => (projection w e).head?.getD false, fun e => ⟨?_, h e⟩⟩
    intro a ha
    simp [ha]

private theorem nonalternating_repeat {n : Nat} (e : Fin (n - 2)) (w : Word n)
    (h : ¬ Alternating (projection w e)) :
    ∃ u m v i t, w = u ++ i :: m ++ i :: v ∧
      edgeVisit e i = some t ∧ ∀ j ∈ m, edgeVisit e j = none := by
  have bad (l : List Bool) (hl : ¬ Alternating l) :
      ∃ a u v, l = u ++ a :: a :: v := by
    induction l with
    | nil => exact (hl trivial).elim
    | cons a l ih =>
      cases l with
      | nil => exact (hl trivial).elim
      | cons b l =>
        by_cases he : a = b
        · exact ⟨a, [], l, by simp [he]⟩
        · obtain ⟨c, u, v, hu⟩ := ih (fun h => hl ⟨he, h⟩)
          exact ⟨c, a :: u, v, congrArg (a :: ·) hu⟩
  obtain ⟨a, l, r, hsplit⟩ := bad _ h
  have one (v : Word n) (b : Bool) (l : List Bool)
      (hv : projection v e = b :: l) :
      ∃ u i t, v = u ++ i :: t ∧ (∀ j ∈ u, edgeVisit e j = none) ∧
        edgeVisit e i = some b ∧ projection t e = l := by
    induction v with
    | nil => simp [projection] at hv
    | cons i v ih =>
      cases he : edgeVisit e i with
      | none =>
        obtain ⟨u, j, t, rfl, hu, hj, ht⟩ := ih (by simpa [projection, he] using hv)
        exact ⟨i :: u, j, t, rfl, by simpa [he] using hu, hj, ht⟩
      | some b' =>
        have hh : b' = b ∧ projection v e = l := by simpa [projection, he] using hv
        exact ⟨[], i, v, rfl, by simp, hh.1 ▸ he, hh.2⟩
  obtain ⟨u, tail, rfl, _, ht⟩ := List.filterMap_eq_append_iff.mp hsplit
  obtain ⟨v, i, tail', rfl, _, hi, ht'⟩ := one tail a (a :: r) ht
  obtain ⟨m, j, t, rfl, hm, hj, _⟩ := one tail' a r ht'
  have hij : i = j := by
    unfold edgeVisit at hi hj
    split at hi <;> split at hj <;> simp_all [Fin.ext_iff]
  subst j
  exact ⟨u ++ v, m, t, i, a, by simp [List.append_assoc], hi, hm⟩

private def mirrorState {n : Nat} (p : State n) : State n :=
  Fin.revPerm.trans (p.trans Fin.revPerm)

private theorem mirror_left {n : Nat} (i : Fin (n - 1)) :
    left i.rev = (right i).rev := by
  apply Fin.ext
  simp only [left, right, Fin.val_rev]
  have hi := i.isLt
  omega

private theorem mirror_right {n : Nat} (i : Fin (n - 1)) :
    right i.rev = (left i).rev := by
  apply Fin.ext
  simp only [left, right, Fin.val_rev]
  have hi := i.isLt
  omega

private theorem mirror_step {n : Nat} (p : State n) (i : Fin (n - 1)) :
    step (mirrorState p) i.rev = mirrorState (step p i) := by
  ext j
  simp only [step, mirrorState, Equiv.trans_apply, Fin.revPerm_apply,
    mirror_left, mirror_right, Equiv.swap_apply_def]
  by_cases hr : j = (right i).rev
  · subst j
    simp [Ne.symm (left_ne_right i)]
  · by_cases hl : j = (left i).rev
    · subst j
      simp [left_ne_right i]
    · have hrev (k : Fin n) (hk : j ≠ k.rev) : j.rev ≠ k := by
        intro he
        exact hk (by simpa using congrArg Fin.rev he)
      simp [hr, hl, hrev _ hr, hrev _ hl]

private theorem mirror_fold {n : Nat} (p : State n) (w : Word n) :
    (w.map Fin.rev).foldl step (mirrorState p) = mirrorState (w.foldl step p) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => rw [List.map_cons, List.foldl_cons, List.foldl_cons, mirror_step, ih]

private theorem mirror_id {n : Nat} : mirrorState (Equiv.refl (Fin n)) = Equiv.refl _ := by
  ext j
  simp [mirrorState]

private theorem mirror_rev {n : Nat} : mirrorState (Fin.revPerm (n := n)) = Fin.revPerm := by
  ext j
  simp [mirrorState]

private def mirrorSet {n : Nat} (S : Finset (Fin n)) : Finset (Fin n) :=
  S.map Fin.revPerm.toEmbedding

private theorem mem_mirrorSet {n : Nat} (S : Finset (Fin n)) (a : Fin n) :
    a.rev ∈ mirrorSet S ↔ a ∈ S := by
  simp [mirrorSet]

private theorem mirror_rank {n : Nat} (S : Finset (Fin n)) (p : State n) (a : Fin n)
    (ha : a ∈ S) :
    rank S p a + rank (mirrorSet S) (mirrorState p) a.rev + 1 = S.card := by
  let above := S.filter (fun b => p.symm a < p.symm b)
  have he : below (mirrorSet S) (mirrorState p) a.rev = mirrorSet above := by
    ext b
    obtain ⟨c, rfl⟩ := Fin.rev_involutive.surjective b
    rw [below, Finset.mem_filter, mem_mirrorSet, mem_mirrorSet]
    simp [mirrorState, above]
  have hsplit : S.filter (fun b => ¬p.symm b < p.symm a) = insert a above := by
    ext b
    simp only [Finset.mem_insert, above, Finset.mem_filter]
    by_cases hb : b = a
    · simp [hb, ha]
    · have hn : p.symm a ≠ p.symm b := fun h => hb (p.symm.injective h).symm
      rw [not_lt]
      simp [hb, lt_iff_le_and_ne, hn]
  have hn : a ∉ above := by simp [above]
  have h := Finset.card_filter_add_card_filter_not (s := S) (fun b => p.symm b < p.symm a)
  rw [hsplit, Finset.card_insert_of_notMem hn, ← Nat.add_assoc] at h
  unfold rank
  rw [he, mirrorSet, Finset.card_map]
  exact h

private theorem rank_lt_card {n : Nat} (S : Finset (Fin n)) (p : State n) (a : Fin n)
    (ha : a ∈ S) : rank S p a < S.card := by
  have h : below S p a ⊆ S.erase a := by
    intro b hb
    obtain ⟨hm, hl⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_erase.mpr ⟨?_, hm⟩
    intro h
    subst b
    exact (lt_irrefl _) hl
  have hc := Finset.card_le_card h
  rw [Finset.card_erase_of_mem ha] at hc
  have hp := Finset.card_pos.mpr ⟨a, ha⟩
  exact show (below S p a).card < S.card by omega

private theorem restrict_mirror {n : Nat} (S : Finset (Fin n)) (p : State n) (w : Word n) :
    restrictFrom (mirrorSet S) (mirrorState p) (w.map Fin.rev) =
      (restrictFrom S p w).map (fun k => S.card - k) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have hl : mirrorState p (left i.rev) = (p (right i)).rev := by simp [mirrorState, mirror_left]
    have hr : mirrorState p (right i.rev) = (p (left i)).rev := by simp [mirrorState, mirror_right]
    rw [List.map_cons, restrict_cons, restrict_cons, mirror_step, hl, hr, ih]
    have he : (p (right i)).rev ∈ mirrorSet S ∧ (p (left i)).rev ∈ mirrorSet S ↔
        p (left i) ∈ S ∧ p (right i) ∈ S := by
      simp [mem_mirrorSet, and_comm]
    by_cases hm : p (left i) ∈ S ∧ p (right i) ∈ S
    · rw [ite_eq_left (he.mpr hm), ite_eq_left hm, List.map_cons, List.cons.injEq]
      refine ⟨?_, rfl⟩
      have hk := mirror_rank S p (p (right i)) hm.2
      rw [rank_right_before S p i hm.1] at hk
      omega
    · rw [ite_eq_right (fun h => hm (he.mp h)), ite_eq_right hm]

private theorem forbidden_mirror (l : List Nat) (h : l.map (fun k => 4 - k) ∈ forbidden)
    (hbound : ∀ k ∈ l, k < 4) : l ∈ forbidden := by
  have hinvol : (l.map (fun k => 4 - k)).map (fun k => 4 - k) = l := by
    rw [List.map_map]
    clear h
    induction l with
    | nil => rfl
    | cons k l ih =>
      have hk := hbound k (by simp)
      simp only [List.map_cons, List.cons.injEq, Function.comp_apply]
      exact ⟨by omega, ih (fun b hb => hbound b (List.mem_cons_of_mem _ hb))⟩
  have hclosed : ∀ a ∈ forbidden, a.map (fun k => 4 - k) ∈ forbidden := by decide
  exact hinvol ▸ hclosed _ h

private theorem restrict_letter_lt {n : Nat} (S : Finset (Fin n)) (p : State n) (w : Word n)
    (k : Nat) (hk : k ∈ restrictFrom S p w) : k < S.card := by
  induction w generalizing p with
  | nil => simp [restrictFrom] at hk
  | cons i w ih =>
    rw [restrict_cons] at hk
    split at hk
    · rename_i hm
      rcases List.mem_cons.mp hk with rfl | ht
      · have hb := rank_lt_card S p (p (right i)) hm.2
        rwa [rank_right_before S p i hm.1] at hb
      · exact ih _ ht
    · exact ih _ hk

private theorem quartet_right {n : Nat} (u m v : Word n) (i : Fin (n - 1))
    (hi : 0 < i.val)
    (hm : ∀ j ∈ m, j.val + 1 ≠ i.val ∧ j.val ≠ i.val)
    (hw : ReducedReversal (u ++ (i :: m ++ i :: v))) :
    ∃ S : Finset (Fin n), S.card = 4 ∧ restrict (u ++ (i :: m ++ i :: v)) S ∈ forbidden := by
  let w := u ++ (i :: m ++ i :: v)
  have hl : i.rev.val + 2 < n := by
    rw [Fin.val_rev]
    have hb := i.isLt
    omega
  have hm' : ∀ j ∈ m.map Fin.rev, j.val ≠ i.rev.val ∧ j.val ≠ i.rev.val + 1 := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    obtain ⟨h₁,h₂⟩ := hm k hk
    have hik := i.isLt
    have hkk := k.isLt
    simp only [Fin.val_rev]
    omega
  have hw' : ReducedReversal (w.map Fin.rev) := by
    refine ⟨by simpa [w] using hw.1, ?_⟩
    rw [← mirror_id, mirror_fold, hw.2, mirror_rev]
  have he : w.map Fin.rev = u.map Fin.rev ++ (i.rev :: m.map Fin.rev ++ i.rev :: v.map Fin.rev) := by
    simp [w]
  obtain ⟨S, hcard, hs⟩ := quartet_left (u.map Fin.rev) (m.map Fin.rev) (v.map Fin.rev) i.rev
    hl hm' (he ▸ hw')
  rw [← he] at hs
  let T := mirrorSet S
  have hT : T.card = 4 := by simpa [T, mirrorSet] using hcard
  have hTT : mirrorSet T = S := by
    ext a
    obtain ⟨b, rfl⟩ := Fin.rev_involutive.surjective a
    rw [mem_mirrorSet]
    change b ∈ mirrorSet S ↔ b.rev ∈ S
    simpa only [Fin.rev_rev] using mem_mirrorSet S b.rev
  refine ⟨T, hT, ?_⟩
  have ht := restrict_mirror T (Equiv.refl _) w
  rw [hTT, mirror_id, hT] at ht
  apply forbidden_mirror (restrict w T)
  · exact ht ▸ hs
  · intro k hk
    have h := restrict_letter_lt T (Equiv.refl _) w k hk
    rwa [hT] at h

private theorem forcedQuartet {n : Nat} (w : Word n) (hw : ReducedReversal w)
    (e : Fin (n - 2)) (hbad : ¬ Alternating (projection w e)) :
    ∃ S : Finset (Fin n), S.card = 4 ∧ restrict w S ∈ forbidden := by
  obtain ⟨u, m, v, i, b, rfl, hi, hm⟩ := nonalternating_repeat e w hbad
  have hnone (j : Fin (n - 1)) (hj : j ∈ m) : j.val ≠ e.val ∧ j.val ≠ e.val + 1 := by
    have h := hm j hj
    unfold edgeVisit at h
    by_cases h₁ : j.val = e.val
    · simp [h₁] at h
    · by_cases h₂ : j.val = e.val + 1
      · simp [h₂] at h
      · exact ⟨h₁, h₂⟩
  rw [List.append_assoc, List.cons_append] at hw ⊢
  have hei := e.isLt
  unfold edgeVisit at hi
  split at hi
  · rename_i he
    apply quartet_left u m v i (by omega) _ hw
    intro j hj
    simpa only [he] using hnone j hj
  · split at hi
    · rename_i he
      apply quartet_right u m v i (by omega) _ hw
      intro j hj
      have h := hnone j hj
      omega
    · contradiction

/-- A reduced reversal word avoiding the four chronological subnetworks of §4.4
admits a sequence of source reflections on the path of generators. -/
theorem avoidance_implies_adapted (n : Nat) (w : Word n)
    (hw : ReducedReversal w) (ha : AvoidsX w) : Adapted w := by
  apply (adapted_iff_alternating w).mpr
  intro e
  by_contra hbad
  obtain ⟨S, hc, hs⟩ := forcedQuartet w hw e hbad
  exact ha S hc hs

/-- A wire changes direction only at the right boundary after moving right,
or at the left boundary after moving left. -/
private inductive Track (bound : Nat) : Nat → Option Bool → List Bool → Prop
  | nil {p d} : Track bound p d []
  | right {p d l} : p < bound → (d ≠ some false ∨ p = 0) →
      Track bound (p + 1) (some true) l → Track bound p d (true :: l)
  | left {p d l} : 0 < p → (d ≠ some true ∨ p = bound) →
      Track bound (p - 1) (some false) l → Track bound p d (false :: l)

/-- The most recent movement fixes the arrow between the two generators
incident to an interior wire position. -/
private def Separated {n : Nat} (o : Orientation n) (p : Nat) (d : Option Bool) : Prop :=
  ∀ b, d = some b → ∀ e : Fin (n - 2), e.val + 1 = p → o e = !b

private theorem visit_true {n : Nat} (e : Fin (n - 2)) (i : Fin (n - 1))
    (h : i.val = e.val) : edgeVisit e i = some true := by simp [edgeVisit, h]

private theorem visit_false {n : Nat} (e : Fin (n - 2)) (i : Fin (n - 1))
    (h : i.val = e.val + 1) : edgeVisit e i = some false := by
  simp [edgeVisit, h]

private theorem legal_track {n : Nat} (p : State n) (a : Fin n) (o : Orientation n)
    (w : Word n) (d : Option Bool) (hlegal : Legal o w)
    (hsep : Separated o (p.symm a).val d) :
    Track (n - 1) (p.symm a).val d (wireDirections p a w) := by
  induction w generalizing p o d with
  | nil => exact .nil
  | cons i w ih =>
    obtain ⟨hsrc, hlegal⟩ := hlegal
    have hleft : (step p i).symm (p (left i)) = right i := by simp [step]
    have hright : (step p i).symm (p (right i)) = left i := by simp [step]
    have hbound := i.isLt
    rw [wireDirections]
    by_cases hl : p (left i) = a
    · rw [ite_eq_left hl, ← hl, Equiv.symm_apply_apply]
      apply Track.right hbound
      · by_cases hd : d = some false
        · right
          by_contra hn
          let e : Fin (n - 2) := ⟨i.val - 1, by omega⟩
          have he : e.val + 1 = i.val := by dsimp [e]; omega
          have hf := hsrc e false (visit_false e i he.symm)
          have ht := hsep false hd e (by rwa [← hl, Equiv.symm_apply_apply])
          rw [hf] at ht
          contradiction
        · exact Or.inl hd
      · have hsep' : Separated (flip o i) ((step p i).symm (p (left i))).val (some true) := by
          intro b hb e he
          obtain rfl := Option.some.inj hb
          rw [hleft] at he
          have hv := visit_true e i (by exact Nat.add_right_cancel he.symm)
          unfold flip
          simp [hv, hsrc e true hv]
        change Track (n - 1) (right i).val (some true) _
        rw [← hleft, hl]
        apply ih _ _ _ hlegal
        rwa [← hl]
    · rw [ite_eq_right hl]
      by_cases hr : p (right i) = a
      · rw [ite_eq_left hr, ← hr, Equiv.symm_apply_apply]
        apply Track.left (show 0 < (right i).val by exact Nat.succ_pos _)
        · by_cases hd : d = some true
          · right
            by_contra hn
            let e : Fin (n - 2) := ⟨i.val, by change i.val + 1 ≠ n - 1 at hn; omega⟩
            have hf := hsrc e true (visit_true e i rfl)
            have ht := hsep true hd e (by rw [← hr, Equiv.symm_apply_apply]; rfl)
            rw [hf] at ht
            contradiction
          · exact Or.inl hd
        · have hsep' : Separated (flip o i) ((step p i).symm (p (right i))).val (some false) := by
            intro b hb e he
            obtain rfl := Option.some.inj hb
            rw [hright] at he
            have hv := visit_false e i he.symm
            unfold flip
            simp [hv, hsrc e false hv]
          change Track (n - 1) (left i).val (some false) _
          rw [← hright, hr]
          apply ih _ _ _ hlegal
          rwa [← hr]
      · rw [ite_eq_right hr]
        have h₁ : p.symm a ≠ left i := fun h => hl ((p.symm_apply_eq.mp h).symm)
        have h₂ : p.symm a ≠ right i := fun h => hr ((p.symm_apply_eq.mp h).symm)
        have he : (step p i).symm a = p.symm a := by
          simp [step, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
        rw [← he]
        apply ih _ _ _ hlegal
        intro b hb e hpos
        rw [he] at hpos
        have hm₁ : i.val ≠ e.val := by
          intro hh
          apply h₂
          exact Fin.ext (by change (p.symm a).val = i.val + 1; omega)
        have hm₂ : i.val ≠ e.val + 1 := by
          intro hh
          apply h₁
          exact Fin.ext (by change (p.symm a).val = i.val; omega)
        simpa [flip, edgeVisit, hm₁, hm₂] using hsep b hb e hpos

private theorem track_stays_right {B p : Nat} {l : List Bool}
    (ht : Track B p (some true) l) (hl : p + l.length ≤ B) :
    l = List.replicate l.length true := by
  generalize hd : some true = d at ht
  induction ht with
  | nil => rfl
  | right _ _ h ih =>
    cases hd
    rw [List.length_cons, List.replicate_succ, List.cons.injEq]
    exact ⟨rfl, ih (by simp only [List.length_cons] at hl; omega) rfl⟩
  | left _ h _ _ =>
    rw [← hd] at h
    simp only [ne_eq, not_true_eq_false, false_or] at h
    simp only [List.length_cons] at hl
    omega

private theorem track_stays_left {B p : Nat} {l : List Bool}
    (ht : Track B p (some false) l) (hl : l.length ≤ p) :
    l = List.replicate l.length false := by
  generalize hd : some false = d at ht
  induction ht with
  | nil => rfl
  | right _ h _ _ =>
    rw [← hd] at h
    simp only [ne_eq, not_true_eq_false, false_or] at h
    simp only [List.length_cons] at hl
    omega
  | left _ _ h ih =>
    cases hd
    rw [List.length_cons, List.replicate_succ, List.cons.injEq]
    exact ⟨rfl, ih (by simp only [List.length_cons] at hl; omega) rfl⟩

private theorem track_one_turn {B p : Nat} {d : Bool} {l : List Bool}
    (ht : Track B p (some d) l) (hl : l.length ≤ B) :
    ∃ a b, l = List.replicate a d ++ List.replicate b (!d) := by
  generalize hd : some d = prev at ht
  induction ht generalizing d with
  | nil => exact ⟨0, 0, rfl⟩
  | @right p prev l hp h ht ih =>
    subst prev
    have hlen : l.length + 1 ≤ B := hl
    cases d
    · simp only [ne_eq, not_true_eq_false, false_or] at h
      have he := track_stays_right ht (by omega)
      exact ⟨0, l.length + 1, congrArg (true :: ·) he⟩
    · obtain ⟨a,b,he⟩ := ih (by omega) rfl
      exact ⟨a + 1,b,congrArg (true :: ·) he⟩
  | @left p prev l hp h ht ih =>
    subst prev
    have hlen : l.length + 1 ≤ B := hl
    cases d
    · obtain ⟨a,b,he⟩ := ih (by omega) rfl
      exact ⟨a + 1,b,congrArg (false :: ·) he⟩
    · simp only [ne_eq, not_true_eq_false, false_or] at h
      have he := track_stays_left ht (by omega)
      exact ⟨0, l.length + 1, congrArg (false :: ·) he⟩

private theorem track_one_turn_start {B p : Nat} {l : List Bool}
    (ht : Track B p none l) (hl : l.length ≤ B) :
    ∃ d a b, l = List.replicate a d ++ List.replicate b (!d) := by
  cases ht with
  | nil => exact ⟨true,0,0,rfl⟩
  | right _ _ h =>
    obtain ⟨a,b,he⟩ := track_one_turn h (by simp only [List.length_cons] at hl; omega)
    exact ⟨true,a+1,b,congrArg (true :: ·) he⟩
  | left _ _ h =>
    obtain ⟨a,b,he⟩ := track_one_turn h (by simp only [List.length_cons] at hl; omega)
    exact ⟨false,a+1,b,congrArg (false :: ·) he⟩


private theorem nonconstant_triple_not_sublist (d x : Bool) (a b : Nat) :
    ¬ [x, !x, x].Sublist (List.replicate a d ++ List.replicate b (!d)) := by
  intro h
  obtain ⟨l, r, he, hl, hr⟩ := List.sublist_append_iff.mp h
  have hL : ∀ k ∈ l, k = d := fun k hk => (List.mem_replicate.mp (hl.subset hk)).2
  have hR : ∀ k ∈ r, k = !d := fun k hk => (List.mem_replicate.mp (hr.subset hk)).2
  have hn : x ≠ !x := by cases x <;> decide
  cases l with
  | nil =>
    simp only [List.nil_append] at he
    subst r
    exact hn ((hR x (by simp)).trans (hR (!x) (by simp)).symm)
  | cons k l =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    cases l with
    | nil =>
      simp only [List.nil_append] at he
      subst r
      exact hn ((hR x (by simp)).trans (hR (!x) (by simp)).symm)
    | cons k l =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact hn ((hL x (by simp)).trans (hL (!x) (by simp)).symm)

private theorem adapted_no_double_turn {n : Nat} (w : Word n)
    (hw : ReducedReversal w) (ha : Adapted w) (a : Fin n) (d : Bool) :
    ¬ [d, !d, d].Sublist (wireDirections (Equiv.refl _) a w) := by
  obtain ⟨o, ho⟩ := ha
  have ht := legal_track (Equiv.refl _) a o w none ho (by simp [Separated])
  obtain ⟨b,x,y,h⟩ := track_one_turn_start ht (wire_directions_bound w a hw)
  rw [h]
  exact nonconstant_triple_not_sublist b d x y


/-- Replay the movements of a selected wire from its current zero-based rank
and a chronological word of one-based restricted generators. -/
private def restrictedDirections (r : Nat) : List Nat → List Bool
  | [] => []
  | k :: ks =>
    if k = r + 1 then true :: restrictedDirections (r + 1) ks
    else if k = r then false :: restrictedDirections (r - 1) ks
    else restrictedDirections r ks

private theorem rank_strict {n : Nat} (S : Finset (Fin n)) (p : State n)
    (a b : Fin n) (ha : a ∈ S) (h : p.symm a < p.symm b) :
    rank S p a < rank S p b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro c hc
    exact Finset.mem_filter.mpr ((Finset.mem_filter.mp hc).imp id (fun hc => hc.trans h))
  · intro he
    have hc : a ∈ below S p b := Finset.mem_filter.mpr ⟨ha, h⟩
    rw [← he] at hc
    exact (lt_irrefl _) (Finset.mem_filter.mp hc).2

private theorem rank_ne {n : Nat} (S : Finset (Fin n)) (p : State n)
    (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    rank S p a ≠ rank S p b := by
  rcases lt_or_gt_of_ne (fun h => hne (p.symm.injective h)) with h | h
  · exact (rank_strict S p a b ha h).ne
  · exact (rank_strict S p b a hb h).ne.symm

private theorem restricted_directions_sublist {n : Nat} (S : Finset (Fin n)) (p : State n)
    (w : Word n) (a : Fin n) (ha : a ∈ S) :
    (restrictedDirections (rank S p a) (restrictFrom S p w)).Sublist
      (wireDirections p a w) := by
  induction w generalizing p with
  | nil => exact .slnil
  | cons i w ih =>
    have ht := ih (step p i)
    rw [restrict_cons, wireDirections]
    by_cases hS : p (left i) ∈ S ∧ p (right i) ∈ S
    · rw [ite_eq_left hS, restrictedDirections]
      by_cases hl : p (left i) = a
      · rw [ite_eq_left hl, hl, ite_eq_left rfl]
        rw [← hl, rank_step_move_right S p i hS.2, hl] at ht
        exact ht.cons_cons _
      · rw [ite_eq_right hl]
        by_cases hr : p (right i) = a
        · rw [ite_eq_left hr]
          have h₁ : rank S p a = rank S p (p (left i)) + 1 := hr ▸ rank_right_before S p i hS.1
          have h₂ : rank S (step p i) a = rank S p a - 1 := by
            rw [← hr, rank_step_move_left S p i hS.1, rank_right_before S p i hS.1]
            rfl
          rw [ite_eq_right (by omega : rank S p (p (left i)) + 1 ≠ rank S p a + 1),
            ite_eq_left h₁.symm]
          rw [h₂] at ht
          exact ht.cons_cons _
        · rw [ite_eq_right hr]
          have hn₁ := rank_ne S p _ _ hS.1 ha hl
          have hn₂ := rank_ne S p _ _ hS.2 ha hr
          rw [rank_right_before S p i hS.1] at hn₂
          rw [ite_eq_right (by omega : rank S p (p (left i)) + 1 ≠ rank S p a + 1),
            ite_eq_right hn₂]
          rwa [rank_other S p i a hl hr] at ht
    · rw [ite_eq_right hS]
      rw [rank_step_stay S p i a ha hS] at ht
      by_cases hl : p (left i) = a
      · rw [ite_eq_left hl]
        exact ht.cons _
      · rw [ite_eq_right hl]
        by_cases hr : p (right i) = a
        · rw [ite_eq_left hr]
          exact ht.cons _
        · rwa [ite_eq_right hr]

private theorem rank_at_orderEmb {n k : Nat} (S : Finset (Fin n))
    (h : S.card = k) (i : Fin k) :
    rank S (Equiv.refl _) (S.orderEmbOfFin h i) = i.val := by
  have he : below S (Equiv.refl _) (S.orderEmbOfFin h i) =
      (Finset.Iio i).map (S.orderEmbOfFin h).toEmbedding := by
    ext b
    rw [below, Finset.mem_filter, Finset.mem_map]
    change (b ∈ S ∧ b < S.orderEmbOfFin h i) ↔
      ∃ j ∈ Finset.Iio i, S.orderEmbOfFin h j = b
    simp only [Finset.mem_Iio]
    constructor
    · rintro ⟨hb, hbi⟩
      have hm : b ∈ (Finset.univ : Finset (Fin k)).map (S.orderEmbOfFin h).toEmbedding := by
        rwa [Finset.map_orderEmbOfFin_univ]
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hm
      change S.orderEmbOfFin h j < S.orderEmbOfFin h i at hbi
      exact ⟨j, (S.orderEmbOfFin h).lt_iff_lt.mp hbi, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (S.orderEmbOfFin h).strictMono hj⟩
  rw [rank, he, Finset.card_map, Fin.card_Iio]

private theorem forbidden_turn (w : List Nat) (hw : w ∈ forbidden) :
    ∃ i : Fin 4, ∃ d : Bool, restrictedDirections i.val w = [d, !d, d] := by
  simp only [forbidden, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨2, false, by decide⟩
  · exact ⟨1, true, by decide⟩
  · exact ⟨1, true, by decide⟩
  · exact ⟨2, false, by decide⟩

private theorem adapted_implies_avoidance (n : Nat) (w : Word n)
    (hw : ReducedReversal w) (had : Adapted w) : AvoidsX w := by
  intro S hS hs
  obtain ⟨i, d, hd⟩ := forbidden_turn (restrict w S) hs
  let a := S.orderEmbOfFin hS i
  have ha : a ∈ S := Finset.orderEmbOfFin_mem _ _ _
  have hr : rank S (Equiv.refl _) a = i.val := rank_at_orderEmb S hS i
  have hsub := restricted_directions_sublist S (Equiv.refl _) w a ha
  rw [hr, ← restrict, hd] at hsub
  exact adapted_no_double_turn w hw had a d hsub

/-- Conjecture 4.10 of Frieden, Pylyavskyy and Rybnikov. -/
theorem conjecture410 (n : Nat) (w : Word n) (hw : ReducedReversal w) :
    AvoidsX w ↔ Adapted w :=
  ⟨avoidance_implies_adapted n w hw, adapted_implies_avoidance n w hw⟩

end D5.S1.Words.Permutations.Frieden
