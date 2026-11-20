/- GID: D5/S1/Words/Permutations/FriedenAdaptedWords
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/FriedenAdaptedWords
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Four-wire avoidance implies source-flip adaptedness for reduced reversal words. -/

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

end D5.S1.Words.Permutations.Frieden
