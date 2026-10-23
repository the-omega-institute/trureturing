/- GID: D5/S1/Words/UnaryGapWords
   generality: G
   mirror-B: D5/B/S1/Words/UnaryGapWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unique occurrence-indexed unary gaps and their native mask traces. -/

import D5.S1.Words.HughesBlockExchange
import Mathlib.Data.List.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.UnaryGapWords

open D5.S1.Words.HughesBlockExchange
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder

noncomputable section

variable {α : Type*}

local instance : DecidableEq α := Classical.decEq α

/-- Actual concatenation, including zero length gaps and repeated separators. -/
def gap (a : α) : List α → List Nat → List α
  | [], h => List.replicate (h.headD 0) a
  | c :: cs, h => List.replicate (h.headD 0) a ++ c :: gap a cs h.tail

private def bump : List Nat → List Nat
  | [] => []
  | n :: ns => (n + 1) :: ns

/-- The non-unary occurrences retain their order and multiplicity. -/
noncomputable def spine (a : α) (w : List α) : List α := by
  classical
  exact w.filter (· ≠ a)

/-- Gap lengths are recovered from the actual word, independently of masks. -/
noncomputable def sizes (a : α) : List α → List Nat := by
  classical
  exact fun w => match w with
    | [] => [0]
    | x :: xs => if x = a then bump (sizes a xs) else 0 :: sizes a xs

private theorem sizes_length (a : α) (w : List α) :
    (sizes a w).length = (spine a w).length + 1 := by
  classical
  induction w with
  | nil => simp [sizes, spine]
  | cons x w ih =>
    by_cases hx : x = a
    · subst x
      have hn : sizes a w ≠ [] := by intro h; simp [h] at ih
      cases hs : sizes a w with
      | nil => exact (hn hs).elim
      | cons n ns => simpa [sizes, spine, bump, hs] using ih
    · simpa [sizes, spine, hx] using ih

private theorem sizes_ne_nil (a : α) (w : List α) : sizes a w ≠ [] := by
  have := sizes_length a w
  intro h
  simp [h] at this

private theorem spine_cons (a x : α) (w : List α) :
    spine a (x :: w) = if x = a then spine a w else x :: spine a w := by
  classical
  by_cases hx : x = a <;> simp [spine, hx]

private theorem spine_away (a : α) (w : List α) : ∀ c ∈ spine a w, c ≠ a := by
  classical
  simp [spine]

private theorem spine_replicate_append (a : α) (n : Nat) (w : List α) :
    spine a (List.replicate n a ++ w) = spine a w := by
  classical
  induction n with
  | zero => simp
  | succ n ih => simpa [List.replicate_succ, spine] using ih

private theorem sizes_replicate_append (a : α) (n : Nat) (w : List α) :
    sizes a (List.replicate n a ++ w) =
      (n + (sizes a w).headD 0) :: (sizes a w).tail := by
  classical
  have hn := sizes_ne_nil a w
  induction n with
  | zero => cases h : sizes a w <;> simp_all
  | succ n ih =>
    simpa [List.replicate_succ, sizes, ih, bump, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using congrArg bump ih

private theorem recover (a : α) (w : List α) :
    gap a (spine a w) (sizes a w) = w := by
  classical
  induction w with
  | nil => simp [spine, sizes, gap]
  | cons x w ih =>
    by_cases hx : x = a
    · subst x
      cases hc : spine a w with
      | nil =>
        cases hh : sizes a w with
        | nil => exact (sizes_ne_nil a w hh).elim
        | cons n ns => simpa [spine_cons, sizes, bump, gap, hc, hh, List.replicate_succ] using (congrArg (a :: ·) ih)
      | cons c cs =>
        cases hh : sizes a w with
        | nil => exact (sizes_ne_nil a w hh).elim
        | cons n ns => simpa [spine_cons, sizes, bump, gap, hc, hh, List.replicate_succ] using (congrArg (a :: ·) ih)
    · simpa [spine_cons, sizes, hx, gap] using congrArg (x :: ·) ih

theorem profile_gap (a : α) (cs : List α) (h : List Nat)
    (ha : ∀ c ∈ cs, c ≠ a) (hl : h.length = cs.length + 1) :
    spine a (gap a cs h) = cs ∧ sizes a (gap a cs h) = h := by
  classical
  induction cs generalizing h with
  | nil =>
    cases h with
    | nil => simp at hl
    | cons n ns =>
      have hn : ns = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst ns
      simp only [gap, List.headD_cons]
      simpa [spine, sizes] using And.intro
        (spine_replicate_append a n []) (sizes_replicate_append a n [])
  | cons c cs ih =>
    cases h with
    | nil => simp at hl
    | cons n hs =>
      have hc : c ≠ a := ha c (by simp)
      have ht := ih hs (fun x hx => ha x (by simp [hx])) (by simpa using hl)
      simp only [gap, List.headD_cons, List.tail_cons]
      rw [spine_replicate_append, sizes_replicate_append, spine_cons]
      simp [sizes, hc, ht.1, ht.2]

/-- Uniqueness is for actual indexed occurrences, even when separators repeat. -/
theorem gap_injective (a : α) (cs ds : List α) (h k : List Nat)
    (hc : ∀ c ∈ cs, c ≠ a) (hd : ∀ d ∈ ds, d ≠ a)
    (hh : h.length = cs.length + 1) (hk : k.length = ds.length + 1)
    (he : gap a cs h = gap a ds k) : cs = ds ∧ h = k := by
  have hp := profile_gap a cs h hc hh
  have hq := profile_gap a ds k hd hk
  constructor
  · simpa [hp.1, hq.1] using congrArg (spine a) he
  · simpa [hp.2, hq.2] using congrArg (sizes a) he

/-- Canonical existence is independent of a shuffle or a minimum. -/
theorem gap_exists (a : α) (w : List α) :
    ∃ cs h, (∀ c ∈ cs, c ≠ a) ∧ h.length = cs.length + 1 ∧ w = gap a cs h :=
  ⟨spine a w, sizes a w, spine_away a w, sizes_length a w, (recover a w).symm⟩

/-- A full positional mask trace, with the non-unary occurrences forced to q.
Each gap retains every source label, rather than just its count. -/
inductive Trace (a : α) (q : Side) : List α → List Nat → List Nat →
    List α → List Side → Prop
  | last (b : List Side) :
      Trace a q [] [b.count q] [b.count (if q = .first then .second else .first)]
        (List.replicate b.length a) b
  | next (b : List Side) (c : α) (hc : c ≠ a)
      {cs : List α} {h e : List Nat} {w : List α} {M : List Side}
      (tail : Trace a q cs h e w M) :
      Trace a q (c :: cs) (b.count q :: h)
        (b.count (if q = .first then .second else .first) :: e)
        (List.replicate b.length a ++ c :: w) (b ++ q :: M)

private theorem count_sides (b : List Side) :
    b.count .first + b.count .second = b.length := by
  induction b with
  | nil => simp
  | cons x b ih => cases x <;> simp_all [List.count_cons] <;> omega

private theorem projection_replicate (a : α) (q : Side) (b : List Side) :
    projection q (List.replicate b.length a) b = List.replicate (b.count q) a := by
  induction b with
  | nil => simp [projection]
  | cons x b ih =>
    cases x <;> cases q <;>
      simp_all [projection, List.replicate_succ, List.count_cons]

private theorem projection_cons (q t : Side) (a : α) (w : List α) (M : List Side) :
    projection q (a :: w) (t :: M) =
      if t = q then a :: projection q w M else projection q w M := by
  by_cases h : t = q <;> simp [projection, List.filterMap_cons, h]

/-- Both original ordered projections are recovered, not inferred from a
single unary commutation. -/
theorem trace_projections (a : α) (q : Side) {cs : List α} {h e : List Nat}
    {w : List α} {M : List Side} (ht : Trace a q cs h e w M) :
    M.length = w.length ∧ h.length = cs.length + 1 ∧ e.length = h.length ∧
    (∀ c ∈ cs, c ≠ a) ∧
    projection q w M = gap a cs h ∧
    projection (if q = .first then .second else .first) w M = List.replicate e.sum a ∧
    w = gap a cs (List.zipWith (· + ·) h e) := by
  induction ht with
  | last b =>
    cases q <;> simp [gap, projection_replicate, count_sides, Nat.add_comm]
  | @next b c hc cs h e w M ht ih =>
    rcases ih with ⟨hl,hh,he,ha,hp,hp',hw⟩
    have hx : (List.replicate b.length a).length = b.length := by simp
    refine ⟨by simp [hl], by simp [hh], by simp [he], ?_, ?_, ?_, ?_⟩
    · simpa using And.intro hc ha
    · rw [projection_append _ _ _ _ _ hx, projection_cons, projection_replicate, hp]
      simp [gap]
    · rw [projection_append _ _ _ _ _ hx, projection_cons, projection_replicate, hp']
      cases q <;> simp
    · cases q <;> simp [gap, ← hw, count_sides, Nat.add_comm]


private theorem trace_prepend (a : α) (q t : Side) {cs : List α}
    {h e : List Nat} {w : List α} {M : List Side} (ht : Trace a q cs h e w M) :
    ∃ h' e', Trace a q cs h' e' (a :: w) (t :: M) := by
  cases ht with
  | last =>
    refine ⟨[(t :: M).count q],
      [(t :: M).count (if q = .first then .second else .first)], ?_⟩
    simpa [List.replicate_succ] using (Trace.last (a := a) (q := q) (t :: M))
  | @next b c hc cs h e w M tail =>
    refine ⟨(t :: b).count q :: h,
      (t :: b).count (if q = .first then .second else .first) :: e, ?_⟩
    simpa [List.replicate_succ] using (Trace.next (t :: b) c hc tail)

/-- Exhaustiveness uses the actual projection of every position. -/
theorem trace_exists (a : α) (q : Side) (w : List α) (M : List Side)
    (hl : M.length = w.length)
    (hp : ∀ x ∈ projection (if q = .first then .second else .first) w M, x = a) :
    ∃ cs h e, Trace a q cs h e w M := by
  induction w generalizing M with
  | nil =>
    have hm : M = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst M
    exact ⟨[], [0], [0], Trace.last []⟩
  | cons x w ih =>
    cases M with
    | nil => simp at hl
    | cons t M =>
      have htail : ∀ y ∈ projection (if q = .first then .second else .first) w M,
          y = a := by
        intro y hy
        apply hp y
        rw [projection_cons]
        split_ifs <;> simp_all
      obtain ⟨cs, h, e, ht⟩ := ih M (by simpa using hl) htail
      by_cases hx : x = a
      · subst x
        obtain ⟨h', e', ht'⟩ := trace_prepend a q t ht
        exact ⟨cs, h', e', ht'⟩
      · have htq : t = q := by
          by_contra hne
          have hp' := hp x
          have hmem : x ∈ projection (if q = .first then .second else .first)
              (x :: w) (t :: M) := by
            cases q <;> cases t <;> simp_all [projection_cons]
          exact hx (hp' hmem)
        subst t
        exact ⟨x :: cs, 0 :: h, 0 :: e, by simpa using Trace.next [] x hx ht⟩

/-- Labels grouped inside their actual letter gaps; the reverse orientation
places outer base mass outside the inserted source. -/
def grouped (q : Side) : List α → List Nat → List Nat → List Side
  | [], h, e => List.replicate (h.headD 0) q ++
      List.replicate (e.headD 0) (if q = .first then .second else .first)
  | _ :: cs, h, e =>
      (if q = .first then
        List.replicate (e.headD 0) .second ++ List.replicate (h.headD 0) .first
      else List.replicate (h.headD 0) .second ++ List.replicate (e.headD 0) .first) ++
        q :: grouped q cs h.tail e.tail

/-- Any nonnegative mass vector is realized by a complete native position mask. -/
theorem trace_construct (a : α) (q : Side) (cs : List α) (h e : List Nat)
    (ha : ∀ c ∈ cs, c ≠ a) (hh : h.length = cs.length + 1)
    (he : e.length = h.length) :
    Trace a q cs h e (gap a cs (List.zipWith (· + ·) h e)) (grouped q cs h e) := by
  induction cs generalizing h e with
  | nil =>
    cases h with
    | nil => simp at hh
    | cons n hs =>
      have hs0 : hs = [] := List.length_eq_zero_iff.mp (by simpa using hh)
      subst hs
      cases e with
      | nil => simp at he
      | cons k es =>
        have es0 : es = [] := List.length_eq_zero_iff.mp (by simpa using he)
        subst es
        let b := List.replicate n q ++ List.replicate k (if q = .first then .second else .first)
        have hb := Trace.last (a := a) (q := q) b
        cases q <;> simpa [grouped, b, gap, List.count_replicate, Nat.add_comm] using hb
  | cons c cs ih =>
    cases h with
    | nil => simp at hh
    | cons n hs =>
      cases e with
      | nil => simp at he
      | cons k es =>
        have ht := ih hs es (fun x hx => ha x (by simp [hx]))
          (by simpa using hh) (by simpa using he)
        let b : List Side := if q = .first then List.replicate k .second ++ List.replicate n .first
          else List.replicate n .second ++ List.replicate k .first
        have hb := Trace.next b c (ha c (by simp)) ht
        cases q <;> simpa [grouped, b, gap, List.count_replicate, Nat.add_comm] using hb

private theorem zip_add_cancel (h e f : List Nat) (he : e.length = h.length)
    (hf : f.length = h.length)
    (hh : List.zipWith (· + ·) h e = List.zipWith (· + ·) h f) : e = f := by
  induction h generalizing e f with
  | nil =>
    have he0 : e = [] := List.length_eq_zero_iff.mp he
    have hf0 : f = [] := List.length_eq_zero_iff.mp hf
    simp [he0, hf0]
  | cons n hs ih =>
    cases e with
    | nil => simp at he
    | cons x es =>
      cases f with
      | nil => simp at hf
      | cons y fs =>
        have hh' := List.cons.inj hh
        have hxy : x = y := Nat.add_left_cancel hh'.1
        have hes : es.length = hs.length := by simpa using he
        have hfs : fs.length = hs.length := by simpa using hf
        exact congrArg₂ List.cons hxy (ih es fs hes hfs hh'.2)

/-- Unique extra masses characterize the actual native shuffle in either
ordered orientation. The role q is the non-unary source. -/
theorem native_gap_iff (a : α) (q : Side) (m : Nat) (cs : List α)
    (h : List Nat) (w : List α) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) :
    (∃ M, M.length = w.length ∧ projection q w M = gap a cs h ∧
      projection (if q = .first then .second else .first) w M = List.replicate m a) ↔
    ∃! e : List Nat, e.length = h.length ∧ e.sum = m ∧
      w = gap a cs (List.zipWith (· + ·) h e) := by
  constructor
  · rintro ⟨M, hl, hp, hu⟩
    have hpu : ∀ x ∈ projection (if q = .first then .second else .first) w M,
        x = a := by
      rw [hu]
      intro x hx
      exact (List.mem_replicate.mp hx).2
    obtain ⟨ds, k, e, ht⟩ := trace_exists a q w M hl hpu
    obtain ⟨_, hk, he, hd, hv, hm, hw⟩ := trace_projections a q ht
    obtain ⟨hcs, hkh⟩ := gap_injective a ds cs k h hd ha hk hh (hv.symm.trans hp)
    subst ds
    subst k
    have hsum : e.sum = m := by simpa using congrArg List.length (hm.symm.trans hu)
    refine ⟨e, ⟨he, hsum, hw⟩, ?_⟩
    intro f hf
    have hlen1 : (List.zipWith (· + ·) h e).length = cs.length + 1 := by
      simp [List.length_zipWith, he, hh]
    have hlen2 : (List.zipWith (· + ·) h f).length = cs.length + 1 := by
      simp [List.length_zipWith, hf.1, hh]
    have hv := gap_injective a cs cs _ _ ha ha hlen2 hlen1 (hf.2.2.symm.trans hw)
    exact zip_add_cancel h f e hf.1 he hv.2
  · rintro ⟨e, ⟨he, hm, hw⟩, _⟩
    let M := grouped q cs h e
    have ht := trace_construct a q cs h e ha hh he
    obtain ⟨hl, _, _, _, hp, hu, _⟩ := trace_projections a q ht
    rw [← hw] at hl hp hu
    exact ⟨M, hl, hp, by simpa [hm] using hu⟩


/-- Every mask of a prescribed enlarged gap word has exactly its prescribed
mass vector. This recovers zero and outer masses as well as positive ones. -/
theorem trace_of_projections (a : α) (q : Side) (cs : List α) (h e : List Nat)
    (w : List α) (M : List Side) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) (he : e.length = h.length)
    (hw : w = gap a cs (List.zipWith (· + ·) h e))
    (hl : M.length = w.length) (hp : projection q w M = gap a cs h)
    (hu : ∀ x ∈ projection (if q = .first then .second else .first) w M, x = a) :
    Trace a q cs h e w M := by
  obtain ⟨ds, k, f, ht⟩ := trace_exists a q w M hl hu
  obtain ⟨_, hk, hf, hd, hv, _, hw'⟩ := trace_projections a q ht
  obtain ⟨hcs, hkh⟩ := gap_injective a ds cs k h hd ha hk hh (hv.symm.trans hp)
  subst ds
  subst k
  have hlen1 : (List.zipWith (· + ·) h e).length = cs.length + 1 := by
    simp [List.length_zipWith, he, hh]
  have hlen2 : (List.zipWith (· + ·) h f).length = cs.length + 1 := by
    simp [List.length_zipWith, hf, hh]
  have heq := (gap_injective a cs cs _ _ ha ha hlen2 hlen1
    (hw'.symm.trans hw)).2
  have hfe := zip_add_cancel h f e hf he heq
  subst f
  exact ht

private theorem bump_modify (e : List Nat) (i k : Nat) :
    bump (e.modify i (· + k)) = (bump e).modify i (· + k) := by
  cases e with
  | nil => simp [bump]
  | cons x e => cases i <;> simp [bump, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem sizes_insert (a : α) (X Y : List α) (k : Nat) :
    sizes a (X ++ List.replicate k a ++ Y) =
      (sizes a (X ++ Y)).modify (spine a X).length (· + k) := by
  induction X with
  | nil =>
    have hn := sizes_ne_nil a Y
    cases he : sizes a Y with
    | nil => exact (hn he).elim
    | cons n ns => simp [sizes_replicate_append, he, spine, Nat.add_comm]
  | cons x X ih =>
    by_cases hx : x = a
    · subst x
      simpa [sizes, spine_cons, bump_modify] using congrArg bump ih
    · simpa [sizes, spine_cons, hx] using congrArg (0 :: ·) ih

private theorem modify_sum (e : List Nat) (i k : Nat) (hi : i < e.length) :
    (e.modify i (· + k)).sum = e.sum + k := by
  induction e generalizing i with
  | nil => simp at hi
  | cons x e ih =>
    cases i with
    | zero => simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | succ i => simpa [Nat.add_assoc] using congrArg (x + ·) (ih i (by simpa using hi))

private theorem modify_add (h e : List Nat) (i k : Nat) (hl : h.length = e.length) :
    (List.zipWith (· + ·) h e).modify i (· + k) =
      List.zipWith (· + ·) h (e.modify i (· + k)) := by
  induction h generalizing e i with
  | nil => have he : e = [] := List.length_eq_zero_iff.mp hl.symm; subst e; simp
  | cons x h ih =>
    cases e with
    | nil => simp at hl
    | cons y e => cases i <;> simp [ih e _ (by simpa using hl), Nat.add_assoc]

/-- Inserting unary letters at a real word cut changes exactly its indexed gap.
The cut index counts non-a occurrences, including repeated occurrences. -/
theorem gap_insert (a : α) (cs : List α) (h e : List Nat)
    (X Y : List α) (k : Nat) (ha : ∀ c ∈ cs, c ≠ a)
    (hh : h.length = cs.length + 1) (he : e.length = h.length)
    (hw : X ++ Y = gap a cs (List.zipWith (· + ·) h e)) :
    let i := (spine a X).length
    i < e.length ∧ (e.modify i (· + k)).length = h.length ∧
      (e.modify i (· + k)).sum = e.sum + k ∧
      X ++ List.replicate k a ++ Y =
        gap a cs (List.zipWith (· + ·) h (e.modify i (· + k))) := by
  dsimp only
  have hzip : (List.zipWith (· + ·) h e).length = cs.length + 1 := by simp [hh, he]
  have hp := profile_gap a cs (List.zipWith (· + ·) h e) ha hzip
  have hc : spine a (X ++ Y) = cs := by rw [hw]; exact hp.1
  have hi : (spine a X).length < e.length := by
    have hl : (spine a X).length ≤ cs.length := by
      rw [← hc]
      simp only [spine, List.filter_append, List.length_append]
      omega
    omega
  refine ⟨hi, by simpa using he, modify_sum e _ k hi, ?_⟩
  have hs : spine a (X ++ List.replicate k a ++ Y) = cs := by
    simpa [spine, List.filter_append, List.filter_replicate] using hc
  have hz := sizes_insert a X Y k
  rw [hw, hp.2, modify_add h e _ k he.symm] at hz
  have hr := recover a (X ++ List.replicate k a ++ Y)
  rw [hs, hz] at hr
  exact hr.symm

end
end D5.S1.Words.UnaryGapWords
