/- GID: D5/S3/ObserverMemory/Trajectories/ZeroRunWordGeometry
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/ZeroRunWordGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Complete intervals and actual transport parity of binary gap words. -/

import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry

set_option autoImplicit false

/-- Positions of the ones in a word with the specified intervening zero lengths.
All positions outside this finite set contain zero. -/
def ones : List ℕ → ℕ → Finset ℕ
  | [], p => {p}
  | l :: ls, p => insert p (ones ls (p + l + 1))

/-- Concrete complete zero intervals, independently of any proposed run list. -/
def Complete (s : Finset ℕ) (a b : ℕ) : Prop :=
  a + 2 ≤ b ∧ a ∈ s ∧ b ∈ s ∧ ∀ x, a < x → x < b → x ∉ s

/-- Explicit intervals contributed by the gaps. Zero gaps contribute no candidate. -/
def intervals : List ℕ → ℕ → Finset (ℕ × ℕ)
  | [], _ => ∅
  | l :: ls, p =>
      (if 0 < l then {(p, p + l + 1)} else ∅) ∪ intervals ls (p + l + 1)

/-- Exhaustion of all complete candidates, including every gap of length one. -/
theorem complete_iff_interval (ls : List ℕ) (p a b : ℕ) :
    Complete (ones ls p) a b ↔ (a, b) ∈ intervals ls p := by
  have lower : ∀ (xs : List ℕ) (p a : ℕ), a ∈ ones xs p → p ≤ a := by
    intro xs
    induction xs with
    | nil => intro p a h; simp only [ones, Finset.mem_singleton] at h; omega
    | cons l ls ih =>
      intro p a h
      simp only [ones, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact le_rfl
      · have := ih _ _ h; omega
  have start : ∀ (xs : List ℕ) (p : ℕ), p ∈ ones xs p := by
    intro xs p
    cases xs <;> simp [ones]
  induction ls generalizing p a b with
  | nil =>
    simp only [ones, intervals, Finset.notMem_empty, iff_false]
    intro ⟨hab, ha, hb, _⟩
    simp only [Finset.mem_singleton] at ha hb
    omega
  | cons l ls ih =>
    simp only [intervals, Finset.mem_union]
    constructor
    · rintro ⟨hab, ha, hb, hz⟩
      simp only [ones, Finset.mem_insert] at ha hb
      by_cases hap : a = p
      · subst a
        have hb' : b ∈ ones ls (p + l + 1) := by
          rcases hb with h | h
          · omega
          · exact h
        have hpb := lower _ _ _ hb'
        have heq : b = p + l + 1 := by
          by_contra hn
          have hn' : p + l + 1 < b := by omega
          exact hz (p + l + 1) (by omega) hn' (by simp [ones, start])
        left
        have hl : 0 < l := by omega
        simp [hl, heq]
      · right
        have ha' : a ∈ ones ls (p + l + 1) := ha.resolve_left hap
        have hpa := lower _ _ _ ha'
        have hb' : b ∈ ones ls (p + l + 1) := by
          rcases hb with h | h
          · omega
          · exact h
        apply (ih _ _ _).mp
        refine ⟨hab, ha', hb', ?_⟩
        intro x hx hxb hxm
        exact hz x hx hxb (by simp [ones, hxm])
    · intro h
      rcases h with h | h
      · split_ifs at h with hl
        · simp only [Finset.mem_singleton, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          refine ⟨by omega, by simp [ones], by simp [ones, start], ?_⟩
          intro x hx hxb hm
          simp only [ones, Finset.mem_insert] at hm
          rcases hm with hm | hm
          · omega
          · have := lower _ _ _ hm; omega
        · simp at h
      · obtain ⟨hab, ha, hb, hz⟩ := (ih _ _ _).mpr h
        have hpa := lower _ _ _ ha
        refine ⟨hab, by simp [ones, ha], by simp [ones, hb], ?_⟩
        intro x hx hxb hm
        simp only [ones, Finset.mem_insert] at hm
        rcases hm with hm | hm
        · omega
        · exact hz x hx hxb hm

/-- Actual XOR transport: parity of every zero after the closing one. -/
def transport (s : Finset ℕ) (b e : ℕ) : ℕ :=
  ((Finset.Ioo b e).filter fun x => x ∉ s).card % 2

/-- The descending odd long gaps with every even number of length-one fillers. -/
def familyGaps : ℕ → (ℕ → ℕ) → List ℕ
  | 0, _ => [3]
  | r + 1, h => (2 * (r + 1) + 3) ::
      (List.replicate (2 * h 0) 1 ++ familyGaps r (fun i => h (i + 1)))

/-- Distance from the first one to the last one. -/
def span (ls : List ℕ) : ℕ := (ls.map (fun l => l + 1)).sum

/-- The geometry and cardinality of the actual one positions. -/
theorem ones_geometry (ls : List ℕ) (p : ℕ) :
    (∀ x ∈ ones ls p, p ≤ x ∧ x ≤ p + span ls) ∧
    (ones ls p).card = ls.length + 1 ∧ p ∈ ones ls p ∧
    p + span ls ∈ ones ls p := by
  induction ls generalizing p with
  | nil => simp [ones, span]
  | cons l ls ih =>
    obtain ⟨hb, hc, hs, he⟩ := ih (p + l + 1)
    have hn : p ∉ ones ls (p + l + 1) := by
      intro hm
      have := (hb p hm).1
      omega
    refine ⟨?_, ?_, by simp [ones], ?_⟩
    · intro x hx
      simp only [ones, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp [span]
      · obtain ⟨hlo, hhi⟩ := hb x hx
        simp only [span, List.map_cons, List.sum_cons] at *
        omega
    · simp [ones, Finset.card_insert_of_notMem hn, hc]
    · have he' : p + span (l :: ls) = p + l + 1 + span ls := by
        simp [span]; omega
      rw [he']
      exact Finset.mem_insert_of_mem he

/-- Counting all zero bits after an actual one, including every filler gap. -/
theorem transport_suffix (pre post : List ℕ) (p n : ℕ) :
    transport (ones (pre ++ post) p) (p + span pre)
      (p + span pre + span post + 1 + n) = (post.sum + n) % 2 := by
  have happ : ∀ (xs ys : List ℕ) (p : ℕ),
      ones (xs ++ ys) p = ones xs p ∪ ones ys (p + span xs) := by
    intro xs
    induction xs with
    | nil =>
      intro ys p
      have hs := (ones_geometry ys p).2.2.1
      simp [ones, span, Finset.insert_eq_of_mem hs]
    | cons l ls ih =>
      intro ys p
      rw [List.cons_append, ones, ih]
      simp [ones, span, Finset.insert_union, Nat.add_assoc]
  have hspan : ∀ xs : List ℕ, span xs = xs.sum + xs.length := by
    intro xs
    induction xs with
    | nil => simp [span]
    | cons l ls ih => simp_all [span]; omega
  let b := p + span pre
  let e := b + span post + 1 + n
  have hpre := (ones_geometry pre p).1
  obtain ⟨hpost, hcard, hstart, _⟩ := ones_geometry post b
  have hfilter : (Finset.Ioo b e).filter (fun x => x ∈ ones (pre ++ post) p) =
      (ones post b).erase b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_erase]
    rw [happ, Finset.mem_union]
    constructor
    · rintro ⟨⟨hbx, hxe⟩, hx | hx⟩
      · have := (hpre x hx).2
        dsimp [b] at hbx
        omega
      · exact ⟨by omega, hx⟩
    · rintro ⟨hne, hx⟩
      obtain ⟨hbx, hxb⟩ := hpost x hx
      refine ⟨⟨by omega, ?_⟩, Or.inr hx⟩
      dsimp [e]
      omega
  have hcount := Finset.card_filter_add_card_filter_not
      (s := Finset.Ioo b e) (fun x => x ∈ ones (pre ++ post) p)
  rw [hfilter, Finset.card_erase_of_mem hstart, hcard, Nat.card_Ioo] at hcount
  have hz : ((Finset.Ioo b e).filter fun x => x ∉ ones (pre ++ post) p).card =
      post.sum + n := by
    have hsp := hspan post
    dsimp [e] at *
    omega
  change ((Finset.Ioo b e).filter fun x => x ∉ ones (pre ++ post) p).card % 2 = _
  rw [hz]

/-- Exact interval decomposition under concatenation, used inside the source selector proof. -/
theorem interval_geometry (ls : List ℕ) (p : ℕ) :
    (∀ c ∈ intervals ls p, p ≤ c.1 ∧ c.1 + 2 ≤ c.2 ∧
      c.2 ≤ p + span ls ∧ c.2 - c.1 - 1 ∈ ls) ∧
    (∀ ys, intervals (ls ++ ys) p =
      intervals ls p ∪ intervals ys (p + span ls)) := by
  induction ls generalizing p with
  | nil => simp [intervals, span]
  | cons l ls ih =>
    obtain ⟨hg, ha⟩ := ih (p + l + 1)
    constructor
    · intro c hc
      simp only [intervals, Finset.mem_union] at hc
      rcases hc with hc | hc
      · split_ifs at hc with hl
        · simp only [Finset.mem_singleton] at hc
          subst c
          simp only [List.mem_cons]
          refine ⟨le_rfl, by omega, ?_, Or.inl (by omega)⟩
          simp [span]; omega
        · simp at hc
      · obtain ⟨hpa, hab, hbe, hlen⟩ := hg c hc
        refine ⟨by omega, hab, ?_, List.mem_cons_of_mem _ hlen⟩
        simp only [span, List.map_cons, List.sum_cons] at *
        omega
    · intro ys
      simp only [List.cons_append, intervals, ha]
      have hp : p + span (l :: ls) = p + l + 1 + span ls := by
        simp [span]; omega
      rw [hp, Finset.union_assoc]

/-- All later candidates are strictly shorter than the first long run. -/
theorem family_head_dominates (r : ℕ) (h : ℕ → ℕ) (p : ℕ) :
    (p, p + 2 * r + 4) ∈ intervals (familyGaps r h) p ∧
    ∀ c ∈ intervals (familyGaps r h) p,
      c = (p, p + 2 * r + 4) ∨ c.2 - c.1 - 1 < 2 * r + 3 := by
  have hbound : ∀ (r : ℕ) (h : ℕ → ℕ) (l : ℕ),
      l ∈ familyGaps r h → l ≤ 2 * r + 3 := by
    intro r
    induction r with
    | zero => intro h l hl; simp [familyGaps] at hl; omega
    | succ r ih =>
      intro h l hl
      simp only [familyGaps, List.mem_cons, List.mem_append] at hl
      rcases hl with rfl | hl | hl
      · omega
      · have := List.eq_of_mem_replicate hl; omega
      · have := ih (fun i => h (i + 1)) l hl; omega
  cases r with
  | zero => simp [familyGaps, intervals]
  | succ r =>
    let b := p + (2 * (r + 1) + 3) + 1
    have hb : b = p + 2 * (r + 1) + 4 := by dsimp [b]; omega
    have hi : intervals (familyGaps (r + 1) h) p =
        insert (p, b) (intervals (List.replicate (2 * h 0) 1 ++
          familyGaps r (fun i => h (i + 1))) b) := by
      simp [familyGaps, intervals, b]
    rw [hi, ← hb]
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    intro c hc
    simp only [Finset.mem_insert] at hc
    rcases hc with hc | hc
    · exact Or.inl hc
    · right
      have hm := ((interval_geometry _ b).1 c hc).2.2.2
      simp only [List.mem_append] at hm
      rcases hm with hm | hm
      · have := List.eq_of_mem_replicate hm; omega
      · have := hbound r (fun i => h (i + 1)) _ hm; omega

end D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry
