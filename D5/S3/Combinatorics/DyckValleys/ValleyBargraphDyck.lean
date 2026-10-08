/- GID: D5/S3/Combinatorics/DyckValleys/ValleyBargraphDyck
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DyckValleys/ValleyBargraphDyck
   mirror-E: none(waiver:direct-dyck-decomposition)
   anchors: []
   utility: none
   digest: First-return avoidance classification and valley statistics for Dyck words. -/

import D5.S3.Combinatorics.DyckValleys.ValleyBargraphDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DyckValleys
open DyckStep List ValleyBargraphDefs

theorem avoids_nest_add (p q : DyckWord) :
    AvoidsUUDD (p.nest + q) ↔
      AvoidsUUDD p ∧ AvoidsUUDD q ∧ p ≠ (0 : DyckWord).nest := by
  have split (xs ys : List DyckStep) :
      [U, U, D, D] <:+: xs ++ ys ↔
      [U, U, D, D] <:+: xs ∨ [U, U, D, D] <:+: ys ∨
      ([U] <:+ xs ∧ [U, D, D] <+: ys) ∨
      ([U, U] <:+ xs ∧ [D, D] <+: ys) ∨
      ([U, U, D] <:+ xs ∧ [D] <+: ys) := by
    rw [infix_append_iff_ne_nil]
    constructor
    · rintro (h | h | ⟨a,b,ha,hb,hab,hax,hby⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · cases a with
        | nil => contradiction
        | cons u a =>
          cases a with
          | nil =>
            simp only [cons_append, nil_append, cons.injEq] at hab
            rcases hab with ⟨rfl, rfl⟩
            exact Or.inr (Or.inr (Or.inl ⟨hax,hby⟩))
          | cons v a =>
            cases a with
            | nil =>
              simp only [cons_append, nil_append, cons.injEq] at hab
              rcases hab with ⟨rfl,rfl,rfl⟩
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hax,hby⟩)))
            | cons w a =>
              cases a with
              | nil =>
                simp only [cons_append, nil_append, cons.injEq] at hab
                rcases hab with ⟨rfl,rfl,rfl,rfl⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hax,hby⟩)))
              | cons z a => cases b <;> simp_all
    · rintro (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨[U],[U,D,D],by simp,by simp,rfl,h⟩)
      · exact Or.inr (Or.inr ⟨[U,U],[D,D],by simp,by simp,rfl,h⟩)
      · exact Or.inr (Or.inr ⟨[U,U,D],[D],by simp,by simp,rfl,h⟩)
  have badPrefix (r : DyckWord) (l : List DyckStep)
      (hcount : l.count U < l.count D) (hl : l <+: r.toList) : False := by
    have h := r.count_D_le_count_U l.length
    rw [← List.prefix_iff_eq_take.mp hl] at h
    omega
  have badSuffix (r : DyckWord) (l : List DyckStep)
      (hcount : l.count D < l.count U) (hl : l <:+ r.toList) : False := by
    obtain ⟨t, ht⟩ := List.suffix_iff_exists_eq_append.mp hl
    have h := r.count_D_le_count_U t.length
    have hb := r.count_U_eq_count_D
    rw [ht, List.take_append] at h
    simp only [List.take_length, Nat.sub_self, List.take_zero, List.append_nil] at h
    rw [ht, List.count_append, List.count_append] at hb
    omega
  have appendCriterion (r s : DyckWord) :
      [U, U, D, D] <:+: (r + s).toList ↔
      [U, U, D, D] <:+: r.toList ∨ [U, U, D, D] <:+: s.toList := by
    change [U, U, D, D] <:+: r.toList ++ s.toList ↔ _
    rw [split]
    constructor
    · rintro (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · exact (badSuffix r [U] (by decide) h.1).elim
      · exact (badPrefix s [D, D] (by decide) h.2).elim
      · exact (badPrefix s [D] (by decide) h.2).elim
    · exact fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h))
  have nestCriterion : [U, U, D, D] <:+: p.nest.toList ↔
      [U, U, D, D] <:+: p.toList ∨ p = (0 : DyckWord).nest := by
    change [U, U, D, D] <:+: U :: (p.toList ++ [D]) ↔ _
    rw [List.infix_cons_iff, split]
    constructor
    · rintro (h | h | h | h | h | h)
      · cases hp : p.toList with
        | nil => simp [hp] at h
        | cons a t =>
          cases t with
          | nil => simp [hp] at h
          | cons b t =>
            cases t with
            | nil =>
              simp only [hp, cons_append, nil_append, cons_prefix_cons,
                prefix_nil, and_true] at h
              rcases h with ⟨_, rfl, rfl⟩
              exact Or.inr (DyckWord.ext hp)
            | cons c t =>
              have hpre : [U, D, D] <+: p.toList := by
                simp only [hp, cons_append, cons_prefix_cons] at h ⊢
                exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, List.nil_prefix⟩
              exact (badPrefix p [U, D, D] (by decide) hpre).elim
      · exact Or.inl h
      · have := h.length_le
        norm_num at this
      · simp at h
      · simp at h
      · exact (badSuffix p [U, U, D] (by decide) h.1).elim
    · rintro (h | rfl)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (by change [U,U,D,D] <+: [U,U,D,D]; exact List.prefix_rfl)
  unfold AvoidsUUDD
  rw [appendCriterion, nestCriterion]
  tauto

theorem valleys_nest_add (p q : DyckWord) :
    valleys (p.nest + q) = valleys p + valleys q + (if q = 0 then 0 else 1) := by
  have countAppend (xs ys : List DyckStep) :
      ((xs ++ ys).zip (xs ++ ys).tail).count (D, U) =
      (xs.zip xs.tail).count (D, U) + (ys.zip ys.tail).count (D, U) +
        if xs.getLast? = some D ∧ ys.head? = some U then 1 else 0 := by
    induction xs with
    | nil => simp
    | cons a t ih =>
      cases t with
      | nil =>
        cases ys with
        | nil => simp
        | cons b s => cases a <;> cases b <;> simp [List.zip_cons_cons]
      | cons b t =>
        simp only [cons_append, tail_cons, zip_cons_cons, count_cons,
          getLast?_cons_cons] at ih ⊢
        rw [ih]
        omega
  have hn : valleys p.nest = valleys p := by
    unfold valleys
    change (([U] ++ p.toList ++ [D]).zip ([U] ++ p.toList ++ [D]).tail).count (D, U) = _
    rw [countAppend, countAppend]
    simp
  have hlast : p.nest.toList.getLast? = some D := by
    rw [List.getLast?_eq_some_getLast (DyckWord.toList_ne_nil.mpr p.nest_ne_zero),
      DyckWord.getLast_eq_D]
  unfold valleys at hn ⊢
  change ((p.nest.toList ++ q.toList).zip (p.nest.toList ++ q.toList).tail).count (D,U) = _
  rw [countAppend, hn, hlast]
  by_cases hq : q = 0
  · subst q
    have hz : (0 : DyckWord).toList = [] := rfl
    simp [hz]
  · have hhead := q.head_eq_U (DyckWord.toList_ne_nil.mpr hq)
    have hhead' : q.toList.head? = some U := by
      rw [List.head?_eq_some_head (DyckWord.toList_ne_nil.mpr hq), hhead]
    simp [hhead', hq]

end D5.S3.Combinatorics.DyckValleys
