/- GID: D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerMatchingTranslations
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Steiner translations identify the matching and switch criterion of a point deletion. -/

import D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch

/-! # Matchings from translations of a Steiner triple system -/

namespace D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations

open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered pair_completion)
open PointDeletedSteinerSwitch (pointDeletedFamily)

variable {r : ℕ} {S : Set (Set (Fin (r + 1)))}
variable (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)

private noncomputable def third {q x : Fin (r + 1)} (hne : x ≠ q) : Fin (r + 1) :=
  (pair_completion valid hne.symm (complete q x hne.symm)).choose

private theorem third_spec {q x : Fin (r + 1)} (hne : x ≠ q) :
    third valid complete hne ≠ q ∧ third valid complete hne ≠ x ∧
      ({q, x, third valid complete hne} : Set (Fin (r + 1))) ∈ S :=
  (pair_completion valid hne.symm (complete q x hne.symm)).choose_spec

/-- Pair the adjoined point with the pivot and the other points by blocks through the pivot. -/
noncomputable def translate (q : Fin (r + 1)) : Option (Fin (r + 1)) → Option (Fin (r + 1))
  | none => some q
  | some x => if h : x = q then none else some (third valid complete h)

/-- The adjoined point is paired with the pivot. -/
@[simp] theorem translate_none (q : Fin (r + 1)) :
    translate valid complete q none = some q := rfl

/-- The pivot is paired with the adjoined point. -/
@[simp] theorem translate_self (q : Fin (r + 1)) :
    translate valid complete q (some q) = none := by
  simp [translate]

private theorem translate_some {q x : Fin (r + 1)} (hne : x ≠ q) :
    translate valid complete q (some x) = some (third valid complete hne) := by
  simp [translate, hne]

private theorem translate_of_block {q x y : Fin (r + 1)} (hne : x ≠ q)
    (block : ({q, x, y} : Set (Fin (r + 1))) ∈ S) :
    translate valid complete q (some x) = some y := by
  obtain ⟨hq, hx, hblock⟩ := third_spec valid complete hne
  have same := valid.2 _ hblock _ block q x hne.symm
    (by simp) (by simp) (by simp) (by simp)
  have mem : third valid complete hne ∈ ({q, x, y} : Set (Fin (r + 1))) :=
    same ▸ (show third valid complete hne ∈ ({q, x, third valid complete hne} :
      Set (Fin (r + 1))) by simp)
  rw [translate_some valid complete hne]
  simpa [hq, hx] using mem

/-- Taking the third point of the same block twice recovers the first point. -/
theorem translate_involutive (q : Fin (r + 1)) :
    Function.Involutive (translate valid complete q) := by
  intro i
  cases i with
  | none => simp
  | some x =>
    by_cases h : x = q
    · subst x
      simp
    · obtain ⟨hq, _, block⟩ := third_spec valid complete h
      rw [translate_some valid complete h]
      apply translate_of_block valid complete hq
      convert block using 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- Each translation gives a matching without fixed points. -/
theorem translate_ne_self (q : Fin (r + 1)) (i : Option (Fin (r + 1))) :
    translate valid complete q i ≠ i := by
  cases i with
  | none => simp
  | some x =>
    by_cases h : x = q
    · subst x
      simp
    · rw [translate_some valid complete h]
      simpa using (third_spec valid complete h).2.1

/-- Translations at distinct pivots assign different partners to every point. -/
theorem translate_ne_translate {q v : Fin (r + 1)} (hqv : q ≠ v)
    (i : Option (Fin (r + 1))) :
    translate valid complete q i ≠ translate valid complete v i := by
  cases i with
  | none => simpa using hqv
  | some x =>
    by_cases hq : x = q
    · subst x
      simp [translate_some valid complete hqv]
    by_cases hv : x = v
    · subst x
      simp [translate_some valid complete hqv.symm]
    obtain ⟨_, hqx, qblock⟩ := third_spec valid complete hq
    obtain ⟨_, _, vblock⟩ := third_spec valid complete hv
    rw [translate_some valid complete hq, translate_some valid complete hv]
    intro same
    have thirdSame := Option.some.inj same
    rw [← thirdSame] at vblock
    have blocks := valid.2 _ qblock _ vblock x (third valid complete hq) hqx.symm
      (by simp) (by simp) (by simp) (by simp)
    have mem : q ∈ ({v, x, third valid complete hq} : Set (Fin (r + 1))) :=
      blocks ▸ (show q ∈ ({q, x, third valid complete hq} : Set (Fin (r + 1))) by simp)
    simpa [hqv, Ne.symm hq, (third_spec valid complete hq).1.symm] using mem

/-- The pivots and their common third point form a square with the adjoined point. -/
theorem translate_special_square {q v : Fin (r + 1)} (hqv : q ≠ v) :
    ∃ z, z ≠ q ∧ z ≠ v ∧ translate valid complete q (some v) = some z ∧
      translate valid complete v (some q) = some z := by
  obtain ⟨hq, hv, block⟩ := third_spec valid complete hqv.symm
  refine ⟨third valid complete hqv.symm, hq, hv,
    translate_some valid complete hqv.symm, ?_⟩
  apply translate_of_block valid complete hqv
  convert block using 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- On the remaining points the deleted pivot's translation gives the leave matching. -/
theorem translate_deleted_match (q : Fin (r + 1)) {m : Fin r → Fin r}
    (hleave : ∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b) (a : Fin r) :
    translate valid complete q (some (q.succAbove a)) = some (q.succAbove (m a)) := by
  have hne := Fin.succAbove_ne q a
  obtain ⟨hq, ha, block⟩ := third_spec valid complete hne
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hq
  have pair_ne : a ≠ b := fun h => ha (hb.symm.trans (congrArg q.succAbove h.symm))
  have in_leave : Uncovered (pointDeletedFamily S q) a b := by
    refine ⟨pair_ne, ?_⟩
    rintro ⟨t, ht, at', bt⟩
    change q.succAbove '' t ∈ S at ht
    have same := valid.2 _ ht _ block (q.succAbove a) (q.succAbove b)
      (fun h => pair_ne (Fin.succAbove_right_injective h))
      ⟨a, at', rfl⟩ ⟨b, bt, rfl⟩ (by simp) (by simp [hb])
    have qmem : q ∈ q.succAbove '' t :=
      same.symm ▸ (show q ∈ ({q, q.succAbove a, third valid complete hne} :
        Set (Fin (r + 1))) by simp)
    obtain ⟨x, _, hx⟩ := qmem
    exact Fin.succAbove_ne q x hx
  rw [translate_some valid complete hne, (hleave _ _).mp in_leave, hb]

/-- The two translations commute at the starting point exactly when the switch closes a triangle. -/
theorem switch_commutes_iff (q : Fin (r + 1)) {m : Fin r → Fin r}
    (hleave : ∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b)
    {a v b d : Fin r} (hvA : v ≠ a) (hvMate : v ≠ m a)
    (hb : ({a, v, b} : Set (Fin r)) ∈ pointDeletedFamily S q)
    (hd : ({m a, v, d} : Set (Fin r)) ∈ pointDeletedFamily S q) :
    translate valid complete (q.succAbove v)
        (translate valid complete q (some (q.succAbove a))) =
      translate valid complete q
        (translate valid complete (q.succAbove v) (some (q.succAbove a))) ↔ d = m b := by
  have retained {x y : Fin r} (h : ({x, v, y} : Set (Fin r)) ∈ pointDeletedFamily S q) :
      ({q.succAbove v, q.succAbove x, q.succAbove y} : Set (Fin (r + 1))) ∈ S := by
    change q.succAbove '' ({x, v, y} : Set (Fin r)) ∈ S at h
    convert h using 1
    ext z
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have at_start := translate_of_block valid complete
    (fun h => hvA (Fin.succAbove_right_injective h).symm) (retained hb)
  have at_mate := translate_of_block valid complete
    (fun h => hvMate (Fin.succAbove_right_injective h).symm) (retained hd)
  rw [translate_deleted_match valid complete q hleave, at_mate, at_start,
    translate_deleted_match valid complete q hleave, Option.some_inj, Fin.succAbove_right_inj]

end D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations
