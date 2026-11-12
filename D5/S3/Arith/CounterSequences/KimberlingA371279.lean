/- GID: D5/S3/Arith/CounterSequences/KimberlingA371279
   generality: I
   mirror-B: D5/B/S3/Arith/CounterSequences/KimberlingA371279
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: First-retention cumulative generation covers every positive rational at most one. -/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.CounterSequences.KimberlingA371279

/-- A left-to-right scan retaining the first occurrence of every value. -/
def firstRetentionAux : List ℚ → List ℚ → List ℚ
  | _, [] => []
  | seen, x :: xs =>
      if x ∈ seen then firstRetentionAux seen xs
      else x :: firstRetentionAux (x :: seen) xs

/-- The source's first-occurrence operation. -/
def firstRetention (xs : List ℚ) : List ℚ := firstRetentionAux [] xs

private theorem firstRetentionAux_filter (seen xs : List ℚ) :
    firstRetentionAux seen xs = (xs.filter (fun x => x ∉ seen)).eraseDups := by
  induction xs generalizing seen with
  | nil => simp [firstRetentionAux]
  | cons x xs ih =>
      by_cases hx : x ∈ seen
      · simp [firstRetentionAux, hx, ih]
      · simp only [firstRetentionAux, if_neg hx, List.filter_cons,
          decide_eq_true_eq, hx, not_false_eq_true, ↓reduceIte, List.eraseDups_cons]
        rw [ih]
        congr 2
        rw [List.filter_filter]
        apply List.filter_congr
        intro a ha
        by_cases hax : a = x <;> by_cases has : a ∈ seen <;> simp [hax, has]

private theorem firstRetention_eq_eraseDups (xs : List ℚ) :
    firstRetention xs = xs.eraseDups := by
  simpa [firstRetention] using firstRetentionAux_filter [] xs

private theorem firstRetentionAux_mem_iff (seen xs : List ℚ) (x : ℚ) :
    x ∈ firstRetentionAux seen xs ↔ x ∈ xs ∧ x ∉ seen := by
  induction xs generalizing seen with
  | nil => simp [firstRetentionAux]
  | cons a xs ih =>
      by_cases ha : a ∈ seen
      · rw [firstRetentionAux, if_pos ha, ih seen]
        by_cases hxa : x = a <;> simp [hxa, ha]
      · rw [firstRetentionAux, if_neg ha]
        simp only [List.mem_cons]
        rw [ih (a :: seen)]
        by_cases hxa : x = a <;> simp [hxa, ha]

private theorem firstRetention_mem_iff (xs : List ℚ) (x : ℚ) :
    x ∈ firstRetention xs ↔ x ∈ xs := by
  simpa [firstRetention] using firstRetentionAux_mem_iff ([] : List ℚ) xs x

private theorem firstRetentionAux_nodup (seen xs : List ℚ) :
    (firstRetentionAux seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => simp [firstRetentionAux]
  | cons a xs ih =>
      by_cases ha : a ∈ seen
      · simp [firstRetentionAux, ha, ih]
      · simp only [firstRetentionAux, if_neg ha]
        apply List.nodup_cons.mpr
        refine ⟨?_, ih (a :: seen)⟩
        intro h
        rw [firstRetentionAux_mem_iff] at h
        exact h.2 (by simp)

private theorem firstRetention_nodup (xs : List ℚ) : (firstRetention xs).Nodup := by
  exact firstRetentionAux_nodup [] xs

private theorem firstRetention_eq_self {xs : List ℚ} (h : xs.Nodup) :
    firstRetention xs = xs := by
  have aux : ∀ (ys seen : List ℚ), ys.Nodup →
      (∀ z ∈ ys, z ∉ seen) → firstRetentionAux seen ys = ys := by
    intro ys
    induction ys with
    | nil => simp [firstRetentionAux]
    | cons a ys ih =>
        intro seen hn hd
        rw [firstRetentionAux, if_neg (hd a (by simp))]
        congr 1
        apply ih (a :: seen) hn.of_cons
        intro z hz
        simp only [List.mem_cons, not_or]
        exact ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ hz),
          hd z (by simp [hz])⟩
  exact aux xs [] h (by simp)

/-- The complete ordered pair list, with the outer index first. -/
def pairList (xs : List ℚ) : List ℚ :=
  xs.flatMap (fun x => xs.map (fun y => x / (1 + y)))

private theorem pairList_mem_iff (xs : List ℚ) (z : ℚ) :
    z ∈ pairList xs ↔ ∃ x ∈ xs, ∃ y ∈ xs, z = x / (1 + y) := by
  constructor
  · intro hz
    rcases (List.mem_flatMap.mp hz) with ⟨x, hx, hz⟩
    rcases List.mem_map.mp hz with ⟨y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hxy.symm⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    apply List.mem_flatMap.mpr
    refine ⟨x, hx, List.mem_map.mpr ⟨y, hy, ?_⟩⟩
    exact hxy.symm

/-- New values are first-retained among the pair list, while the old prefix is untouched. -/
def freshTail (xs : List ℚ) : List ℚ :=
  firstRetention ((pairList xs).filter (fun z => z ∉ xs))

def nextList (xs : List ℚ) : List ℚ := xs ++ freshTail xs

private theorem freshTail_mem_iff (xs : List ℚ) (z : ℚ) :
    z ∈ freshTail xs ↔ z ∈ pairList xs ∧ z ∉ xs := by
  simp [freshTail, firstRetention_mem_iff]

private theorem nextList_mem_iff (xs : List ℚ) (z : ℚ) :
    z ∈ nextList xs ↔ z ∈ xs ∨ ∃ x ∈ xs, ∃ y ∈ xs, z = x / (1 + y) := by
  rw [nextList, List.mem_append, freshTail_mem_iff, pairList_mem_iff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hz : z ∈ xs
      · exact Or.inl hz
      · exact Or.inr ⟨h, hz⟩

private theorem freshTail_nodup (xs : List ℚ) : (freshTail xs).Nodup := by
  exact firstRetention_nodup _

private theorem nextList_nodup {xs : List ℚ} (hxs : xs.Nodup) : (nextList xs).Nodup := by
  apply List.Nodup.append hxs (freshTail_nodup xs)
  intro z hzxs hzfresh
  exact (freshTail_mem_iff xs z).mp hzfresh |>.2 hzxs

private theorem nextList_prefix (xs : List ℚ) : xs <+: nextList xs := by
  exact ⟨freshTail xs, rfl⟩

/-- Equality to literal first-occurrence deletion of the full concatenation. -/
theorem source_update {xs : List ℚ} (h : xs.Nodup) :
    nextList xs = (xs ++ pairList xs).eraseDups := by
  rw [List.eraseDups_append, ← firstRetention_eq_eraseDups xs,
    firstRetention_eq_self h]
  unfold nextList freshTail
  congr 1
  rw [firstRetention_eq_eraseDups]
  congr 1

/-- The cumulative lists `U₁, U₂, ...`, represented with `cumulative 0 = U₁`. -/
def cumulative : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => nextList (cumulative n)

private theorem cumulative_nodup (n : ℕ) : (cumulative n).Nodup := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih => exact nextList_nodup ih

private theorem cumulative_prefix (n : ℕ) : cumulative n <+: cumulative (n + 1) := by
  simpa [cumulative] using nextList_prefix (cumulative n)

private theorem cumulative_mono {m n : ℕ} (hmn : m ≤ n) :
    ∀ z ∈ cumulative m, z ∈ cumulative n := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun z hz => hz
  | succ n hmn ih =>
      intro z hz
      exact (cumulative_prefix n).mem (ih z hz)

private theorem cumulative_one_mem (n : ℕ) : (1 : ℚ) ∈ cumulative n := by
  exact cumulative_mono (Nat.zero_le n) 1 (by simp [cumulative])

private theorem coverage_q : ∀ q p : ℕ, 1 ≤ p → p ≤ q →
    ((p : ℚ) / (q : ℚ)) ∈ cumulative q := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro p hp hpq
      by_cases hpeq : p = q
      · subst q
        have hp0 : (p : ℚ) ≠ 0 := by
          exact_mod_cast (show p ≠ 0 by omega)
        rw [div_self hp0]
        exact cumulative_one_mem p
      have hpq' : p < q := by omega
      by_cases hdiag : 2 * p ≤ q
      · have hd : 1 ≤ q - p := by omega
        have hlt : q - p < q := by omega
        have hpd : p ≤ q - p := by omega
        have ht := ih (q - p) hlt p hp hpd
        have ht' : ((p : ℚ) / ((q - p : ℕ) : ℚ)) ∈ cumulative (q - 1) :=
          cumulative_mono (m := q - p) (n := q - 1) (by omega) _ ht
        have hpair : (p : ℚ) / (q : ℚ) =
            ((p : ℚ) / ((q - p : ℕ) : ℚ)) /
              (1 + (p : ℚ) / ((q - p : ℕ) : ℚ)) := by
          have hq : (q : ℚ) ≠ 0 := by
            exact_mod_cast (show q ≠ 0 by omega)
          have hdq : ((q - p : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast (show q - p ≠ 0 by omega)
          field_simp [hq, hdq]
          norm_num [Nat.cast_sub (by omega : p ≤ q)]
        rw [hpair]
        have hnext := (nextList_mem_iff (cumulative (q - 1)) _).mpr
          (Or.inr ⟨_, ht', _, ht', rfl⟩)
        have hcum : cumulative q = nextList (cumulative (q - 1)) := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
          simp [cumulative]
        rw [hcum]
        exact hnext
      · have ha : 1 ≤ q - p := by omega
        have hlt : p < q := hpq'
        have hat := ih p hlt (q - p) ha (by omega)
        have hat' : ((q - p : ℕ) : ℚ) / (p : ℚ) ∈ cumulative (q - 1) :=
          cumulative_mono (m := p) (n := q - 1) (by omega) _ hat
        have hone : (1 : ℚ) ∈ cumulative (q - 1) := cumulative_one_mem (q - 1)
        have hpair : (p : ℚ) / (q : ℚ) =
            (1 : ℚ) / (1 + ((q - p : ℕ) : ℚ) / (p : ℚ)) := by
          have hq : (q : ℚ) ≠ 0 := by
            exact_mod_cast (show q ≠ 0 by omega)
          have hpq0 : (p : ℚ) ≠ 0 := by
            exact_mod_cast (show p ≠ 0 by omega)
          field_simp [hq, hpq0]
          norm_num [Nat.cast_sub (by omega : p ≤ q)]
        rw [hpair]
        have hnext := (nextList_mem_iff (cumulative (q - 1)) _).mpr
          (Or.inr ⟨1, hone, _, hat', rfl⟩)
        have hcum : cumulative q = nextList (cumulative (q - 1)) := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
          simp [cumulative]
        rw [hcum]
        exact hnext

/-- Every rational in `(0,1]` occurs in the exact first-retention cumulative run. -/
private theorem every_rational_interval (r : ℚ) (hr : 0 < r) (hr1 : r ≤ 1) :
  ∃ p q : ℕ, 1 ≤ p ∧ p ≤ q ∧ r = (p : ℚ) / (q : ℚ) ∧
    (p : ℚ) / (q : ℚ) ∈ cumulative q := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hden : 0 < r.den := r.den_pos
  have hfrac : (r.num : ℚ) / (r.den : ℚ) ≤ 1 := by
    simpa [r.num_div_den] using hr1
  have hnumdenQ : (r.num : ℚ) ≤ (r.den : ℚ) := by
    simpa using (div_le_iff₀ (by exact_mod_cast hden)).mp hfrac
  have hnumden : r.num ≤ (r.den : ℤ) := by exact_mod_cast hnumdenQ
  let p : ℕ := r.num.natAbs
  have hpcast : (p : ℤ) = r.num := by
    simpa [p] using (Int.natAbs_of_nonneg (le_of_lt hnum))
  have hp : 1 ≤ p := by
    have : 0 < p := by
      exact Int.natAbs_pos.mpr (ne_of_gt hnum)
    omega
  have hpq : p ≤ r.den := by
    have hnumden' : (p : ℤ) ≤ (r.den : ℤ) := by
      simpa [hpcast] using hnumden
    exact_mod_cast hnumden'
  have h := coverage_q r.den p hp hpq
  have hpqcast : (p : ℚ) = r.num := by exact_mod_cast hpcast
  have hr_eq : r = (p : ℚ) / (r.den : ℚ) := by
    calc
      r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
      _ = (p : ℚ) / (r.den : ℚ) := by rw [hpqcast]
  exact ⟨p, r.den, hp, hpq, hr_eq, h⟩

/-- Zero-based generation blocks; block `n` is the source's `g(n+1)`. -/
def block : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => freshTail (cumulative n)

/-- The literal positive-generation convention, with no entries at generation zero. -/
def generation : ℕ → List ℚ
  | 0 => []
  | n + 1 => block n

/-- Valid positive generation/index pairs, using optional zero-based list lookup internally. -/
def Occurs (r : ℚ) (position : ℕ × ℕ) : Prop :=
  0 < position.1 ∧ 0 < position.2 ∧
  position.2 ≤ (generation position.1).length ∧
  (generation position.1)[position.2 - 1]? = some r

private theorem cumulative_interval (n : ℕ) :
    ∀ r ∈ cumulative n, 0 < r ∧ r ≤ 1 := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih =>
      intro r hr
      rcases (nextList_mem_iff _ _).mp hr with hr | ⟨x, hx, y, hy, rfl⟩
      · exact ih r hr
      · have hx' := ih x hx
        have hy' := ih y hy
        constructor
        · exact div_pos hx'.1 (by linarith)
        · exact (div_le_iff₀ (by linarith : (0 : ℚ) < 1 + y)).mpr (by linarith)

private theorem block_mem_cumulative (n : ℕ) (r : ℚ) (h : r ∈ block n) :
    r ∈ cumulative n := by
  cases n with
  | zero => exact h
  | succ n => exact List.mem_append_right _ h

private theorem block_nodup (n : ℕ) : (block n).Nodup := by
  cases n with
  | zero => simp [block]
  | succ n => exact freshTail_nodup _

private theorem block_disjoint {m n : ℕ} (hmn : m < n) (r : ℚ)
    (hm : r ∈ block m) (hn : r ∈ block n) : False := by
  cases n with
  | zero => omega
  | succ n =>
      have hr := cumulative_mono (by omega : m ≤ n) r (block_mem_cumulative m r hm)
      exact ((freshTail_mem_iff _ _).mp hn).2 hr

private theorem cumulative_blocks (n : ℕ) :
    cumulative n = ((List.range (n + 1)).flatMap block) := by
  induction n with
  | zero => simp [cumulative, block]
  | succ n ih => simp [List.range_succ, cumulative, nextList, block, ih]

private theorem cumulative_mem_block (n : ℕ) (r : ℚ) (h : r ∈ cumulative n) :
    ∃ m ≤ n, r ∈ block m := by
  rw [cumulative_blocks] at h
  obtain ⟨m, hm, hr⟩ := List.mem_flatMap.mp h
  exact ⟨m, by simpa using (List.mem_range.mp hm), hr⟩

private theorem block_occurrence_unique (r : ℚ) {m n i j : ℕ}
    (hm : (block m)[i]? = some r) (hn : (block n)[j]? = some r) :
    m = n ∧ i = j := by
  have hmr := List.mem_of_getElem? hm
  have hnr := List.mem_of_getElem? hn
  have hmn : m = n := by
    rcases lt_trichotomy m n with h | h | h
    · exact False.elim (block_disjoint h r hmr hnr)
    · exact h
    · exact False.elim (block_disjoint h r hnr hmr)
  subst n
  refine ⟨rfl, (block_nodup m).eq_of_getElem?_eq ?_ (hm.trans hn.symm)⟩
  exact (List.getElem?_eq_some_iff.mp hm).1

private theorem exactly_once (r : ℚ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃! position : ℕ × ℕ, Occurs r position := by
  obtain ⟨p, q, hp, hpq, he, hmem⟩ := every_rational_interval r hr hr1
  rw [← he] at hmem
  obtain ⟨n, hn, hnr⟩ := cumulative_mem_block q r hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hnr
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨(n + 1, i + 1), ⟨by omega, by omega, ?_, ?_⟩, ?_⟩
  · simpa [generation] using Nat.succ_le_of_lt hil
  · simpa [generation] using hi
  · rintro ⟨m, j⟩ ⟨hm, hj, hjl, hmj⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have hu := block_occurrence_unique r (by simpa [generation] using hmj) hi
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

/-- The ordered concatenation of the first `n` generation blocks. -/
def flattenedPrefix (n : ℕ) : List ℚ := (List.range n).flatMap block

private theorem prefix_le {m n : ℕ} (h : m ≤ n) : cumulative m <+: cumulative n := by
  induction n, h using Nat.le_induction with
  | base => exact List.IsPrefix.refl _
  | succ n h ih => exact ih.trans (cumulative_prefix n)

private theorem cumulative_length (n : ℕ) : n ≤ (cumulative n).length := by
  let xs := (List.range n).map (fun j => (1 : ℚ) / (j + 1))
  have hn : xs.Nodup := by
    apply List.Nodup.map _ (List.nodup_range n)
    intro i j hij
    have he : (i : ℚ) + 1 = (j : ℚ) + 1 := one_div_inj.mp hij
    have : (i : ℚ) = (j : ℚ) := by linarith
    exact_mod_cast this
  have hs : xs ⊆ cumulative n := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hjn := List.mem_range.mp hj
    have hc := coverage_q (j + 1) 1 (by omega) (by omega)
    apply cumulative_mono (by omega : j + 1 ≤ n) _
    simpa using hc
  simpa [xs] using hn.length_le_of_subset hs

private theorem cumulative_get_stable {m n i : ℕ} (hmn : m ≤ n)
    (hi : i < (cumulative m).length) :
    (cumulative m)[i]? = (cumulative n)[i]? := by
  obtain ⟨tail, he⟩ := prefix_le hmn
  rw [← he, List.getElem?_append_left hi]

/-- The infinite ordered fraction enumeration, indexed from zero. -/
def fraction (i : ℕ) : ℚ := (cumulative (i + 1))[i]!

/-- Reduced numerator and positive denominator records of the same fraction enumeration. -/
def numerator (i : ℕ) : ℤ := (fraction i).num

def denominator (i : ℕ) : ℕ := (fraction i).den

private theorem fraction_agrees {n i : ℕ} (hi : i < (cumulative n).length) :
    (cumulative n)[i]? = some (fraction i) := by
  have hi' : i < (cumulative (i + 1)).length := lt_of_lt_of_le (by omega) (cumulative_length _)
  have he : (cumulative n)[i]? = (cumulative (i + 1))[i]? := by
    rcases le_total n (i + 1) with h | h
    · exact cumulative_get_stable h hi
    · exact (cumulative_get_stable h hi').symm
  rw [he]
  simp only [fraction, List.getElem!_pos hi', List.getElem?_eq_getElem hi']

private theorem flattenedPrefix_read (n i : ℕ) (hi : i < (flattenedPrefix n).length) :
    (flattenedPrefix n)[i]? = some (fraction i) := by
  cases n with
  | zero => simp [flattenedPrefix] at hi
  | succ n =>
      have he : flattenedPrefix (n + 1) = cumulative n := (cumulative_blocks n).symm
      rw [he] at hi ⊢
      exact fraction_agrees hi

/-- Zero-based flattened offset of a positive generation/index pair. -/
def flatIndex (position : ℕ × ℕ) : ℕ :=
  (flattenedPrefix (position.1 - 1)).length + (position.2 - 1)

private theorem occurrence_flat (r : ℚ) (position : ℕ × ℕ) (h : Occurs r position) :
    fraction (flatIndex position) = r := by
  obtain ⟨n, k⟩ := position
  obtain ⟨hn, hk, hkl, he⟩ := h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hprefix : flattenedPrefix (n + 1) = flattenedPrefix n ++ block n := by
    simp [flattenedPrefix, List.range_succ]
  have hki : k - 1 < (block n).length := by simpa [generation] using (show k - 1 < (generation (n + 1)).length by omega)
  have hlook : (flattenedPrefix (n + 1))[(flattenedPrefix n).length + (k - 1)]? = some r := by
    rw [hprefix, List.getElem?_append_right (by omega)]
    simpa [generation] using he
  have hlen : (flattenedPrefix n).length + (k - 1) < (flattenedPrefix (n + 1)).length := by
    rw [hprefix, List.length_append]
    omega
  have hf := flattenedPrefix_read (n + 1) _ hlen
  have : fraction ((flattenedPrefix n).length + (k - 1)) = r := Option.some.inj (hf.symm.trans hlook)
  simpa [flatIndex] using this

/-- Full source event, with finite-prefix, infinite-order and reduced-coordinate bridges. -/
theorem result :
    (∀ n, cumulative (n + 1) = (cumulative n ++ pairList (cumulative n)).eraseDups) ∧
    (∀ n, cumulative n = flattenedPrefix (n + 1)) ∧
    (∀ n r, r ∈ cumulative n → 0 < r ∧ r ≤ 1) ∧
    (∀ r : ℚ, 0 < r → r ≤ 1 → ∃! position : ℕ × ℕ, Occurs r position) ∧
    (∀ t, ∃ n, t < (flattenedPrefix n).length) ∧
    (∀ n i, i < (flattenedPrefix n).length →
      (flattenedPrefix n)[i]? = some (fraction i)) ∧
    (∀ r position, Occurs r position → fraction (flatIndex position) = r) ∧
    (∀ i, 0 < fraction i ∧ fraction i ≤ 1 ∧
      0 < denominator i ∧ fraction i = (numerator i : ℚ) / (denominator i : ℚ)) := by
  refine ⟨?_, cumulative_blocks, cumulative_interval, exactly_once, ?_,
    flattenedPrefix_read, occurrence_flat, ?_⟩
  · intro n
    exact source_update (cumulative_nodup n)
  · intro t
    refine ⟨t + 2, ?_⟩
    have he : flattenedPrefix (t + 2) = cumulative (t + 1) := (cumulative_blocks _).symm
    rw [he]
    exact lt_of_lt_of_le (by omega) (cumulative_length _)
  · intro i
    have hi : i < (cumulative (i + 1)).length := lt_of_lt_of_le (by omega) (cumulative_length _)
    have hm : fraction i ∈ cumulative (i + 1) := by
      exact List.mem_of_getElem? (by simpa [fraction, List.getElem!_pos hi] using
        (List.getElem?_eq_getElem hi : (cumulative (i + 1))[i]? = _))
    have hin := cumulative_interval (i + 1) _ hm
    exact ⟨hin.1, hin.2, (fraction i).den_pos, (Rat.num_div_den _).symm⟩

end D5.S3.Arith.CounterSequences.KimberlingA371279


