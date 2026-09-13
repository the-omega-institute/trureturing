/- GID: D5/S3/Factorization/Automata/PrimeHistoryGeodesic
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeHistoryGeodesic
   mirror-E: none(waiver:all-histories-sharp-length)
   anchors: []
   utility: none
   digest: A shortest representative of every nonempty guarded prime behavior
     has exact length twice its excursion width minus absolute displacement. -/

import D5.S3.Factorization.Automata.PrimeHistoryNormalForm

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.PrimeHistoryGeodesic

open PrimeHistoryNormalForm

/-- A lower bound on every actual word, not only on a chosen normal-form word.
The maximum is the absolute value of the final integer displacement. -/
theorem word_length_lower_bound (w : List Bool) :
    2 * (high w - low w) - max (displacement w) (-displacement w) ≤
      (w.length : Int) := by
  induction w with
  | nil => simp [high, low, displacement]
  | cons b w ih =>
      rcases excursion_bounds w with ⟨hl, hh, hdlo, hdhi⟩
      cases b <;>
        simp only [List.length_cons, high, low, displacement, jump,
          reduceCtorEq, if_false, if_true, Nat.cast_add, Nat.cast_one] <;>
        omega

/-- Reflection exchanges the two capacity boundaries and reverses displacement. -/
private theorem reflection_signature (w : List Bool) :
    low (w.map Bool.not) = -high w ∧
    high (w.map Bool.not) = -low w ∧
    displacement (w.map Bool.not) = -displacement w := by
  induction w with
  | nil => simp [low, high, displacement]
  | cons b w ih =>
      rcases ih with ⟨hl, hh, hd⟩
      cases b <;>
        simp only [List.map_cons, Bool.not_false, Bool.not_true,
          low, high, displacement, jump, reduceCtorEq, if_false, if_true] <;>
        rw [hl, hh, hd] <;>
        constructor
      · omega
      · constructor <;> omega
      · omega
      · constructor <;> omega

/-- Reflect a proposed partial translation in the midpoint of the capacity interval. -/
def reflected {a : Nat} (t : IntervalMap a) : IntervalMap a where
  lo := (a : Int) - t.hi
  hi := (a : Int) - t.lo
  shift := -t.shift
  lo_nonneg := by have := t.hi_le; omega
  ordered := by have := t.ordered; omega
  hi_le := by have := t.lo_nonneg; omega
  image_lo := by have := t.image_hi; omega
  image_hi := by have := t.image_lo; omega

/-- Visit the nearer optimal-order extreme first: lower then upper for nonnegative
shift; upper then lower for negative shift. The resulting word is explicit. -/
def shortestWord {a : Nat} (t : IntervalMap a) : List Bool :=
  if 0 ≤ t.shift then realize t else (realize (reflected t)).map Bool.not

private theorem realize_length {a : Nat} (t : IntervalMap a) :
    ((realize t).length : Int) = 2 * ((a : Int) - t.hi + t.lo) - t.shift := by
  have h0 := t.lo_nonneg
  have h1 := t.ordered
  have h2 := t.hi_le
  have h3 := t.image_lo
  have h4 := t.image_hi
  simp only [realize, List.length_append, List.length_replicate]
  omega

/-- An explicit representative attains the all-word lower bound. The minimum is
among all histories with the same exact guarded partial map, not merely those
with the same endpoint. Empty behavior is excluded from this statement. -/
theorem shortest_realization {a : Nat} (t : IntervalMap a) :
    normal a (shortestWord t) = some t ∧
    ((shortestWord t).length : Int) =
      2 * ((a : Int) - t.hi + t.lo) - max t.shift (-t.shift) ∧
    ∀ w : List Bool, normal a w = some t → (shortestWord t).length ≤ w.length := by
  have hs :
      low (shortestWord t) = -t.lo ∧ high (shortestWord t) = (a : Int) - t.hi ∧
      displacement (shortestWord t) = t.shift ∧
      ((shortestWord t).length : Int) =
        2 * ((a : Int) - t.hi + t.lo) - max t.shift (-t.shift) := by
    by_cases hd : 0 ≤ t.shift
    · simp only [shortestWord, if_pos hd]
      rcases realize_signature t with ⟨hl, hh, hf⟩
      refine ⟨hl, hh, hf, ?_⟩
      rw [realize_length]
      omega
    · simp only [shortestWord, if_neg hd, List.length_map]
      rcases reflection_signature (realize (reflected t)) with ⟨hl, hh, hf⟩
      rcases realize_signature (reflected t) with ⟨rl, rh, rf⟩
      have hn := realize_length (reflected t)
      dsimp [reflected] at rl rh rf hn
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
  have hnormal : normal a (shortestWord t) = some t := by
    have hc : high (shortestWord t) - low (shortestWord t) ≤ (a : Int) := by
      rw [hs.1, hs.2.1]
      have := t.ordered
      omega
    unfold normal
    rw [dif_pos hc]
    apply congrArg some
    apply IntervalMap.ext <;> simp [hs.1, hs.2.1, hs.2.2.1]
  refine ⟨hnormal, hs.2.2.2, ?_⟩
  intro w hw
  have hcoord : low w = -t.lo ∧ high w = (a : Int) - t.hi ∧
      displacement w = t.shift := by
    unfold normal at hw
    split at hw
    · have ht := Option.some.inj hw
      have hl := congrArg IntervalMap.lo ht
      have hh := congrArg IntervalMap.hi ht
      have hd := congrArg IntervalMap.shift ht
      dsimp at hl hh hd
      constructor
      · omega
      constructor <;> omega
    · simp at hw
  have hb := word_length_lower_bound w
  rw [hcoord.1, hcoord.2.1, hcoord.2.2] at hb
  have heq := hs.2.2.2
  omega

#print axioms word_length_lower_bound
#print axioms shortest_realization

end D5.S3.Factorization.Automata.PrimeHistoryGeodesic
