/- GID: D5/S3/Factorization/Automata/PrimeHistoryGeodesic
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeHistoryGeodesic
   mirror-E: none(waiver:all-histories-sharp-length)
   anchors: []
   utility: none
   digest: A shortest representative of every nonempty guarded prime behavior has exact length twice its excursion width minus absolute displacement. -/

import D5.S3.Factorization.Automata.PrimeHistoryNormalForm
import D5.S3.Factorization.Automata.WordExcursionLowerBound

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.PrimeHistoryGeodesic

open PrimeHistoryNormalForm WordExcursionLowerBound

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

/-- An explicit representative attains the all-word lower bound. The minimum is
among all histories with the same exact guarded partial map, not merely those
with the same endpoint. Empty behavior is excluded from this statement. -/
theorem shortest_realization {a : Nat} (t : IntervalMap a) :
    normal a (shortestWord t) = some t ∧
    ((shortestWord t).length : Int) =
      2 * ((a : Int) - t.hi + t.lo) - max t.shift (-t.shift) ∧
    ∀ w : List Bool, normal a w = some t → (shortestWord t).length ≤ w.length := by
  have reflection_signature (w : List Bool) :
      low (w.map Bool.not) = -high w ∧
      high (w.map Bool.not) = -low w ∧
      displacement (w.map Bool.not) = -displacement w := by
    induction w with
    | nil => simp [low, high, displacement]
    | cons b w ih =>
        rcases ih with ⟨hl, hh, hd⟩
        cases b <;>
          simp only [List.map_cons, Bool.not_false, Bool.not_true,
            low, high, displacement, reduceCtorEq, if_false, if_true] <;>
          rw [hl, hh, hd] <;>
          constructor
        · omega
        · constructor <;> omega
        · omega
        · constructor <;> omega
  have realize_length (s : IntervalMap a) :
      ((realize s).length : Int) = 2 * ((a : Int) - s.hi + s.lo) - s.shift := by
    have h0 := s.lo_nonneg
    have h1 := s.ordered
    have h2 := s.hi_le
    have h3 := s.image_lo
    have h4 := s.image_hi
    simp only [realize, List.length_append, List.length_replicate]
    omega
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
      change low (realize (reflected t)) = -((a : Int) - t.hi) at rl
      change high (realize (reflected t)) = (a : Int) - ((a : Int) - t.lo) at rh
      change displacement (realize (reflected t)) = -t.shift at rf
      change ((realize (reflected t)).length : Int) =
        2 * ((a : Int) - ((a : Int) - t.lo) + ((a : Int) - t.hi)) - (-t.shift) at hn
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
    apply IntervalMap.ext
    · change -low (shortestWord t) = t.lo
      omega
    · change (a : Int) - high (shortestWord t) = t.hi
      omega
    · change displacement (shortestWord t) = t.shift
      exact hs.2.2.1
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
  have hb := WordExcursionLowerBound.word_length_lower_bound w
  rw [hcoord.1, hcoord.2.1, hcoord.2.2] at hb
  have heq := hs.2.2.2
  omega

#print axioms shortest_realization

end D5.S3.Factorization.Automata.PrimeHistoryGeodesic
