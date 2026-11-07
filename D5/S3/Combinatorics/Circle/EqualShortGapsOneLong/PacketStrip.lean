/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/PacketStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/EqualShortGapsOneLong/PacketStrip
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.Range]
   utility: none
   digest: Arbitrarily many labelled packets and their coupled charged prefix strips. -/
import D5.S3.Combinatorics.Circle.PeriodicShortening
import D5.S3.Combinatorics.Circle.ThreeBitSource

/-! Packet endpoints control every physical prefix, including prefixes inside a
positive packet. The charged coordinate is controlled on the same literal list. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
open SourceWidth
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource
open private sum_linear prefix_nonneg_le strip_of_prefix
  from D5.S3.Combinatorics.Circle.PeriodicShortening

/-- Concatenating any finite number of labelled negative/positive packets needs
only their actual peak and valley heights; no value-based relabelling occurs. -/
private theorem packets_strip {α : Type*} (f : α → ℤ)
    (negative : ℕ → α) (positive : ℕ → List α)
    (peak valley : ℕ → ℤ) (lo hi : ℤ) (s n : ℕ)
    (hpeak : ∀ j, s ≤ j → j ≤ s + n → lo ≤ peak j ∧ peak j ≤ hi)
    (hvalley : ∀ j, s ≤ j → j < s + n → lo ≤ valley j ∧ valley j ≤ hi)
    (hnegative : ∀ j, s ≤ j → j < s + n → peak j + f (negative j) = valley j)
    (hpositive : ∀ j, s ≤ j → j < s + n → ∀ x ∈ positive j, 0 ≤ f x)
    (hmass : ∀ j, s ≤ j → j < s + n →
      valley j + ((positive j).map f).sum = peak (j + 1)) :
    InStrip f (hi - lo) (peak s - lo)
      ((List.range' s n).flatMap (fun j => negative j :: positive j)) := by
  induction n generalizing s with
  | zero =>
    have hs := hpeak s (by omega) (by omega)
    simp only [List.range'_zero, List.flatMap_nil, InStrip]
    constructor <;> omega
  | succ n ih =>
    have hs := hpeak s (by omega) (by omega)
    have hv := hvalley s (by omega) (by omega)
    have hn := hnegative s (by omega) (by omega)
    have hm := hmass s (by omega) (by omega)
    have hp := hpositive s (by omega) (by omega)
    have hs' := hpeak (s + 1) (by omega) (by omega)
    have hpos : InStrip f (hi - lo) (valley s - lo) (positive s) :=
      positive_block_strip hp (by omega) (by omega)
    have hblock : InStrip f (hi - lo) (peak s - lo) (negative s :: positive s) := by
      refine ⟨by omega, by omega, ?_⟩
      convert hpos using 1 <;> omega
    have htail : InStrip f (hi - lo) (peak (s + 1) - lo)
        ((List.range' (s + 1) n).flatMap (fun j => negative j :: positive j)) := by
      apply ih
      · intro j hj hj'; exact hpeak j (by omega) (by omega)
      · intro j hj hj'; exact hvalley j (by omega) (by omega)
      · intro j hj hj'; exact hnegative j (by omega) (by omega)
      · intro j hj hj'; exact hpositive j (by omega) (by omega)
      · intro j hj hj'; exact hmass j (by omega) (by omega)
    have htail' : InStrip f (hi - lo)
        (peak s - lo + ((negative s :: positive s).map f).sum)
        ((List.range' (s + 1) n).flatMap (fun j => negative j :: positive j)) := by
      convert htail using 1
      simp only [List.map_cons, List.sum_cons]
      omega
    simpa only [List.range'_succ, Nat.add_zero, Nat.mul_one,
      List.flatMap_cons] using inStrip_append hblock htail'

/-- Every prefix of the same physical word satisfies the second coordinate
strip when its nonnegative charge is bounded by twice the first-coordinate
floor. In particular this covers all partial positive packets. -/
private theorem charged_strip {α : Type*} (l : List α) (f c : α → ℤ)
    (lo hi F C A B : ℤ)
    (hf : InStrip f (hi - lo) (F - lo) l)
    (hc : ∀ x ∈ l, 0 ≤ c x) (hC : 0 ≤ C)
    (hcharge : C + (l.map c).sum ≤ A)
    (hfloor : A ≤ 2 * lo) (hceiling : 2 * hi ≤ B) :
    InStrip (fun x => 2 * f x - c x) B (2 * F - C) l := by
  apply strip_of_prefix
  intro n
  have hF := inStrip_prefix hf n
  have hq := prefix_nonneg_le l c hc n
  have he : ((l.take n).map (fun x => 2 * f x - c x)).sum =
      2 * ((l.take n).map f).sum - ((l.take n).map c).sum := by
    simpa only [sub_eq_add_neg, neg_mul, one_mul] using
      sum_linear (l.take n) f c 2 (-1)
  rw [he]
  constructor <;> omega

/-- A nonnegative lower wall can be forgotten without changing the word or
its starting height. -/
private theorem inStrip_shift {α : Type*} (f : α → ℤ) (lo hi F : ℤ)
    (l : List α) (hlo : 0 ≤ lo)
    (hl : InStrip f (hi - lo) (F - lo) l) : InStrip f hi F l := by
  apply strip_of_prefix
  intro n
  have hp := inStrip_prefix hl n
  constructor <;> omega

end D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
