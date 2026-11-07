/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/PacketStrip
   generality: I
   mirror-B: none(waiver:consumed-packet-proof)
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.Range]
   utility: none
   digest: Arbitrarily many labelled packets and their coupled charged prefix strips. -/
import Batteries.Tactic.OpenPrivate
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

/-- The two packet drifts propagate one upper peak and one lower final valley
to every intermediate prefix. The final positive packet is deliberately absent.
There are `n + 1` negative labels and only `n` positive packets. -/
private theorem descending_packets_strip {α : Type*} (f : α → ℤ)
    (negative : ℕ → α) (positive : ℕ → List α)
    (lo hi F : ℤ) (s n : ℕ)
    (hnegative : ∀ j, s ≤ j → j ≤ s + n → f (negative j) ≤ 0)
    (hpositive : ∀ j, s ≤ j → j < s + n → ∀ x ∈ positive j, 0 ≤ f x)
    (hpeak_drift : ∀ j, s ≤ j → j < s + n →
      f (negative j) + ((positive j).map f).sum ≤ 0)
    (hvalley_drift : ∀ j, s ≤ j → j < s + n →
      ((positive j).map f).sum + f (negative (j + 1)) ≤ 0)
    (hstart : F ≤ hi)
    (hend : lo ≤ F +
      ((((List.range' s n).flatMap (fun j => negative j :: positive j)) ++
        [negative (s + n)]).map f).sum) :
    InStrip f (hi - lo) (F - lo)
      (((List.range' s n).flatMap (fun j => negative j :: positive j)) ++
        [negative (s + n)]) := by
  induction n generalizing s F with
  | zero =>
    have hn := hnegative s (by omega) (by omega)
    simp only [List.range'_zero, List.flatMap_nil, List.nil_append,
      Nat.add_zero, List.map_singleton, List.sum_singleton] at hend ⊢
    simp only [InStrip]
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  | succ n ih =>
    let tail := ((List.range' (s + 1) n).flatMap
      (fun j => negative j :: positive j)) ++ [negative (s + 1 + n)]
    have hword :
        ((List.range' s (n + 1)).flatMap (fun j => negative j :: positive j)) ++
          [negative (s + (n + 1))] = (negative s :: positive s) ++ tail := by
      simp only [List.range'_succ, List.flatMap_cons, List.append_assoc, tail,
        show s + (n + 1) = s + 1 + n by omega]
    rw [hword] at hend ⊢
    have hn := hnegative s (by omega) (by omega)
    have hp := hpositive s (by omega) (by omega)
    have hd := hpeak_drift s (by omega) (by omega)
    have hv := hvalley_drift s (by omega) (by omega)
    let F' := F + f (negative s) + ((positive s).map f).sum
    have hF' : F' ≤ hi := by dsimp [F']; omega
    have htail : InStrip f (hi - lo) (F' - lo) tail := by
      apply ih
      · intro j hj hj'; exact hnegative j (by omega) (by omega)
      · intro j hj hj'; exact hpositive j (by omega) (by omega)
      · intro j hj hj'; exact hpeak_drift j (by omega) (by omega)
      · intro j hj hj'; exact hvalley_drift j (by omega) (by omega)
      · exact hF'
      · simpa only [tail, List.map_append, List.sum_append, List.map_cons,
          List.sum_cons, List.map_nil, List.sum_nil, add_zero, add_assoc, F',
          Nat.add_assoc] using hend
    have htail_valley : lo ≤ F' + f (negative (s + 1)) := by
      have h := inStrip_prefix htail 1
      have he : tail.take 1 = [negative (s + 1)] := by
        cases n <;> simp [tail, List.range'_succ]
      rw [he] at h
      simp only [List.map_singleton, List.sum_singleton] at h
      omega
    have hlow : lo ≤ F + f (negative s) := by dsimp [F'] at htail_valley; omega
    have hpos : InStrip f (hi - lo) (F + f (negative s) - lo) (positive s) :=
      positive_block_strip hp (by omega) (by dsimp [F'] at hF'; omega)
    have hblock : InStrip f (hi - lo) (F - lo) (negative s :: positive s) := by
      refine ⟨by omega, by omega, ?_⟩
      convert hpos using 1 <;> ring
    apply inStrip_append hblock
    convert htail using 1
    simp only [List.map_cons, List.sum_cons]
    dsimp [F']
    ring

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

/-- Replace a coordinate only where a physical word actually visits it. -/
private theorem inStrip_congr {α : Type*} (f g : α → ℤ) (B h : ℤ)
    (l : List α) (he : ∀ x ∈ l, f x = g x)
    (hl : InStrip f B h l) : InStrip g B h l := by
  induction l generalizing h with
  | nil => exact hl
  | cons x xs ih =>
    refine ⟨hl.1, hl.2.1, ?_⟩
    rw [← he x (by simp)]
    exact ih (h + f x) (fun y hy => he y (by simp [hy])) hl.2.2

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
