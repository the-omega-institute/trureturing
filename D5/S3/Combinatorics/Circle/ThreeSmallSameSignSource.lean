/- GID: D5/S3/Combinatorics/Circle/ThreeSmallSameSignSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeSmallSameSignSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Three same-sign SMALL occurrences are inserted into the forward physical LARGE cycle. -/
import D5.S3.Combinatorics.Circle.TwoSmallSource

/-! # Three same-sign SMALL labels in a physical source -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource
open SourceWidth ExpandingSourcePath TwoSmallProfile TwoSmallPlacement
open MixedSuffixEnergy TwoOppositeLargeExchange

/-- The valley decreases along a LARGE pair block.  Bounds at the two
ends and at the first peak control every intermediate physical prefix. -/
private theorem descending_pairs (f : ℕ → ℤ) (N d h : ℤ) (off s len : ℕ)
    (hd : 0 ≤ d) (hend : (4 : ℤ) ^ (s + len) * d ≤ N)
    (hvalley : 0 ≤ h + 2 * d - 2 * (4 : ℤ) ^ (s + len) * d)
    (hpeak : h + 2 * N + 2 * d - 4 * (4 : ℤ) ^ s * d ≤ 3 * N)
    (hv : ∀ j, s ≤ j → j < s + len →
      f (off + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * d ∧
      f (off + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * d) :
    InStrip f (3 * N) (h + 2 * d - 2 * (4 : ℤ) ^ s * d)
      (List.range' (off + 2 * s) (2 * len)) ∧
    ((List.range' (off + 2 * s) (2 * len)).map f).sum =
      -2 * d * ((4 : ℤ) ^ (s + len) - (4 : ℤ) ^ s) := by
  let H := fun j => h + 2 * d - 2 * (4 : ℤ) ^ j * d
  let P := fun j => h + 2 * N + 2 * d - 4 * (4 : ℤ) ^ j * d
  have bounds (j : ℕ) (hj : s ≤ j) (he : j ≤ s + len) :
      0 ≤ H j ∧ H j ≤ P j ∧ P j ≤ 3 * N := by
    have hlo := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hj) hd
    have hhi := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) he) hd
    dsimp [H, P]
    constructor
    · nlinarith only [hhi, hvalley]
    constructor <;> nlinarith only [hlo, hhi, hend, hpeak]
  obtain ⟨hs, hm⟩ := paired_segment f (3 * N) off s len H P
    (fun j hj he => ⟨(bounds j hj he).1,
      le_trans (bounds j hj he).2.1 (bounds j hj he).2.2⟩)
    (fun j hj he => ⟨le_trans (bounds j hj (by omega)).1
      (bounds j hj (by omega)).2.1, (bounds j hj (by omega)).2.2⟩) (by
      intro j hj he
      obtain ⟨hp, hn⟩ := hv j hj he
      dsimp [H, P]
      rw [hp, hn, pow_succ]
      constructor <;> ring)
  refine ⟨hs, ?_⟩
  dsimp [H] at hm
  nlinarith only [hm]

/-- There is no loss of the sharp integer half-strip when the temporary
sixfold heights are bounded by three times the odd modulus. -/
private theorem unscale_six (f : ℕ → ℤ) (N C : ℤ) (hNC : N = 2 * C + 1)
    (L : List ℕ) (hs : InStrip (fun i => 6 * f i) (3 * N) 0 L) :
    InStrip f C 0 L := by
  apply strip_of_all_prefixes
  intro n
  have hp := inStrip_prefix hs n
  simp only [zero_add, List.sum_map_mul_left] at hp
  dsimp only [mass]
  omega

private theorem one_block (D : ℕ) (hD : 0 < D) (f : ℕ → ℤ)
    (h0 : f 0 = 2 * ((4 : ℤ) ^ D - 1))
    (h1 : f 1 = 4 * ((4 : ℤ) ^ D - 1))
    (h2 : f 2 = 8 * ((4 : ℤ) ^ D - 1))
    (hp : ∀ j < D,
      f (3 + 2 * j) = 2 * (8 * (4 : ℤ) ^ D - 1) - 14 * (4 : ℤ) ^ j ∧
      f (3 + 2 * j + 1) = -2 * (8 * (4 : ℤ) ^ D - 1) - 28 * (4 : ℤ) ^ j) :
    ∃ L : List ℕ, L.Perm (List.range (2 * D + 3)) ∧
      InStrip f (3 * (8 * (4 : ℤ) ^ D - 1)) 0 L ∧ (L.map f).sum = 0 ∧
      L.filter (fun j => decide (3 ≤ j)) = List.range' 3 (2 * D) := by
  let H : ℤ := (4 : ℤ) ^ D
  let v : ℤ := (4 : ℤ) ^ (D - 1)
  have hv0 : 1 ≤ v := one_le_pow₀ (by norm_num)
  have hH : H = 4 * v := by
    dsimp [H, v]
    rw [show D = (D - 1) + 1 by omega, pow_succ]
    ring
  let pre := List.range' 3 (2 * (D - 1))
  let last := 3 + 2 * (D - 1)
  let L := [1] ++ pre ++ [0, 2, last, last + 1]
  obtain ⟨hs, hm⟩ := descending_pairs f (8 * H - 1) 7 (4 * (H - 1)) 3 0 (D - 1)
    (by norm_num) (by dsimp [v] at hH; nlinarith) (by dsimp [v] at hH; nlinarith)
    (by norm_num; nlinarith) (by
      intro j _ hj
      obtain ⟨ha, hb⟩ := hp j (by omega)
      constructor <;> dsimp [H] <;> nlinarith only [ha, hb])
  have hs' : InStrip f (3 * (8 * H - 1)) (f 1) pre := by
    simpa only [pre, h1, H, Nat.add_zero, Nat.mul_zero, pow_zero, one_mul] using hs
  have hm' : (pre.map f).sum = -14 * (v - 1) := by
    simpa only [pre, v, Nat.zero_add, pow_zero] using hm
  obtain ⟨hlp, hln⟩ := hp (D - 1) (by omega)
  change f last = 2 * (8 * H - 1) - 14 * v at hlp
  change f (last + 1) = -2 * (8 * H - 1) - 28 * v at hln
  have ht : InStrip f (3 * (8 * H - 1)) (f 1 + (pre.map f).sum)
      [0, 2, last, last + 1] := by
    simp only [InStrip]
    rw [hm', h0, h2, hlp, hln, h1]
    change _
    dsimp only [H] at hH ⊢
    constructor <;> try omega
    all_goals repeat' constructor <;> nlinarith
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · have hinv : [0, 1, 2] ++ (pre ++ [last, last + 1]) = List.range (2 * D + 3) := by
      have he : pre ++ [last, last + 1] = List.range' 3 (2 * D) := by
        dsimp [pre, last]
        rw [show [3 + 2 * (D - 1), 3 + 2 * (D - 1) + 1] =
          List.range' (3 + 2 * (D - 1)) 2 by simp [List.range'_succ]]
        rw [List.range'_append]
        congr 1
        omega
      rw [he, List.range_eq_range']
      have hfront : [0, 1, 2] = List.range' 0 3 := by decide
      rw [hfront, List.range'_append]
      congr 1 <;> omega
    rw [← hinv]
    dsimp [L]
    have he := (List.perm_middle (a := 0) (l₁ := [1] ++ pre) (l₂ := [2, last, last + 1]))
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using he
  · dsimp [L]
    apply inStrip_append
    · simp only [InStrip, zero_add, List.map_singleton, List.sum_singleton]
      refine ⟨by nlinarith [hH], by nlinarith [hH], ?_⟩
      exact ⟨by rw [h1]; nlinarith [hH], by rw [h1]; nlinarith [hH]⟩
    · simp only [List.map_singleton, List.sum_singleton, zero_add]
      exact inStrip_append hs' ht
  · dsimp [L]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    rw [hm', h0, h1, h2, hlp, hln]
    dsimp only [H] at hH ⊢
    nlinarith only [hH]
  · have hpre : pre.filter (fun j => decide (3 ≤ j)) = pre := by
      apply List.filter_eq_self.mpr
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hj
      simp
    have hlast : 3 ≤ last := by dsimp [last]; omega
    dsimp [L]
    simp only [List.filter_append, List.filter_cons, List.filter_nil, hpre]
    simp only [decide_eq_false (by omega : ¬3 ≤ 1), decide_eq_false (by omega : ¬3 ≤ 0),
      decide_eq_false (by omega : ¬3 ≤ 2), decide_eq_true hlast,
      decide_eq_true (by omega : 3 ≤ last + 1), Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.append_nil]
    dsimp [pre, last]
    rw [show [3 + 2 * (D - 1), 3 + 2 * (D - 1) + 1] =
      List.range' (3 + 2 * (D - 1)) 2 by simp [List.range'_succ], List.range'_append]
    congr 1
    omega

end D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource
