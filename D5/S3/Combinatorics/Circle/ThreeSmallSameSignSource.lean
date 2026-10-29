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
    calc
      (4 : ℤ) ^ D = 4 ^ ((D - 1) + 1) := by congr 1; omega
      _ = 4 * 4 ^ (D - 1) := by rw [pow_succ]; ring
  let pre := List.range' 3 (2 * (D - 1))
  let last := 3 + 2 * (D - 1)
  let L := [1] ++ pre ++ [0, 2, last, last + 1]
  obtain ⟨hs, hm⟩ := descending_pairs f (8 * H - 1) 7 (4 * (H - 1)) 3 0 (D - 1)
    (by norm_num) (by simp only [Nat.zero_add]; change v * 7 ≤ 8 * H - 1; nlinarith)
    (by simp only [Nat.zero_add]; change 0 ≤ 4 * (H - 1) + 2 * 7 - 2 * v * 7; nlinarith)
    (by norm_num; nlinarith) (by
      intro j _ hj
      obtain ⟨ha, hb⟩ := hp j (by omega)
      constructor <;> dsimp [H] <;> nlinarith only [ha, hb])
  have hs' : InStrip f (3 * (8 * H - 1)) (f 1) pre := by
    simpa [pre, h1, H] using hs
  have hm' : (pre.map f).sum = -14 * (v - 1) := by
    simpa [pre, v] using hm
  obtain ⟨hlp, hln⟩ := hp (D - 1) (by omega)
  change f last = 2 * (8 * H - 1) - 14 * v at hlp
  change f (last + 1) = -2 * (8 * H - 1) - 28 * v at hln
  have ht : InStrip f (3 * (8 * H - 1)) (f 1 + (pre.map f).sum)
      [0, 2, last, last + 1] := by
    simp only [InStrip]
    rw [hm', h0, h2, hlp, hln, h1]
    dsimp only [H] at hH ⊢
    constructor <;> omega
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · have hinv : [0, 1, 2] ++ (pre ++ [last, last + 1]) = List.range (2 * D + 3) := by
      have he : pre ++ [last, last + 1] = List.range' 3 (2 * D) := by
        dsimp [pre, last]
        rw [show [3 + 2 * (D - 1), 3 + 2 * (D - 1) + 1] =
          List.range' (3 + 2 * (D - 1)) 2 by simp [List.range'_succ]]
        rw [List.range'_append_1]
        congr 1
        omega
      rw [he, List.range_eq_range']
      have hfront : [0, 1, 2] = List.range' 0 3 := by decide
      rw [hfront, List.range'_append_1]
      congr 1; omega
    rw [← hinv]
    apply List.perm_iff_count.mpr
    intro x
    simp only [L, List.count_append, List.count_cons, List.count_nil]
    omega
  · change InStrip f (3 * (8 * H - 1)) 0 (1 :: (pre ++ [0, 2, last, last + 1]))
    refine ⟨by omega, by nlinarith [hH], ?_⟩
    simpa only [zero_add] using inStrip_append hs' ht
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
      decide_eq_true (by omega : 3 ≤ last + 1), Bool.false_eq_true, ↓reduceIte]
    dsimp [pre, last]
    rw [show [3 + 2 * (D - 1), 3 + 2 * (D - 1) + 1] =
      List.range' (3 + 2 * (D - 1)) 2 by simp [List.range'_succ], List.range'_append_1]
    congr 1
    omega

-- The two insertion schedules check each intermediate prefix separately.
set_option maxHeartbeats 800000 in
private theorem two_blocks (B D : ℕ) (hB : 0 < B) (hD : 0 < D)
    (N d e z : ℤ) (hd : 0 < d) (he : 0 < e) (hz : 0 < z)
    (hdN : d < N) (hzN : z < N)
    (hde : 2 * d = N + e)
    (hez : 2 * (4 : ℤ) ^ B * e = N + z)
    (hzd : 2 * (4 : ℤ) ^ D * z = N + d)
    (f : ℕ → ℤ) (ha : f 0 = N - d) (hb : f 1 = N - e)
    (hc : f (2 * B + 2) = N - z)
    (hY : ∀ j < B,
      f (2 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * e ∧
      f (2 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * e)
    (hZ : ∀ j < D,
      f (2 * B + 3 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * z ∧
      f (2 * B + 3 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * z) :
    ∃ L : List ℕ, L.Perm (List.range (2 * B + 2 * D + 3)) ∧
      InStrip f (3 * N) 0 L ∧ (L.map f).sum = 0 ∧
      L.filter (fun j => decide (j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 2 * B + 2)) =
        List.range' 2 (2 * B) ++ List.range' (2 * B + 3) (2 * D) := by
  let G : ℤ := (4 : ℤ) ^ B
  let H : ℤ := (4 : ℤ) ^ D
  have hG : 4 ≤ G := by
    simpa only [G, pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hB
  have hH : 4 ≤ H := by
    simpa only [H, pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hD
  change 2 * G * e = N + z at hez
  change 2 * H * z = N + d at hzd
  have h4e : 4 * e < N := by nlinarith
  have h4z : 4 * z < N := by nlinarith
  let j := if e ≤ z then B - 1 else B
  let v : ℤ := (4 : ℤ) ^ j
  have hj : j ≤ B := by dsimp [j]; split_ifs <;> omega
  have hsplit : (e ≤ z ∧ 4 * v = G) ∨ (z < e ∧ v = G) := by
    dsimp [j, v]
    by_cases h : e ≤ z
    · left
      refine ⟨h, ?_⟩
      simp only [ite_eq_left h]
      dsimp [G]
      calc
        4 * (4 : ℤ) ^ (B - 1) = 4 ^ ((B - 1) + 1) := by rw [pow_succ]; ring
        _ = 4 ^ B := by congr 1; omega
    · right
      exact ⟨by omega, by simp only [ite_eq_right h]; rfl⟩
  have hv1 : 1 ≤ v := one_le_pow₀ (by norm_num)
  have hge : G * e < N := by nlinarith
  have hhz : H * z < N := by nlinarith
  have hpre : 0 ≤ N + e - 2 * v * e := by
    rcases hsplit with ⟨hle, hv⟩ | ⟨hlt, hv⟩ <;> nlinarith
  have hpostpeak : 4 * N + e - d - 4 * v * e ≤ 3 * N := by
    rcases hsplit with ⟨hle, hv⟩ | ⟨hlt, hv⟩ <;> nlinarith
  let Y0 := List.range' 2 (2 * j)
  let Y1 := List.range' (2 + 2 * j) (2 * (B - j))
  let Z0 := List.range' (2 * B + 3) (2 * (D - 1))
  let last := 2 * B + 3 + 2 * (D - 1)
  let gamma := 2 * B + 2
  let L := [1] ++ Y0 ++ [0] ++ Y1 ++ Z0 ++ [gamma, last, last + 1]
  obtain ⟨hsY0, hmY0⟩ := descending_pairs f N e (N - e) 2 0 j (by omega)
    (by simp only [Nat.zero_add]; change v * e ≤ N; nlinarith)
    (by simp only [Nat.zero_add]; change 0 ≤ N - e + 2 * e - 2 * v * e; omega)
    (by norm_num; omega) (fun i _ hi => hY i (by omega))
  have hs0 : InStrip f (3 * N) (N - e) Y0 := by simpa [Y0] using hsY0
  have hm0 : (Y0.map f).sum = -2 * e * (v - 1) := by simpa [Y0, v] using hmY0
  obtain ⟨hsY1, hmY1⟩ := descending_pairs f N e (2 * N - e - d) 2 j (B - j)
    (by omega) (by simpa only [Nat.add_sub_of_le hj, G] using le_of_lt hge)
    (by rw [Nat.add_sub_of_le hj]; change 0 ≤ 2 * N - e - d + 2 * e - 2 * G * e; omega)
    (by change 2 * N - e - d + 2 * N + 2 * e - 4 * v * e ≤ 3 * N; omega)
    (fun i _ hi => hY i (by omega))
  have hs1 : InStrip f (3 * N) (2 * N + e - d - 2 * v * e) Y1 := by
    convert hsY1 using 1 <;> dsimp [Y1, v] <;> ring
  have hm1 : (Y1.map f).sum = -2 * e * (G - v) := by
    simpa [Y1, v, G, Nat.add_sub_of_le hj] using hmY1
  let u : ℤ := (4 : ℤ) ^ (D - 1)
  have hu : 4 * u = H := by
    dsimp [u, H]
    calc
      4 * (4 : ℤ) ^ (D - 1) = 4 ^ ((D - 1) + 1) := by rw [pow_succ]; ring
      _ = 4 ^ D := by congr 1; omega
  have hu1 : 1 ≤ u := one_le_pow₀ (by norm_num)
  have huZ : 8 * u * z = N + d := by
    have hh := congrArg (fun x : ℤ => x * z) hu
    nlinarith only [hh, hzd]
  obtain ⟨hsZ0, hmZ0⟩ := descending_pairs f N z (d - z) (2 * B + 3) 0 (D - 1)
    (by omega) (by simp only [Nat.zero_add]; change u * z ≤ N; nlinarith)
    (by simp only [Nat.zero_add]; change 0 ≤ d - z + 2 * z - 2 * u * z; nlinarith)
    (by norm_num; omega) (fun i _ hi => hZ i (by omega))
  have hsZ : InStrip f (3 * N) (d - z) Z0 := by simpa [Z0] using hsZ0
  have hmZ : (Z0.map f).sum = -2 * z * (u - 1) := by simpa [Z0, u] using hmZ0
  obtain ⟨hlp, hln⟩ := hZ (D - 1) (by omega)
  change f last = 2 * N - 2 * u * z at hlp
  change f (last + 1) = -2 * N - 4 * u * z at hln
  have ht : InStrip f (3 * N) (d - z + (Z0.map f).sum) [gamma, last, last + 1] := by
    simp only [InStrip]
    rw [hmZ, show f gamma = N - z from hc, hlp, hln]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [huZ, hd, hdN, he, hz, h4z, hde]
  have hsYZ := inStrip_append hs1 (by
    rw [hm1]
    convert (inStrip_append hsZ ht) using 1 <;> nlinarith only [hde, hez])
  have hsmall : InStrip f (3 * N) (N + e - 2 * v * e) [0] := by
    have hh := inStrip_prefix hs1 0
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at hh
    simp only [InStrip, ha]
    exact ⟨hpre, by omega, by omega, by omega⟩
  have hsinsert := inStrip_append hsmall (by
    simp only [List.map_singleton, List.sum_singleton, ha]
    convert hsYZ using 1 <;> ring)
  have hsall := inStrip_append hs0 (by rw [hm0]; convert hsinsert using 1 <;> ring)
  have hstrip : InStrip f (3 * N) 0 L := by
    change InStrip f (3 * N) 0 (1 :: (Y0 ++ [0] ++ Y1 ++ Z0 ++ [gamma, last, last + 1]))
    refine ⟨by omega, by omega, ?_⟩
    simpa only [zero_add, hb, List.append_assoc] using hsall
  have hYjoin : Y0 ++ Y1 = List.range' 2 (2 * B) := by
    dsimp [Y0, Y1]
    rw [List.range'_append_1]
    congr 1
    omega
  have hZjoin : Z0 ++ [last, last + 1] = List.range' (2 * B + 3) (2 * D) := by
    dsimp [Z0, last]
    rw [show [2 * B + 3 + 2 * (D - 1), 2 * B + 3 + 2 * (D - 1) + 1] =
      List.range' (2 * B + 3 + 2 * (D - 1)) 2 by simp [List.range'_succ],
      List.range'_append_1]
    congr 1
    omega
  have hinv : [0, 1] ++ (Y0 ++ Y1) ++ [gamma] ++ (Z0 ++ [last, last + 1]) =
      List.range (2 * B + 2 * D + 3) := by
    rw [hYjoin, hZjoin]
    have hpref : [0, 1] ++ List.range' 2 (2 * B) = List.range' 0 (2 * B + 2) := by
      change List.range' 0 2 ++ List.range' (0 + 2) (2 * B) = _
      rw [List.range'_append_1]
      congr 1
      omega
    have hmid : List.range' 0 (2 * B + 2) ++ [gamma] =
        List.range' 0 (2 * B + 3) := by
      simpa only [gamma, Nat.zero_add] using
        (List.range'_1_concat (s := 0) (n := 2 * B + 2)).symm
    change ([0, 1] ++ List.range' 2 (2 * B)) ++ [gamma] ++
      List.range' (2 * B + 3) (2 * D) = _
    rw [hpref, hmid]
    have hjoin := List.range'_append_1 (s := 0) (m := 2 * B + 3) (n := 2 * D)
    simp only [Nat.zero_add] at hjoin
    rw [hjoin, List.range_eq_range']
    congr 1
    omega
  refine ⟨L, ?_, hstrip, ?_, ?_⟩
  · rw [← hinv]
    apply List.perm_iff_count.mpr
    intro x
    simp only [L, List.count_append, List.count_cons, List.count_nil]
    omega
  · simp only [L, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, ha, hb, hm0, hm1, hmZ, hlp, hln]
    rw [show f gamma = N - z from hc]
    nlinarith only [hde, hez, huZ]
  · let p := fun j => decide (j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 2 * B + 2)
    have hkeepY (R : List ℕ) (hR : ∀ x ∈ R, 2 ≤ x ∧ x < 2 * B + 2) :
        R.filter p = R := by
      apply List.filter_eq_self.mpr
      intro x hx
      have := hR x hx
      simp only [p, decide_eq_true_eq]
      omega
    have hy0 : Y0.filter p = Y0 := hkeepY Y0 (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      omega)
    have hy1 : Y1.filter p = Y1 := hkeepY Y1 (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      omega)
    have hz0 : Z0.filter p = Z0 := by
      apply List.filter_eq_self.mpr
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      simp only [p, decide_eq_true_eq]
      dsimp [Z0] at *
      omega
    change L.filter p = _
    dsimp only [L]
    simp only [List.filter_append, hy0, hy1, hz0]
    have hp1 : p 1 = false := by simp [p]
    have hp0 : p 0 = false := by simp [p]
    have hpg : p gamma = false := by simp [p, gamma]
    have hpl : p last = true := by simp only [p, decide_eq_true_eq]; dsimp [last]; omega
    have hpl' : p (last + 1) = true := by simp only [p, decide_eq_true_eq]; dsimp [last]; omega
    simp only [List.filter_cons, List.filter_nil, hp1, hp0, hpg, hpl, hpl',
      Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil]
    rw [hYjoin, List.append_assoc, hZjoin]

private theorem aligned_power (A B D : ℕ) (hD : 0 < D)
    (d e z : ℤ)
    (hd : d = 4 * (4 : ℤ) ^ B * 4 ^ D + 2 * 4 ^ D + 1)
    (he : e = 4 * (4 : ℤ) ^ D * 4 ^ A + 2 * 4 ^ A + 1)
    (hz : z = 4 * (4 : ℤ) ^ A * 4 ^ B + 2 * 4 ^ B + 1)
    (hde : e ≤ d) (hdz : z ≤ d) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧
      d ≤ (4 : ℤ) ^ j * z ∧ (4 : ℤ) ^ j * z ≤ 2 * (d + z) := by
  let F : ℤ := (4 : ℤ) ^ A
  let G : ℤ := (4 : ℤ) ^ B
  let H : ℤ := (4 : ℤ) ^ D
  change d = 4 * G * H + 2 * H + 1 at hd
  change e = 4 * H * F + 2 * F + 1 at he
  change z = 4 * F * G + 2 * G + 1 at hz
  have hF : 1 ≤ F := one_le_pow₀ (by norm_num)
  have hG : 1 ≤ G := one_le_pow₀ (by norm_num)
  have hH : 1 ≤ H := one_le_pow₀ (by norm_num)
  have hAB : A ≤ B := by
    by_contra h
    have h4 : 4 * G ≤ F := by
      have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) (show B + 1 ≤ A by omega)
      simpa only [pow_succ, G, F, mul_comm] using hh
    have hprod := mul_le_mul_of_nonneg_left (show (3 : ℤ) ≤ F - G by omega)
      (show 0 ≤ H by omega)
    nlinarith only [hd, he, hde, hprod, hF, hH]
  have hAD : A ≤ D := by
    by_contra h
    have h4 : 4 * H ≤ F := by
      have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) (show D + 1 ≤ A by omega)
      simpa only [pow_succ, H, F, mul_comm] using hh
    have hprod := mul_le_mul_of_nonneg_right hG (show 0 ≤ F - H by omega)
    nlinarith only [hd, hz, hdz, hprod, h4, hG, hH]
  have hFG : F ≤ G := pow_le_pow_right₀ (by norm_num) hAB
  by_cases hAD' : A = D
  · have hFH : F = H := by simp only [F, H, hAD']
    have hd' := hd
    rw [← hFH] at hd'
    have hGF : G = F := by nlinarith only [hd', hz, hdz, hFG]
    have hdz' : d = z := by rw [hd, hz, ← hFH, hGF]
    refine ⟨1, by omega, hD, ?_, ?_⟩
    rw [pow_one, ← hdz']
    · nlinarith only [hd, hG, hH, mul_nonneg (show 0 ≤ G by omega) (show 0 ≤ H by omega)]
    · rw [pow_one, ← hdz']; omega
  · let j := D - A
    let q : ℤ := (4 : ℤ) ^ j
    have hj : 1 ≤ j := by dsimp [j]; omega
    have hq : 1 ≤ q := one_le_pow₀ (by norm_num)
    have hFq : F * q = H := by
      dsimp [F, q, H, j]
      rw [← pow_add, Nat.add_sub_of_le hAD]
    have hqH : q ≤ H := by
      exact pow_le_pow_right₀ (by norm_num) (show j ≤ D by dsimp [j]; omega)
    have hqz : q * z = 4 * G * H + q * (2 * G + 1) := by
      rw [hz, ← hFq]
      ring
    have hlow := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ 2 * G + 1 - 2 * F by omega)
      (show 0 ≤ q by omega)
    have hupp := mul_le_mul_of_nonneg_right hqH (show 0 ≤ 2 * G + 1 by omega)
    refine ⟨j, hj, by dsimp [j]; omega, ?_, ?_⟩
    · change d ≤ q * z
      nlinarith only [hd, hqz, hlow, hFq, hq]
    · change q * z ≤ 2 * (d + z)
      have hGH := mul_nonneg (show 0 ≤ G by omega) (show 0 ≤ H by omega)
      have hz0 : 0 ≤ z := by nlinarith only [hz, hF, hG, mul_nonneg (show 0 ≤ F by omega) (show 0 ≤ G by omega)]
      nlinarith only [hd, hqz, hupp, hGH, hH, hz0]


set_option maxHeartbeats 800000 in
private theorem three_blocks (A B D : ℕ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (N d e z : ℤ) (hd : 0 < d) (he : 0 < e) (hz : 0 < z)
    (hdN : d < N) (heN : e < N) (hzN : z < N) (hde : e ≤ d) (hdz : z ≤ d)
    (hXY : 2 * (4 : ℤ) ^ A * d = N + e)
    (hYZ : 2 * (4 : ℤ) ^ B * e = N + z)
    (hZX : 2 * (4 : ℤ) ^ D * z = N + d)
    (hdval : d = 4 * (4 : ℤ) ^ B * 4 ^ D + 2 * 4 ^ D + 1)
    (heval : e = 4 * (4 : ℤ) ^ D * 4 ^ A + 2 * 4 ^ A + 1)
    (hzval : z = 4 * (4 : ℤ) ^ A * 4 ^ B + 2 * 4 ^ B + 1)
    (f : ℕ → ℤ) (ha : f 0 = N - d) (hb : f (2 * A + 1) = N - e)
    (hc : f (2 * A + 2 * B + 2) = N - z)
    (hX : ∀ j < A, f (1 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * d ∧
      f (1 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * d)
    (hY : ∀ j < B, f (2 * A + 2 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * e ∧
      f (2 * A + 2 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * e)
    (hZ : ∀ j < D, f (2 * A + 2 * B + 3 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * z ∧
      f (2 * A + 2 * B + 3 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * z) :
    ∃ L : List ℕ, L.Perm (List.range (2 * A + 2 * B + 2 * D + 3)) ∧
      InStrip f (3 * N) 0 L ∧ (L.map f).sum = 0 ∧
      L.filter (fun j => decide (j ≠ 0 ∧ j ≠ 2 * A + 1 ∧ j ≠ 2 * A + 2 * B + 2)) =
        List.range' 1 (2 * A) ++ List.range' (2 * A + 2) (2 * B) ++
          List.range' (2 * A + 2 * B + 3) (2 * D) := by
  let F : ℤ := (4 : ℤ) ^ A
  let G : ℤ := (4 : ℤ) ^ B
  let H : ℤ := (4 : ℤ) ^ D
  change 2 * F * d = N + e at hXY
  change 2 * G * e = N + z at hYZ
  change 2 * H * z = N + d at hZX
  have hF : 4 ≤ F := by
    simpa only [F, pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hA
  have hFd : F * d < N := by nlinarith only [hXY, heN]
  have hGe : G * e < N := by nlinarith only [hYZ, hzN]
  have hHz : H * z < N := by nlinarith only [hZX, hdN]
  have h4d : 4 * d < N := by nlinarith only [hF, hd, hFd]
  have hex : ∃ s : ℕ, s < B ∧ d ≤ (4 : ℤ) ^ (s + 1) * e := by
    refine ⟨B - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hB]
    change d ≤ G * e
    nlinarith only [hd, h4d, hYZ, hz]
  let s := Nat.find hex
  let v : ℤ := (4 : ℤ) ^ s
  have hs : s < B := (Nat.find_spec hex).1
  have hcut : d ≤ 4 * v * e := by
    have hh := (Nat.find_spec hex).2
    simpa only [pow_succ, v, s, mul_assoc, mul_comm, mul_left_comm] using hh
  have hbefore : v * e ≤ d := by
    by_cases hs0 : s = 0
    · simpa only [v, hs0, pow_zero, one_mul] using hde
    · have hm := Nat.find_min hex (show s - 1 < Nat.find hex by change s - 1 < s; omega)
      have hpred : s - 1 < B := by omega
      have hnot : ¬ d ≤ (4 : ℤ) ^ s * e := by
        intro hh
        apply hm
        exact ⟨hpred, by simpa only [Nat.sub_add_cancel (show 1 ≤ s by omega)] using hh⟩
      change (4 : ℤ) ^ s * e ≤ d
      omega
  obtain ⟨jZ, hjZ, hjZD, hzcut, hzupper⟩ := aligned_power A B D hD d e z hdval heval hzval hde hdz
  let u : ℤ := (4 : ℤ) ^ (jZ - 1)
  have hu : 4 * u = (4 : ℤ) ^ jZ := by
    dsimp [u]
    calc
      4 * (4 : ℤ) ^ (jZ - 1) = 4 ^ ((jZ - 1) + 1) := by rw [pow_succ]; ring
      _ = 4 ^ jZ := by congr 1; omega
  rw [← hu] at hzcut hzupper
  have hv1 : 1 ≤ v := one_le_pow₀ (by norm_num)
  have hu1 : 1 ≤ u := one_le_pow₀ (by norm_num)
  let beta := 2 * A + 1
  let gamma := 2 * A + 2 * B + 2
  let X := List.range' 1 (2 * A)
  let Y0 := List.range' (2 * A + 2) (2 * s)
  let Y1 := List.range' (2 * A + 2 + 2 * s) (2 * (B - s))
  let Z0 := List.range' (2 * A + 2 * B + 3) (2 * (jZ - 1))
  let Z1 := List.range' (2 * A + 2 * B + 3 + 2 * (jZ - 1)) (2 * (D - (jZ - 1)))
  let L := [beta] ++ X ++ Y0 ++ [0] ++ Y1 ++ Z0 ++ [gamma] ++ Z1
  obtain ⟨hsX, hmX⟩ := descending_pairs f N d (N - e) 1 0 A (by omega)
    (by simpa only [Nat.zero_add, F] using le_of_lt hFd)
    (by simp only [Nat.zero_add]; change 0 ≤ N - e + 2 * d - 2 * F * d; omega)
    (by norm_num; omega) (fun i _ hi => hX i (by omega))
  have hSX : InStrip f (3 * N) (N - e) X := by simpa [X] using hsX
  have hMX : (X.map f).sum = -2 * d * (F - 1) := by simpa [X, F] using hmX
  obtain ⟨hsY0, hmY0⟩ := descending_pairs f N e (2 * d - 2 * e) (2 * A + 2) 0 s
    (by omega) (by simp only [Nat.zero_add]; change v * e ≤ N; omega)
    (by simp only [Nat.zero_add]; change 0 ≤ 2 * d - 2 * e + 2 * e - 2 * v * e; nlinarith only [hbefore])
    (by norm_num; omega) (fun i _ hi => hY i (by omega))
  have hSY0 : InStrip f (3 * N) (2 * (d - e)) Y0 := by convert hsY0 using 1 <;> simp [Y0] <;> ring
  have hMY0 : (Y0.map f).sum = -2 * e * (v - 1) := by simpa [Y0, v] using hmY0
  obtain ⟨hsY1, hmY1⟩ := descending_pairs f N e (N + d - 2 * e) (2 * A + 2) s (B - s)
    (by omega) (by simpa only [Nat.add_sub_of_le (Nat.le_of_lt hs), G] using le_of_lt hGe)
    (by rw [Nat.add_sub_of_le (Nat.le_of_lt hs)]; change 0 ≤ N + d - 2 * e + 2 * e - 2 * G * e; omega)
    (by change N + d - 2 * e + 2 * N + 2 * e - 4 * v * e ≤ 3 * N; omega)
    (fun i _ hi => hY i (by omega))
  have hSY1 : InStrip f (3 * N) (N + d - 2 * v * e) Y1 := by convert hsY1 using 1 <;> dsimp [Y1, v] <;> ring
  have hMY1 : (Y1.map f).sum = -2 * e * (G - v) := by
    simpa [Y1, v, G, Nat.add_sub_of_le (Nat.le_of_lt hs)] using hmY1
  obtain ⟨hsZ0, hmZ0⟩ := descending_pairs f N z (d - z) (2 * A + 2 * B + 3) 0 (jZ - 1)
    (by omega) (by simp only [Nat.zero_add]; change u * z ≤ N; nlinarith only [hzupper, hdN, hzN])
    (by simp only [Nat.zero_add]; change 0 ≤ d - z + 2 * z - 2 * u * z; nlinarith only [hzupper])
    (by norm_num; omega) (fun i _ hi => hZ i (by omega))
  have hSZ0 : InStrip f (3 * N) (d - z) Z0 := by simpa [Z0] using hsZ0
  have hMZ0 : (Z0.map f).sum = -2 * z * (u - 1) := by simpa [Z0, u] using hmZ0
  have hjZ' : jZ - 1 ≤ D := by omega
  obtain ⟨hsZ1, hmZ1⟩ := descending_pairs f N z (N + d - 2 * z) (2 * A + 2 * B + 3)
    (jZ - 1) (D - (jZ - 1)) (by omega)
    (by simpa only [Nat.add_sub_of_le hjZ', H] using le_of_lt hHz)
    (by rw [Nat.add_sub_of_le hjZ']; change 0 ≤ N + d - 2 * z + 2 * z - 2 * H * z; omega)
    (by change N + d - 2 * z + 2 * N + 2 * z - 4 * u * z ≤ 3 * N; omega)
    (fun i _ hi => hZ i (by omega))
  have hSZ1 : InStrip f (3 * N) (N + d - 2 * u * z) Z1 := by convert hsZ1 using 1 <;> dsimp [Z1, u] <;> ring
  have hMZ1 : (Z1.map f).sum = -2 * z * (H - u) := by
    simpa [Z1, u, H, Nat.add_sub_of_le hjZ'] using hmZ1
  have hsg : InStrip f (3 * N) (d + z - 2 * u * z) [gamma] := by
    have hh := inStrip_prefix hSZ1 0
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at hh
    simp only [InStrip, show f gamma = N - z from hc]
    constructor
    · nlinarith only [hzupper]
    constructor
    · nlinarith only [hd, hdN, hzN,
        mul_nonneg (show 0 ≤ u by omega) (le_of_lt hz)]
    exact ⟨by nlinarith only [hh.1], by nlinarith only [hh.2]⟩
  have hsga := inStrip_append hsg (by simp only [List.map_singleton, List.sum_singleton]; rw [show f gamma = N - z from hc]; convert hSZ1 using 1 <;> ring)
  have hsZ := inStrip_append hSZ0 (by rw [hMZ0]; convert hsga using 1 <;> ring)
  have hsYZ := inStrip_append hSY1 (by rw [hMY1]; convert hsZ using 1 <;> nlinarith only [hYZ])
  have hsa : InStrip f (3 * N) (2 * d - 2 * v * e) [0] := by
    have hh := inStrip_prefix hSY1 0
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at hh
    simp only [InStrip, ha]
    constructor
    · nlinarith only [hbefore]
    constructor
    · nlinarith only [hd, h4d,
        mul_nonneg (show 0 ≤ v by omega) (le_of_lt he)]
    exact ⟨by nlinarith only [hh.1], by nlinarith only [hh.2]⟩
  have hsaa := inStrip_append hsa (by simp only [List.map_singleton, List.sum_singleton, ha]; convert hsYZ using 1 <;> ring)
  have hsY := inStrip_append hSY0 (by rw [hMY0]; convert hsaa using 1 <;> ring)
  have hsXY := inStrip_append hSX (by rw [hMX]; convert hsY using 1 <;> nlinarith only [hXY])
  have hstrip : InStrip f (3 * N) 0 L := by
    change InStrip f (3 * N) 0 (beta :: (X ++ Y0 ++ [0] ++ Y1 ++ Z0 ++ [gamma] ++ Z1))
    refine ⟨by omega, by omega, ?_⟩
    simpa only [zero_add, show f beta = N - e from hb, List.append_assoc] using hsXY
  have hYjoin : Y0 ++ Y1 = List.range' (2 * A + 2) (2 * B) := by
    dsimp [Y0, Y1]
    rw [List.range'_append_1]
    congr 1
    omega
  have hZjoin : Z0 ++ Z1 = List.range' (2 * A + 2 * B + 3) (2 * D) := by
    dsimp [Z0, Z1]
    rw [List.range'_append_1]
    congr 1
    omega
  have hinv : [0] ++ X ++ [beta] ++ (Y0 ++ Y1) ++ [gamma] ++ (Z0 ++ Z1) =
      List.range (2 * A + 2 * B + 2 * D + 3) := by
    rw [hYjoin, hZjoin]
    have hp : [0] ++ X ++ [beta] = List.range' 0 (2 * A + 2) := by
      have hx := (List.range'_1_concat (s := 1) (n := 2 * A)).symm
      change [0] ++ X ++ [beta] = _
      rw [List.append_assoc]
      change 0 :: (List.range' 1 (2 * A) ++ [2 * A + 1]) = _
      rw [show 2 * A + 1 = 1 + 2 * A by omega, hx]
      exact (List.range'_succ (s := 0) (n := 2 * A + 1) (step := 1)).symm
    rw [hp]
    have hy := List.range'_append_1 (s := 0) (m := 2 * A + 2) (n := 2 * B)
    simp only [Nat.zero_add] at hy
    rw [hy]
    have hg := (List.range'_1_concat (s := 0) (n := 2 * A + 2 + 2 * B)).symm
    simp only [Nat.zero_add] at hg
    rw [show gamma = 2 * A + 2 + 2 * B by dsimp [gamma]; omega, hg]
    have hzj := List.range'_append_1 (s := 0) (m := 2 * A + 2 + 2 * B + 1) (n := 2 * D)
    simp only [Nat.zero_add] at hzj
    rw [show 2 * A + 2 * B + 3 = 2 * A + 2 + 2 * B + 1 by omega, hzj, List.range_eq_range']
    congr 1
    omega
  refine ⟨L, ?_, hstrip, ?_, ?_⟩
  · rw [← hinv]
    apply List.perm_iff_count.mpr
    intro x
    simp only [L, List.count_append, List.count_cons, List.count_nil]
    omega
  · simp only [L, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, show f beta = N - e from hb,
      show f gamma = N - z from hc, ha, hMX, hMY0, hMY1, hMZ0, hMZ1]
    nlinarith only [hXY, hYZ, hZX]
  · let p := fun j => decide (j ≠ 0 ∧ j ≠ beta ∧ j ≠ gamma)
    have hkeep (R : List ℕ) (hr : ∀ x ∈ R, x ≠ 0 ∧ x ≠ beta ∧ x ≠ gamma) : R.filter p = R := by
      apply List.filter_eq_self.mpr
      intro x hx
      simpa only [p, decide_eq_true_eq] using hr x hx
    have hx : X.filter p = X := hkeep X (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; dsimp [X, beta, gamma] at *; omega)
    have hy0 : Y0.filter p = Y0 := hkeep Y0 (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; dsimp [Y0, beta, gamma] at *; omega)
    have hy1 : Y1.filter p = Y1 := hkeep Y1 (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; dsimp [Y1, beta, gamma] at *; omega)
    have hz0 : Z0.filter p = Z0 := hkeep Z0 (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; dsimp [Z0, beta, gamma] at *; omega)
    have hz1 : Z1.filter p = Z1 := hkeep Z1 (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; dsimp [Z1, beta, gamma] at *; omega)
    change L.filter p = _
    simp only [L, List.filter_append, hx, hy0, hy1, hz0, hz1]
    have hp0 : p 0 = false := by simp [p]
    have hpb : p beta = false := by simp [p]
    have hpg : p gamma = false := by simp [p]
    simp only [List.filter_cons, List.filter_nil, hp0, hpb, hpg, Bool.false_eq_true,
      ↓reduceIte, List.nil_append, List.append_nil]
    rw [show X ++ Y0 ++ Y1 ++ Z0 ++ Z1 = X ++ (Y0 ++ Y1) ++ (Z0 ++ Z1) by simp only [List.append_assoc], hYjoin, hZjoin]

private theorem positive_three_gap_profile (k : ℕ) (Q N : ℤ) (hQ : 2 ≤ Q)
    (hN : N = 4 * Q - 1) (w : ℕ → ℤ) (p r : ℕ)
    (hp : 0 < p) (hpr : p < r) (hr : r < k)
    (hbound : ∀ j, -(2 * Q - 1) ≤ w j ∧ w j ≤ 2 * Q - 1)
    (hstep : ∀ j, w (j + 1) = doubleStep N (w j))
    (hclose : w k = w 0)
    (hsmall : ∀ j < k, |w j| < Q ↔ j = 0 ∨ j = p ∨ j = r)
    (hpos : 0 < w 0 ∧ 0 < w p ∧ 0 < w r) :
    ∃ A B D : ℕ, k = 2 * A + 2 * B + 2 * D + 3 ∧
      p = 2 * A + 1 ∧ r = 2 * A + 2 * B + 2 ∧
      (let d := N - 6 * w 0
       let e := N - 6 * w p
       let z := N - 6 * w r
       2 * (4 : ℤ) ^ A * d = N + e ∧
       2 * (4 : ℤ) ^ B * e = N + z ∧
       2 * (4 : ℤ) ^ D * z = N + d ∧
       (∀ j < A, 6 * w (1 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * d ∧
         6 * w (1 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * d) ∧
       (∀ j < B, 6 * w (p + 1 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * e ∧
         6 * w (p + 1 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * e) ∧
       (∀ j < D, 6 * w (r + 1 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * z ∧
         6 * w (r + 1 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * z)) := by
  have gap (off len : ℕ) (hs : 0 < w off ∧ w off < Q)
      (hl : ∀ j, 1 ≤ j → j ≤ len → Q ≤ |w (off + j)|)
      (hend : 0 < w (off + (len + 1))) :
      len % 2 = 0 ∧
      ∀ j ≤ len, 3 * w (off + (j + 1)) =
        paritySign j * N + (2 : ℤ) ^ j * (6 * w off - N) := by
    have hh := large_gap_profile Q N hQ hN (fun j => w (off + j)) len
      (fun j _ => hbound (off + j)) (by simpa only [Nat.add_zero] using hs)
      (fun j _ => by simpa only [Nat.add_assoc] using hstep (off + j)) hl
    have he := (hh len (le_refl _)).1
    have hpar : len % 2 = 0 := by
      by_contra hn
      simp only [paritySign, ite_eq_right hn, neg_one_mul] at he
      omega
    exact ⟨hpar, fun j hj => (hh j hj).2⟩
  have hs0 : w 0 < Q := by
    have hh := (hsmall 0 (by omega)).mpr (Or.inl rfl)
    rwa [abs_of_pos hpos.1] at hh
  have hsp : w p < Q := by
    have hh := (hsmall p (by omega)).mpr (Or.inr (Or.inl rfl))
    rwa [abs_of_pos hpos.2.1] at hh
  have hsr : w r < Q := by
    have hh := (hsmall r hr).mpr (Or.inr (Or.inr rfl))
    rwa [abs_of_pos hpos.2.2] at hh
  obtain ⟨hevenX, hPX⟩ := gap 0 (p - 1) ⟨hpos.1, hs0⟩ (by
    intro j hj hje
    by_contra hh
    have hs := (hsmall j (by omega)).mp (by simpa only [Nat.zero_add] using (show |w (0 + j)| < Q by omega))
    omega) (by simpa only [Nat.zero_add, Nat.sub_add_cancel hp] using hpos.2.1)
  obtain ⟨hevenY, hPY⟩ := gap p (r - p - 1) ⟨hpos.2.1, hsp⟩ (by
    intro j hj hje
    by_contra hh
    have hs := (hsmall (p + j) (by omega)).mp (show |w (p + j)| < Q by omega)
    omega) (by convert hpos.2.2 using 1; congr 1; omega)
  obtain ⟨hevenZ, hPZ⟩ := gap r (k - r - 1) ⟨hpos.2.2, hsr⟩ (by
    intro j hj hje
    by_contra hh
    have hs := (hsmall (r + j) (by omega)).mp (show |w (r + j)| < Q by omega)
    omega) (by rw [show r + (k - r - 1 + 1) = k by omega, hclose]; exact hpos.1)
  let A := (p - 1) / 2
  let B := (r - p - 1) / 2
  let D := (k - r - 1) / 2
  have hpA : p = 2 * A + 1 := by dsimp [A]; omega
  have hrB : r = p + 2 * B + 1 := by dsimp [B]; omega
  have hkD : k = r + 2 * D + 1 := by dsimp [D]; omega
  have formulas (off a len : ℕ) (hlen : len = 2 * a)
      (hP : ∀ j ≤ len, 3 * w (off + (j + 1)) = paritySign j * N +
        (2 : ℤ) ^ j * (6 * w off - N)) :
      2 * (4 : ℤ) ^ a * (N - 6 * w off) = N + (N - 6 * w (off + (len + 1))) ∧
      ∀ j < a,
        6 * w (off + 1 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * (N - 6 * w off) ∧
        6 * w (off + 1 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * (N - 6 * w off) := by
    have pow4 (j : ℕ) : (2 : ℤ) ^ (2 * j) = (4 : ℤ) ^ j := by rw [pow_mul]; norm_num
    have hlast := hP len (le_refl _)
    rw [hlen, show paritySign (2 * a) = 1 by simp [paritySign], one_mul, pow4] at hlast
    refine ⟨by rw [hlen]; nlinarith only [hlast], ?_⟩
    intro j hj
    have hplus := hP (2 * j) (by omega)
    have hminus := hP (2 * j + 1) (by omega)
    rw [show paritySign (2 * j) = 1 by simp [paritySign], one_mul, pow4] at hplus
    rw [show paritySign (2 * j + 1) = -1 by simp [paritySign], neg_one_mul, pow_succ, pow4] at hminus
    rw [show off + (2 * j + 1) = off + 1 + 2 * j by omega] at hplus
    rw [show off + (2 * j + 1 + 1) = off + 1 + 2 * j + 1 by omega] at hminus
    constructor <;> nlinarith only [hplus, hminus]
  obtain ⟨hEX, hX⟩ := formulas 0 A (p - 1) (by omega) hPX
  obtain ⟨hEY, hY⟩ := formulas p B (r - p - 1) (by omega) hPY
  obtain ⟨hEZ, hZ⟩ := formulas r D (k - r - 1) (by omega) hPZ
  rw [show 0 + (p - 1 + 1) = p by omega] at hEX
  rw [show p + (r - p - 1 + 1) = r by omega] at hEY
  rw [show r + (k - r - 1 + 1) = k by omega, hclose] at hEZ
  refine ⟨A, B, D, by omega, hpA, by omega, ?_⟩
  simpa only [Nat.zero_add] using And.intro hEX (And.intro hEY (And.intro hEZ (And.intro hX (And.intro hY hZ))))

private theorem three_coordinates {k : ℕ} (hk : 0 < k) (P : Fin k → Prop)
    [DecidablePred P] (hthree : (Finset.univ.filter P).card = 3)
    (a : Fin k) (ha : P a) :
    ∃ p r : ℕ, 0 < p ∧ p < r ∧ r < k ∧
      ∀ j < k, P (phase hk a j) ↔ j = 0 ∨ j = p ∨ j = r := by
  classical
  letI : NeZero k := ⟨ne_of_gt hk⟩
  let S := Finset.univ.filter P
  have haS : a ∈ S := by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  have hcard : (S.erase a).card = 2 := by rw [Finset.card_erase_of_mem haS]; change (Finset.univ.filter P).card - 1 = 2; omega
  obtain ⟨b, c, hbc, hset⟩ := Finset.card_eq_two.mp hcard
  have hb : b ∈ S.erase a := by rw [hset]; simp
  have hc : c ∈ S.erase a := by rw [hset]; simp
  have hab : a ≠ b := by have := (Finset.mem_erase.mp hb).1; omega
  have hac : a ≠ c := by have := (Finset.mem_erase.mp hc).1; omega
  have hP (i : Fin k) : P i ↔ i = a ∨ i = b ∨ i = c := by
    have hs : S = insert a {b, c} := by rw [← hset, Finset.insert_erase haS]
    have hh := Finset.ext_iff.mp hs i
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] using hh
  have heq (z : Fin k) (j : ℕ) (hj : j < k) :
      phase hk a j = z ↔ j = (z - a).val := by
    rw [TwoSmallSource.phase_add]
    have hcast : (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
    rw [hcast]
    constructor
    · intro h
      have hh : (⟨j, hj⟩ : Fin k) = z - a := by rw [← h]; abel
      exact congrArg Fin.val hh
    · intro h
      have hh : (⟨j, hj⟩ : Fin k) = z - a := Fin.ext h
      rw [hh]
      abel
  let p := (b - a).val
  let r := (c - a).val
  have hp0 : 0 < p := by
    by_contra hn
    have he : b - a = 0 := Fin.ext (by dsimp [p] at hn; simpa using (show (b - a).val = 0 by omega))
    exact hab (sub_eq_zero.mp he).symm
  have hr0 : 0 < r := by
    by_contra hn
    have he : c - a = 0 := Fin.ext (by dsimp [r] at hn; simpa using (show (c - a).val = 0 by omega))
    exact hac (sub_eq_zero.mp he).symm
  have hpr : p ≠ r := by
    intro h
    have hh : b - a = c - a := Fin.ext h
    apply hbc
    calc
      b = (b - a) + a := (sub_add_cancel b a).symm
      _ = (c - a) + a := by rw [hh]
      _ = c := sub_add_cancel c a
  have hchar (j : ℕ) (hj : j < k) : P (phase hk a j) ↔ j = 0 ∨ j = p ∨ j = r := by
    rw [hP, heq a j hj, heq b j hj, heq c j hj]
    simp only [sub_self, Fin.val_zero, p, r]
  by_cases h : p < r
  · exact ⟨p, r, hp0, h, (c - a).isLt, hchar⟩
  · exact ⟨r, p, hr0, by omega, (b - a).isLt, fun j hj => by rw [hchar j hj]; tauto⟩

/-- Exactly three physical SMALL occurrences of one sign, including the
zero source and all adjacent configurations. -/
theorem actualSource_three_small_same_sign_full_completion {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (hthree : (Finset.univ.filter (fun i : Fin k =>
      |actualSource k t i| < quarter k)).card = 3)
    (hsame : (∀ i : Fin k, |actualSource k t i| < quarter k → 0 ≤ actualSource k t i) ∨
      (∀ i : Fin k, |actualSource k t i| < quarter k → actualSource k t i ≤ 0)) :
    ∃ L : List (Fin k),
      L.Perm (List.ofFn (fun q : Fin k => q)) ∧
      L.Nodup ∧ L.toFinset = Finset.univ ∧
      InStrip (actualSource k t) (half k) 0 L ∧
      (∀ n : ℕ, 0 ≤ mass (actualSource k t) (L.take n) ∧
        mass (actualSource k t) (L.take n) ≤ half k) ∧
      mass (actualSource k t) L = 0 ∧ Legal k t L ∧
      (L.filter (fun i => decide (quarter k ≤ |actualSource k t i|))).IsRotated
        ((List.finRange k).filter (fun i => decide (quarter k ≤ |actualSource k t i|))) := by
  classical
  letI : NeZero k := ⟨by omega⟩
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  by_cases hz : ∃ i, actualSource k t i = 0
  · obtain ⟨i, hi⟩ := hz
    have hall (j : Fin k) : actualSource k t j = 0 := by
      have hop : actualSource k t i = -actualSource k t i := by rw [hi]; norm_num
      have hh := AntipodalSourceCompletion.opposite_rotation hk t i i hop j
      change actualSource k t (finCycle (i - i) j) = -actualSource k t j at hh
      simp only [sub_self, finCycle_apply, add_zero] at hh
      omega
    have hm (L : List (Fin k)) : mass (actualSource k t) L = 0 := by
      unfold mass
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact hall j
    let L := List.finRange k
    have hpL : L.Perm (List.ofFn (fun q : Fin k => q)) := by
      change (List.finRange k).Perm (List.finRange k)
      exact List.Perm.refl _
    have hnL : L.Nodup := List.nodup_finRange k
    have huL : L.toFinset = Finset.univ := by ext i; simp [L]
    have hprefix (n : ℕ) : 0 ≤ mass (actualSource k t) (L.take n) ∧
        mass (actualSource k t) (L.take n) ≤ half k := by rw [hm]; omega
    have hsL : InStrip (actualSource k t) (half k) 0 L :=
      strip_of_all_prefixes L (by simpa only [zero_add] using hprefix)
    exact ⟨L, hpL, hnL, huL, hsL, hprefix, hm L, legal_of_strip hnL hsL,
      List.IsRotated.refl _⟩
  have hnonzero (i : Fin k) : actualSource k t i ≠ 0 := by intro hi; exact hz ⟨i, hi⟩
  obtain ⟨negative, hpositive⟩ : ∃ negative : Bool,
      ∀ i : Fin k, |actualSource k t i| < quarter k →
        0 < orient negative (actualSource k t i) := by
    rcases hsame with hs | hs
    · exact ⟨false, fun i hi => by have := hs i hi; have := hnonzero i; simp only [orient, Bool.false_eq_true, ite_false]; omega⟩
    · exact ⟨true, fun i hi => by have := hs i hi; have := hnonzero i; simp only [orient, ite_true]; omega⟩
  let S := Finset.univ.filter (fun i : Fin k => |actualSource k t i| < quarter k)
  have hS : S.Nonempty := Finset.card_pos.mp (by change 0 < (Finset.univ.filter _).card; omega)
  obtain ⟨o, hoS, hmin⟩ := Finset.exists_min_image S
    (fun i => orient negative (actualSource k t i)) hS
  have ho : |actualSource k t o| < quarter k := (Finset.mem_filter.mp hoS).2
  obtain ⟨p, r, hp, hpr, hr, hchar⟩ := three_coordinates (by omega)
    (fun i : Fin k => |actualSource k t i| < quarter k) hthree o ho
  let w := fun j => orient negative (actualSource k t (phase (by omega : 0 < k) o j))
  have hsmall (j : ℕ) (hj : j < k) : |w j| < quarter k ↔ j = 0 ∨ j = p ∨ j = r := by
    simpa only [w, orient_abs] using hchar j hj
  have hpos : 0 < w 0 ∧ 0 < w p ∧ 0 < w r := by
    refine ⟨?_, ?_, ?_⟩
    all_goals apply hpositive; apply (hchar _ (by omega)).mpr; omega
  have hbound (j : ℕ) : -(2 * quarter k - 1) ≤ w j ∧ w j ≤ 2 * quarter k - 1 := by
    have hh := centered_bounds hN0 hodd ((2 : ℤ) ^ (phase (by omega) o j).val * t)
    change -(half k) ≤ actualSource k t (phase (by omega) o j) ∧
      actualSource k t (phase (by omega) o j) ≤ half k at hh
    dsimp [w]
    rw [hC] at hh
    cases negative <;> simp only [orient, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hstep (j : ℕ) : w (j + 1) = doubleStep (modulus k) (w j) := by
    have hh := phase_step hk t o j
    dsimp [w]
    rw [hh]
    cases negative <;> simp only [orient, Bool.false_eq_true, ite_false, ite_true]
    exact (doubleStep_neg (le_of_lt hN0)).symm
  have hclose : w k = w 0 := by
    have hh : phase (by omega : 0 < k) o k = phase (by omega) o 0 := by
      apply Fin.ext
      simp only [phase, Nat.add_mod_right, Nat.zero_mod, Nat.add_zero]
    dsimp [w]
    rw [hh]
  obtain ⟨A, B, D, hkABD, hpA, hrB, hXY, hYZ, hZX, hX, hY, hZ⟩ :=
    positive_three_gap_profile k (quarter k) (modulus k) hQ hN w p r hp hpr hr
      hbound hstep hclose hsmall hpos
  let N := modulus k
  let F : ℤ := (4 : ℤ) ^ A
  let G : ℤ := (4 : ℤ) ^ B
  let H : ℤ := (4 : ℤ) ^ D
  let d := N - 6 * w 0
  let e := N - 6 * w p
  let z := N - 6 * w r
  change 2 * F * d = N + e at hXY
  change 2 * G * e = N + z at hYZ
  change 2 * H * z = N + d at hZX
  have hNFGH : N = 8 * F * G * H - 1 := by
    dsimp [N, modulus]
    rw [hkABD, show 2 * A + 2 * B + 2 * D + 3 = 2 * A + (2 * B + (2 * D + 3)) by omega,
      pow_add, pow_add, pow_add]
    have hp4 (j : ℕ) : (2 : ℤ) ^ (2 * j) = (4 : ℤ) ^ j := by rw [pow_mul]; norm_num
    rw [hp4, hp4, hp4]
    dsimp [F, G, H]
    norm_num
    ring
  have hdval : d = 4 * G * H + 2 * H + 1 := by
    apply mul_left_cancel₀ (show N ≠ 0 from ne_of_gt hN0)
    calc
      N * d = (8 * F * G * H - 1) * d := by rw [hNFGH]
      _ = N * (4 * G * H + 2 * H + 1) := by
        linear_combination (4 * G * H) * hXY + (2 * H) * hYZ + hZX
  have heval : e = 4 * H * F + 2 * F + 1 := by
    apply mul_left_cancel₀ (show N ≠ 0 from ne_of_gt hN0)
    calc
      N * e = (8 * F * G * H - 1) * e := by rw [hNFGH]
      _ = N * (4 * H * F + 2 * F + 1) := by
        linear_combination (4 * H * F) * hYZ + (2 * F) * hZX + hXY
  have hzval : z = 4 * F * G + 2 * G + 1 := by
    apply mul_left_cancel₀ (show N ≠ 0 from ne_of_gt hN0)
    calc
      N * z = (8 * F * G * H - 1) * z := by rw [hNFGH]
      _ = N * (4 * F * G + 2 * G + 1) := by
        linear_combination (4 * F * G) * hZX + (2 * G) * hXY + hYZ
  have hF : 1 ≤ F := one_le_pow₀ (by norm_num)
  have hG : 1 ≤ G := one_le_pow₀ (by norm_num)
  have hH : 1 ≤ H := one_le_pow₀ (by norm_num)
  have hd : 0 < d := by nlinarith only [hdval, hG, hH, mul_nonneg (show 0 ≤ G by omega) (show 0 ≤ H by omega)]
  have he : 0 < e := by nlinarith only [heval, hH, hF, mul_nonneg (show 0 ≤ H by omega) (show 0 ≤ F by omega)]
  have hzz : 0 < z := by nlinarith only [hzval, hF, hG, mul_nonneg (show 0 ≤ F by omega) (show 0 ≤ G by omega)]
  have hdN : d < N := by dsimp [d]; omega
  have heN : e < N := by dsimp [e]; omega
  have hzN : z < N := by dsimp [z]; omega
  have hde : e ≤ d := by
    have hm := hmin (phase (by omega : 0 < k) o p)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hchar p (by omega)).mpr (by omega)⟩)
    have hm' : w 0 ≤ w p := by simpa only [w, phase_zero] using hm
    dsimp [e, d]
    omega
  have hdz : z ≤ d := by
    have hm := hmin (phase (by omega : 0 < k) o r)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hchar r hr).mpr (by omega)⟩)
    have hm' : w 0 ≤ w r := by simpa only [w, phase_zero] using hm
    dsimp [z, d]
    omega
  have hD : 0 < D := by
    by_contra hn
    have hD0 : D = 0 := by omega
    simp only [H, hD0, pow_zero, mul_one, one_mul] at hZX
    omega
  have hBzero : B = 0 → A = 0 := by
    intro hB0
    have hEY : 2 * e = N + z := by simpa only [G, hB0, pow_zero, mul_one, one_mul] using hYZ
    by_contra hn
    have hF4 : 4 ≤ F := by
      simpa only [F, pow_one] using
        pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) (show 1 ≤ A by omega)
    nlinarith only [hXY, hEY, hF4, hd, hde, heN, hzz]
  let f := fun j => 6 * w j
  let q := fun j => decide (j ≠ 0 ∧ j ≠ p ∧ j ≠ r)
  have hf0 : f 0 = N - d := by dsimp [f, d]; ring
  have hfp : f p = N - e := by dsimp [f, e]; ring
  have hfr : f r = N - z := by dsimp [f, z]; ring
  have hnormalized : ∃ word : List ℕ, word.Perm (List.range k) ∧
      InStrip f (3 * N) 0 word ∧ (word.map f).sum = 0 ∧
      word.filter q = List.range' 1 (2 * A) ++ List.range' (2 * A + 2) (2 * B) ++
        List.range' (2 * A + 2 * B + 3) (2 * D) := by
    by_cases hA0 : A = 0
    · by_cases hB0 : B = 0
      · have hn : N = 8 * H - 1 := by simpa [F, G, hA0, hB0] using hNFGH
        have hd' : d = 6 * H + 1 := by
          have hh := hdval
          simp only [G, hB0, pow_zero, mul_one, one_mul] at hh
          nlinarith only [hh]
        have he' : e = 4 * H + 3 := by
          have hh := heval
          simp only [F, hA0, pow_zero, mul_one, one_mul] at hh
          nlinarith only [hh]
        have hz' : z = 7 := by simpa [F, G, hA0, hB0] using hzval
        have hp1 : p = 1 := by omega
        have hr2 : r = 2 := by omega
        obtain ⟨word, hperm, hstrip, hsum, hdel⟩ := one_block D hD f
          (by change f 0 = 2 * (H - 1); rw [hf0, hd', hn]; ring)
          (by change f 1 = 4 * (H - 1); rw [← hp1, hfp, he', hn]; ring)
          (by change f 2 = 8 * (H - 1); rw [← hr2, hfr, hz', hn]; ring)
          (by
            intro j hj
            have hh := hZ j hj
            change f (r + 1 + 2 * j) = 2 * N - 2 * (4 : ℤ) ^ j * z ∧
              f (r + 1 + 2 * j + 1) = -2 * N - 4 * (4 : ℤ) ^ j * z at hh
            rw [hr2, hz'] at hh
            have hh' : f (3 + 2 * j) = 2 * N - 14 * (4 : ℤ) ^ j ∧
                f (3 + 2 * j + 1) = -2 * N - 28 * (4 : ℤ) ^ j := by
              constructor <;> nlinarith only [hh.1, hh.2]
            simpa only [hn, H] using hh')
        change InStrip f (3 * (8 * H - 1)) 0 word at hstrip
        rw [← hn] at hstrip
        refine ⟨word, by simpa only [hkABD, hA0, hB0, Nat.mul_zero, Nat.zero_add] using hperm,
          hstrip, hsum, ?_⟩
        have hq : q = (fun j => decide (3 ≤ j)) := by
          funext j
          apply decide_eq_decide.mpr
          omega
        simpa only [hq, hA0, hB0, Nat.mul_zero, Nat.zero_add, List.range'_zero,
          List.nil_append] using hdel
      · have hp1 : p = 1 := by omega
        have hr' : r = 2 * B + 2 := by omega
        obtain ⟨word, hperm, hstrip, hsum, hdel⟩ := two_blocks B D (by omega) hD N d e z
          hd he hzz hdN hzN (by simpa [F, hA0] using hXY) hYZ hZX f hf0
          (by simpa only [hp1] using hfp)
          (by simpa only [hr'] using hfr)
          (by intro j hj; simpa [f, N, e, hpA, hA0, Nat.add_assoc] using hY j hj)
          (by intro j hj; simpa [f, N, z, hrB, hA0, Nat.add_assoc] using hZ j hj)
        refine ⟨word, by simpa only [hkABD, hA0, Nat.mul_zero, Nat.zero_add] using hperm,
          hstrip, hsum, ?_⟩
        simpa only [q, hpA, hrB, hA0, Nat.mul_zero, Nat.zero_add, List.range'_zero,
          List.nil_append] using hdel
    · have hB : 0 < B := by by_contra hn; exact hA0 (hBzero (by omega))
      obtain ⟨word, hperm, hstrip, hsum, hdel⟩ := three_blocks A B D (by omega) hB hD N d e z
        hd he hzz hdN heN hzN hde hdz hXY hYZ hZX hdval heval hzval f hf0
        (by simpa only [hpA] using hfp)
        (by simpa only [hrB] using hfr)
        (by intro j hj; simpa only [f, N, d] using hX j hj)
        (by intro j hj; simpa [f, N, e, hpA, Nat.add_assoc] using hY j hj)
        (by intro j hj; simpa [f, N, z, hrB, Nat.add_assoc] using hZ j hj)
      exact ⟨word, by simpa only [← hkABD] using hperm, hstrip, hsum,
        by simpa only [q, hpA, hrB] using hdel⟩
  obtain ⟨word, hpword, hsword, hmword, hdeleted⟩ := hnormalized
  have hwstrip : InStrip w (half k) 0 word :=
    unscale_six w N (half k) (by dsimp [N]; omega) word hsword
  have hwsum : (word.map w).sum = 0 := by
    have hh : 6 * (word.map w).sum = 0 := by simpa only [f, List.sum_map_mul_left] using hmword
    omega
  have hlarge (j : ℕ) (hj : j < k) : quarter k ≤ |w j| ↔ j ≠ 0 ∧ j ≠ p ∧ j ≠ r := by
    have hh := hsmall j hj
    omega
  have hforwardQ : (List.range k).filter q = word.filter q := by
    rw [hdeleted]
    have hsplit : [0] ++ List.range' 1 (2 * A) ++ [p] ++
        List.range' (2 * A + 2) (2 * B) ++ [r] ++
        List.range' (2 * A + 2 * B + 3) (2 * D) = List.range k := by
      have hp : [0] ++ List.range' 1 (2 * A) ++ [p] =
          List.range' 0 (2 * A + 2) := by
        rw [hpA, List.append_assoc]
        change 0 :: (List.range' 1 (2 * A) ++ [2 * A + 1]) = _
        rw [show 2 * A + 1 = 1 + 2 * A by omega,
          (List.range'_1_concat (s := 1) (n := 2 * A)).symm]
        exact (List.range'_succ (s := 0) (n := 2 * A + 1) (step := 1)).symm
      rw [hp]
      have hy := List.range'_append_1 (s := 0) (m := 2 * A + 2) (n := 2 * B)
      simp only [Nat.zero_add] at hy
      rw [hy, hrB]
      have hg := (List.range'_1_concat (s := 0) (n := 2 * A + 2 + 2 * B)).symm
      simp only [Nat.zero_add] at hg
      rw [show 2 * A + 2 * B + 2 = 2 * A + 2 + 2 * B by omega, hg]
      have hzj := List.range'_append_1 (s := 0) (m := 2 * A + 2 + 2 * B + 1) (n := 2 * D)
      simp only [Nat.zero_add] at hzj
      rw [show 2 * A + 2 * B + 3 = 2 * A + 2 + 2 * B + 1 by omega,
        hzj, List.range_eq_range']
      congr 1
      omega
    have hkeep (off len : ℕ) (hl : ∀ x ∈ List.range' off len, x ≠ 0 ∧ x ≠ p ∧ x ≠ r) :
        (List.range' off len).filter q = List.range' off len := by
      apply List.filter_eq_self.mpr
      intro x hx
      simpa only [q, decide_eq_true_eq] using hl x hx
    rw [← hsplit]
    simp only [List.filter_append]
    rw [hkeep 1 (2 * A) (by intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; omega),
      hkeep (2 * A + 2) (2 * B) (by intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; omega),
      hkeep (2 * A + 2 * B + 3) (2 * D) (by intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; omega)]
    simp [q]
  let phi := phase (by omega : 0 < k) o
  let L := word.map phi
  let e : Equiv.Perm (Fin k) := Equiv.addLeft o
  have hbase : (List.range k).map phi = List.ofFn e := by
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro i _
    change phase (by omega) o i.val = o + i
    apply Fin.ext
    rfl
  have hphase : (List.range k).map phi = (List.finRange k).rotate o.val := by
    rw [hbase]
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, List.getElem_rotate, List.getElem_finRange,
        List.length_ofFn, List.length_rotate, List.length_finRange]
      apply Fin.ext
      simp [e, phi, phase, Fin.val_add, Nat.add_mod, Nat.add_comm]
  let p : Fin k → Bool := fun i => decide (quarter k ≤ |actualSource k t i|)
  have hpred (j : ℕ) (hj : j ∈ word) : p (phi j) = q j := by
    have hjk : j < k := by
      have hh := hpword.mem_iff.mp hj
      simp only [List.mem_range] at hh
      omega
    have hh := hlarge j hjk
    apply decide_eq_decide.mpr
    simpa only [p, q, phi, w, orient_abs] using hh
  have hwordfilter : L.filter p = (word.filter q).map phi := by
    dsimp only [L]
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro j hj
    simpa only [Function.comp_def] using hpred j hj
  have hfullfilter : ((List.range k).map phi).filter p =
      ((List.range k).filter q).map phi := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro j hj
    have hjk := List.mem_range.mp hj
    have hh := hlarge j hjk
    apply decide_eq_decide.mpr
    simpa only [Function.comp_def, p, q, phi, w, orient_abs] using hh
  have hphaseorder : L.filter p ~r (List.finRange k).filter p := by
    rw [hwordfilter, ← hforwardQ, ← hfullfilter, hphase]
    exact TwoSmallSource.filter_rotate p (List.finRange k) o.val

  have hpL : L.Perm (List.ofFn (fun q : Fin k => q)) := by
    have hh := hpword.map phi
    rw [hbase] at hh
    exact hh.trans (by simpa only [Function.comp_def, id_eq] using e.ofFn_comp_perm (fun q => q))
  have hpref (n : ℕ) :
      0 ≤ mass (fun q => orient negative (actualSource k t q)) (L.take n) ∧
      mass (fun q => orient negative (actualSource k t q)) (L.take n) ≤ half k := by
    have hh := inStrip_prefix hwstrip n
    simpa only [L, phi, w, mass, ← List.map_take, List.map_map, Function.comp_def,
      zero_add] using hh
  have hstrip : InStrip (fun q => orient negative (actualSource k t q)) (half k) 0 L :=
    strip_of_all_prefixes L (by simpa only [zero_add] using hpref)
  have hsum : (L.map (fun q => orient negative (actualSource k t q))).sum = 0 := by
    simpa only [L, phi, w, List.map_map, Function.comp_def] using hwsum
  have hcompletion : ∃ R : List (Fin k), R.Perm (List.ofFn (fun q : Fin k => q)) ∧
      InStrip (actualSource k t) (half k) 0 R ∧ mass (actualSource k t) R = 0 ∧
      L.IsRotated R := by
    cases negative with
    | false => exact ⟨L, hpL, by simpa only [orient, Bool.false_eq_true, ite_false] using hstrip,
        by simpa only [orient, Bool.false_eq_true, ite_false, mass] using hsum,
        List.IsRotated.refl L⟩
    | true =>
      obtain ⟨j, hj, hrot⟩ := TwoSmallSource.negate_rotation
        (fun q => orient true (actualSource k t q)) (half k) L hstrip hsum
      have hpR := (List.rotate_perm L j).trans hpL
      have hprefixR (n : ℕ) : 0 ≤ mass (actualSource k t) ((L.rotate j).take n) ∧
          mass (actualSource k t) ((L.rotate j).take n) ≤ half k := by
        simpa only [orient, ite_true, neg_neg, mass] using hrot n
      have hmL : mass (actualSource k t) L = 0 := by
        simp only [orient, ite_true, sum_neg_map] at hsum
        dsimp [mass]; omega
      have hmR : mass (actualSource k t) (L.rotate j) = 0 := by
        dsimp [mass]
        rw [((List.rotate_perm L j).map (actualSource k t)).sum_eq]
        exact hmL
      exact ⟨L.rotate j, hpR, strip_of_all_prefixes _ (by simpa using hprefixR), hmR,
        (List.IsRotated.forall L j).symm⟩
  obtain ⟨R, hpR, hsR, hmR, hLR⟩ := hcompletion
  have hnR : R.Nodup := hpR.nodup_iff.mpr
    (List.nodup_ofFn_ofInjective (f := fun q : Fin k => q) (fun _ _ h => h))
  have huR : R.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro q
    exact List.mem_toFinset.mpr (hpR.mem_iff.mpr (List.mem_ofFn.mpr ⟨q, rfl⟩))
  have hlegal : Legal k t R := legal_of_strip hnR hsR
  have hRfilter : R.filter p ~r (List.finRange k).filter p := by
    rcases hLR with ⟨j, hj⟩
    rw [← hj]
    exact (TwoSmallSource.filter_rotate p L j).trans hphaseorder
  exact ⟨R, hpR, hnR, huR, hsR, hlegal.2, hmR, hlegal, by simpa only [p] using hRfilter⟩


end D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource
