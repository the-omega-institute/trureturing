/- GID: D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeSmallGapPlacement
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Three-small gap blocks admit exact prefix-safe placements in the sixfold integer normalization. -/
import D5.S3.Combinatorics.Circle.TwoSmallSource

/-! # Exact placement of three same-sign SMALL gap blocks -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.ThreeSmallGapPlacement
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


theorem one_block (D : ℕ) (hD : 0 < D) (f : ℕ → ℤ)
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
theorem two_blocks (B D : ℕ) (hB : 0 < B) (hD : 0 < D)
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
theorem three_blocks (A B D : ℕ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
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


end D5.S3.Combinatorics.Circle.ThreeSmallGapPlacement
