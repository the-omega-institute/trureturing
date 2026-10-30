/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeCommonCut
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeCommonCut
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Combinatorics.Colex]
   utility: none
   digest: One physical W mask constructs both native three-negative orders at the same zero cut. -/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.DyadicPrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
open SourceWidth PeriodicShortening
open scoped BigOperators

private theorem pow_lower (n : ℕ) (hn : 2 ≤ n) : (4 : ℤ) ≤ 2 ^ n := by
  have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hn
  norm_num at this
  exact this

private theorem pow_half (n : ℕ) (hn : 0 < n) :
    (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  ring

/-- A congruent ladder has precisely one final negative occurrence. -/
private theorem ladder_value (C p cap : ℤ) (len i : ℕ)
    (hC : 0 ≤ C) (hp : 0 < p) (hcap : 0 ≤ cap ∧ cap ≤ C)
    (hend : (2 : ℤ) ^ len * p = C + 1 + cap) (hi : i ≤ len) :
    centered (2 * C + 1) (2 ^ i * p) =
      if i < len then 2 ^ i * p else -C + cap := by
  have hN : 0 < 2 * C + 1 := by omega
  have ho : (2 * C + 1) % 2 = 1 := by omega
  have hh : (2 * C + 1) / 2 = C := by omega
  by_cases hil : i < len
  · rw [if_pos hil]
    have hhpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show i + 1 ≤ len by omega)
    rw [pow_succ] at hhpow
    have hx := mul_le_mul_of_nonneg_right hhpow (le_of_lt hp)
    apply centered_unique hN ho (centered_bounds hN ho _) ?_ (centered_mod _ _)
    rw [hh]
    have hx0 : 0 ≤ (2 : ℤ) ^ i * p := by positivity
    constructor <;> nlinarith
  · have hei : i = len := by omega
    rw [if_neg hil, hei, hend]
    apply centered_unique hN ho (centered_bounds hN ho _) ?_ ?_
    · rw [hh]; constructor <;> omega
    · rw [centered_mod]
      have he : C + 1 + cap = (-C + cap) + (2 * C + 1) := by ring
      rw [he, Int.add_emod_right]

private theorem positive_strip {α : Type*} (f : α → ℤ) (l : List α) (C h : ℤ)
    (hpos : ∀ x ∈ l, 0 ≤ f x) (hh : 0 ≤ h) (hend : h + (l.map f).sum ≤ C) :
    InStrip f C h l := by
  apply inStrip_reflect
  apply inStrip_nonpos
  · intro x hx; exact neg_nonpos.mpr (hpos x hx)
  · omega
  · rw [sum_neg_map]; omega

/-- The native floor estimate includes the W-charge left behind at the seam. -/
private theorem mask_bound (t u m : ℤ) (hu : 4 ≤ u) (hm : m = 4 ∨ 8 ≤ m)
    (htu : t = m * u) :
    let H := t * u + t + 1
    let f := (t + 1) * (t - u) / H
    let h := (t + 1) * (t - u) - H * f
    0 ≤ f ∧ f ≤ m - 2 ∧ f < t / 2 ∧ 0 ≤ h ∧
      2 * h + 1 + (t + 1) * f ≤ t * (t + 1) / 2 := by
  dsimp only
  let H := t * u + t + 1
  let f := (t + 1) * (t - u) / H
  let h := (t + 1) * (t - u) - H * f
  change 0 ≤ f ∧ f ≤ m - 2 ∧ f < t / 2 ∧ 0 ≤ h ∧
    2 * h + 1 + (t + 1) * f ≤ t * (t + 1) / 2
  have hm4 : 4 ≤ m := by rcases hm with rfl | hm <;> omega
  have ht : 4 * u ≤ t := by nlinarith
  have ht0 : 0 ≤ t := by omega
  have hH : 0 < H := by dsimp [H]; positivity
  have hf0 : 0 ≤ f := Int.ediv_nonneg (mul_nonneg (by omega) (by omega)) (le_of_lt hH)
  have hr0 := Int.emod_nonneg ((t + 1) * (t - u)) (ne_of_gt hH)
  have hr1 := Int.emod_lt_of_pos ((t + 1) * (t - u)) hH
  have hre := Int.emod_add_mul_ediv ((t + 1) * (t - u)) H
  have hh0 : 0 ≤ h := by dsimp [h, f]; omega
  have hh1 : h ≤ H - 1 := by dsimp [h, f]; omega
  have hprod : (t + 1) * (t - u) < H * (m - 1) := by
    have hx : (t + 1) * (t - u) = (t + 1) * u * (m - 1) := by rw [htu]; ring
    rw [hx]
    have hgap : u * (t + 1) < H := by dsimp [H]; nlinarith
    nlinarith [mul_pos (by omega : 0 < m - 1) (by omega : 0 < H - u * (t + 1))]
  have hfm : f ≤ m - 2 := by
    have hmul : H * f ≤ (t + 1) * (t - u) := by dsimp [h] at hh0; omega
    by_contra hf
    have := mul_le_mul_of_nonneg_left (show m - 1 ≤ f by omega) (le_of_lt hH)
    omega
  have hfit : f < t / 2 := by
    have ht2 := Int.emod_add_mul_ediv t 2
    have htmod := Int.emod_lt_of_pos t (by norm_num : (0 : ℤ) < 2)
    nlinarith
  refine ⟨hf0, hfm, hfit, hh0, ?_⟩
  have hg := Int.emod_add_mul_ediv (t * (t + 1)) 2
  have hg0 := Int.emod_nonneg (t * (t + 1)) (by norm_num : (2 : ℤ) ≠ 0)
  have hg1 := Int.emod_lt_of_pos (t * (t + 1)) (by norm_num : (0 : ℤ) < 2)
  rcases hm with hm | hm
  · have ht4 : t = 4 * u := by rw [htu, hm]
    have htwo : 2 * H ≤ (t + 1) * (t - u) := by dsimp [H]; rw [ht4]; nlinarith
    have hf2 : 2 ≤ f := (Int.le_ediv_iff_mul_le hH).mpr (by nlinarith)
    have hfe : f = 2 := by omega
    dsimp [h, H]
    rw [hfe, ht4]
    rw [ht4] at hg hg0 hg1
    nlinarith
  · have ht8 : 8 * u ≤ t := by nlinarith
    have hq : 2 * h + 1 + (t + 1) * f ≤ 2 * t * u + (t + 1) * m - 1 := by
      have hf := mul_le_mul_of_nonneg_left hfm (show 0 ≤ t + 1 by omega)
      dsimp [H] at hh1
      nlinarith
    have hmterm : 4 * ((t + 1) * m) ≤ t * (t + 1) := by
      have hu4 := mul_nonneg (show 0 ≤ u - 4 by omega) (show 0 ≤ m * (t + 1) by positivity)
      nlinarith [show m * u = t by omega]
    have htuterm : 8 * t * u ≤ t * (t + 1) := by
      nlinarith [mul_nonneg ht0 (show 0 ≤ t + 1 - 8 * u by omega)]
    omega


private abbrev K (a c : ℕ) := 2 * a + c
private abbrev seed (a : ℕ) := 1 + 2 ^ a + 2 ^ (2 * a)
private abbrev T (a : ℕ) : ℤ := 2 ^ a
private abbrev U (c : ℕ) : ℤ := 2 ^ c
private abbrev sh (a : ℕ) : ℤ := 2 ^ (a - 1)
private abbrev rh (c : ℕ) : ℤ := 2 ^ (c - 1)
private abbrev A (a : ℕ) : ℤ := T a * T a + T a + 1
private abbrev B (a c : ℕ) : ℤ := (T a + 1) * U c + 1
private abbrev H (a c : ℕ) : ℤ := T a * U c + T a + 1
private abbrev C (a c : ℕ) : ℤ := sh a * T a * U c - 1
private abbrev raw (k v i : ℕ) : ℤ := centered (modulus k) (2 ^ i * v)
private abbrev S (a c i : ℕ) : ℤ := raw (K a c) (seed a) i
private abbrev X (a c i : ℕ) : ℤ := raw (K a c + 1) (2 * seed a) i

/-- Both entries in every row refer to the identical old physical label. -/
private structure Rows (a c : ℕ) : Prop where
  oldMod : modulus (K a c) = 2 * C a c + 1
  newMod : modulus (K a c + 1) = 2 * (2 * C a c + 1) + 1
  cap0 : 0 ≤ C a c
  caps :
    (0 ≤ (T a + 1) * rh c ∧ (T a + 1) * rh c ≤ C a c) ∧
    (0 ≤ sh a * (U c + 1) ∧ sh a * (U c + 1) ≤ C a c) ∧
    (0 ≤ sh a * (T a + 1) ∧ sh a * (T a + 1) ≤ C a c)
  oldU : ∀ i < c - 1, S a c i = 2 ^ i * A a
  newU : ∀ i < c - 1, X a c i = 2 ^ i * (2 * A a)
  oldV : ∀ i < a - 1, S a c (c + i) = 2 ^ i * B a c
  newV : ∀ i < a - 1, X a c (c + i) = 2 ^ i * (2 * B a c - 1)
  oldW : ∀ i < a - 1, S a c (a + c + i) = 2 ^ i * H a c
  newW : ∀ i < a - 1, X a c (a + c + i) = 2 ^ i * (2 * H a c - T a - 1)
  oldAlpha : S a c (c - 1) = -C a c + (T a + 1) * rh c
  newAlpha : X a c (c - 1) = -(2 * C a c + 1) + (T a + 1) * U c
  oldBeta : S a c (a + c - 1) = -C a c + sh a * (U c + 1)
  newBeta : X a c (a + c - 1) = -(2 * C a c + 1) + T a * U c + sh a
  oldGamma : S a c (K a c - 1) = -C a c + sh a * (T a + 1)
  newGamma : X a c (K a c - 1) = -(2 * C a c + 1) + sh a * (T a + 1)
  ear : X a c (K a c) = A a

private theorem source_rows (a c : ℕ) (hc : 2 ≤ c) (hca : c < a) : Rows a c := by
  have ha : 2 ≤ a := by omega
  have ht : 4 ≤ T a := pow_lower a ha
  have hu : 4 ≤ U c := pow_lower c hc
  have hs : 2 ≤ sh a := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ a - 1 by omega)
    norm_num at this; exact this
  have hr : 2 ≤ rh c := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ c - 1 by omega)
    norm_num at this; exact this
  have hts : T a = 2 * sh a := pow_half a (by omega)
  have hur : U c = 2 * rh c := pow_half c (by omega)
  have hseed : (seed a : ℤ) = A a := by
    simp only [seed, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat,
      show 2 * a = a + a by omega, pow_add]
    ring
  have hN : modulus (K a c) = 2 * C a c + 1 := by
    simp only [modulus, K, C, T, U, sh, show 2 * a + c = a + a + c by omega,
      pow_add]
    have ht := pow_half a (by omega)
    nlinarith only [congrArg (fun z : ℤ => z * (2 ^ a * 2 ^ c)) ht]
  have hM : modulus (K a c + 1) = 2 * (2 * C a c + 1) + 1 := by
    simp only [modulus, pow_succ]
    have := hN
    unfold modulus at this
    omega
  have hc0 : 0 ≤ C a c := by dsimp [C]; nlinarith [mul_nonneg (show 0 ≤ sh a * T a - 1 by nlinarith) (show 0 ≤ U c - 1 by omega)]
  have hca0 : 0 ≤ (T a + 1) * rh c := by positivity
  have hcb0 : 0 ≤ sh a * (U c + 1) := by positivity
  have hcg0 : 0 ≤ sh a * (T a + 1) := by positivity
  have hcaC : (T a + 1) * rh c ≤ C a c := by
    dsimp [C]
    have hh : 1 ≤ T a * T a - T a - 1 := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ rh c - 1 by omega) (show 0 ≤ T a * T a - T a - 1 by omega)]
  have hcbC : sh a * (U c + 1) ≤ C a c := by
    dsimp [C]
    have hh : 1 ≤ T a * U c - U c - 1 := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ sh a - 1 by omega) (show 0 ≤ T a * U c - U c - 1 by omega)]
  have hcgC : sh a * (T a + 1) ≤ C a c := by
    dsimp [C]
    have hh : 1 ≤ T a * U c - T a - 1 := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ sh a - 1 by omega) (show 0 ≤ T a * U c - T a - 1 by omega)]
  have hnewa : 0 ≤ (T a + 1) * U c ∧ (T a + 1) * U c ≤ 2 * C a c + 1 := by
    constructor
    · positivity
    · nlinarith only [hcaC, hur]
  have hnewb : 0 ≤ T a * U c + sh a ∧ T a * U c + sh a ≤ 2 * C a c + 1 := by
    constructor
    · positivity
    · nlinarith only [hcbC, hts, hs]
  have hnewg : 0 ≤ sh a * (T a + 1) ∧ sh a * (T a + 1) ≤ 2 * C a c + 1 := by omega
  have hlastU : (2 : ℤ) ^ (c - 1) * A a = C a c + 1 + (T a + 1) * rh c := by
    change rh c * A a = _
    dsimp [A, C]
    nlinarith only [congrArg (fun z : ℤ => sh a * T a * z) hur, hts]
  have hlastV : (2 : ℤ) ^ (a - 1) * B a c = C a c + 1 + sh a * (U c + 1) := by
    dsimp [B, C]; ring
  have hlastW : (2 : ℤ) ^ (a - 1) * H a c = C a c + 1 + sh a * (T a + 1) := by
    dsimp [H, C]; ring
  have hlastUn : (2 : ℤ) ^ (c - 1) * (2 * A a) =
      (2 * C a c + 1) + 1 + (T a + 1) * U c := by nlinarith only [hlastU, hur]
  have hlastVn : (2 : ℤ) ^ (a - 1) * (2 * B a c - 1) =
      (2 * C a c + 1) + 1 + (T a * U c + sh a) := by
    change sh a * (2 * B a c - 1) = _
    dsimp [B, C]
    nlinarith only [hts]
  have hlastWn : (2 : ℤ) ^ (a - 1) * (2 * H a c - T a - 1) =
      (2 * C a c + 1) + 1 + sh a * (T a + 1) := by
    dsimp [H, C]; ring
  have oldU (i : ℕ) (hi : i ≤ c - 1) :=
    ladder_value (C a c) (A a) ((T a + 1) * rh c) (c - 1) i hc0
      (by dsimp [A]; positivity) ⟨hca0, hcaC⟩ hlastU hi
  have newU (i : ℕ) (hi : i ≤ c - 1) :=
    ladder_value (2 * C a c + 1) (2 * A a) ((T a + 1) * U c) (c - 1) i
      (by omega) (by dsimp [A]; positivity) hnewa hlastUn hi
  have oldV (i : ℕ) (hi : i ≤ a - 1) :=
    ladder_value (C a c) (B a c) (sh a * (U c + 1)) (a - 1) i hc0
      (by dsimp [B]; positivity) ⟨hcb0, hcbC⟩ hlastV hi
  have newV (i : ℕ) (hi : i ≤ a - 1) :=
    ladder_value (2 * C a c + 1) (2 * B a c - 1) (T a * U c + sh a) (a - 1) i
      (by omega) (by dsimp [B]; positivity) hnewb hlastVn hi
  have oldW (i : ℕ) (hi : i ≤ a - 1) :=
    ladder_value (C a c) (H a c) (sh a * (T a + 1)) (a - 1) i hc0
      (by dsimp [H]; positivity) ⟨hcg0, hcgC⟩ hlastW hi
  have newW (i : ℕ) (hi : i ≤ a - 1) :=
    ladder_value (2 * C a c + 1) (2 * H a c - T a - 1) (sh a * (T a + 1)) (a - 1) i
      (by omega) (by dsimp [H]; positivity) hnewg hlastWn hi
  have hSu (i : ℕ) : S a c i = centered (2 * C a c + 1) (2 ^ i * A a) := by rw [S, raw, hN, hseed]
  have hXu (i : ℕ) : X a c i = centered (2 * (2 * C a c + 1) + 1) (2 ^ i * (2 * A a)) := by
    simp only [X, raw, hM, Nat.cast_mul, Nat.cast_ofNat, hseed]
  have hSv (i : ℕ) : S a c (c + i) = centered (2 * C a c + 1) (2 ^ i * B a c) := by
    rw [S, raw, hseed, pow_add, hN]
    apply centered_congr
    have he : (2 : ℤ) ^ c * 2 ^ i * A a = 2 ^ i * B a c + (2 * C a c + 1) * 2 ^ i := by
      change U c * 2 ^ i * A a = _
      dsimp [A, B, C]
      nlinarith only [congrArg (fun z : ℤ => z * (T a * U c * 2 ^ i)) hts]
    rw [he, Int.add_mul_emod_self_left]
  have hXv (i : ℕ) : X a c (c + i) =
      centered (2 * (2 * C a c + 1) + 1) (2 ^ i * (2 * B a c - 1)) := by
    rw [hXu, pow_add]
    apply centered_congr
    have he : (2 : ℤ) ^ c * 2 ^ i * (2 * A a) =
        2 ^ i * (2 * B a c - 1) + (2 * (2 * C a c + 1) + 1) * 2 ^ i := by
      change U c * 2 ^ i * (2 * A a) = _
      dsimp [A, B, C]
      nlinarith only [congrArg (fun z : ℤ => z * (T a * U c * 2 ^ i)) hts]
    rw [he, Int.add_mul_emod_self_left]
  have hSw (i : ℕ) : S a c (a + c + i) = centered (2 * C a c + 1) (2 ^ i * H a c) := by
    rw [S, raw, hseed, pow_add, pow_add, hN]
    apply centered_congr
    have he : (2 : ℤ) ^ a * 2 ^ c * 2 ^ i * A a =
        2 ^ i * H a c + (2 * C a c + 1) * ((T a + 1) * 2 ^ i) := by
      change T a * U c * 2 ^ i * A a = _
      dsimp [A, H, C]
      nlinarith only [congrArg (fun z : ℤ => z * (T a * U c * (T a + 1) * 2 ^ i)) hts]
    rw [he, Int.add_mul_emod_self_left]
  have hXw (i : ℕ) : X a c (a + c + i) =
      centered (2 * (2 * C a c + 1) + 1) (2 ^ i * (2 * H a c - T a - 1)) := by
    rw [hXu, pow_add, pow_add]
    apply centered_congr
    have he : (2 : ℤ) ^ a * 2 ^ c * 2 ^ i * (2 * A a) =
        2 ^ i * (2 * H a c - T a - 1) +
          (2 * (2 * C a c + 1) + 1) * ((T a + 1) * 2 ^ i) := by
      change T a * U c * 2 ^ i * (2 * A a) = _
      dsimp [A, H, C]
      nlinarith only [congrArg (fun z : ℤ => z * (T a * U c * (T a + 1) * 2 ^ i)) hts]
    rw [he, Int.add_mul_emod_self_left]
  refine ⟨hN, hM, hc0, ⟨⟨hca0, hcaC⟩, ⟨hcb0, hcbC⟩, hcg0, hcgC⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hSu, oldU i (by omega), if_pos hi]
  · intro i hi; rw [hXu, newU i (by omega), if_pos hi]
  · intro i hi; rw [hSv, oldV i (by omega), if_pos hi]
  · intro i hi; rw [hXv, newV i (by omega), if_pos hi]
  · intro i hi; rw [hSw, oldW i (by omega), if_pos hi]
  · intro i hi; rw [hXw, newW i (by omega), if_pos hi]
  · rw [hSu, oldU _ (le_refl _), if_neg (by omega)]
  · rw [hXu, newU _ (le_refl _), if_neg (by omega)]
  · rw [show a + c - 1 = c + (a - 1) by omega, hSv, oldV _ (le_refl _), if_neg (by omega)]
  · rw [show a + c - 1 = c + (a - 1) by omega, hXv, newV _ (le_refl _), if_neg (by omega)]
  · rw [show K a c - 1 = a + c + (a - 1) by dsimp [K]; omega, hSw, oldW _ (le_refl _), if_neg (by omega)]
  · rw [show K a c - 1 = a + c + (a - 1) by dsimp [K]; omega, hXw, newW _ (le_refl _), if_neg (by omega)]
  · rw [hXu]
    have he : (2 : ℤ) ^ K a c * (2 * A a) =
        A a + (2 * (2 * C a c + 1) + 1) * A a := by
      have hh := hM
      dsimp [modulus] at hh
      rw [pow_succ] at hh
      nlinarith only [congrArg (fun z : ℤ => z * A a) hh]
    have hAe : A a ≤ 2 * C a c + 1 := by
      dsimp [A, C]
      have := mul_nonneg (show 0 ≤ U c - 2 by omega) (show 0 ≤ sh a * T a by positivity)
      nlinarith
    apply centered_unique (by omega) (by omega) (centered_bounds (by omega) (by omega) _) ?_ ?_
    · have hh : (2 * (2 * C a c + 1) + 1) / 2 = 2 * C a c + 1 := by omega
      rw [hh]; constructor <;> dsimp [A] at * <;> nlinarith
    · rw [centered_mod, he, Int.add_mul_emod_self_left]


private abbrev row (off len : ℕ) : List ℕ := List.range' off len

private theorem row_dyadic (off len : ℕ) (f : ℕ → ℤ) (b : ℤ)
    (hf : ∀ i < len, f (off + i) = (2 : ℤ) ^ i * b) :
    Dyadic f b (row off len) := by
  induction len generalizing off b with
  | zero => simp [row, List.range', Dyadic]
  | succ len ih =>
    change f off = b ∧ Dyadic f (2 * b) (row (off + 1) len)
    constructor
    · simpa using hf 0 (by omega)
    · apply ih
      intro i hi
      have hh := hf (i + 1) (by omega)
      rw [show off + (i + 1) = (off + 1) + i by omega, pow_succ] at hh
      nlinarith only [hh]

private theorem row_sum (off len : ℕ) (f : ℕ → ℤ) (b : ℤ)
    (hf : ∀ i < len, f (off + i) = (2 : ℤ) ^ i * b) :
    ((row off len).map f).sum = ((2 : ℤ) ^ len - 1) * b := by
  simpa only [List.length_range'] using dyadic_sum (row_dyadic off len f b hf)

/-- One selection of physical W labels supplies both source masses. -/
private theorem paired_selection (off len n : ℕ) (hn : n < 2 ^ len)
    (f g : ℕ → ℤ) (p q : ℤ)
    (hf : ∀ i < len, f (off + i) = (2 : ℤ) ^ i * p)
    (hg : ∀ i < len, g (off + i) = (2 : ℤ) ^ i * q) :
    ∃ F E : List ℕ, (F ++ E).Perm (row off len) ∧
      (F.map f).sum = (n : ℤ) * p ∧ (F.map g).sum = (n : ℤ) * q := by
  let w := fun i : ℕ => (2 : ℤ) ^ (i - off)
  have hw : Dyadic w 1 (row off len) :=
    row_dyadic off len w 1 (by intro i hi; simp [w])
  obtain ⟨F, E, hp, hs⟩ := dyadic_select hw n (by simpa using hn)
  refine ⟨F, E, hp, ?_, ?_⟩
  have hm (i : ℕ) (hi : i ∈ F) : off ≤ i ∧ i < off + len := by
    have := List.mem_range'.mp (hp.mem_iff.mp (List.mem_append_left E hi))
    omega
  have hlin (v : ℕ → ℤ) (b : ℤ)
      (hv : ∀ i < len, v (off + i) = (2 : ℤ) ^ i * b) :
      (F.map v).sum = (n : ℤ) * b := by
    have he : F.map v = (F.map w).map (fun x => x * b) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hh := hv (i - off) (by have := hm i hi; omega)
      simpa [w, Nat.add_sub_of_le (hm i hi).1] using hh
    rw [he, List.sum_map_mul_right, hs]
    simp
  · exact hlin f p hf
  · exact hlin g q hg

/-- Three negative seams control every natural prefix, including saturated takes. -/
private theorem three_seams (f : ℕ → ℤ) (P Q R : List ℕ) (b g al : ℕ)
    (D p q : ℤ)
    (hP : ∀ x ∈ P, 0 ≤ f x) (hQ : ∀ x ∈ Q, 0 ≤ f x)
    (hR : ∀ x ∈ R, 0 ≤ f x)
    (hb : f b ≤ 0) (hg : f g ≤ 0) (hal : -D ≤ f al ∧ f al ≤ 0)
    (hp : (P.map f).sum + f b = p)
    (hq : p + (Q.map f).sum + f g = q)
    (ht : q + (R.map f).sum + f al = 0)
    (hpb : 0 ≤ p ∧ p ≤ D + f b) (hqb : 0 ≤ q ∧ q ≤ D + f g) :
    InStrip f D 0 (P ++ [b] ++ Q ++ [g] ++ R ++ [al]) := by
  have hRstrip : InStrip f D q (R ++ [al]) := by
    apply inStrip_append (positive_strip f R D q hR hqb.1 (by omega))
    simp only [InStrip]
    omega
  have hQstrip : InStrip f D p (Q ++ [g] ++ R ++ [al]) := by
    rw [List.append_assoc, List.append_assoc]
    apply inStrip_append (positive_strip f Q D p hQ hpb.1 (by omega))
    simp only [List.singleton_append, InStrip]
    refine ⟨by omega, by omega, ?_⟩
    convert hRstrip using 1 <;> omega
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  apply inStrip_append (positive_strip f P D 0 hP (le_refl 0) (by omega))
  simp only [List.singleton_append, InStrip]
  refine ⟨by omega, by omega, ?_⟩
  convert hQstrip using 1 <;> omega

private theorem row_partition (a c : ℕ) (hc : 0 < c) (ha : 0 < a) :
    row 0 (c - 1) ++ [c - 1] ++ row c (a - 1) ++ [a + c - 1] ++
      row (a + c) (a - 1) ++ [K a c - 1] = List.range (K a c) := by
  have hblock (off len : ℕ) : row off len ++ [off + len] = row off (len + 1) := by
    simpa only [row, Nat.mul_one] using (List.range'_concat off len).symm
  have hjoin (off l r : ℕ) : row off l ++ row (off + l) r = row off (l + r) := by
    simpa only [row, Nat.mul_one] using (List.range'_append off l r).symm
  rw [show c - 1 = 0 + (c - 1) by omega, hblock]
  rw [show c - 1 + 1 = c by omega]
  rw [show a + c - 1 = c + (a - 1) by omega, List.append_assoc, hblock]
  rw [show a - 1 + 1 = a by omega]
  rw [show a + c = c + a by omega]
  rw [show K a c - 1 = c + a + (a - 1) by dsimp [K]; omega,
    List.append_assoc, List.append_assoc, hblock]
  rw [show a - 1 + 1 = a by omega]
  rw [hjoin, show c + a + a = K a c by dsimp [K]; omega]
  simpa [row] using (List.range'_eq_range (K a c))

private theorem joint_lift (k v j : ℕ) (hk : 0 < k) (l : List ℕ)
    (hl : l.Perm (List.range k)) (hj : j ≤ k)
    (hs : InStrip (raw k v) (modulus k / 2) 0 l)
    (ht : (l.map (raw k v)).sum = 0)
    (hsn : InStrip (raw (k + 1) (2 * v)) (modulus (k + 1) / 2) 0
      (l.take j ++ [k] ++ l.drop j))
    (htn : ((l.take j ++ [k] ++ l.drop j).map (raw (k + 1) (2 * v))).sum = 0) :
    ∃ sigma : List (Fin k), OriginalOrder k v sigma ∧
      OriginalOrder (k + 1) (2 * v) (RunFirstEarTransport.earWord k sigma j) := by
  let lift : ℕ → Fin k := fun i => ⟨i % k, Nat.mod_lt i hk⟩
  let liftNew : ℕ → Fin (k + 1) := fun i => ⟨i % (k + 1), Nat.mod_lt i (by omega)⟩
  have hmem (i : ℕ) (hi : i ∈ l) : i < k := List.mem_range.mp (hl.mem_iff.mp hi)
  have hold (i : ℕ) (hi : i ∈ l) : actualSource k v (lift i) = raw k v i := by
    simp only [actualSource, lift, raw, Nat.mod_eq_of_lt (hmem i hi)]
  have hnew (i : ℕ) (hi : i ∈ l.take j ++ [k] ++ l.drop j) :
      actualSource (k + 1) (2 * v) (liftNew i) = raw (k + 1) (2 * v) i := by
    have hh : i < k + 1 := by
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with (hi | rfl) | hi
      · exact Nat.lt_succ_of_lt (hmem i (List.mem_of_mem_take hi))
      · omega
      · exact Nat.lt_succ_of_lt (hmem i (List.mem_of_mem_drop hi))
    simp only [actualSource, liftNew, raw, Nat.mod_eq_of_lt hh]
  have hbase : (List.range k).map lift = List.finRange k := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by simpa using hi)
  have hphysical : (l.map (fun i => (lift i).castSucc)) = l.map liftNew := by
    apply List.map_congr_left
    intro i hi
    apply Fin.ext
    simp only [Fin.val_castSucc, lift, liftNew]
    rw [Nat.mod_eq_of_lt (hmem i hi), Nat.mod_eq_of_lt (by have := hmem i hi; omega)]
  have hear : RunFirstEarTransport.earWord k (l.map lift) j =
      (l.take j ++ [k] ++ l.drop j).map liftNew := by
    simp only [RunFirstEarTransport.earWord, List.map_take, List.map_drop,
      List.map_append, List.map_cons, List.map_nil]
    rw [← List.map_take, ← List.map_drop, List.map_map, List.map_map]
    change (l.take j).map (fun i => (lift i).castSucc) ++ [Fin.last k] ++
      (l.drop j).map (fun i => (lift i).castSucc) = _
    rw [List.map_take, List.map_drop, hphysical]
    congr 2
    apply Fin.ext
    simp [liftNew, Nat.mod_eq_of_lt (by omega : k < k + 1)]
  have newperm : (l.take j ++ [k] ++ l.drop j).Perm (List.range (k + 1)) := by
    have hp : (l.take j ++ [k] ++ l.drop j).Perm (l ++ [k]) := by
      have hh := (List.perm_append_comm : ([k] ++ l.drop j).Perm (l.drop j ++ [k])).append_left (l.take j)
      simpa [List.append_assoc, ← List.append_assoc, List.take_append_drop] using hh
    exact hp.trans (by simpa [List.range_succ] using hl.append_right [k])
  have hbaseNew : (List.range (k + 1)).map liftNew = List.finRange (k + 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by simpa using hi)
  have mapped (n : ℕ) (w : List ℕ) (f : Fin n → ℤ) (r : ℕ → ℤ) (g : ℕ → Fin n)
      (he : ∀ i ∈ w, f (g i) = r i) : (w.map g).map f = w.map r := by
    rw [List.map_map]
    exact List.map_congr_left he
  refine ⟨l.map lift, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [hbase] using hl.map lift
  · simpa only [mapped _ _ _ _ _ hold] using ht
  · intro n
    have he := mapped k (l.take n) (actualSource k v) (raw k v) lift
      (fun i hi => hold i (List.mem_of_mem_take hi))
    rw [← List.map_take, he]
    exact inStrip_prefix hs n
  · rw [hear]
    refine ⟨?_, ?_, ?_⟩
    · simpa [hbaseNew] using newperm.map liftNew
    · rw [mapped _ _ _ _ _ hnew]; exact htn
    · intro n
      have he := mapped (k + 1) ((l.take j ++ [k] ++ l.drop j).take n)
        (actualSource (k + 1) (2 * v)) (raw (k + 1) (2 * v)) liftNew
        (fun i hi => hnew i (List.mem_of_mem_take hi))
      rw [← List.map_take, he]
      exact inStrip_prefix hsn n

end D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
