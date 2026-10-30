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
    have htm : 4 * m ≤ t := by nlinarith [mul_nonneg (show 0 ≤ u - 4 by omega) (show 0 ≤ m by omega)]
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
      calc
        4 * ((t + 1) * m) ≤ u * ((t + 1) * m) :=
          mul_le_mul_of_nonneg_right hu (by positivity)
        _ = t * (t + 1) := by rw [htu]; ring
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
  have hNraw : 2 * C a c + 1 = T a * T a * U c - 1 := by
    dsimp only [C]
    rw [hts]
    ring
  have hCraw : C a c = T a * T a * rh c - 1 := by
    dsimp only [C]
    rw [hts, hur]
    ring
  have hc0 : 0 ≤ C a c := by
    have hst : (1 : ℤ) * 1 ≤ sh a * T a :=
      mul_le_mul (by omega) (by omega) (by norm_num) (by omega)
    have hprod : (1 : ℤ) * 1 ≤ (sh a * T a) * U c :=
      mul_le_mul (by simpa using hst) (by omega) (by norm_num) (by nlinarith only [hst])
    dsimp only [C]
    nlinarith only [hprod]
  have hca0 : 0 ≤ (T a + 1) * rh c := by positivity
  have hcb0 : 0 ≤ sh a * (U c + 1) := by positivity
  have hcg0 : 0 ≤ sh a * (T a + 1) := by positivity
  have hcaC : (T a + 1) * rh c ≤ C a c := by
    rw [hCraw]
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
    · calc
        (T a + 1) * U c = 2 * ((T a + 1) * rh c) := by rw [hur]; ring
        _ ≤ 2 * C a c + 1 := by omega
  have hnewb : 0 ≤ T a * U c + sh a ∧ T a * U c + sh a ≤ 2 * C a c + 1 := by
    constructor
    · positivity
    · calc
        T a * U c + sh a = 2 * (sh a * (U c + 1)) - sh a := by rw [hts]; ring
        _ ≤ 2 * C a c + 1 := by omega
  have hnewg : 0 ≤ sh a * (T a + 1) ∧ sh a * (T a + 1) ≤ 2 * C a c + 1 := by omega
  have hlastU : (2 : ℤ) ^ (c - 1) * A a = C a c + 1 + (T a + 1) * rh c := by
    rw [hCraw]
    dsimp only [A]
    ring
  have hlastV : (2 : ℤ) ^ (a - 1) * B a c = C a c + 1 + sh a * (U c + 1) := by
    dsimp [B, C]; ring
  have hlastW : (2 : ℤ) ^ (a - 1) * H a c = C a c + 1 + sh a * (T a + 1) := by
    dsimp [H, C]; ring
  have hlastUn : (2 : ℤ) ^ (c - 1) * (2 * A a) =
      (2 * C a c + 1) + 1 + (T a + 1) * U c := by
    calc
      _ = 2 * ((2 : ℤ) ^ (c - 1) * A a) := by ring
      _ = 2 * (C a c + 1 + (T a + 1) * rh c) := by rw [hlastU]
      _ = _ := by rw [hur]; ring
  have hlastVn : (2 : ℤ) ^ (a - 1) * (2 * B a c - 1) =
      (2 * C a c + 1) + 1 + (T a * U c + sh a) := by
    calc
      _ = 2 * ((2 : ℤ) ^ (a - 1) * B a c) - sh a := by ring
      _ = 2 * (C a c + 1 + sh a * (U c + 1)) - sh a := by rw [hlastV]
      _ = _ := by rw [hts]; ring
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
      rw [hNraw]
      dsimp only [A, B]
      ring
    rw [he, Int.add_mul_emod_self_left]
  have hXv (i : ℕ) : X a c (c + i) =
      centered (2 * (2 * C a c + 1) + 1) (2 ^ i * (2 * B a c - 1)) := by
    rw [hXu, pow_add]
    apply centered_congr
    have he : (2 : ℤ) ^ c * 2 ^ i * (2 * A a) =
        2 ^ i * (2 * B a c - 1) + (2 * (2 * C a c + 1) + 1) * 2 ^ i := by
      change U c * 2 ^ i * (2 * A a) = _
      rw [hNraw]
      dsimp only [A, B]
      ring
    rw [he, Int.add_mul_emod_self_left]
  have hSw (i : ℕ) : S a c (a + c + i) = centered (2 * C a c + 1) (2 ^ i * H a c) := by
    rw [S, raw, hseed, pow_add, pow_add, hN]
    apply centered_congr
    have he : (2 : ℤ) ^ a * 2 ^ c * 2 ^ i * A a =
        2 ^ i * H a c + (2 * C a c + 1) * ((T a + 1) * 2 ^ i) := by
      change T a * U c * 2 ^ i * A a = _
      rw [hNraw]
      dsimp only [A, H]
      ring
    rw [he, Int.add_mul_emod_self_left]
  have hXw (i : ℕ) : X a c (a + c + i) =
      centered (2 * (2 * C a c + 1) + 1) (2 ^ i * (2 * H a c - T a - 1)) := by
    rw [hXu, pow_add, pow_add]
    apply centered_congr
    have he : (2 : ℤ) ^ a * 2 ^ c * 2 ^ i * (2 * A a) =
        2 ^ i * (2 * H a c - T a - 1) +
          (2 * (2 * C a c + 1) + 1) * ((T a + 1) * 2 ^ i) := by
      change T a * U c * 2 ^ i * (2 * A a) = _
      rw [hNraw]
      dsimp only [A, H]
      ring
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
      rw [hNraw]
      dsimp only [A]
      nlinarith [mul_nonneg (show 0 ≤ U c - 2 by omega) (sq_nonneg (T a))]
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
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp (hp.mem_iff.mp (List.mem_append_left E hi))
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
    simpa only [row, Nat.mul_one] using (List.range'_1_concat (s := off) (n := len)).symm
  have hjoin (off l r : ℕ) : row off l ++ row (off + l) r = row off (l + r) := by
    simpa only [row, Nat.mul_one] using (List.range'_append_1 (s := off) (m := l) (n := r))
  rw [show c - 1 = 0 + (c - 1) by omega, hblock]
  rw [show c - 1 + 1 = c by omega]
  rw [show a + c - 1 = c + (a - 1) by omega, List.append_assoc, hblock]
  rw [show a - 1 + 1 = a by omega]
  rw [show a + c = c + a by omega]
  rw [show K a c - 1 = c + a + (a - 1) by dsimp [K]; omega,
    List.append_assoc, List.append_assoc, hblock]
  rw [show a - 1 + 1 = a by omega]
  rw [hjoin, show c + a + a = K a c by dsimp [K]; omega]
  simpa [row] using (List.range_eq_range' (n := K a c)).symm

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


/-- Assemble the two literal words using a single partition of the physical W row. -/
private theorem assemble (a c : ℕ) (hc : 2 ≤ c) (hca : c < a)
    (before : Bool) (F E : List ℕ) (n : ℕ)
    (hFE : (F ++ E).Perm (row (a + c) (a - 1)))
    (hFs : (F.map (S a c)).sum = (n : ℤ) * H a c)
    (hFx : (F.map (X a c)).sum = (n : ℤ) * (2 * H a c - T a - 1))
    (hh : 0 ≤ (T a + 1) * (T a - U c) - H a c * n ∧
      (T a + 1) * (T a - U c) - H a c * n ≤ sh a * (T a + 1))
    (hqq : 0 ≤ 2 * ((T a + 1) * (T a - U c) - H a c * n) -
        T a * (T a + 1) + (T a + 1) * n + (if before then A a else 0) ∧
      2 * ((T a + 1) * (T a - U c) - H a c * n) -
        T a * (T a + 1) + (T a + 1) * n + (if before then A a else 0) ≤
          sh a * (T a + 1)) :
    ∃ sigma : List (Fin (K a c)), ∃ j : ℕ, j ≤ K a c ∧
      OriginalOrder (K a c) (seed a) sigma ∧
      OriginalOrder (K a c + 1) (2 * seed a)
        (RunFirstEarTransport.earWord (K a c) sigma j) := by
  let d := source_rows a c hc hca
  let UL := row 0 (c - 1)
  let VL := row c (a - 1)
  let WL := row (a + c) (a - 1)
  let al := c - 1
  let be := a + c - 1
  let ga := K a c - 1
  let l := VL ++ [be] ++ E ++ [ga] ++ F ++ UL ++ [al]
  let Qn := E ++ (if before then [K a c] else [])
  let Rn := (if before then [] else [K a c]) ++ F ++ UL
  let ln := VL ++ [be] ++ Qn ++ [ga] ++ Rn ++ [al]
  let j := (VL ++ [be] ++ E).length + (if before then 0 else 1)
  let delta := T a - U c
  let h := (T a + 1) * delta - H a c * n
  let q := 2 * h - T a * (T a + 1) + (T a + 1) * n +
    (if before then A a else 0)
  have ht : 4 ≤ T a := pow_lower a (by omega)
  have hu : 4 ≤ U c := pow_lower c hc
  have hs : 0 ≤ sh a := by positivity
  have hr : 0 ≤ rh c := by positivity
  have hts : T a = 2 * sh a := pow_half a (by omega)
  have hur : U c = 2 * rh c := pow_half c (by omega)
  have hut : 2 * U c ≤ T a := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show c + 1 ≤ a by omega)
    simpa only [pow_succ] using hp
  have hup (i : ℕ) (hi : i < c - 1) : S a c (0 + i) = (2 : ℤ) ^ i * A a := by simpa using d.oldU i hi
  have hux (i : ℕ) (hi : i < c - 1) : X a c (0 + i) = (2 : ℤ) ^ i * (2 * A a) := by simpa using d.newU i hi
  have su := row_sum 0 (c - 1) (S a c) (A a) hup
  have xu := row_sum 0 (c - 1) (X a c) (2 * A a) hux
  have sv := row_sum c (a - 1) (S a c) (B a c) d.oldV
  have xv := row_sum c (a - 1) (X a c) (2 * B a c - 1) d.newV
  have sw := row_sum (a + c) (a - 1) (S a c) (H a c) d.oldW
  have xw := row_sum (a + c) (a - 1) (X a c) (2 * H a c - T a - 1) d.newW
  have netu : (UL.map (S a c)).sum + S a c al = (T a + 1) * (U c - T a) := by
    rw [su, d.oldAlpha]
    dsimp only [A, C]
    rw [hts, hur]
    ring
  have netv : (VL.map (S a c)).sum + S a c be = delta := by
    rw [sv, d.oldBeta]
    dsimp only [B, C, delta]
    rw [hts]
    ring
  have netw : (WL.map (S a c)).sum + S a c ga = T a * delta := by
    rw [sw, d.oldGamma]
    dsimp only [H, C, delta]
    rw [hts]
    ring
  have netun : (UL.map (X a c)).sum + X a c al = 2 * (T a + 1) * (U c - T a) - 1 := by
    rw [xu, d.newAlpha]
    dsimp only [A, C]
    rw [hts, hur]
    ring
  have netvn : (VL.map (X a c)).sum + X a c be = 2 * delta - T a := by
    rw [xv, d.newBeta]
    dsimp only [B, C, delta]
    rw [hts]
    ring
  have netwn : (WL.map (X a c)).sum + X a c ga = 2 * T a * delta - T a * T a := by
    rw [xw, d.newGamma]
    dsimp only [H, C, delta]
    rw [hts]
    ring
  have hEs : (E.map (S a c)).sum = (WL.map (S a c)).sum - (n : ℤ) * H a c := by
    have hh := (hFE.map (S a c)).sum_eq
    simp only [List.map_append, List.sum_append, hFs] at hh
    omega
  have hEx : (E.map (X a c)).sum = (WL.map (X a c)).sum -
      (n : ℤ) * (2 * H a c - T a - 1) := by
    have hh := (hFE.map (X a c)).sum_eq
    simp only [List.map_append, List.sum_append, hFx] at hh
    omega
  have hperm : l.Perm (List.range (K a c)) := by
    rw [← row_partition a c (by omega) (by omega)]
    apply List.perm_iff_count.mpr
    intro i
    have hh := hFE.count_eq i
    simp only [List.count_append] at hh
    dsimp only [l, UL, VL, WL, al, be, ga]
    simp only [List.count_append]
    omega
  have hj : j ≤ K a c := by
    have hh := hFE.length_eq
    simp only [List.length_append, List.length_range'] at hh
    dsimp only [j, VL]
    simp only [List.length_append, List.length_range', List.length_singleton]
    split_ifs <;> dsimp only [K] <;> omega
  have hear : l.take j ++ [K a c] ++ l.drop j = ln := by
    cases before <;>
      simp [l, j, ln, Qn, Rn, List.append_assoc, List.take_append, List.drop_append]
  have hpos (v : ℕ → ℤ) (off len : ℕ) (b : ℤ) (hb : 0 ≤ b)
      (hv : ∀ i < len, v (off + i) = (2 : ℤ) ^ i * b) :
      ∀ i ∈ row off len, 0 ≤ v i :=
    dyadic_nonneg hb (row_dyadic off len v b hv)
  have hsu := hpos (S a c) 0 (c - 1) (A a) (by dsimp [A]; positivity) hup
  have hxu := hpos (X a c) 0 (c - 1) (2 * A a) (by dsimp [A]; positivity) hux
  have hsv := hpos (S a c) c (a - 1) (B a c) (by dsimp [B]; positivity) d.oldV
  have hxv := hpos (X a c) c (a - 1) (2 * B a c - 1) (by dsimp [B]; positivity) d.newV
  have hsw := hpos (S a c) (a + c) (a - 1) (H a c) (by dsimp [H]; positivity) d.oldW
  have hxw := hpos (X a c) (a + c) (a - 1) (2 * H a c - T a - 1) (by dsimp [H]; positivity) d.newW
  have hsubF (i : ℕ) (hi : i ∈ F) : i ∈ WL := hFE.mem_iff.mp (List.mem_append_left E hi)
  have hsubE (i : ℕ) (hi : i ∈ E) : i ∈ WL := hFE.mem_iff.mp (List.mem_append_right F hi)
  have hPs : ∀ i ∈ VL, 0 ≤ S a c i := hsv
  have hQs : ∀ i ∈ E, 0 ≤ S a c i := fun i hi => hsw i (hsubE i hi)
  have hRs : ∀ i ∈ F ++ UL, 0 ≤ S a c i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hsw i (hsubF i hi)
    · exact hsu i hi
  have hPx : ∀ i ∈ VL, 0 ≤ X a c i := hxv
  have hQx : ∀ i ∈ Qn, 0 ≤ X a c i := by
    intro i hi
    simp only [Qn, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hxw i (hsubE i hi)
    · cases before <;> simp only [Bool.false_eq_true, if_false, if_true,
        List.mem_nil_iff, List.mem_singleton] at hi
      subst i
      rw [d.ear]
      dsimp [A]; positivity
  have hRx : ∀ i ∈ Rn, 0 ≤ X a c i := by
    intro i hi
    simp only [Rn, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · cases before <;> simp only [Bool.false_eq_true, if_false, if_true,
        List.mem_nil_iff, List.mem_singleton] at hi
      subst i
      rw [d.ear]
      dsimp [A]; positivity
    · exact hxw i (hsubF i hi)
    · exact hxu i hi
  have htot : (l.map (S a c)).sum = 0 := by
    have he : (T a + 1) * (U c - T a) + delta + T a * delta = 0 := by dsimp [delta]; ring
    dsimp only [l]
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    linarith [netu, netv, netw, hEs, hFs]
  have htotn : (ln.map (X a c)).sum = 0 := by
    have he : (2 * (T a + 1) * (U c - T a) - 1) +
        (2 * delta - T a) + (2 * T a * delta - T a * T a) + A a = 0 := by
      dsimp [delta, A]; ring
    have hearg : ((if before then [K a c] else []).map (X a c)).sum +
        ((if before then [] else [K a c]).map (X a c)).sum = A a := by
      cases before <;> simp [d.ear]
    dsimp only [ln, Qn, Rn]
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    linarith [netun, netvn, netwn, hEx, hFx]
  have hpn : (VL.map (X a c)).sum + X a c be = T a - 2 * U c := by
    dsimp [delta] at netvn
    linarith
  have hqn : (T a - 2 * U c) + (Qn.map (X a c)).sum + X a c ga = q := by
    have hearg : ((if before then [K a c] else []).map (X a c)).sum =
        (if before then A a else 0) := by cases before <;> simp [d.ear]
    dsimp only [Qn]
    simp only [List.map_append, List.sum_append]
    rw [hearg, hEx]
    dsimp only [q, h, delta]
    nlinarith only [netwn]
  have hqs : delta + (E.map (S a c)).sum + S a c ga = h := by
    rw [hEs]
    dsimp only [h]
    nlinarith only [netw]
  have hbeta : 0 ≤ delta ∧ delta ≤ sh a * (U c + 1) := by
    dsimp only [delta]
    constructor
    · omega
    · nlinarith [mul_nonneg (show 0 ≤ T a by omega) (show 0 ≤ U c - 1 by omega)]
  have hbetan : 0 ≤ T a - 2 * U c ∧ T a - 2 * U c ≤ T a * U c + sh a := by
    constructor
    · omega
    · nlinarith [mul_nonneg (show 0 ≤ T a by omega) (show 0 ≤ U c - 1 by omega)]
  have hstrip : InStrip (S a c) (C a c) 0 l := by
    change InStrip (S a c) (C a c) 0 (VL ++ [be] ++ E ++ [ga] ++ (F ++ UL) ++ [al])
    apply three_seams (S a c) VL E (F ++ UL) be ga al (C a c) delta h
      hPs hQs hRs
    · rw [d.oldBeta]; linarith [d.caps.2.1.2]
    · rw [d.oldGamma]; linarith [d.caps.2.2.2]
    · rw [d.oldAlpha]; constructor <;> linarith [d.caps.1]
    · exact netv
    · exact hqs
    · simp only [List.map_append, List.sum_append] at htot ⊢
      dsimp only [l] at htot
      simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at htot
      linarith
    · rw [d.oldBeta]; simpa using hbeta
    · rw [d.oldGamma]; simpa using hh
  have hstripn : InStrip (X a c) (2 * C a c + 1) 0 ln := by
    apply three_seams (X a c) VL Qn Rn be ga al (2 * C a c + 1) (T a - 2 * U c) q
      hPx hQx hRx
    · rw [d.newBeta]
      have hh := d.caps.2.1.2
      nlinarith only [hh, hts, hs]
    · rw [d.newGamma]
      linarith [d.caps.2.2.2, d.cap0]
    · rw [d.newAlpha]
      constructor <;> nlinarith only [d.caps.1.1, d.caps.1.2, hur]
    · exact hpn
    · exact hqn
    · dsimp only [ln] at htotn
      simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at htotn
      linarith
    · rw [d.newBeta]; simpa using hbetan
    · rw [d.newGamma]; simpa only [q, h, delta] using hqq
  obtain ⟨sigma, ho, hn⟩ := joint_lift (K a c) (seed a) j (by dsimp [K]; omega) l hperm hj
    (by simpa only [d.oldMod, show (2 * C a c + 1) / 2 = C a c by omega] using hstrip)
    htot
    (by rw [hear]; simpa only [d.newMod, show (2 * (2 * C a c + 1) + 1) / 2 = 2 * C a c + 1 by omega] using hstripn)
    (by rw [hear]; exact htotn)
  exact ⟨sigma, j, hj, ho, hn⟩

/-- For every c<a, one native physical permutation and one literal ear cut
complete both centered sources, with all natural prefixes and exact total zero. -/
theorem native_three_negative_common_cut (a c : ℕ) (hc : 2 ≤ c) (hca : c < a) :
    let k := 2 * a + c
    let v := 1 + 2 ^ a + 2 ^ (2 * a)
    ∃ sigma : List (Fin k), ∃ j : ℕ, j ≤ k ∧ OriginalOrder k v sigma ∧
      OriginalOrder (k + 1) (2 * v) (RunFirstEarTransport.earWord k sigma j) := by
  have ht : 4 ≤ T a := pow_lower a (by omega)
  have hu : 4 ≤ U c := pow_lower c hc
  have hts : T a = 2 * sh a := pow_half a (by omega)
  have hg : T a * (T a + 1) / 2 = sh a * (T a + 1) := by
    have he : T a * (T a + 1) = 2 * (sh a * (T a + 1)) := by rw [hts]; ring
    rw [he]; omega
  by_cases hboundary : a = c + 1
  · have htu : T a = 2 * U c := by rw [hboundary]; simp only [T, U, pow_succ]; ring
    apply assemble a c hc hca false [] (row (a + c) (a - 1)) 0
      (by simp) (by simp) (by simp)
    · simp only [Nat.cast_zero, mul_zero, sub_zero]
      constructor
      · positivity
      · nlinarith only [htu, hts]
    · simp only [Bool.false_eq_true, if_false, Nat.cast_zero, mul_zero, sub_zero, add_zero]
      constructor <;> nlinarith only [htu]
  · have hgap : 2 ≤ a - c := by omega
    let m : ℤ := 2 ^ (a - c)
    have hm : m = 4 ∨ 8 ≤ m := by
      by_cases he : a - c = 2
      · left; simp [m, he]
      · right
        have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 3 ≤ a - c by omega)
        norm_num at hh
        exact hh
    have htu : T a = m * U c := by
      dsimp only [T, U, m]
      rw [← pow_add, show a - c + c = a by omega]
    let f := (T a + 1) * (T a - U c) / H a c
    have hf := mask_bound (T a) (U c) m hu hm htu
    change 0 ≤ f ∧ f ≤ m - 2 ∧ f < T a / 2 ∧
      0 ≤ (T a + 1) * (T a - U c) - H a c * f ∧
      2 * ((T a + 1) * (T a - U c) - H a c * f) + 1 + (T a + 1) * f ≤
        T a * (T a + 1) / 2 at hf
    let n := f.toNat
    have hn : (n : ℤ) = f := Int.toNat_of_nonneg hf.1
    have hnfit : n < 2 ^ (a - 1) := by
      have hs : T a / 2 = sh a := by omega
      have hh : (n : ℤ) < (2 : ℤ) ^ (a - 1) := by simpa only [hn, hs] using hf.2.2.1
      exact_mod_cast hh
    let d := source_rows a c hc hca
    obtain ⟨F, E, hFE, hFs, hFx⟩ := paired_selection (a + c) (a - 1) n hnfit
      (S a c) (X a c) (H a c) (2 * H a c - T a - 1) d.oldW d.newW
    apply assemble a c hc hca true F E n hFE hFs hFx
    · rw [hn]
      constructor
      · exact hf.2.2.2.1
      · rw [hg] at hf
        nlinarith [mul_nonneg (show 0 ≤ T a + 1 by omega) hf.1]
    · simp only [if_true, hn]
      have he : A a = T a * (T a + 1) + 1 := by dsimp [A]; ring
      rw [he, ← hg]
      constructor
      · nlinarith [mul_nonneg (show 0 ≤ T a + 1 by omega) hf.1, hf.2.2.2.1]
      · nlinarith only [hf.2.2.2.2]

#print axioms native_three_negative_common_cut

end D5.S3.Combinatorics.Circle.ThreeNegativeCommonCut
