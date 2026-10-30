/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeMiddleGapJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeMiddleGapJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A floor-mask physical joint constructor for all strictly ordered middle-minimum gaps. -/
import D5.S3.Combinatorics.Circle.ThreeBitSource
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Nat.Prime.Basic
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeMiddleGapJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private label lift_order marked_word schedule_from_tail ladder_sum from
  D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private mask_labels mask_labels_bound mask_labels_sum labelled_permutation from
  D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem floor_margin (r s t p C : ℤ)
    (hs : 4 ≤ s) (hr : 2 * s ≤ r) (hp : s = 2 * p)
    (ht : t = 2 * r ∨ 4 * r ≤ t) (hC : 2 * C = r * s * t - 2)
    (hodd : r % (s + 1) ≠ 0) :
    0 < s * t + p - 1 - 2 * (C % (1 + r + r * s)) := by
  let u := 1 + r + r * s
  have hu : 0 < u := by
    have hh : 0 ≤ r * s := mul_nonneg (by omega) (by omega)
    dsimp [u]; omega
  have hG0 := Int.emod_nonneg C (ne_of_gt hu)
  have hGu := Int.emod_lt_of_pos C hu
  change 0 < s * t + p - 1 - 2 * (C % u)
  rcases ht with ht | ht
  · let h := r / (s + 1)
    let d := r % (s + 1)
    have hd0 : 1 ≤ d := by
      have := Int.emod_nonneg r (show s + 1 ≠ 0 by omega)
      dsimp [d]; omega
    have hds : d ≤ s := by
      have := Int.emod_lt_of_pos r (show 0 < s + 1 by omega)
      dsimp [d]; omega
    have hh0 : 0 ≤ h := Int.ediv_nonneg (by omega) (by omega)
    have hde : r = h * (s + 1) + d := by
      have := Int.emod_add_mul_ediv r (s + 1)
      dsimp [h, d]; nlinarith only [this]
    have hhr : h < r := by
      have hh := mul_le_mul_of_nonneg_left (show 1 ≤ s + 1 by omega) hh0
      nlinarith only [hh, hde, hd0]
    let w := r * (s - d) + h
    have hw0 : 0 ≤ w := by
      have hsd : 0 ≤ s - d := by omega
      have hr0 : 0 ≤ r := by omega
      dsimp [w]; positivity
    have hwrs : w < r * s := by
      dsimp [w]
      nlinarith [mul_le_mul_of_nonneg_left hd0 (show 0 ≤ r by omega)]
    have hwu : w < u := by dsimp [u]; omega
    have he : C = u * (r - h - 1) + w := by
      rw [ht] at hC
      dsimp [u, w]
      nlinarith only [hC, congrArg (fun x : ℤ => r * x) hde]
    have hG : C % u = w := by
      rw [he]
      simp [Int.add_emod, Int.mul_emod, Int.emod_eq_of_lt hw0 hwu]
    rw [ht, hG]
    nlinarith only [hwrs, hp, hs]
  · have hst := mul_le_mul_of_nonneg_left ht (show 0 ≤ s by omega)
    have hrs := mul_le_mul_of_nonneg_left (show 1 ≤ s by omega) (show 0 ≤ r by omega)
    dsimp [u] at hGu
    nlinarith only [hst, hrs, hGu, hp, hs]

private theorem power_odd_remainder (a b : ℕ) (hb : 1 ≤ b) :
    (2 : ℤ) ^ a % ((2 : ℤ) ^ b + 1) ≠ 0 := by
  have he : (2 : ℕ) ^ b = 2 * 2 ^ (b - 1) := by
    rw [show b = (b - 1) + 1 by omega, pow_succ]
    ring
  have hodd : Odd ((2 : ℕ) ^ b + 1) := by
    refine ⟨2 ^ (b - 1), ?_⟩
    omega
  have hcop : Nat.Coprime ((2 : ℕ) ^ b + 1) (2 ^ a) :=
    (Nat.coprime_two_right.mpr hodd).pow_right a
  intro hz
  have hd : ((2 : ℤ) ^ b + 1) ∣ (2 : ℤ) ^ a := Int.emod_eq_zero.mp hz
  have hd' : ((2 : ℕ) ^ b + 1) ∣ (2 : ℕ) ^ a := by exact_mod_cast hd
  have hh := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hd'
  have hb0 : 0 < (2 : ℕ) ^ b := by positivity
  omega

private theorem paired_chains (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    let r : ℤ := 2 ^ a
    let s : ℤ := 2 ^ b
    let t : ℤ := 2 ^ c
    let k := a + b + c
    let N := modulus k
    let v := 1 + r + r * s
    let B := 1 + t + t * r
    let L := 1 + s + s * t
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
    let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * v))
    (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
    (∀ i < c - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧
    (∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧
      g (c + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧
    (∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧
      g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧
    f (c - 1) = -(N - B) / 2 ∧
    f (c + b - 1) = -(N - L) / 2 ∧
    f (k - 1) = -(N - v) / 2 ∧
    g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧
    g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧
    g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v := by
  dsimp only
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let t : ℤ := 2 ^ c
  let k := a + b + c
  let N := modulus k
  let M := modulus (k + 1)
  let v := 1 + r + r * s
  let B := 1 + t + t * r
  let L := 1 + s + s * t
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * v)
  let F := fun i : ℕ => centered M ((2 : ℤ) ^ i * v)
  let g := fun i : ℕ => centered M ((2 : ℤ) ^ i * (2 * v))
  change (1 ≤ v ∧ v < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
    (∀ i < c - 1, f i = (2 : ℤ) ^ i * v ∧ g i = (2 : ℤ) ^ i * (2 * v)) ∧
    (∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧
      g (c + i) = (2 : ℤ) ^ i * (2 * B - 1)) ∧
    (∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧
      g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1)) ∧
    f (c - 1) = -(N - B) / 2 ∧ f (c + b - 1) = -(N - L) / 2 ∧
    f (k - 1) = -(N - v) / 2 ∧
    g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 ∧
    g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 ∧
    g (k - 1) = -((2 * N + 1) - v) / 2 ∧ g k = v
  obtain ⟨hv, hB, hL, _, hU, hV, hW⟩ :=
    ThreeNegativeEqualOuterSourceBridge.actual_source_chains a b c (by omega) (by omega) hc
  change (1 ≤ v ∧ v < N) at hv
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ e < c, f e = if e + 1 < c then (2 : ℤ) ^ e * v else -(N - B) / 2 at hU
  change ∀ e < b, f (c + e) = if e + 1 < b then (2 : ℤ) ^ e * B else -(N - L) / 2 at hV
  change ∀ e < a, f (c + b + e) = if e + 1 < a then (2 : ℤ) ^ e * L else -(N - v) / 2 at hW
  obtain ⟨_, _, _, _, hU', hV', hW'⟩ :=
    ThreeNegativeEqualOuterSourceBridge.actual_source_chains a b (c + 1) (by omega) (by omega) (by omega)
  have hM : modulus (a + b + (c + 1)) = M := rfl
  have ht : (2 : ℤ) ^ (c + 1) = 2 * t := by dsimp [t]; rw [pow_succ]; ring
  have hB' : 1 + (2 : ℤ) ^ (c + 1) + 2 ^ (c + 1) * 2 ^ a = 2 * B - 1 := by
    rw [ht]; change 1 + 2 * t + 2 * t * r = _; dsimp [B]; ring
  have hL' : 1 + (2 : ℤ) ^ b + 2 ^ b * 2 ^ (c + 1) = 2 * L - s - 1 := by
    rw [ht]; change 1 + s + s * (2 * t) = _; dsimp [L]; ring
  rw [hM, hB'] at hU'
  rw [hM, hB', hL'] at hV'
  rw [hM, hL'] at hW'
  have hshift (i : ℕ) : g i = F (i + 1) := by
    dsimp [g, F]; rw [pow_succ]; congr 1; ring
  have hMN : M = 2 * N + 1 := by dsimp [M, N, modulus]; rw [pow_succ]; ring
  refine ⟨hv, hB, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < c by omega)] using hU i (by omega)
    · rw [hshift]
      have h := hU' (i + 1) (by omega)
      rw [ite_eq_left (by omega), pow_succ] at h
      change F (i + 1) = _ at h
      rw [h]; ring
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < b by omega)] using hV i (by omega)
    · rw [hshift, show c + i + 1 = (c + 1) + i by omega]
      exact (hV' i (by omega)).trans (ite_eq_left (by omega))
  · intro i hi
    constructor
    · simpa only [ite_eq_left (show i + 1 < a by omega)] using hW i (by omega)
    · rw [hshift, show c + b + i + 1 = (c + 1) + b + i by omega]
      exact (hW' i (by omega)).trans (ite_eq_left (by omega))
  · simpa only [ite_eq_right (by omega : ¬ c - 1 + 1 < c)] using hU (c - 1) (by omega)
  · simpa only [show c + (b - 1) = c + b - 1 by omega,
      ite_eq_right (by omega : ¬ b - 1 + 1 < b)] using hV (b - 1) (by omega)
  · simpa only [show c + b + (a - 1) = k - 1 by dsimp [k]; omega,
      ite_eq_right (by omega : ¬ a - 1 + 1 < a)] using hW (a - 1) (by omega)
  · rw [hshift, show c - 1 + 1 = c by omega]
    simpa only [ite_eq_right (by omega : ¬ c + 1 < c + 1), F, hMN] using hU' c (by omega)
  · rw [hshift, show c + b - 1 + 1 = (c + 1) + (b - 1) by omega]
    simpa only [ite_eq_right (by omega : ¬ b - 1 + 1 < b), F, hMN] using hV' (b - 1) (by omega)
  · rw [hshift, show k - 1 + 1 = (c + 1) + b + (a - 1) by dsimp [k]; omega]
    simpa only [ite_eq_right (by omega : ¬ a - 1 + 1 < a), F, hMN] using hW' (a - 1) (by omega)
  · have hvNat : ((1 + 2 ^ a + 2 ^ (a + b) : ℕ) : ℤ) = v := by
      push_cast; dsimp [v, r, s]; rw [pow_add]
    have hp : g k = centered M v := by
      rw [hshift]
      change centered M ((2 : ℤ) ^ (k + 1) * v) = _
      rw [← hvNat]
      exact centered_full_period (k + 1) _
    rw [hp]
    dsimp [centered]
    have hhalf : M / 2 = N := by omega
    rw [hhalf, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

set_option maxHeartbeats 4000000 in
/-- The complete middle-minimum chamber has one actual physical order and one
literal natural ear cut, uniformly in all three exponents. -/
theorem actualSource_three_negative_middle_gap_joint_lift (a b c : ℕ)
    (hb : 2 ≤ b) (hba : b < a) (hac : a < c) :
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ,
      j ≤ a + b + c ∧
      OriginalOrder (a + b + c) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + c + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + c) sigma j) := by
  classical
  let k := a + b + c
  let r : ℤ := 2 ^ a
  let s : ℤ := 2 ^ b
  let t : ℤ := 2 ^ c
  let q : ℤ := 2 ^ (a - 1)
  let p : ℤ := 2 ^ (b - 1)
  let vhalf : ℤ := 2 ^ (c - 1)
  let N := modulus k
  let C := q * s * t - 1
  let u := 1 + r + r * s
  let B := 1 + t + t * r
  let L := 1 + s + s * t
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
  let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * u))
  have hs : 4 ≤ s := by
    simpa [s] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
  have hrq : r = 2 * q := by
    dsimp [r, q]; rw [show a = (a - 1) + 1 by omega, pow_succ]; ring
  have hsp : s = 2 * p := by
    dsimp [s, p]; rw [show b = (b - 1) + 1 by omega, pow_succ]; ring
  have htv : t = 2 * vhalf := by
    dsimp [t, vhalf]; rw [show c = (c - 1) + 1 by omega, pow_succ]; ring
  have hqs : s ≤ q := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show b ≤ a - 1 by omega)
  have htr : 2 * r ≤ t := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a + 1 ≤ c by omega)
    simpa only [pow_succ, r, t, mul_comm] using hh
  have hcases : t = 2 * r ∨ 4 * r ≤ t := by
    by_cases hc : c = a + 1
    · left; dsimp [t, r]; rw [hc, pow_succ]; ring
    · right
      have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a + 2 ≤ c by omega)
      have he : (2 : ℤ) ^ (a + 2) = 4 * r := by dsimp [r]; rw [pow_add]; norm_num; ring
      simpa only [he] using hh
  have hN : N = r * s * t - 1 := by
    dsimp [N, modulus, k, r, s, t]; rw [pow_add, pow_add]
  have hNC : N = 2 * C + 1 := by rw [hN]; dsimp [C]; rw [hrq]; ring
  have hhalf : modulus k / 2 = C := by change N / 2 = C; omega
  have hnewhalf : modulus (k + 1) / 2 = N := by
    have hm : modulus (k + 1) = 2 * N + 1 := by dsimp [modulus, N]; rw [pow_succ]; ring
    omega
  obtain ⟨hu, hB, hL, hU, hV, hW, hfA, hfB, hfG, hgA, hgB, hgG, hgear⟩ :=
    paired_chains a b c (by omega) hb (by omega)
  change (1 ≤ u ∧ u < N) at hu
  change (1 ≤ B ∧ B < N) at hB
  change (1 ≤ L ∧ L < N) at hL
  change ∀ i < c - 1, f i = (2 : ℤ) ^ i * u ∧ g i = (2 : ℤ) ^ i * (2 * u) at hU
  change ∀ i < b - 1, f (c + i) = (2 : ℤ) ^ i * B ∧ g (c + i) = (2 : ℤ) ^ i * (2 * B - 1) at hV
  change ∀ i < a - 1, f (c + b + i) = (2 : ℤ) ^ i * L ∧
    g (c + b + i) = (2 : ℤ) ^ i * (2 * L - s - 1) at hW
  change f (c - 1) = -(N - B) / 2 at hfA
  change f (c + b - 1) = -(N - L) / 2 at hfB
  change f (k - 1) = -(N - u) / 2 at hfG
  change g (c - 1) = -((2 * N + 1) - (2 * B - 1)) / 2 at hgA
  change g (c + b - 1) = -((2 * N + 1) - (2 * L - s - 1)) / 2 at hgB
  change g (k - 1) = -((2 * N + 1) - u) / 2 at hgG
  change g k = u at hgear
  let Ha := C - vhalf * (r + 1)
  let Hb := C - p * (t + 1)
  let Hg := C - q * (s + 1)
  let Ka := 2 * Ha + 1
  let Kb := 2 * Hb + p + 1
  let Kg := 2 * Hg + q * (s + 1) + 1
  have hHa : 2 * Ha = N - B := by
    rw [hN]; dsimp [Ha, C, B]; rw [hrq, htv]; ring
  have hHb : 2 * Hb = N - L := by
    rw [hN]; dsimp [Hb, C, L]; rw [hrq, hsp]; ring
  have hHg : 2 * Hg = N - u := by
    rw [hN]; dsimp [Hg, C, u]; rw [hrq]; ring
  have hKa : 2 * Ka = (2 * N + 1) - (2 * B - 1) := by dsimp [Ka]; omega
  have hKb : 2 * Kb = (2 * N + 1) - (2 * L - s - 1) := by dsimp [Kb]; omega
  have hKg : 2 * Kg = (2 * N + 1) - u := by
    dsimp [Kg]
    have he : u = 2 * (q * (s + 1)) + 1 := by dsimp [u]; rw [hrq]; ring
    omega
  have hfA' : f (c - 1) = -Ha := by rw [hfA]; omega
  have hfB' : f (c + b - 1) = -Hb := by rw [hfB]; omega
  have hfG' : f (k - 1) = -Hg := by rw [hfG]; omega
  have hgA' : g (c - 1) = -Ka := by rw [hgA]; omega
  have hgB' : g (c + b - 1) = -Kb := by rw [hgB]; omega
  have hgG' : g (k - 1) = -Kg := by rw [hgG]; omega
  have hHa0 : 0 ≤ Ha := by omega
  have hHb0 : 0 ≤ Hb := by omega
  have hHg0 : 0 ≤ Hg := by omega
  have hHgC : Hg ≤ C := by omega
  have hKa0 : 0 ≤ Ka := by dsimp [Ka]; omega
  have hKb0 : 0 ≤ Kb := by dsimp [Kb]; omega
  have hKg0 : 0 ≤ Kg := by dsimp [Kg]; positivity
  have hKgN : Kg ≤ N := by omega
  have hC0 : 0 ≤ C := by omega
  let m := (C / u).toNat
  let G := C % u
  have hm0 : 0 ≤ C / u := Int.ediv_nonneg hC0 (by omega)
  have hmc : (m : ℤ) = C / u := Int.toNat_of_nonneg hm0
  have hG0 : 0 ≤ G := Int.emod_nonneg C (by omega)
  have hGu : G < u := Int.emod_lt_of_pos C (by omega)
  have hdivision : C = u * (m : ℤ) + G := by
    have he := Int.emod_add_mul_ediv C u
    rw [← hmc] at he
    dsimp only [G]
    nlinarith only [he]
  have hcapacity : m < 2 ^ (c - 1) := by
    have hprod : C < u * vhalf := by
      have ht0 : 0 < vhalf := by dsimp [vhalf]; positivity
      have he : u * vhalf - C = vhalf * (r + 1) + 1 := by
        dsimp [u, C]; rw [hrq, htv]; ring
      have hpos : 0 ≤ vhalf * (r + 1) := by positivity
      omega
    have hm : (m : ℤ) < vhalf := by
      by_contra hn
      have he := mul_le_mul_of_nonneg_left (show vhalf ≤ (m : ℤ) by omega) (show 0 ≤ u by omega)
      omega
    exact_mod_cast hm
  let z := 2 ^ (a - 1) - 1
  have hzcap : z < 2 ^ (a - 1) := by dsimp [z]; have : 0 < (2 : ℕ) ^ (a - 1) := by positivity; omega
  have hzc : (z : ℤ) = q - 1 := by
    dsimp [z, q]
    rw [Nat.cast_sub (show 1 ≤ (2 : ℕ) ^ (a - 1) by positivity)]
    norm_cast
  let P := mask_labels (c - 1) 0 m hcapacity
  let T := mask_labels (a - 1) (c + b) z hzcap
  let Q := Finset.range k \ (P ∪ T ∪ {c + b - 1, c - 1, k - 1})
  let word := P.toList ++ (c + b - 1) :: Q.toList ++ (c - 1) :: T.toList ++ [k - 1]
  let plus := P.toList ++ (c + b - 1) :: k :: Q.toList ++ (c - 1) :: T.toList ++ [k - 1]
  have hPbound {i : ℕ} (hi : i ∈ P) : i < c - 1 := by
    have hh := mask_labels_bound hi; omega
  have hTbound {i : ℕ} (hi : i ∈ T) : c + b ≤ i ∧ i < k - 1 := by
    have hh := mask_labels_bound hi; dsimp [k]; omega
  have hPsub : P ⊆ Finset.range k := by intro i hi; have := hPbound hi; exact Finset.mem_range.mpr (by dsimp [k]; omega)
  have hTsub : T ⊆ Finset.range k := by intro i hi; have := hTbound hi; exact Finset.mem_range.mpr (by omega)
  have hPT : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have := hPbound hi; have := hTbound hj; omega
  have hPn : ∀ i ∈ P, i ≠ c + b - 1 ∧ i ≠ c - 1 ∧ i ≠ k - 1 := by
    intro i hi; have := hPbound hi; dsimp [k]; omega
  have hTn : ∀ i ∈ T, i ≠ c + b - 1 ∧ i ≠ c - 1 ∧ i ≠ k - 1 := by
    intro i hi; have := hTbound hi; omega
  have hp : word.Perm (List.range k) := by
    have hi := labelled_permutation k (c + b - 1) (c - 1) (k - 1) P T hPsub hTsub hPT
      (by dsimp [k]; omega) (by dsimp [k]; omega) hPn hTn
    change (P.toList ++ (c + b - 1) :: T.toList ++ (c - 1) :: Q.toList ++ [k - 1]).Perm _ at hi
    have he : (P.toList ++ [c + b - 1] ++ Q.toList ++ [c - 1] ++ T.toList ++ [k - 1]).Perm
        (P.toList ++ [c + b - 1] ++ T.toList ++ [c - 1] ++ Q.toList ++ [k - 1]) := by
      apply Multiset.coe_eq_coe.mp
      simp only [← Multiset.coe_add]
      ac_rfl
    exact (by simpa only [word, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using he).trans hi
  have hplus : plus.Perm (List.range (k + 1)) := by
    have he : plus.Perm (word ++ [k]) := by
      have he' : (P.toList ++ [c + b - 1] ++ [k] ++ Q.toList ++ [c - 1] ++ T.toList ++ [k - 1]).Perm
          ((P.toList ++ [c + b - 1] ++ Q.toList ++ [c - 1] ++ T.toList ++ [k - 1]) ++ [k]) := by
        apply Multiset.coe_eq_coe.mp
        simp only [← Multiset.coe_add]
        ac_rfl
      simpa only [plus, word, List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append] using he'
    exact he.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have hWbase : 0 ≤ 2 * L - s - 1 := by
    have hst : 0 ≤ s * t := by positivity
    dsimp [L]; nlinarith
  have hpositive (i : ℕ) (hi : i < k)
      (hn : i ≠ c - 1 ∧ i ≠ c + b - 1 ∧ i ≠ k - 1) : 0 ≤ f i ∧ 0 ≤ g i := by
    by_cases h1 : i < c - 1
    · obtain ⟨hf, hg⟩ := hU i h1
      rw [hf, hg]; constructor <;> positivity
    · by_cases h2 : i < c + b - 1
      · have he : i = c + (i - c) := by omega
        obtain ⟨hf, hg⟩ := hV (i - c) (by omega)
        rw [he, hf, hg]
        have hbb : 0 ≤ 2 * B - 1 := by omega
        constructor <;> positivity
      · have he : i = c + b + (i - (c + b)) := by omega
        obtain ⟨hf, hg⟩ := hW (i - (c + b)) (by dsimp [k] at hi hn; omega)
        rw [he, hf, hg]; constructor <;> positivity
  have hPpos : ∀ i ∈ P.toList, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; have hm := Finset.mem_toList.mp hi
    have hn := hPn i hm
    exact hpositive i (Finset.mem_range.mp (hPsub hm)) ⟨hn.2.1, hn.1, hn.2.2⟩
  have hTpos : ∀ i ∈ T.toList, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; have hm := Finset.mem_toList.mp hi
    have hn := hTn i hm
    exact hpositive i (Finset.mem_range.mp (hTsub hm)) ⟨hn.2.1, hn.1, hn.2.2⟩
  have hQpos : ∀ i ∈ Q.toList, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hm := Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)
    have hn : i ≠ c - 1 ∧ i ≠ c + b - 1 ∧ i ≠ k - 1 := by
      have hh : i ∉ ({c + b - 1, c - 1, k - 1} : Finset ℕ) :=
        fun hh => hm.2 (Finset.mem_union_right _ hh)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
      exact ⟨hh.2.1, hh.1, hh.2.2⟩
    exact hpositive i (Finset.mem_range.mp hm.1) hn
  let x := u * (m : ℤ)
  let xn := 2 * x
  let y := (q - 1) * L
  let yn := (q - 1) * (2 * L - s - 1)
  have hPsum : (P.toList.map f).sum = x ∧ (P.toList.map g).sum = xn := by
    constructor
    · rw [Finset.sum_map_toList]
      exact (mask_labels_sum (c - 1) 0 m hcapacity f u (fun i hi => by simpa using (hU i hi).1)).trans (by dsimp [x]; ring)
    · rw [Finset.sum_map_toList]
      exact (mask_labels_sum (c - 1) 0 m hcapacity g (2 * u) (fun i hi => by simpa using (hU i hi).2)).trans (by dsimp [xn, x]; ring)
  have hTsum : (T.toList.map f).sum = y ∧ (T.toList.map g).sum = yn := by
    constructor
    · rw [Finset.sum_map_toList, mask_labels_sum (a - 1) (c + b) z hzcap f L (fun i hi => (hW i hi).1), hzc]
    · rw [Finset.sum_map_toList, mask_labels_sum (a - 1) (c + b) z hzcap g (2 * L - s - 1) (fun i hi => (hW i hi).2), hzc]
  have hA : 0 < xn - Kb := by
    have hh := floor_margin r s t p C hs (by omega) hsp hcases (by rw [hN] at hNC; omega)
      (power_odd_remainder a b (by omega))
    have he : xn - Kb = s * t + p - 1 - 2 * G := by
      change 2 * (u * (m : ℤ)) - (2 * (C - p * (t + 1)) + p + 1) = _
      have hx : u * (m : ℤ) = C - G := by omega
      rw [hx, hsp]; ring
    rw [he]
    exact hh
  let delta := Hg - y
  let D := Kg - yn
  have hdelta : delta = s * (t - r) + s - r := by
    dsimp [delta, Hg, y, C, L]; rw [hrq]; ring
  have hdelta0 : 0 ≤ delta := by
    rw [hdelta]
    have hh := mul_le_mul_of_nonneg_left htr (show 0 ≤ s by omega)
    have hs1 := mul_le_mul_of_nonneg_left (show 1 ≤ s by omega) (show 0 ≤ r by omega)
    nlinarith
  have hD : D = 2 * delta + r * (s + 1) - s := by
    dsimp [D, Kg, delta, yn, y]; rw [hrq]; ring
  have hcharge : 0 ≤ r * (s + 1) - s := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ r by omega) (show 0 ≤ s + 1 by omega)
    omega
  have hslack : N - Ka - D = t * (r + 1 - 2 * s) + r * (s + 1) - s := by
    rw [hD, hdelta, hN]
    dsimp [Ka, Ha, C]; rw [hrq, htv]; ring
  have hslack0 : 0 < N - Ka - D := by
    rw [hslack]
    have hh : 0 < t * (r + 1 - 2 * s) := mul_pos (by omega) (by omega)
    omega
  have hfirst : Hb ≤ x ∧ x ≤ C := by
    dsimp only [xn, Kb] at hA
    have hx : x = C - G := by dsimp [x]; omega
    constructor <;> omega
  have hfirstn : Kb ≤ xn ∧ xn ≤ N := by
    have ha := hA
    change 0 < 2 * x - Kb at ha
    change Kb ≤ 2 * x ∧ 2 * x ≤ N
    constructor <;> omega
  have htail : y ≤ Hg ∧ Ha + Hg - y ≤ C := by
    have hh : N - Ka = 2 * (C - Ha) := by dsimp [Ka]; omega
    have hd : delta ≤ C - Ha := by omega
    change Hg - y ≤ C - Ha at hd
    change 0 ≤ Hg - y at hdelta0
    constructor <;> omega
  have htailn : yn ≤ Kg ∧ Ka + Kg - yn ≤ N := by dsimp only [D] at hD hslack0; constructor <;> omega
  have hseed : ((1 + 2 ^ a + 2 ^ (a + b) : ℕ) : ℤ) = u := by
    push_cast; dsimp [u, r, s]; rw [pow_add]
  have hzero : ((List.range k).map f).sum = 0 := by
    have hz := ThreeNegativeEqualOuterSourceBridge.source_zero k (1 + 2 ^ a + 2 ^ (a + b)) (by dsimp [k]; omega)
    simpa only [hseed] using hz
  have hzero' : ((List.range (k + 1)).map g).sum = 0 := by
    have hz := ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by dsimp [k]; omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed] using hz
  have hold : InStrip f C 0 word := schedule_from_tail f (List.range k) P.toList Q.toList T.toList
    (c + b - 1) (c - 1) (k - 1) Hb Ha Hg C hp hfB' hfA' hfG'
    hHb0 hHa0 ⟨hHg0, hHgC⟩ (fun i hi => (hPpos i hi).1)
    (fun i hi => (hQpos i hi).1) (fun i hi => (hTpos i hi).1)
    (by simpa only [hPsum.1] using hfirst) (by simpa only [hTsum.1] using htail) hzero
  have hnew : InStrip g N 0 plus := schedule_from_tail g (List.range (k + 1)) P.toList (k :: Q.toList) T.toList
    (c + b - 1) (c - 1) (k - 1) Kb Ka Kg N hplus hgB' hgA' hgG'
    hKb0 hKa0 ⟨hKg0, hKgN⟩ (fun i hi => (hPpos i hi).2)
    (by intro i hi; rcases List.mem_cons.mp hi with rfl | hi
        · rw [hgear]; omega
        · exact (hQpos i hi).2)
    (fun i hi => (hTpos i hi).2)
    (by simpa only [hPsum.2] using hfirstn) (by simpa only [hTsum.2] using htailn) hzero'
  let j := P.toList.length + 1
  have hj : j ≤ k := by
    have hsub : P ⊆ Finset.range (c - 1) := by intro i hi; exact Finset.mem_range.mpr (hPbound hi)
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_range] at hh
    dsimp [j, k]
    simpa only [Finset.length_toList] using (show P.card + 1 ≤ a + b + c by omega)
  have hk : 0 < k := by dsimp [k]; omega
  refine ⟨word.map (label k hk), j, hj, ?_, ?_⟩
  · refine lift_order k (1 + 2 ^ a + 2 ^ (a + b)) hk word hp ?_ ?_
    · simpa only [hseed, hhalf] using hold
    · simpa only [hseed] using hzero
  · have he : earWord k (word.map (label k hk)) j = plus.map (label (k + 1) (by omega)) := by
      have hpre : (P.toList ++ [c + b - 1]).length = j := by simp [j]
      have hw : (P.toList ++ [c + b - 1]) ++ (Q.toList ++ (c - 1) :: T.toList ++ [k - 1]) = word := by
        simp only [word, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
      have hpw : (P.toList ++ [c + b - 1]) ++ k :: (Q.toList ++ (c - 1) :: T.toList ++ [k - 1]) = plus := by
        simp only [plus, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
      simpa only [hw, hpw] using marked_word k j hk (P.toList ++ [c + b - 1])
        (Q.toList ++ (c - 1) :: T.toList ++ [k - 1]) hpre (by rw [hw]; exact hp)
    rw [he]
    refine lift_order (k + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (by omega) plus hplus ?_ ?_
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed, hnewhalf] using hnew
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, hseed] using hzero'

#print axioms actualSource_three_negative_middle_gap_joint_lift
end D5.S3.Combinatorics.Circle.ThreeNegativeMiddleGapJointLift
