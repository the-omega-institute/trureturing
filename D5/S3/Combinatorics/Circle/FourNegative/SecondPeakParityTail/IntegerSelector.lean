/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/IntegerSelector
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Two interlaced integer lattices select an exact bounded parity reserve. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Selection
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Batteries.Tactic.OpenPrivate

/-! Two interlaced integer lattices give exact bounded allocation data.
The Euclidean ceiling retains its negative-input semantics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail

-- Reuse the existing signed ceiling, including its negative-input semantics.
open private ceilDiv
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Selection

private theorem signed_ceiling_bounds (n d : ℤ) (hd : 0 < d) :
    n ≤ d * ceilDiv n d ∧ d * ceilDiv n d < n + d := by
  have rem0 := Int.emod_nonneg (-n) (ne_of_gt hd)
  have remlt := Int.emod_lt_of_pos (-n) hd
  have division := Int.emod_add_mul_ediv (-n) d
  dsimp only [ceilDiv]
  constructor <;> nlinarith only [rem0, remlt, division]

private theorem signed_ceiling_le (n d k : ℤ) (hd : 0 < d)
    (hn : n ≤ d * k) : ceilDiv n d ≤ k := by
  have hfloor : -k ≤ (-n) / d :=
    (Int.le_ediv_iff_mul_le hd).mpr (by nlinarith only [hn])
  dsimp only [ceilDiv]
  omega

/-- Select the smaller of the two first points above B, with its actual branch.
The predecessor in the other lattice proves the sharp union-spacing bound. -/
private theorem interlaced_choice (M A D B : ℤ)
    (hM : 0 < M) (hA : 0 < A) (hAA : 2 * A ≤ M) :
    ∃ p K : ℤ, (p = 0 ∨ p = 1) ∧
      K = ceilDiv (D + B - p * A) M ∧
      (∀ q : ℤ, q = 0 ∨ q = 1 →
        K * M - D + p * A ≤ ceilDiv (D + B - q * A) M * M - D + q * A) ∧
      0 ≤ K * M - D + p * A - B ∧
      K * M - D + p * A - B < M - A := by
  let K0 := ceilDiv (D + B) M
  let K1 := ceilDiv (D + B - A) M
  let C0 := K0 * M - D
  let C1 := K1 * M - D + A
  have hb0 := signed_ceiling_bounds (D + B) M hM
  have hb1 := signed_ceiling_bounds (D + B - A) M hM
  have hg0 : 0 ≤ C0 - B := by
    dsimp only [C0, K0]
    nlinarith only [hb0.1]
  have hg1 : 0 ≤ C1 - B := by
    dsimp only [C1, K1]
    nlinarith only [hb1.1]
  have hMA : 0 < M - A := by omega
  by_cases hc : C0 ≤ C1
  · refine ⟨0, K0, Or.inl rfl, ?_, ?_, ?_, ?_⟩
    · simp only [zero_mul, sub_zero, K0]
    · intro q hq
      rcases hq with rfl | rfl
      · simpa only [zero_mul, sub_zero, add_zero] using (le_refl C0)
      · simpa only [zero_mul, sub_zero, add_zero, one_mul] using hc
    · simpa only [zero_mul, add_zero] using hg0
    · suffices hgap : C0 - B < M - A by
        simpa only [zero_mul, add_zero] using hgap
      by_contra hh
      have hlarge : M - A ≤ C0 - B := le_of_not_gt hh
      have hprev : D + B - A ≤ M * (K0 - 1) := by
        dsimp only [C0] at hlarge
        nlinarith only [hlarge]
      have hk : K1 ≤ K0 - 1 := signed_ceiling_le (D + B - A) M (K0 - 1) hM hprev
      have hm := mul_le_mul_of_nonneg_right hk hM.le
      have hbefore : C1 < C0 := by
        dsimp only [C0, C1]
        nlinarith only [hm, hMA]
      linarith only [hc, hbefore]
  · refine ⟨1, K1, Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · simp only [one_mul, K1]
    · intro q hq
      rcases hq with rfl | rfl
      · have hle : C1 ≤ C0 := by omega
        simpa only [one_mul, zero_mul, sub_zero, add_zero] using hle
      · simpa only [one_mul] using (le_refl C1)
    · simpa only [one_mul] using hg1
    · have hshort : C1 - B < A := by
        by_contra hh
        have hlarge : A ≤ C1 - B := le_of_not_gt hh
        have hprev : D + B ≤ M * K1 := by
          dsimp only [C1] at hlarge
          nlinarith only [hlarge]
        have hk : K0 ≤ K1 := signed_ceiling_le (D + B) M K1 hM hprev
        have hm := mul_le_mul_of_nonneg_right hk hM.le
        have hbefore : C0 < C1 := by
          dsimp only [C0, C1]
          nlinarith only [hm, hA]
        exact hc hbefore.le
      have hgap : C1 - B < M - A := by omega
      simpa only [one_mul] using hgap

/-- The maximum with one retains the zero-gap case rather than truncating it. -/
private theorem positive_round_bounds (n d : ℤ) (hd : 0 < d) (hn : 0 ≤ n) :
    let r := max 1 (ceilDiv n d)
    1 ≤ r ∧ n ≤ d * r ∧ d * r ≤ n + d := by
  let q := ceilDiv n d
  have hb := signed_ceiling_bounds n d hd
  change n ≤ d * q ∧ d * q < n + d at hb
  change 1 ≤ max 1 q ∧ n ≤ d * max 1 q ∧ d * max 1 q ≤ n + d
  by_cases hq : q ≤ 1
  · rw [max_eq_left hq]
    have hm := mul_le_mul_of_nonneg_left hq hd.le
    refine ⟨by omega, ?_, ?_⟩
    · nlinarith only [hb.1, hm]
    · nlinarith only [hn]
  · rw [max_eq_right (show 1 ≤ q by omega)]
    exact ⟨by omega, hb.1, hb.2.le⟩

/-- Exact integer allocation data for the future U,X,W,V physical consumer.
The divisibility premises are actual dyadic input facts. Evenness of u is
retained in the caller contract; evenness of h already suffices for u*h/2.
All division below is integer Euclidean division, never rational division. -/
private theorem integer_tail_selector (u z h : ℤ)
    (hu : 4 ≤ u) (hz : 16 ≤ z) (hh : 2 * z ≤ h)
    (_huEven : (2 : ℤ) ∣ u) (hzEight : (8 : ℤ) ∣ z) (hhEven : (2 : ℤ) ∣ h) :
    let M := 2 * u * (z + 1)
    let A := u * z + 1
    let D := (u ^ 2 - 1) * h
    let B := 15 * u * z / 8
    let J := 2 * (u - 1)
    8 * B = 15 * u * z ∧
    ∃ alpha S delta p K r : ℤ,
      (p = 0 ∨ p = 1) ∧
      K = ceilDiv (D + B - p * A) M ∧
      (∀ q : ℤ, q = 0 ∨ q = 1 →
        K * M - D + p * A ≤ ceilDiv (D + B - q * A) M * M - D + q * A) ∧
      r = max 1 (ceilDiv (K * M - D + p * A - B) J) ∧
      S = 2 * r + p ∧
      alpha = u * h / 2 + r - K ∧
      delta = J * r - (K * M - D + p * A - B) ∧
      0 ≤ K * M - D + p * A - B ∧
      K * M - D + p * A - B < u * z + 2 * u - 1 ∧
      (K * M - D + p * A - B = 0 → r = 1 ∧ delta = J) ∧
      2 ≤ S ∧ 4 * S ≤ 7 * z ∧ S ≤ 7 * z / 4 ∧
      0 < h - S ∧ h - S < h ∧
      0 ≤ delta ∧ delta ≤ J ∧
      (u - 1) * S < 3 * (u - 1) + (u * z + 2 * u - 1) ∧
      M * alpha = (u ^ 2 * z + 1) * h + A * S - B + delta := by
  let M := 2 * u * (z + 1)
  let A := u * z + 1
  let D := (u ^ 2 - 1) * h
  let B := 15 * u * z / 8
  let J := 2 * (u - 1)
  let G := u * z + 2 * u - 1
  have hu0 : 0 < u := by omega
  have hz0 : 0 < z := by omega
  have hM : 0 < M := by
    dsimp only [M]
    exact mul_pos (mul_pos (by norm_num) hu0) (by omega)
  have hA : 0 < A := by
    dsimp only [A]
    exact add_pos (mul_pos hu0 hz0) (by norm_num)
  have hAA : 2 * A ≤ M := by
    dsimp only [A, M]
    nlinarith only [hu]
  have hJ : 0 < J := by dsimp only [J]; omega
  have hBdvd : (8 : ℤ) ∣ 15 * u * z := by
    obtain ⟨v, hv⟩ := hzEight
    refine ⟨15 * u * v, ?_⟩
    rw [hv]
    ring
  have hB : 8 * B = 15 * u * z := Int.mul_ediv_cancel' hBdvd
  have hhalfDvd : (2 : ℤ) ∣ u * h := by
    obtain ⟨v, hv⟩ := hhEven
    refine ⟨u * v, ?_⟩
    rw [hv]
    ring
  have hhalf : 2 * (u * h / 2) = u * h := Int.mul_ediv_cancel' hhalfDvd
  obtain ⟨p, K, hp, hK, hmin, hgap0, hgapWidth⟩ := interlaced_choice M A D B hM hA hAA
  let gap := K * M - D + p * A - B
  have hgapNonneg : 0 ≤ gap := hgap0
  have hgapG : gap < G := by
    change K * M - D + p * A - B < G
    dsimp only [M, A, G] at hgapWidth ⊢
    nlinarith only [hgapWidth]
  let r := max 1 (ceilDiv gap J)
  let S := 2 * r + p
  let alpha := u * h / 2 + r - K
  let delta := J * r - gap
  have hrange := positive_round_bounds gap J hJ hgapNonneg
  have hr1 : 1 ≤ r := hrange.1
  have hroundLow : gap ≤ J * r := hrange.2.1
  have hroundHi : J * r ≤ gap + J := hrange.2.2
  have hp0 : 0 ≤ p := by rcases hp with rfl | rfl <;> omega
  have hp1 : p ≤ 1 := by rcases hp with rfl | rfl <;> omega
  have hS2 : 2 ≤ S := by dsimp only [S]; omega
  have hdelta0 : 0 ≤ delta := by dsimp only [delta]; omega
  have hdeltaJ : delta ≤ J := by dsimp only [delta]; omega
  have hzero : gap = 0 → r = 1 ∧ delta = J := by
    intro hg
    have hceil0 : ceilDiv gap J = 0 := by simp [hg, ceilDiv]
    have hrzero : r = 1 := by simp [r, hceil0]
    refine ⟨hrzero, ?_⟩
    simp only [delta, hrzero, hg, mul_one, sub_zero]
  have hpMul : (u - 1) * p ≤ u - 1 := by
    have hm := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ u - 1 by omega)
    simpa only [mul_one] using hm
  have hSstrict : (u - 1) * S < 3 * (u - 1) + G := by
    dsimp only [S]
    dsimp only [J] at hroundHi
    nlinarith only [hroundHi, hpMul, hgapG]
  have hmargin : 0 ≤ (3 * u - 7) * z - 20 * u + 16 := by
    have hm : 0 ≤ (3 * u - 7) * (z - 16) :=
      mul_nonneg (by omega) (by omega)
    nlinarith only [hm, hu]
  have hcapacity : 4 * (3 * (u - 1) + G) ≤ (u - 1) * (7 * z) := by
    dsimp only [G]
    nlinarith only [hmargin]
  have hS4 : 4 * S ≤ 7 * z := by
    by_contra hhS
    have hbad : 7 * z ≤ 4 * S := by omega
    have hm := mul_le_mul_of_nonneg_left hbad (show 0 ≤ u - 1 by omega)
    nlinarith only [hSstrict, hcapacity, hm]
  have hSdiv : S ≤ 7 * z / 4 := by
    exact (Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 4)).mpr
      (by nlinarith only [hS4])
  have hR0 : 0 < h - S := by omega
  have hRh : h - S < h := by omega
  have hmass : M * (u * h / 2) = u ^ 2 * (z + 1) * h := by
    calc
      M * (u * h / 2) = u * (z + 1) * (2 * (u * h / 2)) := by dsimp only [M]; ring
      _ = u * (z + 1) * (u * h) := by rw [hhalf]
      _ = u ^ 2 * (z + 1) * h := by ring
  have hidentity : M * alpha = (u ^ 2 * z + 1) * h + A * S - B + delta := by
    dsimp only [alpha, S, delta, gap]
    calc
      M * (u * h / 2 + r - K) = M * (u * h / 2) + M * r - M * K := by ring
      _ = u ^ 2 * (z + 1) * h + M * r - M * K := by rw [hmass]
      _ = (u ^ 2 * z + 1) * h + A * (2 * r + p) - B +
          (J * r - (K * M - D + p * A - B)) := by
        dsimp only [M, A, D, J]
        ring
  exact ⟨hB, alpha, S, delta, p, K, r, hp, hK, hmin, rfl, rfl, rfl, rfl,
    hgap0, hgapG, hzero, hS2, hS4, hSdiv, hR0, hRh, hdelta0, hdeltaJ,
    hSstrict, hidentity⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail
