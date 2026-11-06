/- GID: D5/S3/ArithSums/IsraelA103573RootFloor
   generality: I
   mirror-B: D5/B/S3/ArithSums/IsraelA103573RootFloor
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer root-difference thresholds and Israel's A103573 ceiling formula. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.ArithSums.IsraelA103573RootFloor

noncomputable def f (x : ℝ) : ℝ := Real.sqrt x - x ^ (1 / 3 : ℝ)
noncomputable def T (n : ℕ) : ℝ :=
  (n : ℝ)^2 + 2 * (n : ℝ)^(5 / 3 : ℝ) + (7 / 3 : ℝ) * (n : ℝ)^(4 / 3 : ℝ) +
    2 * (n : ℝ) + (110 / 81 : ℝ) * (n : ℝ)^(2 / 3 : ℝ) +
    (182 / 243 : ℝ) * (n : ℝ)^(1 / 3 : ℝ)
def IsSourceSequence (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, IsLeast {k : ℕ | ⌊f (k : ℝ)⌋ = (n : ℤ)} (a n)
def claim : Prop :=
  (∃ a : ℕ → ℕ, IsSourceSequence a) ∧
    ∀ a : ℕ → ℕ, IsSourceSequence a → ∀ n : ℕ,
      (a n : ℤ) = ⌈T n⌉ ∨ (a n : ℤ) = ⌈T n⌉ + 1

private def q (t : ℝ) : ℝ := t^3 - t^2
private def p (n x : ℝ) : ℝ := x * (x + 3*n^2)^2 - ((3*n+1)*x+n^3)^2
private noncomputable def u (y : ℝ) : ℝ :=
  y^6 + 2*y^5 + (7/3:ℝ)*y^4 + 2*y^3 + (110/81:ℝ)*y^2 + (182/243:ℝ)*y

private theorem q_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) : q a < q b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hpos : 0 < b^2 + b*a + a^2 - b - a := by
    have h1 : 0 ≤ b*(b-1) := mul_nonneg hb0.le (by linarith)
    have h2 : 0 ≤ a*(a-1) := mul_nonneg ha0.le (by linarith)
    have h3 : 0 < b*a := mul_pos hb0 ha0
    nlinarith
  have h : 0 < (b-a)*(b^2+b*a+a^2-b-a) := mul_pos (sub_pos.mpr hab) hpos
  dsimp [q]
  nlinarith

private theorem f_repr {x : ℝ} (hx : 0 ≤ x) : f x = q (x^(1/6:ℝ)) := by
  have h3 : (x^(1/6:ℝ))^3 = x^(1/2:ℝ) := by
    rw [← Real.rpow_mul_natCast hx]; norm_num
  have h2 : (x^(1/6:ℝ))^2 = x^(1/3:ℝ) := by
    rw [← Real.rpow_mul_natCast hx]; norm_num
  simp only [f, q, h3, h2, Real.sqrt_eq_rpow]

private theorem f_mono {x z : ℝ} (hx : 1 ≤ x) (hxz : x < z) : f x < f z := by
  rw [f_repr (by linarith), f_repr (by linarith)]
  exact q_mono (Real.one_le_rpow hx (by norm_num))
    (Real.rpow_lt_rpow (by linarith) hxz (by norm_num))

private theorem p_sign {n x : ℝ} (hn : 0 ≤ n) (hx : 0 < x) :
    (p n x < 0 ↔ f x < n) ∧ (0 < p n x ↔ n < f x) := by
  let s := Real.sqrt x
  let b := x^(1/3:ℝ)
  let A := x+3*n^2
  let B := (3*n+1)*x+n^3
  have hs : s^2 = x := Real.sq_sqrt hx.le
  have hb : b^3 = x := by
    dsimp [b]; rw [← Real.rpow_mul_natCast hx.le]; norm_num
  have hs0 : 0 < s := Real.sqrt_pos.2 hx
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hfac : p n x = (s*A-B)*(s*A+B) := by dsimp [p]; nlinarith [sq_nonneg (s*A-B)]
  have hc : s*A-B = (s-n)^3-b^3 := by dsimp [A,B]; nlinarith
  have hpos : 0 < s*A+B := by positivity
  have hlt : p n x < 0 ↔ (s-n)^3 < b^3 := by
    rw [hfac, mul_neg_iff]; constructor
    · rintro (⟨_,h⟩ | ⟨h,_⟩)
      · linarith
      · linarith [hc]
    · intro h; exact Or.inr ⟨by linarith [hc], hpos⟩
  have hgt : 0 < p n x ↔ b^3 < (s-n)^3 := by
    rw [hfac, mul_pos_iff]; constructor
    · rintro (⟨h,_⟩ | ⟨_,h⟩)
      · linarith [hc]
      · linarith
    · intro h; exact Or.inl ⟨by linarith [hc], hpos⟩
  have ho : Odd (3:ℕ) := by decide
  constructor
  · rw [hlt, ho.pow_lt_pow]; dsimp [f]; change s-n < b ↔ s-b < n; constructor <;> intro h <;> linarith
  · rw [hgt, ho.pow_lt_pow]; dsimp [f]; change b < s-n ↔ n < s-b; constructor <;> intro h <;> linarith

private theorem poly_bracket {y : ℝ} (hy : 0 < y) :
    p (y^3) (u y) < 0 ∧ 0 < p (y^3) (u y+1) := by
  have hA : 0 < 8049132 + 23160592*y + 36657612*y^2 + 68637564*y^3 +
      99037836*y^4 + 109705752*y^5 + 105345603*y^6 + 86592078*y^7 + 57395628*y^8 := by positivity
  have hB : 0 < 10746918 + 35584434*y + 7011260*y^2 + 76211271*y^3 +
      110517102*y^4 + 101846862*y^5 + 124128288*y^6 + 129019878*y^7 +
      114292620*y^8 + 114791256*y^9 := by positivity
  have h0 : 14348907 * p (y^3) (u y) = -y^2 *
      (8049132 + 23160592*y + 36657612*y^2 + 68637564*y^3 +
      99037836*y^4 + 109705752*y^5 + 105345603*y^6 + 86592078*y^7 + 57395628*y^8) := by
    dsimp [p,u]; ring
  have h1 : 14348907 * p (y^3) (u y+1) = y *
      (10746918 + 35584434*y + 7011260*y^2 + 76211271*y^3 +
      110517102*y^4 + 101846862*y^5 + 124128288*y^6 + 129019878*y^7 +
      114292620*y^8 + 114791256*y^9) := by
    dsimp [p,u]; ring
  constructor
  · have h := mul_pos (sq_pos_of_pos hy) hA; nlinarith [h0]
  · have h := mul_pos hy hB; nlinarith [h1]

private theorem T_normalize (n : ℕ) : T n = u ((n:ℝ)^(1/3:ℝ)) := by
  have hx : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have h (k : ℕ) : ((n:ℝ)^(1/3:ℝ))^k = (n:ℝ)^((k:ℝ)/3) := by
    rw [← Real.rpow_mul_natCast hx]; congr 1; ring
  dsimp [T,u]
  rw [h 6,h 5,h 4,h 3,h 2]
  norm_num

private theorem T_bracket (n : ℕ) (hn : 0 < n) :
    1 ≤ T n ∧ f (T n) < (n:ℝ) ∧ (n:ℝ) < f (T n+1) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by positivity
  have hT : 1 ≤ T n := by
    dsimp [T]
    have hpow : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ hn1
    have hrest : 0 ≤ 2 * (n:ℝ)^(5/3:ℝ) + (7/3:ℝ)*(n:ℝ)^(4/3:ℝ) +
        2*(n:ℝ) + (110/81:ℝ)*(n:ℝ)^(2/3:ℝ) + (182/243:ℝ)*(n:ℝ)^(1/3:ℝ) := by positivity
    linarith
  have hc : ((n:ℝ)^(1/3:ℝ))^3 = (n:ℝ) := by
    rw [← Real.rpow_mul_natCast hn0.le]; norm_num
  have hh := poly_bracket (Real.rpow_pos_of_pos hn0 (1/3:ℝ))
  rw [← T_normalize n, hc] at hh
  exact ⟨hT, (p_sign hn0.le (by linarith : 0 < T n)).1.mp hh.1,
    (p_sign hn0.le (by linarith : 0 < T n+1)).2.mp hh.2⟩

private theorem threshold (n : ℕ) (hn : 0 < n) :
    ∃ r : ℝ, 1 < r ∧ f r = (n:ℝ) := by
  have hn0 : (0:ℝ) < n := by positivity
  have hcont : ContinuousOn q (Set.Icc (1:ℝ) ((n:ℝ)+1)) := by
    exact ((continuous_id.pow 3).sub (continuous_id.pow 2)).continuousOn
  have hleft : q 1 ≤ (n:ℝ) := by dsimp [q]; linarith
  have hright : (n:ℝ) ≤ q ((n:ℝ)+1) := by
    dsimp [q]
    have : 0 ≤ (n:ℝ)^3 := by positivity
    nlinarith [sq_nonneg (n:ℝ)]
  obtain ⟨t, ht, htn⟩ := intermediate_value_Icc (by linarith : (1:ℝ) ≤ (n:ℝ)+1) hcont ⟨hleft,hright⟩
  have ht1 : 1 < t := by
    have : t ≠ 1 := by intro h; subst t; norm_num [q] at htn; linarith
    exact lt_of_le_of_ne ht.1 (Ne.symm this)
  have ht0 : 0 ≤ t := by linarith
  refine ⟨t^6, ?_, ?_⟩
  · exact one_lt_pow₀ ht1 (by decide)
  · dsimp [f]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul ht0, ← Real.rpow_natCast_mul ht0]
    norm_num
    exact htn

private theorem threshold_bracket (n : ℕ) (hn : 0 < n) (r : ℝ)
    (hr : 1 < r) (hfr : f r = (n:ℝ)) : T n < r ∧ r < T n+1 := by
  obtain ⟨hT,hlo,hhi⟩ := T_bracket n hn
  constructor
  · by_contra h
    have hle : r ≤ T n := le_of_not_gt h
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [← heq,hfr] at hlo; exact (lt_irrefl _ hlo)
    · have := f_mono hr.le hlt; linarith
  · by_contra h
    have hle : T n+1 ≤ r := le_of_not_gt h
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq,hfr] at hhi; exact (lt_irrefl _ hhi)
    · have := f_mono (by linarith : 1 ≤ T n+1) hlt; linarith

private theorem positive_candidate (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, IsLeast {j : ℕ | ⌊f (j:ℝ)⌋ = (n:ℤ)} k ∧
      ((k:ℤ) = ⌈T n⌉ ∨ (k:ℤ) = ⌈T n⌉+1) := by
  obtain ⟨r,hr,hfr⟩ := threshold n hn
  obtain ⟨hTr,hrT⟩ := threshold_bracket n hn r hr hfr
  let k : ℕ := (⌈r⌉ : ℤ).toNat
  have hkcast : (k:ℤ) = ⌈r⌉ := Int.toNat_of_nonneg (Int.ceil_nonneg (by linarith : 0 ≤ r))
  have hkreal : (k:ℝ) = (⌈r⌉:ℝ) := by exact_mod_cast hkcast
  have hrk : r ≤ (k:ℝ) := by rw [hkreal]; exact Int.le_ceil r
  have hkr : (k:ℝ) < r+1 := by rw [hkreal]; exact Int.ceil_lt_add_one r
  have hlow : (n:ℝ) ≤ f (k:ℝ) := by
    rcases eq_or_lt_of_le hrk with heq | hlt
    · rw [← heq,hfr]
    · exact (hfr ▸ f_mono hr.le hlt).le
  have hsqrt : Real.sqrt (k:ℝ) < Real.sqrt r + 1 := by
    apply (Real.sqrt_lt (by positivity) (by positivity)).2
    have hs := Real.sq_sqrt (by linarith : 0 ≤ r)
    have hp := Real.sqrt_nonneg r
    nlinarith
  have hcube : r^(1/3:ℝ) ≤ (k:ℝ)^(1/3:ℝ) :=
    Real.rpow_le_rpow (by linarith) hrk (by norm_num)
  have hhigh : f (k:ℝ) < (n:ℝ)+1 := by dsimp [f] at *; linarith
  have hfloor : ⌊f (k:ℝ)⌋ = (n:ℤ) := Int.floor_eq_iff.mpr (by exact_mod_cast And.intro hlow hhigh)
  refine ⟨k, ⟨hfloor, ?_⟩, ?_⟩
  · intro j hj
    by_contra hnot
    have hjk : j < k := Nat.lt_of_not_ge hnot
    have hjkz : (j:ℤ) < ⌈r⌉ := by rw [← hkcast]; exact_mod_cast hjk
    have hjr : (j:ℝ) < r := Int.lt_ceil.mp hjkz
    have hjf : f (j:ℝ) < (n:ℝ) := by
      by_cases hj0 : j=0
      · subst j; norm_num [f]; exact_mod_cast hn
      · have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        rw [← hfr]; exact f_mono hj1 hjr
    have := (Int.floor_eq_iff.mp hj).1
    norm_cast at this
    linarith
  · have hlo : ⌈T n⌉ ≤ (k:ℤ) := by rw [hkcast]; exact Int.ceil_le_ceil hTr.le
    have hhi : (k:ℤ) ≤ ⌈T n⌉+1 := by
      rw [hkcast]
      have := Int.ceil_le_ceil hrT.le
      simpa only [Int.ceil_add_one] using this
    omega

private theorem candidate (n : ℕ) :
    ∃ k : ℕ, IsLeast {j : ℕ | ⌊f (j:ℝ)⌋ = (n:ℤ)} k ∧
      ((k:ℤ) = ⌈T n⌉ ∨ (k:ℤ) = ⌈T n⌉+1) := by
  by_cases hn : n=0
  · subst n
    refine ⟨0, ⟨?_, ?_⟩, Or.inl ?_⟩
    · norm_num [f]
    · intro j _; exact Nat.zero_le j
    · norm_num [T]
  · exact positive_candidate n (Nat.pos_of_ne_zero hn)

theorem result : claim := by
  classical
  have hex : ∃ a : ℕ → ℕ, IsSourceSequence a := by
    refine ⟨fun n => Classical.choose (candidate n), ?_⟩
    intro n
    exact (Classical.choose_spec (candidate n)).1
  refine ⟨hex, ?_⟩
  intro a ha n
  obtain ⟨k,hk,hformula⟩ := candidate n
  have heq : a n = k := (ha n).unique hk
  simpa only [heq] using hformula

end D5.S3.ArithSums.IsraelA103573RootFloor
