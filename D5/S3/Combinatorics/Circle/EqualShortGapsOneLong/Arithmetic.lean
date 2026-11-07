/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/EqualShortGapsOneLong/Arithmetic
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Exact native charges for arbitrarily many equal short gaps and one long gap. -/
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
open SourceWidth PeriodicShorteningArithmetic
open scoped BigOperators

def width (a p d : ℕ) : ℕ := d + a * (p - 1)

theorem radix_ge (a : ℕ) (ha : 2 ≤ a) : (4 : ℤ) ≤ 2 ^ a := by
  simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha

theorem geom_left (a n : ℕ) (ha : 1 ≤ a) :
    (geom a (n + 1) : ℤ) = (2 : ℤ)^a * geom a n + 1 := by
  have h1 := geom_mul a n ha
  have h2 := geom_mul a (n+1) ha
  rw [pow_succ] at h2
  have hr : (2 : ℤ) ≤ 2 ^ a := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
  nlinarith

theorem geom_split (a n m : ℕ) (ha : 1 ≤ a) :
    (geom a (n+m) : ℤ) = ((2 : ℤ)^a)^m * geom a n + geom a m := by
  have hn := geom_mul a n ha
  have hm := geom_mul a m ha
  have hnm := geom_mul a (n+m) ha
  rw [pow_add] at hnm
  have hr : (2 : ℤ) ≤ 2 ^ a := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
  have he : ((2 : ℤ)^a-1) *
      ((geom a (n+m) : ℤ) - (((2 : ℤ)^a)^m * geom a n + geom a m)) = 0 := by
    linear_combination hnm - ((2 : ℤ)^a)^m * hn - hm
  rcases mul_eq_zero.mp he with h | h
  · omega
  · omega

theorem geom_small (a n : ℕ) (ha : 2 ≤ a) :
    2 * (geom a n : ℤ) < ((2 : ℤ)^a)^n := by
  have h := geom_mul a n (by omega)
  have hR := radix_ge a ha
  have hE := Int.natCast_nonneg (geom a n)
  nlinarith

theorem geom_tail_bound (a n : ℕ) (ha : 2 ≤ a) :
    (geom a (n+1) : ℤ) < 2*((2 : ℤ)^a)^n := by
  rw [geom_succ a n (by omega)]
  have hs := geom_small a n ha
  have hn := Int.natCast_nonneg (geom a n)
  omega

theorem width_ge (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    2 ≤ width a p d ∧ a*p ≤ width a p d := by
  have he : a*p = a*(p-1)+a := by rw [← mul_add]; congr 1; omega
  dsimp [width]
  omega

theorem seed_bound (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    geom a p ≤ 2 ^ (width a p d - 1) - 1 := by
  have hk := width_ge a p d ha hp hd
  have hs := geom_small a p ha
  rw [← pow_mul] at hs
  have hmono := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hk.2
  have hpow : (2 : ℤ) ^ width a p d = 2 * 2 ^ (width a p d - 1) := by
    rw [show width a p d = (width a p d-1)+1 by omega, pow_succ]
    ring
  rw [hpow] at hmono
  have hb : (geom a p : ℤ)+1 ≤ (2 : ℤ)^(width a p d-1) := by omega
  have hb' : geom a p + 1 ≤ 2 ^ (width a p d-1) := by exact_mod_cast hb
  omega

theorem negative_quotient (a p d j : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p)
    (hd : a ≤ d) (hj : j < p) :
    (geom a p : ℤ) / (2 : ℤ)^(width a p d-1-(d-1+a*j)) = geom a (j+1) := by
  have he : width a p d-1-(d-1+a*j) = a*(p-1-j) := by
    dsimp [width]
    have : a*j ≤ a*(p-1) := Nat.mul_le_mul_left a (by omega)
    omega
  rw [he, pow_mul]
  have hs := geom_split a (j+1) (p-1-j) (by omega)
  rw [show j+1+(p-1-j)=p by omega] at hs
  rw [hs, add_comm, Int.add_mul_ediv_left _ _ (by positivity)]
  have hr := geom_small a (p-1-j) ha
  have hzero : (geom a (p-1-j) : ℤ) / ((2 : ℤ)^a)^(p-1-j) = 0 := by
    apply Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _)
    have := Int.natCast_nonneg (geom a (p-1-j))
    omega
  simp only [hzero, zero_add]

theorem long_charge_zero (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p)
    (hd : a ≤ d) (i : Fin (width a p d)) (hi : i.val < d-1) :
    charge (width a p d) (geom a p) i = 0 := by
  have hs := geom_tail_bound a (p-1) ha
  rw [show p-1+1=p by omega, ←pow_mul] at hs
  have hmono : a*(p-1)+1 ≤ width a p d-1-i.val := by dsimp [width]; omega
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hmono
  rw [pow_succ] at hh
  have hzero : (geom a p : ℤ)/(2 : ℤ)^(width a p d-1-i.val)=0 :=
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by linarith)
  simp [charge,hzero]

theorem negative_charge (a p d j : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p)
    (hd : a ≤ d) (hj : j < p) (hlabel : d-1+a*j < width a p d) :
    charge (width a p d) (geom a p) ⟨d-1+a*j,hlabel⟩ =
      ((geom a (j+1) : ℤ)+1)/2 ∧
    2*charge (width a p d) (geom a p) ⟨d-1+a*j,hlabel⟩ =
      (geom a (j+1) : ℤ)+1 := by
  have hodd := geom_left a j (by omega)
  have hpw : (2 : ℤ)^a = 2*2^(a-1) := by
    rw [show a=(a-1)+1 by omega,pow_succ]; ring
  rw [hpw] at hodd
  have hodd' : (geom a (j+1) : ℤ) = 2*(2^(a-1)*(geom a j : ℤ))+1 := by
    linarith [hodd]
  dsimp [charge]
  rw [negative_quotient a p d j ha hp hd hj]
  omega

theorem positive_quotient (a p d j u : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p)
    (hd : a ≤ d) (hj : j+1 < p) (hu : u < a-1) :
    (geom a p : ℤ)/(2 : ℤ)^(width a p d-1-(d+a*j+u)) =
      (2 : ℤ)^(u+1)*geom a (j+1) := by
  let r := p-1-j
  let b : ℤ := 2^(width a p d-1-(d+a*j+u))
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hb : 0 < b := by dsimp [b]; positivity
  have he : width a p d-1-(d+a*j+u) = a*r-1-u := by
    dsimp [width,r]
    have hja : a*(j+1) ≤ a*(p-1) := Nat.mul_le_mul_left a (by omega)
    have hu' : u+1 ≤ a := by omega
    nlinarith
  have hpow : ((2 : ℤ)^a)^r = b*2^(u+1) := by
    dsimp [b]
    rw [he,←pow_mul,←pow_add]
    congr 1
    have : a ≤ a*r := by nlinarith
    omega
  have hs := geom_split a (j+1) r (by omega)
  rw [show j+1+r=p by dsimp [r];omega,hpow] at hs
  have hbmin : 2*(2 : ℤ)^(a*(r-1)) ≤ b := by
    have hemin : a*(r-1)+1 ≤ a*r-1-u := by
      have her : a*r = a*(r-1)+a := by rw [←mul_add]; congr 1;omega
      omega
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hemin
    dsimp [b]
    rw [he]
    simpa only [pow_succ,mul_comm] using h
  have hrem := geom_tail_bound a (r-1) ha
  rw [show r-1+1=r by omega,←pow_mul] at hrem
  have hzero : (geom a r : ℤ)/b=0 :=
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by omega)
  change (geom a p : ℤ)/b = _
  have hs' : (geom a p : ℤ) = geom a r + b*(2^(u+1)*(geom a (j+1) : ℤ)) := by
    rw [hs]; ring
  rw [hs',Int.add_mul_ediv_left _ _ (ne_of_gt hb),hzero,zero_add]

theorem positive_charge (a p d j u : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p)
    (hd : a ≤ d) (hj : j+1 < p) (hu : u < a-1)
    (hlabel : d+a*j+u < width a p d) :
    charge (width a p d) (geom a p) ⟨d+a*j+u,hlabel⟩ =
      (2 : ℤ)^u*geom a (j+1) := by
  dsimp [charge]
  rw [positive_quotient a p d j u ha hp hd hj hu]
  have he : (2 : ℤ)^(u+1)*(geom a (j+1) : ℤ) =
      2*((2 : ℤ)^u*geom a (j+1)) := by rw [pow_succ];ring
  rw [he]
  omega

theorem native_pair (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d)
    (i : Fin (width a p d)) :
    0 ≤ charge (width a p d) (geom a p) i ∧
    actualSource (width a p d) (geom a p) i =
      (2 : ℤ)^i.val*geom a p - ((2 : ℤ)^width a p d-1)*
        charge (width a p d) (geom a p) i ∧
    actualSource (width a p d+1) (2*geom a p) i.castSucc =
      2*actualSource (width a p d) (geom a p) i -
        charge (width a p d) (geom a p) i := by
  obtain ⟨h0,hf,hg⟩ := digit_data (width a p d) (geom a p)
    (width_ge a p d ha hp hd).1 (seed_bound a p d ha hp hd) i
  refine ⟨h0,hf,?_⟩
  convert hg using 1
  unfold actualSource
  congr 1
  simp only [Fin.val_castSucc,Fin.val_mk,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  ring

theorem native_fresh (a p d : ℕ) (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    actualSource (width a p d+1) (2*geom a p) (Fin.last (width a p d)) =
      (geom a p : ℤ) := by
  have hk := (width_ge a p d ha hp hd).1
  have hs := seed_bound a p d ha hp hd
  unfold actualSource
  have he : (2 : ℤ)^(Fin.last (width a p d)).val*(2*geom a p : ℕ) =
      (2 : ℤ)^(width a p d+1)*(geom a p : ℤ) := by
    simp only [Fin.val_last,Nat.cast_mul,Nat.cast_ofNat,pow_succ];ring
  rw [he,centered_full_period]
  obtain ⟨hN,ho⟩ := TwoRunSource.modulus_positive_odd (width a p d+1) (by omega)
  have hh : modulus (width a p d+1)/2 = (2 : ℤ)^width a p d-1 := by
    unfold modulus;rw [pow_succ];omega
  have hs' : (geom a p : ℤ) < (2 : ℤ)^(width a p d-1) := by
    exact_mod_cast (show geom a p < 2^(width a p d-1) by omega)
  have hmono := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show width a p d-1 ≤ width a p d by omega)
  exact centered_unique hN ho (centered_bounds hN ho _) (by rw [hh];constructor <;>omega)
    (centered_mod _ _)

end D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
