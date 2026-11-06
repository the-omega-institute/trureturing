/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19Stabilizer
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: All-r exceptional19 full physical integer-zero family has trivial rotation stabilizer. -/
/- Ordinary proof input: exceptional19-all-r-trivial-stabilizer-pro-ordinary-proof-20261106.txt
SHA256 2e789336d445d47cf067b23a7db5464e4388abee8ca31cbf0dc1b0fd9bdc8db6.
This mathematical input is not kernel evidence. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer.Basic
public import D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
import all D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
public import D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
import all D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
public import D5.S3.Combinatorics.Circle.Orbit.MersennePhaseRotationStabilizer
import all D5.S3.Combinatorics.Circle.Orbit.MersennePhaseRotationStabilizer
public import D5.S3.Combinatorics.Circle.Orbit.MersennePhaseThreeTrace
import all D5.S3.Combinatorics.Circle.Orbit.MersennePhaseThreeTrace
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Tactic

/-! # Full exceptional19 physical rotational stabilizer

Every original physical subset and every natural exponent remain in scope.
The all-r profile and its unique cyclic marker are derived inside the proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer

open scoped BigOperators
open SourceWidth ZeroSumSubsets
open private rotate_pow_val from D5.S3.Combinatorics.Circle.Orbit.MersennePhaseRotationStabilizer open private centered_scaled from D5.S3.Combinatorics.Circle.Orbit.MersennePhaseThreeTrace open private from D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
open D5.S3.Combinatorics.Circle.ZeroSumSubsets (mask_surjective mask_as_geom)
open private pow_rotate_mod image_proper mask_lt_of_ne_univ from D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets

private def s19 (j : ℕ) : ℤ := (2 ^ (j % 18) % 19 : ℕ)
private def z19 (j : ℕ) : ℤ := 12 * s19 j % 19
private def W0 (j : ℕ) : ℤ := (2*z19 j-5*s19 j)/19
private def W1 (j : ℕ) : ℤ := (3*s19 j-5*z19 j)/19
private def W2 (j : ℕ) : ℤ := (2*s19 j+3*z19 j)/19
private def F0 (j : ℕ) : ℤ := W0 j - 2*z19 j/19 + 8*s19 j/19 - 4*s19 j/19
private def F1 (j : ℕ) : ℤ := W1 j + 8*z19 j/19 - 4*z19 j/19 - 4*s19 j/19
private def F2 (j : ℕ) : ℤ := W2 j - 2*s19 j/19 - 4*z19 j/19

private def P0 : ℕ → ℤ
  | 4 => -1
  | 13 => 1
  | _ => 0
private def P1 : ℕ → ℤ
  | 4 | 7 | 9 | 10 | 11 | 12 | 14 | 15 | 17 => -1
  | _ => 0
private def P2 : ℕ → ℤ
  | 3 | 4 | 5 | 6 | 8 | 9 | 10 | 11 | 16 => 1
  | _ => 0

private theorem residue_data (j : ℕ) :
    1 ≤ s19 j ∧ s19 j ≤ 18 ∧ 1 ≤ z19 j ∧ z19 j ≤ 18 ∧
    (11*z19 j+s19 j)%19=0 ∧ (12*s19 j-z19 j)%19=0 ∧
    19*W0 j=2*z19 j-5*s19 j ∧
    19*W1 j=3*s19 j-5*z19 j ∧
    19*W2 j=2*s19 j+3*z19 j ∧
    (∀ ell : ℤ, ell=2 ∨ ell=4 ∨ ell=8 →
      1 ≤ ell*s19 j%19 ∧ ell*s19 j%19 ≤ 18 ∧
      1 ≤ ell*z19 j%19 ∧ ell*z19 j%19 ≤ 18) ∧
    F0 j=P0 (j % 18) ∧
    F1 j=P1 (j % 18) ∧
    F2 j=P2 (j % 18) := by
  have hj : j%18 < 18 := Nat.mod_lt _ (by norm_num)
  interval_cases hqeq : j % 18 <;>
    norm_num [s19,z19,W0,W1,W2,F0,F1,F2,P0,P1,P2,hqeq]

private def Lblock (r j : ℕ) : ℤ := (z19 j * base r + (2 : ℤ)^j)/19
private def Mblock (r j : ℕ) : ℤ := (s19 j * base r + (2 : ℤ)^j-z19 j)/19
private def Ublock (r j : ℕ) : ℤ := ((2 : ℤ)^j-s19 j)/19
private def Qmask (r : ℕ) : ℕ := (base r ^ 2 + base r + 1)/19

private theorem Q_exact (r : ℕ) :
    (19 : ℤ) * Qmask r = (base r : ℤ)^2 + base r + 1 := by
  have hb := (base_facts r).2.1
  have hm : (base r^2+base r+1)%19 = 0 := by
    norm_num [Nat.add_mod,Nat.pow_mod,hb]
  have he := Nat.mod_add_div (base r^2+base r+1) 19
  rw [hm,zero_add] at he
  change 19*Qmask r=base r^2+base r+1 at he
  exact_mod_cast he

private theorem blocks_arithmetic (r j : ℕ) (hj : j < degree r) :
    let B : ℤ := base r
    let n : ℤ := 2^j
    19*Lblock r j=z19 j*B+n ∧
    19*Mblock r j=s19 j*B+n-z19 j ∧
    19*Ublock r j=n-s19 j ∧
    0 ≤ Lblock r j ∧ Lblock r j < B ∧
    0 ≤ Mblock r j ∧ Mblock r j < B ∧
    0 ≤ Ublock r j ∧ 8*Ublock r j < B ∧
    Lblock r j+B*Mblock r j+B^2*Ublock r j=n*Qmask r := by
  dsimp
  obtain ⟨hs0,hs1,hz0,hz1,hres0,hres1,hw0,hw1,hw2,hrest⟩ := residue_data j
  have hb : (4096 : ℤ) ≤ base r := by exact_mod_cast (base_facts r).1
  have hbm : (base r : ℤ)%19=11 := by exact_mod_cast (base_facts r).2.1
  have hnm : (2 : ℤ)^j%19=s19 j := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) (pow_mod19 j)
    simpa only [s19, Int.natCast_mod, Nat.cast_pow, Nat.cast_ofNat] using h
  have hn : (1 : ℤ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hncap : 2*(2 : ℤ)^j ≤ base r := by
    calc
      2*(2 : ℤ)^j = 2^(j+1) := by rw [pow_succ]; ring
      _ ≤ 2^degree r := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = base r := by simp [base]
  have hmods :
      (z19 j*(base r : ℤ)+2^j)%19=0 ∧
      (s19 j*(base r : ℤ)+2^j-z19 j)%19=0 ∧
      ((2 : ℤ)^j-s19 j)%19=0 := by
    have hsmod : s19 j % 19 = s19 j := Int.emod_eq_of_lt (by omega) (by omega)
    have hbEq : (base r : ℤ) ≡ 11 [ZMOD 19] := by
      change (base r : ℤ) % 19 = 11 % 19
      simpa only [show (11 : ℤ) % 19 = 11 by norm_num] using hbm
    have hnEq : (2 : ℤ) ^ j ≡ s19 j [ZMOD 19] := by
      change (2 : ℤ) ^ j % 19 = s19 j % 19
      rw [hnm, hsmod]
    have e0 := (hbEq.mul_left (z19 j)).add hnEq
    have e1 := ((hbEq.mul_left (s19 j)).add hnEq).sub_right (z19 j)
    have e2 := hnEq.sub_right (s19 j)
    change _ % 19 = _ % 19 at e0 e1 e2
    rw [show z19 j * 11 + s19 j = 11 * z19 j + s19 j by ring, hres0] at e0
    rw [show s19 j * 11 + s19 j - z19 j = 12 * s19 j - z19 j by ring, hres1] at e1
    simp only [sub_self, Int.zero_emod] at e2
    exact ⟨e0,e1,e2⟩

  obtain ⟨hLm,hMm,hUm⟩ := hmods
  have hL : 19*Lblock r j=z19 j*(base r : ℤ)+2^j := by
    have h := Int.emod_add_mul_ediv (z19 j*(base r : ℤ)+2^j) 19
    simpa [Lblock,hLm] using h
  have hM : 19*Mblock r j=s19 j*(base r : ℤ)+2^j-z19 j := by
    have h := Int.emod_add_mul_ediv (s19 j*(base r : ℤ)+2^j-z19 j) 19
    simpa [Mblock,hMm] using h
  have hU : 19*Ublock r j=(2 : ℤ)^j-s19 j := by
    have h := Int.emod_add_mul_ediv ((2 : ℤ)^j-s19 j) 19
    simpa [Ublock,hUm] using h
  have hslo := mul_nonneg (show 0 ≤ s19 j-1 by omega) (show (0 : ℤ) ≤ base r by omega)
  have hshi := mul_nonneg (show 0 ≤ 18-s19 j by omega) (show (0 : ℤ) ≤ base r by omega)
  have hzlo := mul_nonneg (show 0 ≤ z19 j-1 by omega) (show (0 : ℤ) ≤ base r by omega)
  have hzhi := mul_nonneg (show 0 ≤ 18-z19 j by omega) (show (0 : ℤ) ≤ base r by omega)
  have hns : s19 j ≤ (2 : ℤ)^j := by omega
  refine ⟨hL,hM,hU,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · omega
  · omega
  · have he : 19*(Lblock r j+(base r : ℤ)*Mblock r j+
          (base r : ℤ)^2*Ublock r j-(2 : ℤ)^j*Qmask r)=0 := by
      linear_combination hL + (base r : ℤ)*hM + (base r : ℤ)^2*hU -
        (2 : ℤ)^j * Q_exact r
    nlinarith only [he]

private theorem interior_floors (B n s z L M ell : ℤ)
    (hB : 4096 ≤ B) (hn : 1 ≤ n) (hncap : 16*n ≤ B)
    (hz : 1 ≤ z ∧ z ≤ 18) (hell : ell=2 ∨ ell=4 ∨ ell=8)
    (hL : 19*L=z*B+n) (hM : 19*M=s*B+n-z)
    (hrs : 1 ≤ ell*s%19 ∧ ell*s%19 ≤ 18)
    (hrz : 1 ≤ ell*z%19 ∧ ell*z%19 ≤ 18) :
    ell*L/B=ell*z/19 ∧ ell*M/B=ell*s/19 := by
  have he0 : 0 < ell := by rcases hell with rfl | rfl | rfl <;> norm_num
  have he8 : ell ≤ 8 := by rcases hell with rfl | rfl | rfl <;> norm_num
  have henz := mul_nonneg (show 0 ≤ ell by omega) (show 0 ≤ n by omega)
  have hencap := mul_nonneg (show 0 ≤ 8-ell by omega) (show 0 ≤ n by omega)
  have hezlo := mul_nonneg (show 0 ≤ ell by omega) (show 0 ≤ z by omega)
  have hezhi := mul_nonneg (show 0 ≤ 8-ell by omega) (show 0 ≤ z by omega)
  have henzhi : 2*(ell*n) ≤ B := by nlinarith
  have hez144 : ell*z ≤ 144 := by nlinarith
  have erL : 19*(ell*L-(ell*z/19)*B) = (ell*z%19)*B+ell*n := by
    have he := Int.emod_add_mul_ediv (ell*z) 19
    linear_combination ell*hL - B*he
  have erM : 19*(ell*M-(ell*s/19)*B) = (ell*s%19)*B+ell*(n-z) := by
    have he := Int.emod_add_mul_ediv (ell*s) 19
    linear_combination ell*hM - B*he
  have hrl0 := mul_nonneg (show 0 ≤ ell*z%19-1 by omega) (show 0 ≤ B by omega)
  have hrl1 := mul_nonneg (show 0 ≤ 18-ell*z%19 by omega) (show 0 ≤ B by omega)
  have hrm0 := mul_nonneg (show 0 ≤ ell*s%19-1 by omega) (show 0 ≤ B by omega)
  have hrm1 := mul_nonneg (show 0 ≤ 18-ell*s%19 by omega) (show 0 ≤ B by omega)
  constructor <;> apply floor_unique (by omega) <;> nlinarith

/-- Pro (19)--(23), with the exact boundary floors retained. -/
private theorem block_floors (r j : ℕ) (hj : j < degree r) :
    let B : ℤ := base r
    let L := Lblock r j
    let M := Mblock r j
    (2*M/B=2*s19 j/19) ∧ (4*M/B=4*s19 j/19) ∧ (8*M/B=8*s19 j/19) ∧
    (2*L/B=2*z19 j/19+(if j=degree r-1 then 1 else 0)) ∧
    (4*L/B=4*z19 j/19+(if j=degree r-2 then 1 else 0)+(if j=degree r-1 then 1 else 0)) ∧
    (8*L/B=8*z19 j/19+(if j=degree r-3 then 1 else 0)+
      (if j=degree r-2 then 1 else 0)+(if j=degree r-1 then 1 else 0)) := by
  dsimp
  have hd : 12 ≤ degree r := by simp [degree]
  obtain ⟨hL,hM,hU,hrest⟩ := blocks_arithmetic r j hj
  obtain ⟨hs0,hs1,hz0,hz1,hres0,hres1,hw0,hw1,hw2,hres,hwords⟩ := residue_data j
  have hb : (4096 : ℤ) ≤ base r := by exact_mod_cast (base_facts r).1
  have hn : (1 : ℤ) ≤ 2^j := one_le_pow₀ (by norm_num)
  by_cases hi : j+4 ≤ degree r
  · have hcap : 16*(2 : ℤ)^j ≤ base r := by
      calc
        16*(2 : ℤ)^j = 2^(j+4) := by norm_num [pow_add]; ring
        _ ≤ 2^degree r := pow_le_pow_right₀ (by norm_num) hi
        _ = base r := by simp [base]
    have h2 := interior_floors (base r) (2^j) (s19 j) (z19 j)
      (Lblock r j) (Mblock r j) 2 hb hn hcap ⟨hz0,hz1⟩ (by decide) hL hM
      ⟨(hres 2 (by decide)).1,(hres 2 (by decide)).2.1⟩
      ⟨(hres 2 (by decide)).2.2.1,(hres 2 (by decide)).2.2.2⟩
    have h4 := interior_floors (base r) (2^j) (s19 j) (z19 j)
      (Lblock r j) (Mblock r j) 4 hb hn hcap ⟨hz0,hz1⟩ (by decide) hL hM
      ⟨(hres 4 (by decide)).1,(hres 4 (by decide)).2.1⟩
      ⟨(hres 4 (by decide)).2.2.1,(hres 4 (by decide)).2.2.2⟩
    have h8 := interior_floors (base r) (2^j) (s19 j) (z19 j)
      (Lblock r j) (Mblock r j) 8 hb hn hcap ⟨hz0,hz1⟩ (by decide) hL hM
      ⟨(hres 8 (by decide)).1,(hres 8 (by decide)).2.1⟩
      ⟨(hres 8 (by decide)).2.2.1,(hres 8 (by decide)).2.2.2⟩
    have hn1 : j ≠ degree r-1 := by omega
    have hn2 : j ≠ degree r-2 := by omega
    have hn3 : j ≠ degree r-3 := by omega
    simp only [if_neg hn1,if_neg hn2,if_neg hn3,add_zero]
    exact ⟨h2.2,h4.2,h8.2,h2.1,h4.1,h8.1⟩
  · have hc : j=degree r-3 ∨ j=degree r-2 ∨ j=degree r-1 := by omega
    have hshift (q : ℕ) (hq : j+q=degree r) : (2 : ℤ)^q * 2^j=base r := by
      rw [← pow_add,show q+j=degree r by omega]
      norm_cast
    rcases hc with hj3 | hj2 | hj1
    · have he := hshift 3 (by omega)
      have hjm : j%18=9 := by dsimp [degree] at hj3; omega
      have hs : s19 j=18 := by norm_num [s19,hjm]
      have hz : z19 j=7 := by norm_num [z19,hs]
      have hn2 : j ≠ degree r-2 := by dsimp [degree] at *; omega
      have hn3 : j = degree r-3 := by dsimp [degree] at *; omega
      have hn1 : j ≠ degree r-1 := by dsimp [degree] at *; omega
      simp only [hs,hz] at hL hM ⊢
      simp only [if_neg hn1,if_neg hn2,if_pos hn3]
      norm_num at he ⊢
      refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
        apply floor_unique (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 4096) hb) <;>
          linarith only [hL,hM,he,hb]
    · have he := hshift 2 (by omega)
      have hjm : j%18=10 := by dsimp [degree] at hj2; omega
      have hs : s19 j=17 := by norm_num [s19,hjm]
      have hz : z19 j=14 := by norm_num [z19,hs]
      have hn2 : j = degree r-2 := by dsimp [degree] at *; omega
      have hn3 : j ≠ degree r-3 := by dsimp [degree] at *; omega
      have hn1 : j ≠ degree r-1 := by dsimp [degree] at *; omega
      simp only [hs,hz] at hL hM ⊢
      simp only [if_neg hn1,if_pos hn2,if_neg hn3]
      norm_num at he ⊢
      refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
        apply floor_unique (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 4096) hb) <;>
          linarith only [hL,hM,he,hb]
    · have he := hshift 1 (by omega)
      have hjm : j%18=11 := by dsimp [degree] at hj1; omega
      have hs : s19 j=15 := by norm_num [s19,hjm]
      have hz : z19 j=9 := by norm_num [z19,hs]
      have hn2 : j ≠ degree r-2 := by dsimp [degree] at *; omega
      have hn3 : j ≠ degree r-3 := by dsimp [degree] at *; omega
      have hn1 : j = degree r-1 := by dsimp [degree] at *; omega
      simp only [hs,hz] at hL hM ⊢
      simp only [if_pos hn1,if_neg hn2,if_neg hn3]
      norm_num at he ⊢
      refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
        apply floor_unique (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 4096) hb) <;>
          linarith only [hL,hM,he,hb]

private theorem mask_turn_mod {k : ℕ} (hk : 2 ≤ k) (a : ℕ) (ha : a < k)
    (A : Finset (Fin k)) :
    (mask (turn a A) : ℤ) ≡ (2 : ℤ)^a * mask A [ZMOD modulus k] := by
  classical
  have h := Int.ModEq.sum (s := A) (fun i _ => pow_rotate_mod hk ha i)
  simpa only [turn,rot,mask,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,
    Finset.sum_image (fun _ _ _ _ h => (rot k a).injective h),
    Finset.mul_sum] using h

private theorem modulus_pow (r : ℕ) :
    modulus (3*degree r) = ((2^(3*degree r)-1 : ℕ) : ℤ) := by
  have hp : 1 ≤ (2 : ℕ)^(3*degree r) := Nat.one_le_two_pow
  simp only [modulus, Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

private theorem Q_bounds (r : ℕ) :
    0 < Qmask r ∧ Qmask r < 2^(3*degree r)-1 := by
  have he := Q_exact r
  obtain ⟨hg,hH,hodd⟩ := centered_parameters r
  have hq : (0 : ℤ) < Qmask r := by nlinarith only [he,hH]
  have hB : (4096 : ℤ) ≤ base r := by exact_mod_cast (base_facts r).1
  have hlt : (Qmask r : ℤ) < modulus (3*degree r) := by
    rw [modulus_factor,← he]
    nlinarith [mul_pos (show (0 : ℤ) < 19*((base r : ℤ)-1)-1 by omega) hq]
  rw [modulus_pow] at hlt
  exact ⟨by exact_mod_cast hq,by exact_mod_cast hlt⟩

private theorem Q_bound_pow (r : ℕ) : Qmask r<2^(3*degree r) := by
  have h := (Q_bounds r).2
  have hp : 0<(2 : ℕ)^(3*degree r) := by positivity
  omega

private noncomputable def witness (r : ℕ) : Finset (Fin (3*degree r)) :=
  Classical.choose (mask_surjective (3*degree r) (Qmask r)
    (Q_bound_pow r))

private theorem witness_mask (r : ℕ) : mask (witness r)=Qmask r :=
  Classical.choose_spec (mask_surjective (3*degree r) (Qmask r)
    (Q_bound_pow r))

private theorem shifted_witness_mask (r j : ℕ) (hj : j < degree r) :
    (mask (turn j (witness r)) : ℤ) = (2 : ℤ)^j * Qmask r := by
  have hd : 2 ≤ 3*degree r := by dsimp [degree] <;> omega
  have hm := mask_turn_mod hd j (by omega) (witness r)
  rw [witness_mask] at hm
  have hproper : witness r ≠ Finset.univ := by
    intro he
    have hx := witness_mask r
    rw [he,mask_full] at hx
    have := (Q_bounds r).2
    omega
  have hi := mask_lt_of_ne_univ (turn j (witness r))
    (image_proper (rot (3*degree r) j) (witness r) hproper)
  have him : (mask (turn j (witness r)) : ℤ) < modulus (3*degree r) := by
    rw [modulus_pow]
    exact_mod_cast hi
  have him0 : (0 : ℤ) ≤ mask (turn j (witness r)) := by positivity
  have hncap : 2*(2 : ℤ)^j ≤ base r := by
    calc
      2*(2 : ℤ)^j = 2^(j+1) := by rw [pow_succ]; ring
      _ ≤ 2^degree r := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = base r := by simp [base]
  have hb : (4096 : ℤ) ≤ base r := by exact_mod_cast (base_facts r).1
  have hq : (0 : ℤ) < Qmask r := by exact_mod_cast (Q_bounds r).1
  have hsmall : (2 : ℤ)^j * Qmask r < modulus (3*degree r) := by
    calc
      (2 : ℤ)^j * Qmask r < (19*((base r : ℤ)-1))*Qmask r :=
        mul_lt_mul_of_pos_right (by omega) hq
      _ = ((base r : ℤ)-1) * (19*Qmask r) := by ring
      _ = modulus (3*degree r) := by rw [Q_exact,modulus_factor]
  change (mask (turn j (witness r)) : ℤ)%modulus (3*degree r) =
    ((2 : ℤ)^j*Qmask r)%modulus (3*degree r) at hm
  rw [Int.emod_eq_of_lt him0 him,
    Int.emod_eq_of_lt (by positivity) hsmall] at hm
  exact hm

private theorem digits_unique (B l m u L M U : ℤ) (hB : 0 < B)
    (hl : 0 ≤ l ∧ l < B) (hm : 0 ≤ m ∧ m < B)
    (hL : 0 ≤ L ∧ L < B) (hM : 0 ≤ M ∧ M < B)
    (he : l+B*m+B^2*u=L+B*M+B^2*U) : l=L ∧ m=M ∧ u=U := by
  have he0 := congrArg (fun x : ℤ => x%B) he
  have heL : l=L := by
    simpa [Int.add_emod,Int.mul_emod,pow_two,
      Int.emod_eq_of_lt hl.1 hl.2,Int.emod_eq_of_lt hL.1 hL.2] using he0
  have he1 : m+B*u=M+B*U := by
    apply mul_left_cancel₀ (ne_of_gt hB)
    nlinarith only [he,heL]
  have heM : m=M := by
    have h := congrArg (fun x : ℤ => x%B) he1
    simpa [Int.add_emod,Int.mul_emod,
      Int.emod_eq_of_lt hm.1 hm.2,Int.emod_eq_of_lt hM.1 hM.2] using h
  refine ⟨heL,heM,?_⟩
  apply mul_left_cancel₀ (ne_of_gt hB)
  linarith only [he1,heM]

private theorem witness_blocks (r j : ℕ) (hj : j < degree r) :
    let A := turn j (witness r)
    (mask (slice 0 A) : ℤ)=Lblock r j ∧
    (mask (slice 1 A) : ℤ)=Mblock r j ∧
    (mask (slice 2 A) : ℤ)=Ublock r j := by
  dsimp
  have hd : 0 < degree r := by dsimp [degree] <;> omega
  have hb : (0 : ℤ) < base r := by exact_mod_cast pow_pos (by norm_num : 0<(2:ℕ)) (degree r)
  have hbounds (p : Fin 3) :
      0 ≤ (mask (slice p (turn j (witness r))) : ℤ) ∧
      (mask (slice p (turn j (witness r))) : ℤ)<base r := by
    refine ⟨by positivity,?_⟩
    have h := mask_bound (slice p (turn j (witness r)))
    have hpow : 0 < (2 : ℕ)^degree r := by positivity
    exact_mod_cast (show mask (slice p (turn j (witness r)))<base r by
      change mask (slice p (turn j (witness r)))<2^degree r; omega)
  obtain ⟨hL,hM,hU,hL0,hL1,hM0,hM1,hU0,hU1,he⟩ := blocks_arithmetic r j hj
  have hs := mask_slices hd (turn j (witness r))
  rw [shifted_witness_mask r j hj] at hs
  have hp : (2 : ℤ)^degree r=base r := by simp [base]
  have hp2 : (2 : ℤ)^(2*degree r)=(base r : ℤ)^2 := by
    rw [show 2*degree r=degree r*2 by omega,pow_mul,hp]
  rw [hp,hp2] at hs
  exact digits_unique (base r) _ _ _ _ _ _ hb (hbounds 0) (hbounds 1)
    ⟨hL0,hL1⟩ ⟨hM0,hM1⟩ (hs.symm.trans he.symm)

private theorem slices_turn_degree (r : ℕ) (A : Finset (Fin (3*degree r))) :
    slice 0 (turn (degree r) A)=slice 2 A ∧
    slice 1 (turn (degree r) A)=slice 0 A ∧
    slice 2 (turn (degree r) A)=slice 1 A := by
  classical
  have hd : 0 < degree r := by dsimp [degree] <;> omega
  have hrot0 (j : Fin (degree r)) :
      rot (3*degree r) (degree r) (place 0 j)=place 1 j := by
    apply Fin.ext
    rw [rot_val (by omega)]
    dsimp [place]
    rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    omega
  have hrot1 (j : Fin (degree r)) :
      rot (3*degree r) (degree r) (place 1 j)=place 2 j := by
    apply Fin.ext
    rw [rot_val (by omega)]
    dsimp [place]
    rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    omega
  have hrot2 (j : Fin (degree r)) :
      rot (3*degree r) (degree r) (place 2 j)=place 0 j := by
    apply Fin.ext
    rw [rot_val (by omega)]
    dsimp [place]
    have he : 2*degree r+j.val+degree r=j.val+3*degree r := by omega
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    omega
  have hs (p q : Fin 3) (h : ∀ j, rot (3*degree r) (degree r) (place p j)=place q j) :
      slice q (turn (degree r) A)=slice p A := by
    ext j
    simp only [slice,Finset.mem_filter,Finset.mem_univ,true_and,turn,Finset.mem_image]
    constructor
    · rintro ⟨i,hi,he⟩
      have heq : i=place p j := (rot (3*degree r) (degree r)).injective (he.trans (h j).symm)
      simpa [heq] using hi
    · intro hj
      exact ⟨place p j,hj,h j⟩
  exact ⟨hs 2 0 hrot2,hs 0 1 hrot0,hs 1 2 hrot1⟩

private theorem witness_phase_sums (r j : ℕ) (hj : j < degree r) :
    total r (turn j (witness r)) =
      ((base r : ℤ)-1)*charge (base r) (Lblock r j) (Mblock r j) (Ublock r j) ∧
    total r (turn (degree r+j) (witness r)) =
      ((base r : ℤ)-1)*charge (base r) (Ublock r j) (Lblock r j) (Mblock r j) ∧
    total r (turn (2*degree r+j) (witness r)) =
      ((base r : ℤ)-1)*charge (base r) (Mblock r j) (Ublock r j) (Lblock r j) := by
  obtain ⟨h0,h1,h2⟩ := witness_blocks r j hj
  have hs0 := actual_sum_blocks r (turn j (witness r))
  have hs1 := actual_sum_blocks r (turn (degree r) (turn j (witness r)))
  have hs2 := actual_sum_blocks r (turn (degree r) (turn (degree r) (turn j (witness r))))
  obtain ⟨e0,e1,e2⟩ := slices_turn_degree r (turn j (witness r))
  obtain ⟨f0,f1,f2⟩ := slices_turn_degree r (turn (degree r) (turn j (witness r)))
  rw [h0,h1,h2] at hs0
  rw [e0,e1,e2,h0,h1,h2] at hs1
  rw [f0,f1,f2,e0,e1,e2,h0,h1,h2] at hs2
  simp only [turn_add] at hs1 hs2
  rw [show degree r+(degree r+j)=2*degree r+j by omega] at hs2
  exact ⟨hs0,hs1,hs2⟩

/-- The three uncorrected sums in Pro (17) are proved from the block equations,
not assumed as a profile premise. -/
private theorem uncorrected_sums (r j : ℕ) (hj : j < degree r) :
    let B : ℤ := base r
    let H := B^2+B+1
    let L := Lblock r j
    let M := Mblock r j
    let U := Ublock r j
    (2*B-3)*L-(5*B+2)*M+(3*B+5)*U=H*W0 j ∧
    (2*B-3)*U-(5*B+2)*L+(3*B+5)*M=H*W1 j ∧
    (2*B-3)*M-(5*B+2)*U+(3*B+5)*L=H*W2 j := by
  dsimp
  obtain ⟨hL,hM,hU,hrest⟩ := blocks_arithmetic r j hj
  obtain ⟨hs0,hs1,hz0,hz1,hres0,hres1,hw0,hw1,hw2,hrest'⟩ := residue_data j
  constructor
  · have he : 19*((2*(base r : ℤ)-3)*Lblock r j-(5*(base r : ℤ)+2)*Mblock r j+
        (3*(base r : ℤ)+5)*Ublock r j-((base r : ℤ)^2+base r+1)*W0 j)=0 := by
      linear_combination (2*(base r : ℤ)-3)*hL - (5*(base r : ℤ)+2)*hM +
        (3*(base r : ℤ)+5)*hU - ((base r : ℤ)^2+base r+1)*hw0
    nlinarith only [he]
  · constructor
    · have he : 19*((2*(base r : ℤ)-3)*Ublock r j-(5*(base r : ℤ)+2)*Lblock r j+
          (3*(base r : ℤ)+5)*Mblock r j-((base r : ℤ)^2+base r+1)*W1 j)=0 := by
        linear_combination (2*(base r : ℤ)-3)*hU - (5*(base r : ℤ)+2)*hL +
          (3*(base r : ℤ)+5)*hM - ((base r : ℤ)^2+base r+1)*hw1
      nlinarith only [he]
    · have he : 19*((2*(base r : ℤ)-3)*Mblock r j-(5*(base r : ℤ)+2)*Ublock r j+
          (3*(base r : ℤ)+5)*Lblock r j-((base r : ℤ)^2+base r+1)*W2 j)=0 := by
        linear_combination (2*(base r : ℤ)-3)*hM - (5*(base r : ℤ)+2)*hU +
          (3*(base r : ℤ)+5)*hL - ((base r : ℤ)^2+base r+1)*hw2
      nlinarith only [he]

private theorem charge_profile (r j : ℕ) (hj : j < degree r) :
    let B : ℤ := base r
    let H := B^2+B+1
    let L := Lblock r j
    let M := Mblock r j
    let U := Ublock r j
    charge B L M U=H*(F0 j-(if j=degree r-1 then 1 else 0)) ∧
    charge B U L M=H*(F1 j+(if j=degree r-3 then 1 else 0)) ∧
    charge B M U L=H*(F2 j-(if j=degree r-2 then 1 else 0)-
      (if j=degree r-1 then 1 else 0)) := by
  dsimp
  obtain ⟨h0,h1,h2⟩ := uncorrected_sums r j hj
  obtain ⟨f2M,f4M,f8M,f2L,f4L,f8L⟩ := block_floors r j hj
  obtain ⟨hL,hM,hU,hL0,hL1,hM0,hM1,hU0,hU8,hrest⟩ := blocks_arithmetic r j hj
  have hb : (0 : ℤ) < base r := by exact_mod_cast pow_pos (by norm_num : 0<(2:ℕ)) (degree r)
  have f2U : 2*Ublock r j/(base r : ℤ)=0 := by
    apply floor_unique hb <;> omega
  have f4U : 4*Ublock r j/(base r : ℤ)=0 := by
    apply floor_unique hb <;> omega
  have f8U : 8*Ublock r j/(base r : ℤ)=0 := by
    apply floor_unique hb <;> omega
  simp only [charge,h0,h1,h2,f2L,f4L,f8L,f2M,f4M,f8M,f2U,f4U,f8U]
  dsimp [F0,F1,F2]
  constructor
  · ring
  · constructor <;> ring

private def profile (r h : ℕ) : ℤ :=
  if h<degree r then F0 h-(if h=degree r-1 then 1 else 0)
  else if h<2*degree r then F1 (h-degree r)+(if h-degree r=degree r-3 then 1 else 0)
  else F2 (h-2*degree r)-(if h-2*degree r=degree r-2 then 1 else 0)-
    (if h-2*degree r=degree r-1 then 1 else 0)

private theorem actual_profile (r h : ℕ) (hh : h<3*degree r) :
    total r (turn h (witness r))=modulus (3*degree r)*profile r h := by
  by_cases h0 : h<degree r
  · have hs := (witness_phase_sums r h h0).1
    rw [(charge_profile r h h0).1] at hs
    rw [modulus_factor]
    simpa only [profile,if_pos h0,mul_assoc] using hs
  · by_cases h1 : h<2*degree r
    · have hj : h-degree r<degree r := by omega
      have hs := (witness_phase_sums r (h-degree r) hj).2.1
      rw [show degree r+(h-degree r)=h by omega] at hs
      rw [(charge_profile r (h-degree r) hj).2.1] at hs
      rw [modulus_factor]
      simpa only [profile,if_neg h0,if_pos h1,mul_assoc] using hs
    · have hj : h-2*degree r<degree r := by omega
      have hs := (witness_phase_sums r (h-2*degree r) hj).2.2
      rw [show 2*degree r+(h-2*degree r)=h by omega] at hs
      rw [(charge_profile r (h-2*degree r) hj).2.2] at hs
      rw [modulus_factor]
      simpa only [profile,if_neg h0,if_neg h1,mul_assoc] using hs

/-- The zero locations of the proved profile. The endpoint clauses include r=0. -/
private def zeroAt (r h : ℕ) : Prop :=
  (h<degree r ∧ h%18≠4 ∧ h%18≠13 ∧ h≠degree r-1) ∨
  (degree r≤h ∧ h<2*degree r ∧
    ((h-degree r)%18=0 ∨ (h-degree r)%18=1 ∨ (h-degree r)%18=2 ∨
     (h-degree r)%18=3 ∨ (h-degree r)%18=5 ∨ (h-degree r)%18=6 ∨
     (h-degree r)%18=8 ∨ (h-degree r)%18=13 ∨ (h-degree r)%18=16 ∨
     h=2*degree r-3)) ∨
  (2*degree r≤h ∧ h<3*degree r ∧
    ((h-2*degree r)%18=0 ∨ (h-2*degree r)%18=1 ∨ (h-2*degree r)%18=2 ∨
     (h-2*degree r)%18=7 ∨ (h-2*degree r)%18=12 ∨ (h-2*degree r)%18=13 ∨
     (h-2*degree r)%18=14 ∨ (h-2*degree r)%18=15 ∨ (h-2*degree r)%18=17 ∨
     h=3*degree r-2 ∨ h=3*degree r-1))

private theorem phase0_zero (r j : ℕ) (hj : j<degree r) :
    F0 j-(if j=degree r-1 then 1 else 0)=0 ↔
      j%18≠4 ∧ j%18≠13 ∧ j≠degree r-1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,h0,h1,h2⟩ := residue_data j
  rw [h0]
  have hq : j%18<18 := Nat.mod_lt _ (by norm_num)
  dsimp [degree] at *
  interval_cases hqeq : j % 18 <;> norm_num [P0,hqeq] <;> (try split_ifs) <;> norm_num <;> omega

private theorem phase1_zero (r j : ℕ) (hj : j<degree r) :
    F1 j+(if j=degree r-3 then 1 else 0)=0 ↔
      j%18=0 ∨ j%18=1 ∨ j%18=2 ∨ j%18=3 ∨ j%18=5 ∨ j%18=6 ∨
      j%18=8 ∨ j%18=13 ∨ j%18=16 ∨ j=degree r-3 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,h0,h1,h2⟩ := residue_data j
  rw [h1]
  have hq : j%18<18 := Nat.mod_lt _ (by norm_num)
  dsimp [degree] at *
  interval_cases hqeq : j % 18 <;> norm_num [P1,hqeq] <;> (try split_ifs) <;> norm_num <;> omega

private theorem phase2_zero (r j : ℕ) (hj : j<degree r) :
    F2 j-(if j=degree r-2 then 1 else 0)-(if j=degree r-1 then 1 else 0)=0 ↔
      j%18=0 ∨ j%18=1 ∨ j%18=2 ∨ j%18=7 ∨ j%18=12 ∨ j%18=13 ∨
      j%18=14 ∨ j%18=15 ∨ j%18=17 ∨ j=degree r-2 ∨ j=degree r-1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,h0,h1,h2⟩ := residue_data j
  rw [h2]
  have hq : j%18<18 := Nat.mod_lt _ (by norm_num)
  dsimp [degree] at *
  interval_cases hqeq : j % 18 <;> norm_num [P2,hqeq] <;> (try split_ifs) <;> norm_num <;> omega

private theorem profile_zero (r h : ℕ) (hh : h<3*degree r) :
    profile r h=0 ↔ zeroAt r h := by
  by_cases h0 : h<degree r
  · rw [profile,if_pos h0,phase0_zero r h h0]
    dsimp [zeroAt,degree] at *
    omega
  · by_cases h1 : h<2*degree r
    · rw [profile,if_neg h0,if_pos h1,phase1_zero r (h-degree r) (by omega)]
      dsimp [zeroAt,degree] at *
      omega
    · rw [profile,if_neg h0,if_neg h1,phase2_zero r (h-2*degree r) (by omega)]
      dsimp [zeroAt,degree] at *
      omega

private theorem actual_zero_profile (r h : ℕ) :
    total r (turn h (witness r))=0 ↔ zeroAt r (h%(3*degree r)) := by
  have hk : 0<3*degree r := by dsimp [degree] <;> omega
  have hm : h%(3*degree r)<3*degree r := Nat.mod_lt _ hk
  have hturn := turn_period hk h (witness r)
  rw [← hturn,actual_profile r _ hm]
  have hN : modulus (3*degree r)≠0 := by
    rw [modulus_factor]
    exact ne_of_gt (mul_pos (centered_parameters r).1 (centered_parameters r).2.1)
  rw [mul_eq_zero,or_iff_right hN]
  exact profile_zero r _ hm

private def marker (r h : ℕ) : Prop :=
  ¬zeroAt r ((h+(3*degree r-1))%(3*degree r)) ∧
  zeroAt r (h%(3*degree r)) ∧
  zeroAt r ((h+1)%(3*degree r)) ∧
  zeroAt r ((h+2)%(3*degree r)) ∧
  ¬zeroAt r ((h+3)%(3*degree r))

set_option maxHeartbeats 4000000 in
-- The 18 residue branches prove a cyclic predicate with both boundary neighbors.
set_option maxRecDepth 8192 in
/-- This is the sole cyclic run calculation. It proves the full marker
predicate, including the predecessor and successor, for every r. No counts
of runs, finite r controls, or marker uniqueness assumptions are used. -/
private theorem unique_marker (r h : ℕ) (hh : h<3*degree r) :
    marker r h ↔ h=2*degree r := by
  have hk : 0<3*degree r := by dsimp [degree]; omega
  have hsmall (q : ℕ) (hq : q≤3) : zeroAt r q := by
    have hqmod : q%18=q := Nat.mod_eq_of_lt (by omega)
    unfold zeroAt
    left
    dsimp [degree]
    rw [hqmod]
    omega
  by_cases he : h=0
  · subst h
    have hz : zeroAt r ((0+3)%(3*degree r)) := by
      rw [Nat.mod_eq_of_lt (by dsimp [degree]; omega)]
      exact hsmall 3 (by omega)
    apply iff_of_false
    · intro hm
      exact hm.2.2.2.2 hz
    · dsimp [degree]
      omega
  · by_cases hn : h+3<3*degree r
    · have hprev : (h+(3*degree r-1))%(3*degree r)=h-1 := by
        rw [show h+(3*degree r-1)=(h-1)+3*degree r by omega,
          Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      have hnext (q : ℕ) (hq : q≤3) : (h+q)%(3*degree r)=h+q :=
        Nat.mod_eq_of_lt (by omega)
      rw [marker,hprev,Nat.mod_eq_of_lt hh,hnext 1 (by omega),
        hnext 2 (by omega),hnext 3 (by omega)]
      clear hprev hnext hsmall
      dsimp [zeroAt,degree] at *
      have hres : h%18<18 := Nat.mod_lt _ (by norm_num)
      interval_cases hqeq : h%18 <;> omega
    · have hm : (h+3)%(3*degree r)=h+3-3*degree r := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      have hz : zeroAt r ((h+3)%(3*degree r)) := by
        rw [hm]
        exact hsmall _ (by omega)
      apply iff_of_false
      · intro hmark
        exact hmark.2.2.2.2 hz
      · dsimp [degree] at *
        omega

private theorem marker_mod (r h : ℕ) :
    marker r (h%(3*degree r)) ↔ marker r h := by
  simp only [marker,Nat.mod_add_mod,Nat.mod_mod]

/-- Every physical subset is quantified, with the original natural seed and
unrestricted exponent. All arithmetic and profile helpers above are private. -/
theorem actual_zero_family_rotation_iff (r a : ℕ) :
    let d := 18*r+12
    (∀ A : Finset (Fin (3*d)),
      (∑ i ∈ A.image ((finRotate (3*d) : Equiv.Perm (Fin (3*d)))^a),
        SourceWidth.actualSource (3*d) ((2^d-1)*(2^(d+1)-3)) i)=0 ↔
      (∑ i ∈ A, SourceWidth.actualSource (3*d) ((2^d-1)*(2^(d+1)-3)) i)=0) ↔
    (3*d) ∣ a := by
  classical
  change (∀ A : Finset (Fin (3*degree r)),
    total r (turn a A)=0 ↔ total r A=0) ↔ (3*degree r) ∣ a
  have hk : 0<3*degree r := by dsimp [degree] <;> omega
  constructor
  · intro hfamily
    have hz (h : ℕ) :
        zeroAt r ((h+a)%(3*degree r)) ↔ zeroAt r (h%(3*degree r)) := by
      have hs := hfamily (turn h (witness r))
      rw [turn_add,show a+h=h+a by omega] at hs
      simpa only [actual_zero_profile] using hs
    have hmarker (h : ℕ) : marker r (h+a) ↔ marker r h := by
      have hp := hz (h+(3*degree r-1))
      have h0 := hz h
      have h1 := hz (h+1)
      have h2 := hz (h+2)
      have h3 := hz (h+3)
      unfold marker
      refine and_congr ?_ (and_congr h0 (and_congr ?_ (and_congr ?_ ?_)))
      · exact not_congr (by simpa only [Nat.add_right_comm] using hp)
      · simpa only [Nat.add_right_comm] using h1
      · simpa only [Nat.add_right_comm] using h2
      · exact not_congr (by simpa only [Nat.add_right_comm] using h3)
    have hm0 : marker r (2*degree r) :=
      (unique_marker r _ (by omega)).mpr rfl
    have hm1 := (hmarker (2*degree r)).mpr hm0
    have hm2 := (marker_mod r (2*degree r+a)).mpr hm1
    have he := (unique_marker r ((2*degree r+a)%(3*degree r))
      (Nat.mod_lt _ hk)).mp hm2
    have hmod : 2*degree r+a ≡ 2*degree r+0 [MOD 3*degree r] := by
      change (2*degree r+a)%(3*degree r)=(2*degree r+0)%(3*degree r)
      simpa only [add_zero,Nat.mod_eq_of_lt (by omega : 2*degree r<3*degree r)] using he
    exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' (2*degree r) hmod)
  · intro ha A
    rw [turn_of_dvd hk ha]

end D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
