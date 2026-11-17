/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19Stabilizer/Basic
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
open private rotate_pow_val from D5.S3.Combinatorics.Circle.Orbit.MersennePhaseRotationStabilizer
open private centered_scaled from D5.S3.Combinatorics.Circle.Orbit.MersennePhaseThreeTrace
open D5.S3.Combinatorics.Circle.ZeroSumSubsets (mask_surjective mask_as_geom)
open private pow_rotate_mod image_proper mask_lt_of_ne_univ from D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets

def degree (r : ℕ) : ℕ := 18 * r + 12
def base (r : ℕ) : ℕ := 2 ^ degree r
def seed (r : ℕ) : ℕ :=
  (2 ^ degree r - 1) * (2 ^ (degree r + 1) - 3)
abbrev rot (k a : ℕ) : Equiv.Perm (Fin k) := (finRotate k) ^ a
def turn {k : ℕ} (a : ℕ) (A : Finset (Fin k)) : Finset (Fin k) :=
  A.image (rot k a)
def total (r : ℕ) (A : Finset (Fin (3 * degree r))) : ℤ :=
  ∑ i ∈ A, actualSource (3 * degree r) (seed r) i

theorem turn_add {k : ℕ} (a b : ℕ) (A : Finset (Fin k)) :
    turn a (turn b A) = turn (a + b) A := by
  classical
  simp only [turn, Finset.image_image, rot, pow_add, Equiv.Perm.coe_mul]

theorem rot_val {k : ℕ} (hk : 0 < k) (a : ℕ) (i : Fin k) :
    (rot k a i).val = (i.val + a) % k := by
  by_cases h1 : k = 1
  · subst k
    have hi : i.val = 0 := by have := i.isLt; omega
    have hv : (rot 1 a i).val = 0 := by have := (rot 1 a i).isLt; omega
    simpa only [hi, Nat.mod_one] using hv
  · exact rotate_pow_val (by omega) a i

private theorem rot_period {k : ℕ} (hk : 0 < k) : rot k k = 1 := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  simp only [rot_val hk, Equiv.Perm.one_apply, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.isLt]

theorem turn_period {k : ℕ} (hk : 0 < k) (a : ℕ) (A : Finset (Fin k)) :
    turn (a % k) A = turn a A := by
  classical
  have he : rot k (a%k)=rot k a := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    simp only [rot_val hk,Nat.add_mod,Nat.mod_mod]
  simp only [turn,he]

theorem turn_of_dvd {k a : ℕ} (hk : 0 < k) (ha : k ∣ a)
    (A : Finset (Fin k)) : turn a A = A := by
  obtain ⟨b,rfl⟩ := ha
  change A.image ((finRotate k)^(k*b))=A
  rw [pow_mul,show (finRotate k)^k=1 from rot_period hk]
  simp

/-- Only the ordinary finite-residue computation is closed by `norm_num`.
The exponent reduction here is valid for every natural exponent. -/
theorem pow_mod19 (j : ℕ) : 2 ^ j % 19 = 2 ^ (j % 18) % 19 := by
  have h18 : 2^18%19=(1 : ℕ) := by norm_num
  have hpow : (2^18)^(j/18)%19=(1 : ℕ) := by
    rw [Nat.pow_mod,h18]
    simp
  calc
    2^j%19=2^(j%18+18*(j/18))%19 := by rw [Nat.mod_add_div]
    _ = 2^(j%18)%19 := by
      rw [pow_add,pow_mul,Nat.mul_mod,hpow]
      simp

theorem base_facts (r : ℕ) :
    4096 ≤ base r ∧ base r % 19 = 11 ∧ base r % 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change 2 ^ 12 ≤ 2 ^ degree r
    exact pow_le_pow_right₀ (by norm_num) (by dsimp [degree] <;> omega)
  · rw [base, pow_mod19]
    have hd : degree r % 18 = 12 := by dsimp [degree] <;> omega
    rw [hd]
    norm_num
  · have hd : degree r = (degree r - 1) + 1 := by dsimp [degree] <;> omega
    rw [base, hd, pow_succ, Nat.mul_mod]
    norm_num

private theorem seed_cast (r : ℕ) :
    (seed r : ℤ) = ((base r : ℤ) - 1) * (2 * (base r : ℤ) - 3) := by
  have hb := (base_facts r).1
  have hnext : (2 : ℕ) ^ (degree r + 1) = 2 * base r := by
    simp [pow_succ, base, Nat.mul_comm]
  change (((base r - 1) * (2 ^ (degree r + 1) - 3) : ℕ) : ℤ) = _
  rw [hnext, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ base r),
    Nat.cast_sub (by omega : 3 ≤ 2 * base r)]
  norm_cast

theorem modulus_factor (r : ℕ) :
    modulus (3 * degree r) =
      ((base r : ℤ) - 1) * ((base r : ℤ) ^ 2 + base r + 1) := by
  unfold modulus
  have hp : (2 : ℤ) ^ (3 * degree r) = (base r : ℤ) ^ 3 := by
    rw [show 3 * degree r = degree r * 3 by omega, pow_mul]
    norm_cast
  rw [hp]
  ring

theorem centered_parameters (r : ℕ) :
    let B : ℤ := base r
    0 < B - 1 ∧ 0 < B ^ 2 + B + 1 ∧
      ((B - 1) * (B ^ 2 + B + 1)) % 2 = 1 := by
  dsimp
  have hb : (4096 : ℤ) ≤ base r := by exact_mod_cast (base_facts r).1
  refine ⟨by omega, by positivity, ?_⟩
  rw [← modulus_factor, modulus]
  have hp : (2 : ℤ) ^ (3 * degree r) % 2 = 0 := by
    have he : 3 * degree r = (3 * degree r - 1) + 1 := by
      dsimp [degree] <;> omega
    rw [he, pow_succ, Int.mul_emod]
    norm_num
  omega

def v0 (d : ℕ) (B x : ℤ) (j : ℕ) : ℤ :=
  (2 * B - 3) * x - (B ^ 2 + B + 1) * (if j = d - 1 then 1 else 0)
def v1 (d : ℕ) (B x : ℤ) (j : ℕ) : ℤ :=
  -(5 * B + 2) * x + (B ^ 2 + B + 1) *
    ((if j = d - 3 then 1 else 0) + (if j = d - 2 then 1 else 0) +
      2 * (if j = d - 1 then 1 else 0))
def v2 (d : ℕ) (B x : ℤ) (j : ℕ) : ℤ :=
  (3 * B + 5) * x - (B ^ 2 + B + 1) *
    ((if j = d - 2 then 1 else 0) + 2 * (if j = d - 1 then 1 else 0))

set_option maxHeartbeats 800000 in
-- Six endpoint interval pairs share a nonlinear normalization budget.
private theorem phase_bounds (r j : ℕ) (hj : j < degree r) :
    let B : ℤ := base r
    let x : ℤ := 2 ^ j
    let H := B ^ 2 + B + 1
    (-H < 2 * v0 (degree r) B x j ∧ 2 * v0 (degree r) B x j < H) ∧
    (-H < 2 * v1 (degree r) B x j ∧ 2 * v1 (degree r) B x j < H) ∧
    (-H < 2 * v2 (degree r) B x j ∧ 2 * v2 (degree r) B x j < H) := by
  dsimp
  have hb : (4096 : ℤ) ≤ base r := by exact_mod_cast (base_facts r).1
  have hd : 12 ≤ degree r := by simp [degree]
  have hx : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hshift (q : ℕ) (hq : j + q = degree r) :
      (2 : ℤ) ^ q * 2 ^ j = base r := by
    rw [← pow_add, show q + j = degree r by omega]
    norm_cast
  by_cases hlow : j + 4 ≤ degree r
  · have h16 : 16 * (2 : ℤ) ^ j ≤ base r := by
      calc
        16 * (2 : ℤ) ^ j = 2 ^ (j + 4) := by norm_num [pow_add]; ring
        _ ≤ 2 ^ degree r := pow_le_pow_right₀ (by norm_num) hlow
        _ = base r := by simp [base]
    have h0 : j ≠ degree r - 1 := by omega
    have h1 : j ≠ degree r - 2 := by omega
    have h2 : j ≠ degree r - 3 := by omega
    simp only [v0, v1, v2, if_neg h0, if_neg h1, if_neg h2,
      mul_zero, zero_add, add_zero, sub_zero]
    have hp0 := mul_nonneg (show 0 ≤ 2 * (base r : ℤ) - 3 by omega)
      (show 0 ≤ (base r : ℤ) - 16 * 2 ^ j by omega)
    have hp1 := mul_nonneg (show 0 ≤ 5 * (base r : ℤ) + 2 by omega)
      (show 0 ≤ (base r : ℤ) - 16 * 2 ^ j by omega)
    have hp2 := mul_nonneg (show 0 ≤ 3 * (base r : ℤ) + 5 by omega)
      (show 0 ≤ (base r : ℤ) - 16 * 2 ^ j by omega)
    have hn0 := mul_nonneg (show 0 ≤ 2 * (base r : ℤ) - 3 by omega)
      (show 0 ≤ (2 : ℤ) ^ j by positivity)
    have hn1 := mul_nonneg (show 0 ≤ 5 * (base r : ℤ) + 2 by omega)
      (show 0 ≤ (2 : ℤ) ^ j by positivity)
    have hn2 := mul_nonneg (show 0 ≤ 3 * (base r : ℤ) + 5 by omega)
      (show 0 ≤ (2 : ℤ) ^ j by positivity)
    constructor
    · constructor <;> nlinarith [sq_nonneg (base r : ℤ)]
    · constructor <;> constructor <;> nlinarith [sq_nonneg (base r : ℤ)]
  · have hcases : j = degree r - 3 ∨ j = degree r - 2 ∨ j = degree r - 1 := by
      omega
    rcases hcases with h | h | h
    · have he := hshift 3 (by omega)
      have hn1 : j ≠ degree r - 1 := by dsimp [degree] at *; omega
      have hn2 : j ≠ degree r - 2 := by dsimp [degree] at *; omega
      simp only [v0, v1, v2, if_pos h, if_neg hn1, if_neg hn2]
      norm_num at he ⊢
      rw [← he] at hb ⊢
      constructor
      · constructor <;> nlinarith [sq_nonneg ((2 : ℤ) ^ j - 1)]
      · constructor <;> constructor <;> nlinarith [sq_nonneg ((2 : ℤ) ^ j - 1)]
    · have he := hshift 2 (by omega)
      have hn1 : j ≠ degree r - 1 := by dsimp [degree] at *; omega
      have hn3 : j ≠ degree r - 3 := by dsimp [degree] at *; omega
      simp only [v0, v1, v2, if_pos h, if_neg hn1, if_neg hn3]
      norm_num at he ⊢
      rw [← he] at hb ⊢
      constructor
      · constructor <;> nlinarith [sq_nonneg ((2 : ℤ) ^ j - 1)]
      · constructor <;> constructor <;> nlinarith [sq_nonneg ((2 : ℤ) ^ j - 1)]
    · have he := hshift 1 (by omega)
      have hn2 : j ≠ degree r - 2 := by dsimp [degree] at *; omega
      have hn3 : j ≠ degree r - 3 := by dsimp [degree] at *; omega
      simp only [v0, v1, v2, if_pos h, if_neg hn2, if_neg hn3]
      norm_num at he ⊢
      rw [← he] at hb ⊢
      constructor
      · constructor <;> nlinarith [sq_nonneg ((2 : ℤ) ^ j - 1)]
      · constructor <;> constructor <;> nlinarith [sq_nonneg ((2 : ℤ) ^ j - 1)]

theorem source_phases (r : ℕ) (j : Fin (degree r)) :
    let B : ℤ := base r
    let g := B - 1
    let x : ℤ := 2 ^ j.val
    actualSource (3 * degree r) (seed r) ⟨j.val, by have := j.isLt; omega⟩ =
      g * v0 (degree r) B x j.val ∧
    actualSource (3 * degree r) (seed r) ⟨degree r + j.val, by have := j.isLt; omega⟩ =
      g * v1 (degree r) B x j.val ∧
    actualSource (3 * degree r) (seed r) ⟨2 * degree r + j.val, by have := j.isLt; omega⟩ =
      g * v2 (degree r) B x j.val := by
  dsimp
  obtain ⟨hg, hH, hodd⟩ := centered_parameters r
  obtain ⟨h0, h1, h2⟩ := phase_bounds r j.val j.isLt
  have hp : (2 : ℤ) ^ degree r = base r := by simp [base]
  have hp2 : (2 : ℤ) ^ (2 * degree r) = (base r : ℤ) ^ 2 := by
    rw [show 2 * degree r = degree r * 2 by omega, pow_mul, hp]
  simp only [actualSource, modulus_factor, seed_cast, pow_add, hp, hp2]
  have harg0 : (2 : ℤ) ^ j.val *
      (((base r : ℤ) - 1) * (2 * (base r : ℤ) - 3)) =
      ((base r : ℤ) - 1) * ((2 * (base r : ℤ) - 3) * 2 ^ j.val) := by ring
  have harg1 : (base r : ℤ) * 2 ^ j.val *
      (((base r : ℤ) - 1) * (2 * (base r : ℤ) - 3)) =
      ((base r : ℤ) - 1) * ((base r : ℤ) * (2 * (base r : ℤ) - 3) * 2 ^ j.val) := by ring
  have harg2 : (base r : ℤ) ^ 2 * 2 ^ j.val *
      (((base r : ℤ) - 1) * (2 * (base r : ℤ) - 3)) =
      ((base r : ℤ) - 1) * ((base r : ℤ) ^ 2 * (2 * (base r : ℤ) - 3) * 2 ^ j.val) := by ring
  rw [harg0, harg1, harg2]
  refine ⟨centered_scaled (ell := if j.val = degree r - 1 then 1 else 0) hg hH hodd ?_ h0,
    centered_scaled (ell := 2 * (2 : ℤ) ^ j.val -
      ((if j.val = degree r - 3 then 1 else 0) +
       (if j.val = degree r - 2 then 1 else 0) +
       2 * (if j.val = degree r - 1 then 1 else 0))) hg hH hodd ?_ h1, centered_scaled (ell := (2 * (base r : ℤ) - 5) * 2 ^ j.val +
      ((if j.val = degree r - 2 then 1 else 0) +
       2 * (if j.val = degree r - 1 then 1 else 0))) hg hH hodd ?_ h2⟩
  · dsimp [v0]
    ring
  · dsimp [v1]
    ring
  · dsimp [v2]
    ring

def place {d : ℕ} (p : Fin 3) (j : Fin d) : Fin (3 * d) :=
  ⟨p.val * d + j.val, by
    calc
      p.val*d+j.val < p.val*d+d := Nat.add_lt_add_left j.isLt _
      _ = (p.val+1)*d := by ring
      _ ≤ 3*d := Nat.mul_le_mul_right d (by have := p.isLt; omega)⟩
def slice {d : ℕ} (p : Fin 3) (A : Finset (Fin (3 * d))) : Finset (Fin d) :=
  Finset.univ.filter (fun j => place p j ∈ A)

theorem sum_slices {R : Type*} [AddCommMonoid R] {d : ℕ} (hd : 0 < d) (A : Finset (Fin (3 * d)))
    (f : Fin (3 * d) → R) :
    (∑ i ∈ A, f i) =
      (∑ j ∈ slice 0 A, f (place 0 j)) +
      (∑ j ∈ slice 1 A, f (place 1 j)) +
      (∑ j ∈ slice 2 A, f (place 2 j)) := by
  classical
  let e : Fin 3 × Fin d ≃ Fin (3 * d) :=
    { toFun := fun ij => place ij.1 ij.2
      invFun := fun i => (⟨i.val / d, by
        exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)⟩, ⟨i.val % d, Nat.mod_lt _ hd⟩)
      left_inv := by
        rintro ⟨i,j⟩
        apply Prod.ext <;> apply Fin.ext
        · dsimp [place]
          rw [Nat.mul_comm i.val d, Nat.mul_add_div hd, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
        · simp [place, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
      right_inv := by
        intro i
        apply Fin.ext
        dsimp [place]
        simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div i.val d }
  have he := e.sum_comp (fun i => if i ∈ A then f i else 0)
  simpa [e, slice, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_succ, add_assoc] using he.symm

theorem mask_slices {d : ℕ} (hd : 0 < d) (A : Finset (Fin (3 * d))) :
    (mask A : ℤ) = (mask (slice 0 A) : ℤ) +
      (2 : ℤ) ^ d * mask (slice 1 A) + (2 : ℤ) ^ (2 * d) * mask (slice 2 A) := by
  have h := sum_slices hd A (fun i => (2 : ℤ) ^ i.val)
  simp only [place, Fin.val_mk, zero_mul, zero_add, one_mul,
    show (0 : Fin 3).val = 0 from rfl,
    show (1 : Fin 3).val = 1 from rfl, show (2 : Fin 3).val = 2 from rfl,
    pow_zero, one_mul, pow_add, ← Finset.mul_sum] at h
  simpa only [mask, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using h

theorem floor_unique {B x q : ℤ} (hB : 0 < B)
    (hlo : q * B ≤ x) (hhi : x < q * B + B) : x / B = q :=
  (Int.ediv_eq_iff_of_pos hB).mpr ⟨hlo,hhi⟩

/-- Low physical labels contribute a strict sub-unit remainder, even if
some other labels carry equal *source values*. This is a mask statement. -/
private theorem low_mask_lt {d c : ℕ} (A : Finset (Fin d)) :
    mask (A.filter (fun j => j.val < c)) < 2 ^ c := by
  classical
  rw [mask_as_geom]
  apply Nat.geomSum_lt (by norm_num)
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact (Finset.mem_filter.mp hi).2

private def bit {d : ℕ} (A : Finset (Fin d)) (j : ℕ) : ℤ :=
  if h : j<d then (if (⟨j,h⟩ : Fin d) ∈ A then 1 else 0) else 0

private theorem top_floors {d : ℕ} (hd : 3 ≤ d) (A : Finset (Fin d)) :
    (2 * (mask A : ℤ)) / (2 : ℤ) ^ d = bit A (d-1) ∧
    (4 * (mask A : ℤ)) / (2 : ℤ) ^ d = bit A (d-2) + 2 * bit A (d-1) ∧
    (8 * (mask A : ℤ)) / (2 : ℤ) ^ d =
      bit A (d-3) + 2 * bit A (d-2) + 4 * bit A (d-1) := by
  classical
  have hb : (0 : ℤ) < 2 ^ d := by positivity
  have split_mask (q : ℕ) :
      (mask A : ℤ) = (mask (A.filter (fun j => j.val < d-q)) : ℤ) +
        mask (A.filter (fun j => d-q ≤ j.val)) := by
    simp only [mask, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Finset.sum_filter_add_sum_filter_not A (fun j => j.val < d-q)]
    simp only [not_lt]
  have floor_at (q : ℕ) (hq : q ≤ d) (w : ℤ)
      (hw : (mask (A.filter (fun j => d-q ≤ j.val)) : ℤ) =
        (2 : ℤ) ^ (d-q) * w) :
      ((2 : ℤ) ^ q * mask A) / (2 : ℤ) ^ d = w := by
    have hp : (2 : ℤ) ^ d = 2 ^ q * 2 ^ (d-q) := by
      rw [← pow_add, Nat.add_sub_of_le hq]
    have hlo : (0 : ℤ) ≤ mask (A.filter (fun j => j.val < d-q)) := by positivity
    have hhi : (mask (A.filter (fun j => j.val < d-q)) : ℤ) < (2 : ℤ) ^ (d-q) := by
      exact_mod_cast low_mask_lt (c := d-q) A
    have he := split_mask q
    rw [hw] at he
    have he' : (2 : ℤ)^q*mask A =
        2^q*mask (A.filter (fun j => j.val<d-q)) + 2^d*w := by
      rw [he,hp]
      ring
    apply floor_unique hb
    · nlinarith only [he',mul_nonneg (show (0 : ℤ) ≤ 2^q by positivity) hlo]
    · have hhi' := mul_lt_mul_of_pos_left hhi (show (0 : ℤ)<2^q by positivity)
      rw [← hp] at hhi'
      nlinarith only [he',hhi']
  let i1 : Fin d := ⟨d-1,by omega⟩
  let i2 : Fin d := ⟨d-2,by omega⟩
  let i3 : Fin d := ⟨d-3,by omega⟩
  have hi12 : i1 ≠ i2 := by intro h; have := congrArg Fin.val h; dsimp [i1,i2] at this; omega
  have hi13 : i1 ≠ i3 := by intro h; have := congrArg Fin.val h; dsimp [i1,i3] at this; omega
  have hi23 : i2 ≠ i3 := by intro h; have := congrArg Fin.val h; dsimp [i2,i3] at this; omega
  have set1 : A.filter (fun j => d-1 ≤ j.val) = ({i1} : Finset (Fin d)).filter (fun j => j ∈ A) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    have hj := j.isLt
    constructor
    · rintro ⟨hA,hj'⟩
      exact ⟨Fin.ext (by dsimp [i1]; omega),hA⟩
    · rintro ⟨rfl,hA⟩
      exact ⟨hA,by simp [i1]⟩
  have set2 : A.filter (fun j => d-2 ≤ j.val) = ({i2,i1} : Finset (Fin d)).filter (fun j => j ∈ A) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    have hj := j.isLt
    constructor
    · rintro ⟨hA,hj'⟩
      refine ⟨?_,hA⟩
      have : j.val = d-2 ∨ j.val = d-1 := by omega
      rcases this with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    · rintro ⟨h,hA⟩
      rcases h with rfl | rfl <;> exact ⟨hA,by dsimp [i1,i2]; omega⟩
  have set3 : A.filter (fun j => d-3 ≤ j.val) = ({i3,i2,i1} : Finset (Fin d)).filter (fun j => j ∈ A) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    have hj := j.isLt
    constructor
    · rintro ⟨hA,hj'⟩
      refine ⟨?_,hA⟩
      have : j.val = d-3 ∨ j.val = d-2 ∨ j.val = d-1 := by omega
      rcases this with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    · rintro ⟨h,hA⟩
      rcases h with rfl | rfl | rfl <;> exact ⟨hA,by dsimp [i1,i2,i3]; omega⟩
  have hp2 : (2 : ℤ) ^ (d-1) = 2 ^ (d-2) * 2 := by
    rw [← pow_succ, show d-2+1 = d-1 by omega]
  have hp3 : (2 : ℤ) ^ (d-2) = 2 ^ (d-3) * 2 := by
    rw [← pow_succ, show d-3+1 = d-2 by omega]
  have hbit (j : ℕ) (hj : j < d) :
      bit A j = if (⟨j,hj⟩ : Fin d) ∈ A then 1 else 0 := by simp [bit,hj]
  have h21 : i2 ∉ ({i1} : Finset (Fin d)) := by simp [Ne.symm hi12]
  have h321 : i3 ∉ ({i2,i1} : Finset (Fin d)) := by
    simp [Ne.symm hi13,Ne.symm hi23]
  refine ⟨?_,?_,?_⟩
  · simpa only [show (2 : ℤ)^1=2 by norm_num] using floor_at 1 (by omega) (bit A (d-1)) (by
      rw [set1]
      simp only [mask,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,
        Finset.sum_filter,Finset.sum_singleton,i1,Fin.val_mk,hbit (d-1) (by omega)]
      simp only [apply_ite, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero]
      split_ifs <;> ring)
  · simpa only [show (2 : ℤ)^2=4 by norm_num] using floor_at 2 (by omega) (bit A (d-2)+2*bit A (d-1)) (by
      rw [set2]
      simp only [mask,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,Finset.sum_filter]
      rw [Finset.sum_insert h21,Finset.sum_singleton]
      simp only [i1,i2,Fin.val_mk,hbit (d-1) (by omega),hbit (d-2) (by omega)]
      simp only [apply_ite, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero]
      rw [hp2]
      split_ifs <;> ring)
  · simpa only [show (2 : ℤ)^3=8 by norm_num] using floor_at 3 (by omega)
      (bit A (d-3)+2*bit A (d-2)+4*bit A (d-1)) (by
      rw [set3]
      simp only [mask,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,Finset.sum_filter]
      rw [Finset.sum_insert h321,Finset.sum_insert h21,Finset.sum_singleton]
      simp only [i1,i2,i3,Fin.val_mk,hbit (d-1) (by omega),
        hbit (d-2) (by omega),hbit (d-3) (by omega)]
      simp only [apply_ite, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero]
      rw [hp2,hp3]
      split_ifs <;> ring)

def charge (B L M U : ℤ) : ℤ :=
  (2*B-3)*L - (5*B+2)*M + (3*B+5)*U +
    (B^2+B+1) * (-(2*L/B) + 8*M/B - 4*M/B - 4*U/B)

theorem actual_sum_blocks (r : ℕ) (A : Finset (Fin (3 * degree r))) :
    total r A = ((base r : ℤ)-1) * charge (base r)
      (mask (slice 0 A)) (mask (slice 1 A)) (mask (slice 2 A)) := by
  classical
  have hd : 3 ≤ degree r := by dsimp [degree] <;> omega
  have htop0 := top_floors hd (slice 0 A)
  have htop1 := top_floors hd (slice 1 A)
  have htop2 := top_floors hd (slice 2 A)
  have hp : (2 : ℤ) ^ degree r = base r := by simp [base]
  rw [hp] at htop0 htop1 htop2
  have hs := sum_slices (d := degree r) (by omega) A
    (actualSource (3 * degree r) (seed r))
  change total r A = _ at hs
  rw [hs]
  have hs0 := fun j : Fin (degree r) => (source_phases r j).1
  have hs1 := fun j : Fin (degree r) => (source_phases r j).2.1
  have hs2 := fun j : Fin (degree r) => (source_phases r j).2.2
  simp only [place, Fin.val_mk, show (0 : Fin 3).val = 0 from rfl,
    show (1 : Fin 3).val = 1 from rfl, show (2 : Fin 3).val = 2 from rfl,
    zero_mul, zero_add, one_mul] at hs0 hs1 hs2 ⊢
  simp_rw [hs0, hs1, hs2]
  simp only [← Finset.mul_sum]
  simp only [v0,v1,v2,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  have sum_bit (A' : Finset (Fin (degree r))) (j : ℕ) (hj : j < degree r) :
      (∑ i ∈ A', if i.val = j then (1 : ℤ) else 0) = bit A' j := by
    simp only [bit,dif_pos hj]
    have he : ∀ i : Fin (degree r), i.val = j ↔ i = ⟨j,hj⟩ := by
      intro i
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp_rw [he]
    simp
  simp_rw [sum_bit (slice 0 A) (degree r-1) (by dsimp [degree] <;> omega),
    sum_bit (slice 1 A) (degree r-3) (by dsimp [degree] <;> omega),
    sum_bit (slice 1 A) (degree r-2) (by dsimp [degree] <;> omega),
    sum_bit (slice 1 A) (degree r-1) (by dsimp [degree] <;> omega),
    sum_bit (slice 2 A) (degree r-2) (by dsimp [degree] <;> omega),
    sum_bit (slice 2 A) (degree r-1) (by dsimp [degree] <;> omega)]
  have mask_cast (A' : Finset (Fin (degree r))) :
      (∑ j ∈ A', (2 : ℤ) ^ j.val) = mask A' := by
    simp [mask]
  simp_rw [mask_cast]
  dsimp [charge]
  rw [htop0.1,htop1.2.2,htop1.2.1,htop2.2.1]
  ring


end D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
