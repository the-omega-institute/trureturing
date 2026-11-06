/- GID: D5/S3/Combinatorics/Circle/MersenneExceptional19ZeroCount
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Powerset]
   utility: none
   digest: Exact physical mask sieve and exceptional19 integer-floor count development.

Exceptional 19: exact count development.

The active source contains definitions and complete local proof scripts only.
The four mathematical bridges listed at the end are OPEN, not declarations
with substitute tactic bodies. The sole intended public theorem is preserved
there verbatim, with its final composition, but is NOT yet declared.
The original candidate has not been changed. No kernel success is claimed.
-/
module
public import D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
import all D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
public import D5.S3.Combinatorics.Circle.ZeroSumSubsets
import all D5.S3.Combinatorics.Circle.ZeroSumSubsets
public import D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily
import all D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily
public import Batteries.Tactic.OpenPrivate
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

/-! # Exact exceptional19 physical zero-subset counting

The physical-to-mask sieve and integer block transport are proved below.
The final all-parameter cardinality claim remains the exact open target. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount

open SourceWidth ZeroSumSubsets
open scoped BigOperators

open private mask_surjective
  from D5.S3.Combinatorics.Circle.ZeroSumSubsets
open private phase_scaled_gcd
  from D5.S3.Combinatorics.Circle.MersennePhaseNoncyclicFamily

private def d (r : ℕ) : ℕ := 18 * r + 12
private def B (r : ℕ) : ℕ := 2 ^ d r
private def N (r : ℕ) : ℕ := B r ^ 3 - 1
private def seed (r : ℕ) : ℕ := (B r - 1) * (2 * B r - 3)
private def C (b : ℕ) : ℕ := b ^ 2 + b + 1
private def Q (r : ℕ) : ℕ := C (B r) / 19
private def K (r : ℕ) : ℕ := 19 * (B r - 1)
private def M (r : ℕ) : ℕ := (B r + 8) / 152
private def L (m : ℕ) : ℕ := 152 * m - 9

private def physicalZero (r : ℕ) : Finset (Finset (Fin (3 * d r))) :=
  Finset.univ.filter (fun A =>
    (∑ i ∈ A, actualSource (3 * d r) (seed r) i) = 0)

private theorem d_lower (r : ℕ) : 3 ≤ d r := by dsimp [d]; omega

private theorem d_positive (r : ℕ) : 0 < d r := by
  have := d_lower r
  omega

private theorem b_lower (r : ℕ) : 4096 ≤ B r := by
  have he : 12 ≤ d r := by dsimp [d]; omega
  have hp : (2 : ℕ) ^ 12 ≤ 2 ^ d r :=
    Nat.pow_le_pow_right (by decide) he
  norm_num at hp
  exact hp

private theorem b_multiple_eight (r : ℕ) : 8 ∣ B r := by
  have hd := d_lower r
  refine ⟨2 ^ (d r - 3), ?_⟩
  change 2 ^ d r = 8 * 2 ^ (d r - 3)
  calc
    2 ^ d r = 2 ^ (3 + (d r - 3)) := by congr 1; omega
    _ = 8 * 2 ^ (d r - 3) := by rw [pow_add]; norm_num

private theorem b_mod_nineteen (r : ℕ) : B r % 19 = 11 := by
  change (2 : ℕ) ^ (18 * r + 12) % 19 = 11
  rw [pow_add, pow_mul, Nat.mul_mod]
  have hpow : ((2 : ℕ) ^ 18) ^ r % 19 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [hpow]
  norm_num

private theorem b_add_eight (r : ℕ) : B r + 8 = 152 * M r := by
  have h8 : B r % 8 = 0 := Nat.mod_eq_zero_of_dvd (b_multiple_eight r)
  have h19 := b_mod_nineteen r
  have h152 : (B r + 8) % 152 = 0 := by omega
  have hdiv := Nat.mod_add_div (B r + 8) 152
  dsimp [M]
  omega

private theorem b_affine (r : ℕ) : B r = 152 * M r - 8 := by
  have := b_add_eight r
  omega

private theorem m_lower (r : ℕ) : 27 ≤ M r := by
  have := b_add_eight r
  have := b_lower r
  omega

private theorem original_seed (r : ℕ) :
    (2 ^ d r - 1) * (2 ^ (d r + 1) - 3) = seed r := by
  simp only [seed, B, pow_succ, Nat.mul_comm]

private theorem n_pow (r : ℕ) : N r = 2 ^ (3 * d r) - 1 := by
  change ((2 : ℕ) ^ d r) ^ 3 - 1 = 2 ^ (3 * d r) - 1
  rw [← pow_mul, Nat.mul_comm (d r) 3]

private theorem n_positive (r : ℕ) : 0 < N r := by
  have hd := d_positive r
  have hp := Nat.one_lt_two_pow (show 3 * d r ≠ 0 by omega)
  rw [n_pow]
  omega

private theorem n_factor (r : ℕ) : N r = (B r - 1) * C (B r) := by
  have hb : 1 ≤ B r := by have := b_lower r; omega
  have he : B r - 1 + 1 = B r := Nat.sub_add_cancel hb
  have hp : (B r - 1 + 1) ^ 3 =
      (B r - 1) * C (B r - 1 + 1) + 1 := by dsimp [C]; ring
  rw [he] at hp
  dsimp [N]
  omega

private theorem gcd_exceptional (r : ℕ) :
    Nat.gcd (seed r) (N r) = K r := by
  have hb := b_lower r
  have hm := b_mod_nineteen r
  have hdiv : 19 ∣ 2 ^ (d r + 1) - 3 := by
    rw [pow_succ]
    change 19 ∣ B r * 2 - 3
    omega
  have hg := phase_scaled_gcd (d r) (d_positive r)
  rw [Nat.gcd_eq_right hdiv, original_seed r, ← n_pow r] at hg
  simpa only [B, K, Nat.mul_comm] using hg

private theorem q_eq_quotient (r : ℕ) :
    N r / Nat.gcd (seed r) (N r) = Q r := by
  rw [gcd_exceptional, n_factor]
  change (B r - 1) * C (B r) / (19 * (B r - 1)) = C (B r) / 19
  rw [Nat.mul_comm 19 (B r - 1)]
  exact Nat.mul_div_mul_left _ _ (by have := b_lower r; omega)

private theorem q_positive (r : ℕ) : 0 < Q r := by
  rw [← q_eq_quotient r]
  exact Nat.div_gcd_pos_of_pos_right (seed r) (n_positive r)

private theorem q_mul_k (r : ℕ) : Q r * K r = N r := by
  have h := Nat.div_mul_cancel (Nat.gcd_dvd_right (seed r) (N r))
  rw [q_eq_quotient r, gcd_exceptional r] at h
  exact h

private theorem zero_sum_implies_candidate (r : ℕ)
    (A : Finset (Fin (3 * d r)))
    (hA : (∑ i ∈ A, actualSource (3 * d r) (seed r) i) = 0) :
    Q r ∣ mask A := by
  have hd := zero_mask_dvd A hA
  rw [← n_pow r] at hd
  have hq := quotient_dvd (n_positive r) hd
  rwa [q_eq_quotient r] at hq

/- The inverse is selected from the SEALED physical mask bijection. This is
   not a new binary-set foundation; every physical label is retained. -/
private noncomputable def subsetOfMask (r m : ℕ) : Finset (Fin (3 * d r)) :=
  if hm : m < 2 ^ (3 * d r) then
    (mask_surjective (3 * d r) m hm).choose
  else ∅

private theorem mask_subsetOfMask (r m : ℕ) (hm : m < 2 ^ (3 * d r)) :
    mask (subsetOfMask r m) = m := by
  simp only [subsetOfMask, dite_eq_left hm]
  exact (mask_surjective (3 * d r) m hm).choose_spec

private theorem subsetOfMask_mask (r : ℕ) (A : Finset (Fin (3 * d r))) :
    subsetOfMask r (mask A) = A := by
  apply mask_injective (3 * d r)
  apply mask_subsetOfMask
  have hb := mask_bound A
  have hp : 1 ≤ (2 : ℕ) ^ (3 * d r) := Nat.one_le_two_pow
  omega

private noncomputable def sumAtMask (r m : ℕ) : ℤ :=
  ∑ i ∈ subsetOfMask r m, actualSource (3 * d r) (seed r) i

private theorem sumAtMask_mask (r : ℕ) (A : Finset (Fin (3 * d r))) :
    sumAtMask r (mask A) = ∑ i ∈ A, actualSource (3 * d r) (seed r) i := by
  unfold sumAtMask
  rw [subsetOfMask_mask r A]

private theorem full_mask_is_zero (r : ℕ) :
    (∑ i : Fin (3 * d r), actualSource (3 * d r) (seed r) i) = 0 := by
  exact (source_cycle (show 0 < 3 * d r by have := d_positive r; omega)
    (seed r)).2.1

private theorem sumAtMask_full (r : ℕ) : sumAtMask r (N r) = 0 := by
  have h := sumAtMask_mask r (Finset.univ : Finset (Fin (3 * d r)))
  rw [mask_full, ← n_pow r] at h
  exact h.trans (full_mask_is_zero r)

private noncomputable def candidateMasks (r : ℕ) : Finset ℕ :=
  (Finset.range (K r + 1)).filter (fun k => sumAtMask r (k * Q r) = 0)

/- This sieve is an exact physical-cardinality reduction, BEFORE the open
   carry/profile computation. It does not replace literal zero by divisibility. -/
private theorem physical_candidate_card (r : ℕ) :
    (physicalZero r).card = (candidateMasks r).card := by
  classical
  unfold candidateMasks
  apply Finset.card_nbij (fun A : Finset (Fin (3 * d r)) => mask A / Q r)
  · intro A hA
    have hz := (Finset.mem_filter.mp hA).2
    have hd := zero_sum_implies_candidate r A hz
    have hb := mask_bound A
    rw [← n_pow r] at hb
    have hu := Nat.div_le_div_right hb (c := Q r)
    rw [← q_mul_k r, Nat.mul_div_cancel_left _ (q_positive r)] at hu
    dsimp only
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.div_mul_cancel hd, sumAtMask_mask r A]
    exact hz
  · intro A hA D hD he
    dsimp only at he
    have hdA := zero_sum_implies_candidate r A (Finset.mem_filter.mp hA).2
    have hdD := zero_sum_implies_candidate r D (Finset.mem_filter.mp hD).2
    apply mask_injective (3 * d r)
    calc
      mask A = mask A / Q r * Q r := (Nat.div_mul_cancel hdA).symm
      _ = mask D / Q r * Q r := by rw [he]
      _ = mask D := Nat.div_mul_cancel hdD
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkbound : k ≤ K r := by have := Finset.mem_range.mp hk'.1; omega
    have hm : k * Q r ≤ N r := by
      calc
        k * Q r ≤ K r * Q r := Nat.mul_le_mul_right _ hkbound
        _ = N r := by rw [Nat.mul_comm, q_mul_k r]
    have hm' : k * Q r < 2 ^ (3 * d r) := by
      rw [n_pow r] at hm
      have hp : 1 ≤ (2 : ℕ) ^ (3 * d r) := Nat.one_le_two_pow
      omega
    refine ⟨subsetOfMask r (k * Q r), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change sumAtMask r (k * Q r) = 0
      exact hk'.2
    · dsimp only
      rw [mask_subsetOfMask r _ hm', Nat.mul_div_cancel _ (q_positive r)]

/- Correct five signed floors. EACH Nat quotient is cast BEFORE subtraction. -/
private def carryCorrection (r m : ℕ) : ℤ :=
  ((2 * m / B r : ℕ) : ℤ) - ((8 * m / B r ^ 2 : ℕ) : ℤ) +
  ((4 * m / B r ^ 2 : ℕ) : ℤ) - ((m / B r ^ 2 : ℕ) : ℤ) +
  ((4 * m / B r ^ 3 : ℕ) : ℤ)

open private degree base total slice charge mask_slices actual_sum_blocks
  from D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer

private theorem scale_div (x b q : ℤ) (hq : 0 < q) (hdiv : q ∣ b) :
    q * x / b = x / (b / q) := by
  obtain ⟨t, rfl⟩ := hdiv
  rw [Int.mul_ediv_cancel_left _ (ne_of_gt hq), Int.mul_ediv_mul_of_pos _ _ hq]

private theorem scale_div_shift (x b q : ℤ) (j : ℕ)
    (hb : 0 < b) (hq : 0 < q) (hdiv : q ∣ b) :
    q * x / b ^ (j+1) = q * (x / b ^ j) / b := by
  have ht : 0 ≤ b / q := Int.ediv_nonneg hb.le hq.le
  calc
    q*x/b^(j+1) = (q*x/b)/b^j := by
      rw [Int.ediv_ediv_of_nonneg hb.le, pow_succ']
    _ = x/(b/q)/b^j := by rw [scale_div x b q hq hdiv]
    _ = x/b^j/(b/q) := by
      rw [Int.ediv_ediv_of_nonneg ht,
        Int.ediv_ediv_of_nonneg (pow_nonneg hb.le j), mul_comm (b/q)]
    _ = q*(x/b^j)/b := (scale_div _ b q hq hdiv).symm

private theorem mask_block_quotients (r : ℕ) (A : Finset (Fin (3 * d r))) :
    let b : ℤ := B r
    (mask A : ℤ) / b =
      (mask (slice 1 A) : ℤ) + b * mask (slice 2 A) ∧
    (mask A : ℤ) / b^2 = mask (slice 2 A) := by
  dsimp
  have hb : (0 : ℤ) < B r := by have := b_lower r; positivity
  have hs := mask_slices (d := d r) (d_positive r) A
  have hp : (2 : ℤ) ^ d r = B r := by simp [B]
  have hp2 : (2 : ℤ) ^ (2*d r) = (B r : ℤ)^2 := by
    rw [show 2*d r=d r*2 by omega,pow_mul,hp]
  rw [hp,hp2] at hs
  have hbound (p : Fin 3) :
      0 ≤ (mask (slice p A) : ℤ) ∧ (mask (slice p A) : ℤ) < B r := by
    refine ⟨by positivity, ?_⟩
    have h := mask_bound (slice p A)
    have hp' : 0 < B r := by have := b_lower r; omega
    change mask (slice p A) ≤ B r-1 at h
    exact_mod_cast (show mask (slice p A) < B r by omega)
  obtain ⟨hl0, hl1⟩ := hbound 0
  obtain ⟨hm0, hm1⟩ := hbound 1
  obtain ⟨hu0, hu1⟩ := hbound 2
  constructor
  · apply (Int.ediv_eq_iff_of_pos hb).mpr
    constructor <;> nlinarith only [hs, hl0, hl1]
  · apply (Int.ediv_eq_iff_of_pos (sq_pos_of_pos hb)).mpr
    have ht0 := mul_nonneg hb.le hm0
    have ht1 := mul_nonneg hb.le (show 0 ≤ (B r : ℤ)-1-mask (slice 1 A) by omega)
    constructor <;> nlinarith only [hs, hl0, hl1, ht0, ht1]

private theorem actual_sum_floor (r : ℕ) (A : Finset (Fin (3 * d r))) :
    (∑ i ∈ A, actualSource (3 * d r) (MersenneExceptional19ZeroCount.seed r) i) =
      (MersenneExceptional19ZeroCount.seed r : ℤ) * mask A -
        (N r : ℤ) * carryCorrection r (mask A) := by
  have hb : (0 : ℤ) < B r := by have := b_lower r; positivity
  have hb8 : (8 : ℤ) ∣ B r := by exact_mod_cast b_multiple_eight r
  have hb4 : (4 : ℤ) ∣ B r := dvd_trans (by norm_num) hb8
  have hs := actual_sum_blocks r A
  have hm := mask_slices (d := d r) (d_positive r) A
  obtain ⟨hq1,hq2⟩ := mask_block_quotients r A
  have hp : (2 : ℤ)^d r=B r := by simp [B]
  have hp2 : (2 : ℤ)^(2*d r)=(B r : ℤ)^2 := by
    rw [show 2*d r=d r*2 by omega,pow_mul,hp]
  rw [hp,hp2] at hm
  have h2 : (2*(mask A : ℤ))/(B r : ℤ) =
      2*(mask (slice 0 A) : ℤ)/(B r : ℤ) +
        (2*mask (slice 1 A)+2*(B r : ℤ)*mask (slice 2 A)) := by
    rw [hm]
    have he : 2*((mask (slice 0 A) : ℤ)+(B r : ℤ)*mask (slice 1 A)+(B r : ℤ)^2*mask (slice 2 A)) =
        2*mask (slice 0 A)+(2*mask (slice 1 A)+2*(B r : ℤ)*mask (slice 2 A))*(B r : ℤ) := by ring
    rw [he,Int.add_mul_ediv_right _ _ (ne_of_gt hb)]
  have h8 : 8*(mask A : ℤ)/(B r : ℤ)^2 =
      8*(mask (slice 1 A) : ℤ)/(B r : ℤ)+8*mask (slice 2 A) := by
    rw [scale_div_shift _ _ 8 1 hb (by norm_num) hb8,pow_one,hq1]
    have he : 8*((mask (slice 1 A) : ℤ)+(B r : ℤ)*mask (slice 2 A)) =
        8*mask (slice 1 A)+(8*mask (slice 2 A))*(B r : ℤ) := by ring
    rw [he,Int.add_mul_ediv_right _ _ (ne_of_gt hb)]
  have h4 : 4*(mask A : ℤ)/(B r : ℤ)^2 =
      4*(mask (slice 1 A) : ℤ)/(B r : ℤ)+4*mask (slice 2 A) := by
    rw [scale_div_shift _ _ 4 1 hb (by norm_num) hb4,pow_one,hq1]
    have he : 4*((mask (slice 1 A) : ℤ)+(B r : ℤ)*mask (slice 2 A)) =
        4*mask (slice 1 A)+(4*mask (slice 2 A))*(B r : ℤ) := by ring
    rw [he,Int.add_mul_ediv_right _ _ (ne_of_gt hb)]
  have htop : 4*(mask A : ℤ)/(B r : ℤ)^3 = 4*(mask (slice 2 A) : ℤ)/(B r : ℤ) := by
    rw [scale_div_shift _ _ 4 2 hb (by norm_num) hb4,hq2]
  have hn : (N r : ℤ) = ((B r : ℤ)-1)*((B r : ℤ)^2+B r+1) := by
    rw [n_factor]
    have h : 1 ≤ B r := by have := b_lower r; omega
    simp [C,Nat.cast_sub h]
  have ht : (MersenneExceptional19ZeroCount.seed r : ℤ) =
      ((B r : ℤ)-1)*(2*(B r : ℤ)-3) := by
    have h1 : 1 ≤ B r := by have := b_lower r; omega
    have h3 : 3 ≤ 2*B r := by have := b_lower r; omega
    simp [MersenneExceptional19ZeroCount.seed, Nat.cast_sub h1,Nat.cast_sub h3]
  change (∑ i ∈ A, actualSource (3*d r) ((2^d r-1)*(2^(d r+1)-3)) i) =
    ((B r : ℤ)-1)*charge (B r) (mask (slice 0 A)) (mask (slice 1 A)) (mask (slice 2 A)) at hs
  rw [original_seed r] at hs
  rw [hs]
  dsimp [charge,carryCorrection]
  rw [h2,h8,h4,hq2,htop,hn,ht,hm]
  ring

private def binarySum (r m : ℕ) : ℤ :=
  ∑ i : Fin (3 * d r),
    (if (m / 2 ^ i.val) % 2 = 1 then (1 : ℤ) else 0) *
      actualSource (3 * d r) (seed r) i

private def epsilon (r : ℕ) (i : Fin (3 * d r)) : ℤ :=
  if i.val = d r - 2 then 1
  else if i.val = 2 * d r - 4 then -1
  else if i.val = 2 * d r - 3 then 1
  else if i.val = 2 * d r - 1 then -1
  else if i.val = 3 * d r - 3 then 1
  else if i.val = 3 * d r - 1 then -1
  else 0

private def f (r k : ℕ) : ℤ :=
  (((2 * B r - 3) / 19 : ℕ) : ℤ) * (k : ℤ) -
    carryCorrection r (k * Q r)

private theorem candidate_sum_formula (r k : ℕ) (hk : k ≤ K r) :
    sumAtMask r (k * Q r) = (N r : ℤ) * f r k := by
  have hm : k*Q r ≤ N r := by
    calc
      k*Q r ≤ K r*Q r := Nat.mul_le_mul_right _ hk
      _ = N r := by rw [Nat.mul_comm,q_mul_k r]
  have hm' : k*Q r < 2^(3*d r) := by
    rw [n_pow] at hm
    have hp : 1 ≤ (2 : ℕ)^(3*d r) := Nat.one_le_two_pow
    omega
  have hs := actual_sum_floor r (subsetOfMask r (k*Q r))
  rw [mask_subsetOfMask r _ hm'] at hs
  change sumAtMask r (k*Q r) = _ at hs
  rw [hs]
  have hd19 : 19 ∣ 2*B r-3 := by have := b_mod_nineteen r; omega
  have hcoef : (19 : ℤ)*(((2*B r-3)/19 : ℕ) : ℤ) = 2*(B r : ℤ)-3 := by
    have he := Nat.mul_div_cancel' hd19
    have h3 : 3 ≤ 2*B r := by have := b_lower r; omega
    exact_mod_cast (show 19*((2*B r-3)/19)=2*B r-3 by omega)
  have hC19 : 19 ∣ C (B r) := by
    apply Nat.dvd_of_mod_eq_zero
    norm_num [C,Nat.add_mod,Nat.pow_mod,b_mod_nineteen]
  have hQ : (19 : ℤ)*(Q r : ℤ) = (B r : ℤ)^2+B r+1 := by
    have h := Nat.mul_div_cancel' hC19
    change 19*(C (B r)/19)=C (B r) at h
    exact_mod_cast h
  have hn : (N r : ℤ) = ((B r : ℤ)-1)*((B r : ℤ)^2+B r+1) := by
    rw [n_factor]
    have hb : 1 ≤ B r := by have := b_lower r; omega
    simp [C,Nat.cast_sub hb]
  have ht : (MersenneExceptional19ZeroCount.seed r : ℤ) =
      ((B r : ℤ)-1)*(2*(B r : ℤ)-3) := by
    have h1 : 1 ≤ B r := by have := b_lower r; omega
    have h3 : 3 ≤ 2*B r := by have := b_lower r; omega
    simp [MersenneExceptional19ZeroCount.seed,Nat.cast_sub h1,Nat.cast_sub h3]
  simp only [f,Nat.cast_mul]
  rw [ht,hn,←hcoef,←hQ]
  ring

/- All three arguments are Nat; all field arithmetic is explicitly Rat. -/
private def rowB (m : ℕ) : ℚ := (152 : ℚ) * (m : ℚ) - 8
private def X (m v u : ℕ) : ℚ :=
  ((19 : ℚ) * (u : ℚ) + (v : ℚ)) / (19 * rowB m)
private def Z (m v u : ℕ) : ℚ :=
  (v : ℚ) / 19 + X m v u * (1 + 1 / rowB m)
private def Hjump (z : ℚ) : ℤ := ⌊8 * z⌋ - ⌊4 * z⌋ + ⌊z⌋
private def rowValue (m v u : ℕ) : ℤ :=
  -⌊(5 : ℚ) * (v : ℚ) / 19 + 2 * X m v u⌋ + Hjump (Z m v u) -
    ⌊4 * X m v u * (1 + 1 / rowB m + 1 / rowB m ^ 2)⌋
private def rowZeroCount (m v : ℕ) : ℕ :=
  ((Finset.range (L m)).filter (fun u => rowValue m v u = 0)).card

/-- The same five floors, with common positive integer denominators. -/
private def normalizedRow (b u v : ℤ) : ℤ :=
  -( (38*u+(5*b+2)*v) / (19*b)) +
    (152*(b+1)*u+8*v*(b^2+b+1))/(19*b^2) -
    (76*(b+1)*u+4*v*(b^2+b+1))/(19*b^2) +
    (19*(b+1)*u+v*(b^2+b+1))/(19*b^2) -
    (76*(b^2+b+1)*u+4*v*(b^2+b+1))/(19*b^3)

private theorem candidate_normalized (r u v : ℕ) :
    f r (19*u+v) = normalizedRow (B r) u v := by
  have hb : (0 : ℤ) < B r := by have := b_lower r; positivity
  have hd19 : 19 ∣ 2*B r-3 := by have := b_mod_nineteen r; omega
  have h3 : 3 ≤ 2*B r := by have := b_lower r; omega
  have hcoef : (19 : ℤ)*(((2*B r-3)/19 : ℕ) : ℤ) = 2*(B r : ℤ)-3 := by
    have he : 19*((2*B r-3)/19)=2*B r-3 := Nat.mul_div_cancel' hd19
    exact_mod_cast he
  have hC19 : 19 ∣ C (B r) := by
    apply Nat.dvd_of_mod_eq_zero
    norm_num [C,Nat.add_mod,Nat.pow_mod,b_mod_nineteen]
  have hQ : (19 : ℤ)*(Q r : ℤ) = (B r : ℤ)^2+B r+1 := by
    have h : 19*(C (B r)/19)=C (B r) := Nat.mul_div_cancel' hC19
    exact_mod_cast h
  let b : ℤ := B r
  let q : ℤ := Q r
  let t : ℤ := ((2*B r-3)/19 : ℕ)
  have hq : 19*q=b^2+b+1 := hQ
  have ht : 19*t=2*b-3 := hcoef
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hpow (a : ℤ) (j : ℕ) :
      a*((19*(u:ℤ)+v)*q)/b^j =
        (19*a*((19*(u:ℤ)+v)*q))/(19*b^j) := by
    simpa only [mul_assoc] using
      (Int.mul_ediv_mul_of_pos (a*((19*(u:ℤ)+v)*q)) (b^j)
        (by norm_num : (0 : ℤ)<19)).symm
  have hfirst : 2*((19*(u:ℤ)+v)*q)/b =
      (2*b+2)*u+t*v + (38*(u:ℤ)+(5*b+2)*v)/(19*b) := by
    calc
      _ = (19*(2*((19*(u:ℤ)+v)*q)))/(19*b) := by
        rw [Int.mul_ediv_mul_of_pos _ _ (by norm_num : (0 : ℤ)<19)]
      _ = (((2*b+2)*u+t*v)*(19*b)+(38*(u:ℤ)+(5*b+2)*v))/(19*b) := by
        congr 1
        linear_combination 2*(19*(u:ℤ)+v)*hq - b*(v:ℤ)*ht
      _ = _ := by rw [Int.mul_add_ediv_right _ _ (mul_ne_zero (by norm_num) hb0)]
  have hother (a : ℤ) : a*((19*(u:ℤ)+v)*q)/b^2 =
      a*u+(19*a*(b+1)*u+a*v*(b^2+b+1))/(19*b^2) := by
    rw [hpow a 2]
    have he : 19*a*((19*(u:ℤ)+v)*q) =
        (a*u)*(19*b^2)+(19*a*(b+1)*u+a*v*(b^2+b+1)) := by
      linear_combination a*(19*(u:ℤ)+v)*hq
    rw [he,Int.mul_add_ediv_right _ _ (mul_ne_zero (by norm_num) (pow_ne_zero _ hb0))]
  have hlast : 4*((19*(u:ℤ)+v)*q)/b^3 =
      (76*(b^2+b+1)*u+4*v*(b^2+b+1))/(19*b^3) := by
    rw [hpow 4 3]
    congr 1
    linear_combination 4*(19*(u:ℤ)+v)*hq
  dsimp [f,carryCorrection,normalizedRow]
  push_cast
  change t*(19*(u:ℤ)+v) -
    (2*((19*(u:ℤ)+v)*q)/b-8*((19*(u:ℤ)+v)*q)/b^2+
      4*((19*(u:ℤ)+v)*q)/b^2-((19*(u:ℤ)+v)*q)/b^2+
      4*((19*(u:ℤ)+v)*q)/b^3) = _
  rw [hfirst,hother 8,hother 4,show ((19*(u:ℤ)+v)*q)/b^2 =
    u+(19*(b+1)*u+v*(b^2+b+1))/(19*b^2) by simpa using hother 1,hlast]
  dsimp [b] at *
  linear_combination (u:ℤ)*ht

private theorem rowValue_normalized (m v u : ℕ) (hm : 27 ≤ m) :
    rowValue m v u = normalizedRow (152*(m:ℤ)-8) u v := by
  let b : ℤ := 152*(m:ℤ)-8
  have hb : 0 < b := by dsimp [b]; omega
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hrow : rowB m = (b : ℚ) := by simp [rowB,b]
  have hf (a c : ℤ) (hc : 0 ≤ c) : ⌊(a : ℚ)/(c : ℚ)⌋ = a/c := by
    rw [Int.floor_div_cast_of_nonneg hc,Int.floor_intCast]
  have ha : (5:ℚ)*v/19+2*X m v u =
      ((38*(u:ℤ)+(5*b+2)*v : ℤ) : ℚ) / ((19*b : ℤ) : ℚ) := by
    dsimp [X]
    rw [hrow]
    push_cast
    field_simp
    <;> ring
  have hz (a : ℤ) : (a : ℚ)*Z m v u =
      ((19*a*(b+1)*u+a*v*(b^2+b+1) : ℤ) : ℚ)/((19*b^2 : ℤ) : ℚ) := by
    dsimp [Z,X]
    rw [hrow]
    push_cast
    field_simp
    <;> ring
  have hc : 4*X m v u*(1+1/rowB m+1/rowB m^2) =
      ((76*(b^2+b+1)*u+4*v*(b^2+b+1) : ℤ) : ℚ)/((19*b^3 : ℤ) : ℚ) := by
    dsimp [X]
    rw [hrow]
    push_cast
    field_simp
    <;> ring
  have hz8 := hz 8
  have hz4 := hz 4
  have hz1 := hz 1
  norm_num only [Int.cast_ofNat,Int.cast_one,one_mul] at hz8 hz4 hz1
  dsimp [rowValue,Hjump]
  rw [ha,hz8,hz4,hz1,hc]
  rw [hf _ _ (by positivity),hf _ _ (by positivity),hf _ _ (by positivity),
    hf _ _ (by positivity),hf _ _ (by positivity)]
  norm_num [normalizedRow,b]
  <;> ring

private theorem candidate_profile (r u v : ℕ) :
    f r (19*u+v) = rowValue (M r) v u := by
  rw [candidate_normalized,rowValue_normalized _ _ _ (m_lower r)]
  congr 1
  have h := b_add_eight r
  omega




/-- Endpoint certificates imply a floor value on every integer in the cell. -/
private theorem floor_on_cell (a b c l h z u : ℤ)
    (hc : 0 < c) (ha : 0 ≤ a)
    (hlo : z*c ≤ a*l+b) (hhi : a*(h-1)+b < (z+1)*c)
    (hu : l ≤ u ∧ u < h) : (a*u+b)/c=z := by
  apply (Int.ediv_eq_iff_of_pos hc).mpr
  have hleft := mul_nonneg ha (sub_nonneg.mpr hu.1)
  have hright := mul_nonneg ha (show 0 ≤ h-1-u by omega)
  constructor <;> nlinarith only [hlo,hhi,hleft,hright]

private theorem cell_0_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (19*n+512)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_1 (n u : ℕ) (hu : (19*n+512) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_2 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (57*n+1536)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_3 (n u : ℕ) (hu : (57*n+1536) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_4 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (95*n+2560)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_5 (n u : ℕ) (hu : (95*n+2560) ≤ u ∧ u < (114*n+3072)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_6 (n u : ℕ) (hu : (114*n+3072) ≤ u ∧ u < (133*n+3584)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_7 (n u : ℕ) (hu : (133*n+3584) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_0 (n : ℕ) :
    rowZeroCount (n+27) 0 = 76*n+2047 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 0 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 0 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 0 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 0=0) = ((((Finset.Ico (0*n+0) (19*n+512) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (57*n+1536) : Finset ℕ)) ∪ (Finset.Ico (95*n+2560) (114*n+3072) : Finset ℕ)) ∪ (Finset.Ico (133*n+3584) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (19*n+512)
      · have hf := cell_0_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (38*n+1024)
        · have hf := cell_0_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (57*n+1536)
          · have hf := cell_0_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (76*n+2048)
            · have hf := cell_0_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (95*n+2560)
              · have hf := cell_0_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (114*n+3072)
                · have hf := cell_0_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (133*n+3584)
                  · have hf := cell_0_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · have hf := cell_0_7 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (19*n+512) : Finset ℕ) (Finset.Ico (38*n+1024) (57*n+1536) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (19*n+512) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (57*n+1536) : Finset ℕ)) (Finset.Ico (95*n+2560) (114*n+3072) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (19*n+512) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (57*n+1536) : Finset ℕ)) ∪ (Finset.Ico (95*n+2560) (114*n+3072) : Finset ℕ)) (Finset.Ico (133*n+3584) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_1_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (11*n+297)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (11*(n:ℤ)+297) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (11*(n:ℤ)+297) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (11*(n:ℤ)+297) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (11*(n:ℤ)+297) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (11*(n:ℤ)+297) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_1 (n u : ℕ) (hu : (11*n+297) ≤ u ∧ u < (30*n+809)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (11*(n:ℤ)+297) (30*(n:ℤ)+809) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (11*(n:ℤ)+297) (30*(n:ℤ)+809) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (11*(n:ℤ)+297) (30*(n:ℤ)+809) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (11*(n:ℤ)+297) (30*(n:ℤ)+809) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (11*(n:ℤ)+297) (30*(n:ℤ)+809) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_2 (n u : ℕ) (hu : (30*n+809) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (30*(n:ℤ)+809) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (30*(n:ℤ)+809) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (30*(n:ℤ)+809) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (30*(n:ℤ)+809) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (30*(n:ℤ)+809) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_3 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (49*n+1321)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (49*(n:ℤ)+1321) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (49*(n:ℤ)+1321) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (49*(n:ℤ)+1321) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (49*(n:ℤ)+1321) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (49*(n:ℤ)+1321) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_4 (n u : ℕ) (hu : (49*n+1321) ≤ u ∧ u < (56*n+1509)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (49*(n:ℤ)+1321) (56*(n:ℤ)+1509) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (49*(n:ℤ)+1321) (56*(n:ℤ)+1509) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (49*(n:ℤ)+1321) (56*(n:ℤ)+1509) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (49*(n:ℤ)+1321) (56*(n:ℤ)+1509) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (49*(n:ℤ)+1321) (56*(n:ℤ)+1509) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_5 (n u : ℕ) (hu : (56*n+1509) ≤ u ∧ u < (68*n+1832)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (56*(n:ℤ)+1509) (68*(n:ℤ)+1832) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (56*(n:ℤ)+1509) (68*(n:ℤ)+1832) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (56*(n:ℤ)+1509) (68*(n:ℤ)+1832) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (56*(n:ℤ)+1509) (68*(n:ℤ)+1832) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (56*(n:ℤ)+1509) (68*(n:ℤ)+1832) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_6 (n u : ℕ) (hu : (68*n+1832) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (68*(n:ℤ)+1832) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (68*(n:ℤ)+1832) (76*(n:ℤ)+2048) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (68*(n:ℤ)+1832) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (68*(n:ℤ)+1832) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (68*(n:ℤ)+1832) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (87*n+2344)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (87*(n:ℤ)+2344) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (87*(n:ℤ)+2344) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (87*(n:ℤ)+2344) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (87*(n:ℤ)+2344) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (87*(n:ℤ)+2344) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_8 (n u : ℕ) (hu : (87*n+2344) ≤ u ∧ u < (106*n+2856)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (87*(n:ℤ)+2344) (106*(n:ℤ)+2856) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (87*(n:ℤ)+2344) (106*(n:ℤ)+2856) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (87*(n:ℤ)+2344) (106*(n:ℤ)+2856) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (87*(n:ℤ)+2344) (106*(n:ℤ)+2856) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (87*(n:ℤ)+2344) (106*(n:ℤ)+2856) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_9 (n u : ℕ) (hu : (106*n+2856) ≤ u ∧ u < (114*n+3072)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (106*(n:ℤ)+2856) (114*(n:ℤ)+3072) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (106*(n:ℤ)+2856) (114*(n:ℤ)+3072) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (106*(n:ℤ)+2856) (114*(n:ℤ)+3072) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (106*(n:ℤ)+2856) (114*(n:ℤ)+3072) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (106*(n:ℤ)+2856) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_10 (n u : ℕ) (hu : (114*n+3072) ≤ u ∧ u < (125*n+3368)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3072) (125*(n:ℤ)+3368) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (125*(n:ℤ)+3368) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (125*(n:ℤ)+3368) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (125*(n:ℤ)+3368) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3072) (125*(n:ℤ)+3368) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_11 (n u : ℕ) (hu : (125*n+3368) ≤ u ∧ u < (132*n+3557)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (125*(n:ℤ)+3368) (132*(n:ℤ)+3557) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (125*(n:ℤ)+3368) (132*(n:ℤ)+3557) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (125*(n:ℤ)+3368) (132*(n:ℤ)+3557) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (125*(n:ℤ)+3368) (132*(n:ℤ)+3557) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (125*(n:ℤ)+3368) (132*(n:ℤ)+3557) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_12 (n u : ℕ) (hu : (132*n+3557) ≤ u ∧ u < (144*n+3880)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (132*(n:ℤ)+3557) (144*(n:ℤ)+3880) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (132*(n:ℤ)+3557) (144*(n:ℤ)+3880) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (132*(n:ℤ)+3557) (144*(n:ℤ)+3880) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (132*(n:ℤ)+3557) (144*(n:ℤ)+3880) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (132*(n:ℤ)+3557) (144*(n:ℤ)+3880) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_1_13 (n u : ℕ) (hu : (144*n+3880) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 1 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*1))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*1) (19*(152*((n:ℤ)+27)-8)) (144*(n:ℤ)+3880) (152*(n:ℤ)+4095) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (144*(n:ℤ)+3880) (152*(n:ℤ)+4095) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (144*(n:ℤ)+3880) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (144*(n:ℤ)+3880) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*1*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (144*(n:ℤ)+3880) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_1 (n : ℕ) :
    rowZeroCount (n+27) 1 = 84*n+2265 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 1 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 1 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 1 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 1=0) = ((((((((Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ)) ∪ (Finset.Ico (56*n+1509) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (68*n+1832) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (87*n+2344) (106*n+2856) : Finset ℕ)) ∪ (Finset.Ico (106*n+2856) (114*n+3072) : Finset ℕ)) ∪ (Finset.Ico (125*n+3368) (132*n+3557) : Finset ℕ)) ∪ (Finset.Ico (144*n+3880) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (11*n+297)
      · have hf := cell_1_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (30*n+809)
        · have hf := cell_1_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1024)
          · have hf := cell_1_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (49*n+1321)
            · have hf := cell_1_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (56*n+1509)
              · have hf := cell_1_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (68*n+1832)
                · have hf := cell_1_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_1_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (87*n+2344)
                    · have hf := cell_1_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (106*n+2856)
                      · have hf := cell_1_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3072)
                        · have hf := cell_1_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (125*n+3368)
                          · have hf := cell_1_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (132*n+3557)
                            · have hf := cell_1_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (144*n+3880)
                              · have hf := cell_1_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_1_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ)) (Finset.Ico (56*n+1509) (68*n+1832) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ)) ∪ (Finset.Ico (56*n+1509) (68*n+1832) : Finset ℕ)) (Finset.Ico (68*n+1832) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ)) ∪ (Finset.Ico (56*n+1509) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (68*n+1832) (76*n+2048) : Finset ℕ)) (Finset.Ico (87*n+2344) (106*n+2856) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ)) ∪ (Finset.Ico (56*n+1509) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (68*n+1832) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (87*n+2344) (106*n+2856) : Finset ℕ)) (Finset.Ico (106*n+2856) (114*n+3072) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ)) ∪ (Finset.Ico (56*n+1509) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (68*n+1832) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (87*n+2344) (106*n+2856) : Finset ℕ)) ∪ (Finset.Ico (106*n+2856) (114*n+3072) : Finset ℕ)) (Finset.Ico (125*n+3368) (132*n+3557) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (11*n+297) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (49*n+1321) : Finset ℕ)) ∪ (Finset.Ico (56*n+1509) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (68*n+1832) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (87*n+2344) (106*n+2856) : Finset ℕ)) ∪ (Finset.Ico (106*n+2856) (114*n+3072) : Finset ℕ)) ∪ (Finset.Ico (125*n+3368) (132*n+3557) : Finset ℕ)) (Finset.Ico (144*n+3880) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_2_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (3*n+81)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (3*(n:ℤ)+81) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (3*(n:ℤ)+81) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (3*(n:ℤ)+81) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (3*(n:ℤ)+81) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (3*(n:ℤ)+81) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_1 (n u : ℕ) (hu : (3*n+81) ≤ u ∧ u < (22*n+593)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (3*(n:ℤ)+81) (22*(n:ℤ)+593) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (3*(n:ℤ)+81) (22*(n:ℤ)+593) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (3*(n:ℤ)+81) (22*(n:ℤ)+593) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (3*(n:ℤ)+81) (22*(n:ℤ)+593) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (3*(n:ℤ)+81) (22*(n:ℤ)+593) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_2 (n u : ℕ) (hu : (22*n+593) ≤ u ∧ u < (36*n+970)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (22*(n:ℤ)+593) (36*(n:ℤ)+970) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (22*(n:ℤ)+593) (36*(n:ℤ)+970) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (22*(n:ℤ)+593) (36*(n:ℤ)+970) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (22*(n:ℤ)+593) (36*(n:ℤ)+970) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (22*(n:ℤ)+593) (36*(n:ℤ)+970) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_3 (n u : ℕ) (hu : (36*n+970) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_4 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (41*n+1105)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (41*(n:ℤ)+1105) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (41*(n:ℤ)+1105) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (41*(n:ℤ)+1105) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (41*(n:ℤ)+1105) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (41*(n:ℤ)+1105) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_5 (n u : ℕ) (hu : (41*n+1105) ≤ u ∧ u < (60*n+1617)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (41*(n:ℤ)+1105) (60*(n:ℤ)+1617) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (41*(n:ℤ)+1105) (60*(n:ℤ)+1617) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (41*(n:ℤ)+1105) (60*(n:ℤ)+1617) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (41*(n:ℤ)+1105) (60*(n:ℤ)+1617) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (41*(n:ℤ)+1105) (60*(n:ℤ)+1617) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_6 (n u : ℕ) (hu : (60*n+1617) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (60*(n:ℤ)+1617) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (60*(n:ℤ)+1617) (76*(n:ℤ)+2048) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (60*(n:ℤ)+1617) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (60*(n:ℤ)+1617) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (60*(n:ℤ)+1617) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (79*n+2129)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (79*(n:ℤ)+2129) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (79*(n:ℤ)+2129) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (79*(n:ℤ)+2129) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (79*(n:ℤ)+2129) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (79*(n:ℤ)+2129) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_8 (n u : ℕ) (hu : (79*n+2129) ≤ u ∧ u < (98*n+2641)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (79*(n:ℤ)+2129) (98*(n:ℤ)+2641) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (79*(n:ℤ)+2129) (98*(n:ℤ)+2641) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (79*(n:ℤ)+2129) (98*(n:ℤ)+2641) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (79*(n:ℤ)+2129) (98*(n:ℤ)+2641) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (79*(n:ℤ)+2129) (98*(n:ℤ)+2641) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_9 (n u : ℕ) (hu : (98*n+2641) ≤ u ∧ u < (112*n+3018)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (98*(n:ℤ)+2641) (112*(n:ℤ)+3018) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (98*(n:ℤ)+2641) (112*(n:ℤ)+3018) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (98*(n:ℤ)+2641) (112*(n:ℤ)+3018) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (98*(n:ℤ)+2641) (112*(n:ℤ)+3018) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (98*(n:ℤ)+2641) (112*(n:ℤ)+3018) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_10 (n u : ℕ) (hu : (112*n+3018) ≤ u ∧ u < (114*n+3072)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (112*(n:ℤ)+3018) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (112*(n:ℤ)+3018) (114*(n:ℤ)+3072) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (112*(n:ℤ)+3018) (114*(n:ℤ)+3072) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (112*(n:ℤ)+3018) (114*(n:ℤ)+3072) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (112*(n:ℤ)+3018) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_11 (n u : ℕ) (hu : (114*n+3072) ≤ u ∧ u < (117*n+3152)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = -2 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3072) (117*(n:ℤ)+3152) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (117*(n:ℤ)+3152) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (117*(n:ℤ)+3152) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (117*(n:ℤ)+3152) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3072) (117*(n:ℤ)+3152) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_12 (n u : ℕ) (hu : (117*n+3152) ≤ u ∧ u < (136*n+3664)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (117*(n:ℤ)+3152) (136*(n:ℤ)+3664) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (117*(n:ℤ)+3152) (136*(n:ℤ)+3664) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (117*(n:ℤ)+3152) (136*(n:ℤ)+3664) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (117*(n:ℤ)+3152) (136*(n:ℤ)+3664) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (117*(n:ℤ)+3152) (136*(n:ℤ)+3664) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_2_13 (n u : ℕ) (hu : (136*n+3664) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 2 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*2))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*2) (19*(152*((n:ℤ)+27)-8)) (136*(n:ℤ)+3664) (152*(n:ℤ)+4095) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (136*(n:ℤ)+3664) (152*(n:ℤ)+4095) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (136*(n:ℤ)+3664) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (136*(n:ℤ)+3664) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*2*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (136*(n:ℤ)+3664) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_2 (n : ℕ) :
    rowZeroCount (n+27) 2 = 89*n+2398 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 2 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 2 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 2 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 2=0) = (((((((Finset.Ico (0*n+0) (3*n+81) : Finset ℕ) ∪ (Finset.Ico (36*n+970) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (41*n+1105) (60*n+1617) : Finset ℕ)) ∪ (Finset.Ico (60*n+1617) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (79*n+2129) (98*n+2641) : Finset ℕ)) ∪ (Finset.Ico (98*n+2641) (112*n+3018) : Finset ℕ)) ∪ (Finset.Ico (136*n+3664) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (3*n+81)
      · have hf := cell_2_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (22*n+593)
        · have hf := cell_2_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (36*n+970)
          · have hf := cell_2_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1024)
            · have hf := cell_2_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (41*n+1105)
              · have hf := cell_2_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (60*n+1617)
                · have hf := cell_2_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_2_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (79*n+2129)
                    · have hf := cell_2_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (98*n+2641)
                      · have hf := cell_2_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (112*n+3018)
                        · have hf := cell_2_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3072)
                          · have hf := cell_2_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (117*n+3152)
                            · have hf := cell_2_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (136*n+3664)
                              · have hf := cell_2_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_2_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (3*n+81) : Finset ℕ) (Finset.Ico (36*n+970) (38*n+1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (3*n+81) : Finset ℕ) ∪ (Finset.Ico (36*n+970) (38*n+1024) : Finset ℕ)) (Finset.Ico (41*n+1105) (60*n+1617) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (3*n+81) : Finset ℕ) ∪ (Finset.Ico (36*n+970) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (41*n+1105) (60*n+1617) : Finset ℕ)) (Finset.Ico (60*n+1617) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (3*n+81) : Finset ℕ) ∪ (Finset.Ico (36*n+970) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (41*n+1105) (60*n+1617) : Finset ℕ)) ∪ (Finset.Ico (60*n+1617) (76*n+2048) : Finset ℕ)) (Finset.Ico (79*n+2129) (98*n+2641) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (3*n+81) : Finset ℕ) ∪ (Finset.Ico (36*n+970) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (41*n+1105) (60*n+1617) : Finset ℕ)) ∪ (Finset.Ico (60*n+1617) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (79*n+2129) (98*n+2641) : Finset ℕ)) (Finset.Ico (98*n+2641) (112*n+3018) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (3*n+81) : Finset ℕ) ∪ (Finset.Ico (36*n+970) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (41*n+1105) (60*n+1617) : Finset ℕ)) ∪ (Finset.Ico (60*n+1617) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (79*n+2129) (98*n+2641) : Finset ℕ)) ∪ (Finset.Ico (98*n+2641) (112*n+3018) : Finset ℕ)) (Finset.Ico (136*n+3664) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_3_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (14*n+378)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (14*(n:ℤ)+378) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (14*(n:ℤ)+378) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (14*(n:ℤ)+378) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (14*(n:ℤ)+378) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (14*(n:ℤ)+378) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_1 (n u : ℕ) (hu : (14*n+378) ≤ u ∧ u < (16*n+431)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (14*(n:ℤ)+378) (16*(n:ℤ)+431) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (14*(n:ℤ)+378) (16*(n:ℤ)+431) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (14*(n:ℤ)+378) (16*(n:ℤ)+431) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (14*(n:ℤ)+378) (16*(n:ℤ)+431) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (14*(n:ℤ)+378) (16*(n:ℤ)+431) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_2 (n u : ℕ) (hu : (16*n+431) ≤ u ∧ u < (33*n+889)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (16*(n:ℤ)+431) (33*(n:ℤ)+889) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (16*(n:ℤ)+431) (33*(n:ℤ)+889) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (16*(n:ℤ)+431) (33*(n:ℤ)+889) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (16*(n:ℤ)+431) (33*(n:ℤ)+889) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (16*(n:ℤ)+431) (33*(n:ℤ)+889) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_3 (n u : ℕ) (hu : (33*n+889) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (33*(n:ℤ)+889) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (33*(n:ℤ)+889) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (33*(n:ℤ)+889) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (33*(n:ℤ)+889) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (33*(n:ℤ)+889) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_4 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (52*n+1401)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_5 (n u : ℕ) (hu : (52*n+1401) ≤ u ∧ u < (71*n+1913)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (52*(n:ℤ)+1401) (71*(n:ℤ)+1913) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (52*(n:ℤ)+1401) (71*(n:ℤ)+1913) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (52*(n:ℤ)+1401) (71*(n:ℤ)+1913) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (52*(n:ℤ)+1401) (71*(n:ℤ)+1913) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (52*(n:ℤ)+1401) (71*(n:ℤ)+1913) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_6 (n u : ℕ) (hu : (71*n+1913) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (71*(n:ℤ)+1913) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (71*(n:ℤ)+1913) (76*(n:ℤ)+2048) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (71*(n:ℤ)+1913) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (71*(n:ℤ)+1913) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (71*(n:ℤ)+1913) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (90*n+2425)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (90*(n:ℤ)+2425) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (90*(n:ℤ)+2425) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (90*(n:ℤ)+2425) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (90*(n:ℤ)+2425) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (90*(n:ℤ)+2425) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_8 (n u : ℕ) (hu : (90*n+2425) ≤ u ∧ u < (92*n+2479)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (90*(n:ℤ)+2425) (92*(n:ℤ)+2479) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (90*(n:ℤ)+2425) (92*(n:ℤ)+2479) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (90*(n:ℤ)+2425) (92*(n:ℤ)+2479) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (90*(n:ℤ)+2425) (92*(n:ℤ)+2479) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (90*(n:ℤ)+2425) (92*(n:ℤ)+2479) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_9 (n u : ℕ) (hu : (92*n+2479) ≤ u ∧ u < (109*n+2937)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (92*(n:ℤ)+2479) (109*(n:ℤ)+2937) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (92*(n:ℤ)+2479) (109*(n:ℤ)+2937) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (92*(n:ℤ)+2479) (109*(n:ℤ)+2937) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (92*(n:ℤ)+2479) (109*(n:ℤ)+2937) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (92*(n:ℤ)+2479) (109*(n:ℤ)+2937) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_10 (n u : ℕ) (hu : (109*n+2937) ≤ u ∧ u < (114*n+3072)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (109*(n:ℤ)+2937) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (109*(n:ℤ)+2937) (114*(n:ℤ)+3072) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (109*(n:ℤ)+2937) (114*(n:ℤ)+3072) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (109*(n:ℤ)+2937) (114*(n:ℤ)+3072) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (109*(n:ℤ)+2937) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_11 (n u : ℕ) (hu : (114*n+3072) ≤ u ∧ u < (128*n+3449)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3072) (128*(n:ℤ)+3449) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (128*(n:ℤ)+3449) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (128*(n:ℤ)+3449) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (128*(n:ℤ)+3449) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3072) (128*(n:ℤ)+3449) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_12 (n u : ℕ) (hu : (128*n+3449) ≤ u ∧ u < (147*n+3961)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (128*(n:ℤ)+3449) (147*(n:ℤ)+3961) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (128*(n:ℤ)+3449) (147*(n:ℤ)+3961) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (128*(n:ℤ)+3449) (147*(n:ℤ)+3961) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (128*(n:ℤ)+3449) (147*(n:ℤ)+3961) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (128*(n:ℤ)+3449) (147*(n:ℤ)+3961) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_3_13 (n u : ℕ) (hu : (147*n+3961) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 3 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*3))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*3) (19*(152*((n:ℤ)+27)-8)) (147*(n:ℤ)+3961) (152*(n:ℤ)+4095) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (147*(n:ℤ)+3961) (152*(n:ℤ)+4095) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (147*(n:ℤ)+3961) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (147*(n:ℤ)+3961) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*3*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (147*(n:ℤ)+3961) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_3 (n : ℕ) :
    rowZeroCount (n+27) 3 = 90*n+2425 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 3 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 3 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 3 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 3=0) = (((((((Finset.Ico (16*n+431) (33*n+889) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (52*n+1401) (71*n+1913) : Finset ℕ)) ∪ (Finset.Ico (76*n+2048) (90*n+2425) : Finset ℕ)) ∪ (Finset.Ico (90*n+2425) (92*n+2479) : Finset ℕ)) ∪ (Finset.Ico (109*n+2937) (114*n+3072) : Finset ℕ)) ∪ (Finset.Ico (128*n+3449) (147*n+3961) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (14*n+378)
      · have hf := cell_3_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (16*n+431)
        · have hf := cell_3_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (33*n+889)
          · have hf := cell_3_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1024)
            · have hf := cell_3_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (52*n+1401)
              · have hf := cell_3_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (71*n+1913)
                · have hf := cell_3_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_3_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (90*n+2425)
                    · have hf := cell_3_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (92*n+2479)
                      · have hf := cell_3_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (109*n+2937)
                        · have hf := cell_3_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3072)
                          · have hf := cell_3_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (128*n+3449)
                            · have hf := cell_3_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (147*n+3961)
                              · have hf := cell_3_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_3_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (16*n+431) (33*n+889) : Finset ℕ) (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (16*n+431) (33*n+889) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) (Finset.Ico (52*n+1401) (71*n+1913) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (16*n+431) (33*n+889) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (52*n+1401) (71*n+1913) : Finset ℕ)) (Finset.Ico (76*n+2048) (90*n+2425) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (16*n+431) (33*n+889) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (52*n+1401) (71*n+1913) : Finset ℕ)) ∪ (Finset.Ico (76*n+2048) (90*n+2425) : Finset ℕ)) (Finset.Ico (90*n+2425) (92*n+2479) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (16*n+431) (33*n+889) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (52*n+1401) (71*n+1913) : Finset ℕ)) ∪ (Finset.Ico (76*n+2048) (90*n+2425) : Finset ℕ)) ∪ (Finset.Ico (90*n+2425) (92*n+2479) : Finset ℕ)) (Finset.Ico (109*n+2937) (114*n+3072) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (16*n+431) (33*n+889) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (52*n+1401) (71*n+1913) : Finset ℕ)) ∪ (Finset.Ico (76*n+2048) (90*n+2425) : Finset ℕ)) ∪ (Finset.Ico (90*n+2425) (92*n+2479) : Finset ℕ)) ∪ (Finset.Ico (109*n+2937) (114*n+3072) : Finset ℕ)) (Finset.Ico (128*n+3449) (147*n+3961) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_4_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (6*n+162)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (6*(n:ℤ)+162) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (6*(n:ℤ)+162) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (6*(n:ℤ)+162) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (6*(n:ℤ)+162) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (6*(n:ℤ)+162) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_1 (n u : ℕ) (hu : (6*n+162) ≤ u ∧ u < (25*n+674)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (6*(n:ℤ)+162) (25*(n:ℤ)+674) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (6*(n:ℤ)+162) (25*(n:ℤ)+674) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (6*(n:ℤ)+162) (25*(n:ℤ)+674) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (6*(n:ℤ)+162) (25*(n:ℤ)+674) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (6*(n:ℤ)+162) (25*(n:ℤ)+674) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_2 (n u : ℕ) (hu : (25*n+674) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (25*(n:ℤ)+674) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (25*(n:ℤ)+674) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (25*(n:ℤ)+674) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (25*(n:ℤ)+674) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (25*(n:ℤ)+674) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_3 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (44*n+1186)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (44*(n:ℤ)+1186) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (44*(n:ℤ)+1186) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (44*(n:ℤ)+1186) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (44*(n:ℤ)+1186) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (44*(n:ℤ)+1186) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_4 (n u : ℕ) (hu : (44*n+1186) ≤ u ∧ u < (63*n+1698)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (44*(n:ℤ)+1186) (63*(n:ℤ)+1698) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (44*(n:ℤ)+1186) (63*(n:ℤ)+1698) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (44*(n:ℤ)+1186) (63*(n:ℤ)+1698) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (44*(n:ℤ)+1186) (63*(n:ℤ)+1698) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (44*(n:ℤ)+1186) (63*(n:ℤ)+1698) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_5 (n u : ℕ) (hu : (63*n+1698) ≤ u ∧ u < (72*n+1940)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (63*(n:ℤ)+1698) (72*(n:ℤ)+1940) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (63*(n:ℤ)+1698) (72*(n:ℤ)+1940) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (63*(n:ℤ)+1698) (72*(n:ℤ)+1940) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (63*(n:ℤ)+1698) (72*(n:ℤ)+1940) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (63*(n:ℤ)+1698) (72*(n:ℤ)+1940) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_6 (n u : ℕ) (hu : (72*n+1940) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (72*(n:ℤ)+1940) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (72*(n:ℤ)+1940) (76*(n:ℤ)+2048) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (72*(n:ℤ)+1940) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (72*(n:ℤ)+1940) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (72*(n:ℤ)+1940) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (82*n+2209)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (82*(n:ℤ)+2209) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (82*(n:ℤ)+2209) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (82*(n:ℤ)+2209) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (82*(n:ℤ)+2209) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (82*(n:ℤ)+2209) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_8 (n u : ℕ) (hu : (82*n+2209) ≤ u ∧ u < (101*n+2721)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (82*(n:ℤ)+2209) (101*(n:ℤ)+2721) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (82*(n:ℤ)+2209) (101*(n:ℤ)+2721) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (82*(n:ℤ)+2209) (101*(n:ℤ)+2721) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (82*(n:ℤ)+2209) (101*(n:ℤ)+2721) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (82*(n:ℤ)+2209) (101*(n:ℤ)+2721) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_9 (n u : ℕ) (hu : (101*n+2721) ≤ u ∧ u < (114*n+3072)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (101*(n:ℤ)+2721) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (101*(n:ℤ)+2721) (114*(n:ℤ)+3072) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (101*(n:ℤ)+2721) (114*(n:ℤ)+3072) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (101*(n:ℤ)+2721) (114*(n:ℤ)+3072) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (101*(n:ℤ)+2721) (114*(n:ℤ)+3072) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_10 (n u : ℕ) (hu : (114*n+3072) ≤ u ∧ u < (120*n+3233)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3072) (120*(n:ℤ)+3233) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (120*(n:ℤ)+3233) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (120*(n:ℤ)+3233) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (120*(n:ℤ)+3233) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3072) (120*(n:ℤ)+3233) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_11 (n u : ℕ) (hu : (120*n+3233) ≤ u ∧ u < (139*n+3745)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (120*(n:ℤ)+3233) (139*(n:ℤ)+3745) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (120*(n:ℤ)+3233) (139*(n:ℤ)+3745) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (120*(n:ℤ)+3233) (139*(n:ℤ)+3745) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (120*(n:ℤ)+3233) (139*(n:ℤ)+3745) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (120*(n:ℤ)+3233) (139*(n:ℤ)+3745) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_12 (n u : ℕ) (hu : (139*n+3745) ≤ u ∧ u < (148*n+3988)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (139*(n:ℤ)+3745) (148*(n:ℤ)+3988) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (139*(n:ℤ)+3745) (148*(n:ℤ)+3988) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (139*(n:ℤ)+3745) (148*(n:ℤ)+3988) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (139*(n:ℤ)+3745) (148*(n:ℤ)+3988) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (139*(n:ℤ)+3745) (148*(n:ℤ)+3988) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_4_13 (n u : ℕ) (hu : (148*n+3988) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 4 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*4))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*4) (19*(152*((n:ℤ)+27)-8)) (148*(n:ℤ)+3988) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (148*(n:ℤ)+3988) (152*(n:ℤ)+4095) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (148*(n:ℤ)+3988) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (148*(n:ℤ)+3988) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*4*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (148*(n:ℤ)+3988) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_4 (n : ℕ) :
    rowZeroCount (n+27) 4 = 90*n+2426 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 4 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 4 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 4 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 4=0) = ((((((((Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) ∪ (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1186) : Finset ℕ)) ∪ (Finset.Ico (44*n+1186) (63*n+1698) : Finset ℕ)) ∪ (Finset.Ico (72*n+1940) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (101*n+2721) (114*n+3072) : Finset ℕ)) ∪ (Finset.Ico (120*n+3233) (139*n+3745) : Finset ℕ)) ∪ (Finset.Ico (148*n+3988) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (6*n+162)
      · have hf := cell_4_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (25*n+674)
        · have hf := cell_4_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1024)
          · have hf := cell_4_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (44*n+1186)
            · have hf := cell_4_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (63*n+1698)
              · have hf := cell_4_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (72*n+1940)
                · have hf := cell_4_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_4_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (82*n+2209)
                    · have hf := cell_4_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (101*n+2721)
                      · have hf := cell_4_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3072)
                        · have hf := cell_4_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (120*n+3233)
                          · have hf := cell_4_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (139*n+3745)
                            · have hf := cell_4_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (148*n+3988)
                              · have hf := cell_4_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_4_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) ∪ (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ)) (Finset.Ico (38*n+1024) (44*n+1186) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) ∪ (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1186) : Finset ℕ)) (Finset.Ico (44*n+1186) (63*n+1698) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) ∪ (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1186) : Finset ℕ)) ∪ (Finset.Ico (44*n+1186) (63*n+1698) : Finset ℕ)) (Finset.Ico (72*n+1940) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) ∪ (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1186) : Finset ℕ)) ∪ (Finset.Ico (44*n+1186) (63*n+1698) : Finset ℕ)) ∪ (Finset.Ico (72*n+1940) (76*n+2048) : Finset ℕ)) (Finset.Ico (101*n+2721) (114*n+3072) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) ∪ (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1186) : Finset ℕ)) ∪ (Finset.Ico (44*n+1186) (63*n+1698) : Finset ℕ)) ∪ (Finset.Ico (72*n+1940) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (101*n+2721) (114*n+3072) : Finset ℕ)) (Finset.Ico (120*n+3233) (139*n+3745) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (6*n+162) : Finset ℕ) ∪ (Finset.Ico (6*n+162) (25*n+674) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1186) : Finset ℕ)) ∪ (Finset.Ico (44*n+1186) (63*n+1698) : Finset ℕ)) ∪ (Finset.Ico (72*n+1940) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (101*n+2721) (114*n+3072) : Finset ℕ)) ∪ (Finset.Ico (120*n+3233) (139*n+3745) : Finset ℕ)) (Finset.Ico (148*n+3988) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_5_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (17*n+458)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (17*(n:ℤ)+458) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (17*(n:ℤ)+458) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (17*(n:ℤ)+458) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (17*(n:ℤ)+458) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (17*(n:ℤ)+458) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_1 (n u : ℕ) (hu : (17*n+458) ≤ u ∧ u < (36*n+970)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (17*(n:ℤ)+458) (36*(n:ℤ)+970) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (17*(n:ℤ)+458) (36*(n:ℤ)+970) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (17*(n:ℤ)+458) (36*(n:ℤ)+970) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (17*(n:ℤ)+458) (36*(n:ℤ)+970) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (17*(n:ℤ)+458) (36*(n:ℤ)+970) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_2 (n u : ℕ) (hu : (36*n+970) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (36*(n:ℤ)+970) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_3 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (52*n+1401)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (52*(n:ℤ)+1401) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_4 (n u : ℕ) (hu : (52*n+1401) ≤ u ∧ u < (55*n+1482)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (52*(n:ℤ)+1401) (55*(n:ℤ)+1482) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (52*(n:ℤ)+1401) (55*(n:ℤ)+1482) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (52*(n:ℤ)+1401) (55*(n:ℤ)+1482) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (52*(n:ℤ)+1401) (55*(n:ℤ)+1482) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (52*(n:ℤ)+1401) (55*(n:ℤ)+1482) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_5 (n u : ℕ) (hu : (55*n+1482) ≤ u ∧ u < (74*n+1994)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (55*(n:ℤ)+1482) (74*(n:ℤ)+1994) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (55*(n:ℤ)+1482) (74*(n:ℤ)+1994) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (55*(n:ℤ)+1482) (74*(n:ℤ)+1994) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (55*(n:ℤ)+1482) (74*(n:ℤ)+1994) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (55*(n:ℤ)+1482) (74*(n:ℤ)+1994) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_6 (n u : ℕ) (hu : (74*n+1994) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (74*(n:ℤ)+1994) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (74*(n:ℤ)+1994) (76*(n:ℤ)+2048) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (74*(n:ℤ)+1994) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (74*(n:ℤ)+1994) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (74*(n:ℤ)+1994) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (93*n+2506)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (93*(n:ℤ)+2506) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (93*(n:ℤ)+2506) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (93*(n:ℤ)+2506) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (93*(n:ℤ)+2506) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (93*(n:ℤ)+2506) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_8 (n u : ℕ) (hu : (93*n+2506) ≤ u ∧ u < (112*n+3018)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (93*(n:ℤ)+2506) (112*(n:ℤ)+3018) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (93*(n:ℤ)+2506) (112*(n:ℤ)+3018) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (93*(n:ℤ)+2506) (112*(n:ℤ)+3018) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (93*(n:ℤ)+2506) (112*(n:ℤ)+3018) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (93*(n:ℤ)+2506) (112*(n:ℤ)+3018) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_9 (n u : ℕ) (hu : (112*n+3018) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (112*(n:ℤ)+3018) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (112*(n:ℤ)+3018) (114*(n:ℤ)+3071) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (112*(n:ℤ)+3018) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (112*(n:ℤ)+3018) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (112*(n:ℤ)+3018) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_10 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (128*n+3449)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (128*(n:ℤ)+3449) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (128*(n:ℤ)+3449) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (128*(n:ℤ)+3449) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (128*(n:ℤ)+3449) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (128*(n:ℤ)+3449) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_11 (n u : ℕ) (hu : (128*n+3449) ≤ u ∧ u < (131*n+3529)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (128*(n:ℤ)+3449) (131*(n:ℤ)+3529) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (128*(n:ℤ)+3449) (131*(n:ℤ)+3529) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (128*(n:ℤ)+3449) (131*(n:ℤ)+3529) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (128*(n:ℤ)+3449) (131*(n:ℤ)+3529) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (128*(n:ℤ)+3449) (131*(n:ℤ)+3529) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_12 (n u : ℕ) (hu : (131*n+3529) ≤ u ∧ u < (150*n+4041)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (131*(n:ℤ)+3529) (150*(n:ℤ)+4041) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (131*(n:ℤ)+3529) (150*(n:ℤ)+4041) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (131*(n:ℤ)+3529) (150*(n:ℤ)+4041) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (131*(n:ℤ)+3529) (150*(n:ℤ)+4041) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (131*(n:ℤ)+3529) (150*(n:ℤ)+4041) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_5_13 (n u : ℕ) (hu : (150*n+4041) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 5 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*5))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*5) (19*(152*((n:ℤ)+27)-8)) (150*(n:ℤ)+4041) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (150*(n:ℤ)+4041) (152*(n:ℤ)+4095) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (150*(n:ℤ)+4041) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (150*(n:ℤ)+4041) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*5*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (150*(n:ℤ)+4041) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_5 (n : ℕ) :
    rowZeroCount (n+27) 5 = 106*n+2857 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 5 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 5 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 5 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 5=0) = ((((((((Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (55*n+1482) (74*n+1994) : Finset ℕ)) ∪ (Finset.Ico (74*n+1994) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (93*n+2506) (112*n+3018) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (128*n+3449) : Finset ℕ)) ∪ (Finset.Ico (131*n+3529) (150*n+4041) : Finset ℕ)) ∪ (Finset.Ico (150*n+4041) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (17*n+458)
      · have hf := cell_5_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (36*n+970)
        · have hf := cell_5_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1024)
          · have hf := cell_5_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (52*n+1401)
            · have hf := cell_5_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (55*n+1482)
              · have hf := cell_5_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (74*n+1994)
                · have hf := cell_5_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_5_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (93*n+2506)
                    · have hf := cell_5_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (112*n+3018)
                      · have hf := cell_5_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3071)
                        · have hf := cell_5_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (128*n+3449)
                          · have hf := cell_5_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (131*n+3529)
                            · have hf := cell_5_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (150*n+4041)
                              · have hf := cell_5_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_5_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) (Finset.Ico (55*n+1482) (74*n+1994) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (55*n+1482) (74*n+1994) : Finset ℕ)) (Finset.Ico (74*n+1994) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (55*n+1482) (74*n+1994) : Finset ℕ)) ∪ (Finset.Ico (74*n+1994) (76*n+2048) : Finset ℕ)) (Finset.Ico (93*n+2506) (112*n+3018) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (55*n+1482) (74*n+1994) : Finset ℕ)) ∪ (Finset.Ico (74*n+1994) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (93*n+2506) (112*n+3018) : Finset ℕ)) (Finset.Ico (114*n+3071) (128*n+3449) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (55*n+1482) (74*n+1994) : Finset ℕ)) ∪ (Finset.Ico (74*n+1994) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (93*n+2506) (112*n+3018) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (128*n+3449) : Finset ℕ)) (Finset.Ico (131*n+3529) (150*n+4041) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (17*n+458) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (52*n+1401) : Finset ℕ)) ∪ (Finset.Ico (55*n+1482) (74*n+1994) : Finset ℕ)) ∪ (Finset.Ico (74*n+1994) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (93*n+2506) (112*n+3018) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (128*n+3449) : Finset ℕ)) ∪ (Finset.Ico (131*n+3529) (150*n+4041) : Finset ℕ)) (Finset.Ico (150*n+4041) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_6_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (9*n+243)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (9*(n:ℤ)+243) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (9*(n:ℤ)+243) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (9*(n:ℤ)+243) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (9*(n:ℤ)+243) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (9*(n:ℤ)+243) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_1 (n u : ℕ) (hu : (9*n+243) ≤ u ∧ u < (28*n+755)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (9*(n:ℤ)+243) (28*(n:ℤ)+755) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (9*(n:ℤ)+243) (28*(n:ℤ)+755) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (9*(n:ℤ)+243) (28*(n:ℤ)+755) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (9*(n:ℤ)+243) (28*(n:ℤ)+755) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (9*(n:ℤ)+243) (28*(n:ℤ)+755) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_2 (n u : ℕ) (hu : (28*n+755) ≤ u ∧ u < (32*n+862)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (28*(n:ℤ)+755) (32*(n:ℤ)+862) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (28*(n:ℤ)+755) (32*(n:ℤ)+862) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (28*(n:ℤ)+755) (32*(n:ℤ)+862) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (28*(n:ℤ)+755) (32*(n:ℤ)+862) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (28*(n:ℤ)+755) (32*(n:ℤ)+862) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_3 (n u : ℕ) (hu : (32*n+862) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (32*(n:ℤ)+862) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (32*(n:ℤ)+862) (38*(n:ℤ)+1024) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (32*(n:ℤ)+862) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (32*(n:ℤ)+862) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (32*(n:ℤ)+862) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_4 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (47*n+1266)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (47*(n:ℤ)+1266) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (47*(n:ℤ)+1266) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (47*(n:ℤ)+1266) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (47*(n:ℤ)+1266) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (47*(n:ℤ)+1266) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_5 (n u : ℕ) (hu : (47*n+1266) ≤ u ∧ u < (66*n+1778)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (47*(n:ℤ)+1266) (66*(n:ℤ)+1778) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (47*(n:ℤ)+1266) (66*(n:ℤ)+1778) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (47*(n:ℤ)+1266) (66*(n:ℤ)+1778) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (47*(n:ℤ)+1266) (66*(n:ℤ)+1778) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (47*(n:ℤ)+1266) (66*(n:ℤ)+1778) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_6 (n u : ℕ) (hu : (66*n+1778) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (66*(n:ℤ)+1778) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (66*(n:ℤ)+1778) (76*(n:ℤ)+2048) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (66*(n:ℤ)+1778) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (66*(n:ℤ)+1778) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (66*(n:ℤ)+1778) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (85*n+2290)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (85*(n:ℤ)+2290) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (85*(n:ℤ)+2290) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (85*(n:ℤ)+2290) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (85*(n:ℤ)+2290) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (85*(n:ℤ)+2290) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_8 (n u : ℕ) (hu : (85*n+2290) ≤ u ∧ u < (104*n+2802)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (85*(n:ℤ)+2290) (104*(n:ℤ)+2802) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (85*(n:ℤ)+2290) (104*(n:ℤ)+2802) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (85*(n:ℤ)+2290) (104*(n:ℤ)+2802) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (85*(n:ℤ)+2290) (104*(n:ℤ)+2802) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (85*(n:ℤ)+2290) (104*(n:ℤ)+2802) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_9 (n u : ℕ) (hu : (104*n+2802) ≤ u ∧ u < (108*n+2910)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (104*(n:ℤ)+2802) (108*(n:ℤ)+2910) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (104*(n:ℤ)+2802) (108*(n:ℤ)+2910) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (104*(n:ℤ)+2802) (108*(n:ℤ)+2910) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (104*(n:ℤ)+2802) (108*(n:ℤ)+2910) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (104*(n:ℤ)+2802) (108*(n:ℤ)+2910) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_10 (n u : ℕ) (hu : (108*n+2910) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (108*(n:ℤ)+2910) (114*(n:ℤ)+3071) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (108*(n:ℤ)+2910) (114*(n:ℤ)+3071) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (108*(n:ℤ)+2910) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (108*(n:ℤ)+2910) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (108*(n:ℤ)+2910) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_11 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (123*n+3314)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (123*(n:ℤ)+3314) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (123*(n:ℤ)+3314) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (123*(n:ℤ)+3314) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (123*(n:ℤ)+3314) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (123*(n:ℤ)+3314) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_12 (n u : ℕ) (hu : (123*n+3314) ≤ u ∧ u < (142*n+3826)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (123*(n:ℤ)+3314) (142*(n:ℤ)+3826) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (123*(n:ℤ)+3314) (142*(n:ℤ)+3826) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (123*(n:ℤ)+3314) (142*(n:ℤ)+3826) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (123*(n:ℤ)+3314) (142*(n:ℤ)+3826) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (123*(n:ℤ)+3314) (142*(n:ℤ)+3826) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_6_13 (n u : ℕ) (hu : (142*n+3826) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 6 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*6))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*6) (19*(152*((n:ℤ)+27)-8)) (142*(n:ℤ)+3826) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (142*(n:ℤ)+3826) (152*(n:ℤ)+4095) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (142*(n:ℤ)+3826) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (142*(n:ℤ)+3826) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*6*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (142*(n:ℤ)+3826) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_6 (n : ℕ) :
    rowZeroCount (n+27) 6 = 98*n+2641 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 6 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 6 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 6 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 6=0) = ((((((((Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) ∪ (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (47*n+1266) (66*n+1778) : Finset ℕ)) ∪ (Finset.Ico (66*n+1778) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (85*n+2290) (104*n+2802) : Finset ℕ)) ∪ (Finset.Ico (108*n+2910) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (123*n+3314) (142*n+3826) : Finset ℕ)) ∪ (Finset.Ico (142*n+3826) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (9*n+243)
      · have hf := cell_6_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (28*n+755)
        · have hf := cell_6_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (32*n+862)
          · have hf := cell_6_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1024)
            · have hf := cell_6_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (47*n+1266)
              · have hf := cell_6_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (66*n+1778)
                · have hf := cell_6_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_6_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (85*n+2290)
                    · have hf := cell_6_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (104*n+2802)
                      · have hf := cell_6_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (108*n+2910)
                        · have hf := cell_6_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3071)
                          · have hf := cell_6_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (123*n+3314)
                            · have hf := cell_6_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (142*n+3826)
                              · have hf := cell_6_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_6_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) ∪ (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ)) (Finset.Ico (47*n+1266) (66*n+1778) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) ∪ (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (47*n+1266) (66*n+1778) : Finset ℕ)) (Finset.Ico (66*n+1778) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) ∪ (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (47*n+1266) (66*n+1778) : Finset ℕ)) ∪ (Finset.Ico (66*n+1778) (76*n+2048) : Finset ℕ)) (Finset.Ico (85*n+2290) (104*n+2802) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) ∪ (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (47*n+1266) (66*n+1778) : Finset ℕ)) ∪ (Finset.Ico (66*n+1778) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (85*n+2290) (104*n+2802) : Finset ℕ)) (Finset.Ico (108*n+2910) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) ∪ (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (47*n+1266) (66*n+1778) : Finset ℕ)) ∪ (Finset.Ico (66*n+1778) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (85*n+2290) (104*n+2802) : Finset ℕ)) ∪ (Finset.Ico (108*n+2910) (114*n+3071) : Finset ℕ)) (Finset.Ico (123*n+3314) (142*n+3826) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (9*n+243) : Finset ℕ) ∪ (Finset.Ico (32*n+862) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (47*n+1266) (66*n+1778) : Finset ℕ)) ∪ (Finset.Ico (66*n+1778) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (85*n+2290) (104*n+2802) : Finset ℕ)) ∪ (Finset.Ico (108*n+2910) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (123*n+3314) (142*n+3826) : Finset ℕ)) (Finset.Ico (142*n+3826) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_7_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (1*n+27)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (1*(n:ℤ)+27) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (1*(n:ℤ)+27) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (1*(n:ℤ)+27) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (1*(n:ℤ)+27) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (1*(n:ℤ)+27) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_1 (n u : ℕ) (hu : (1*n+27) ≤ u ∧ u < (12*n+323)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (1*(n:ℤ)+27) (12*(n:ℤ)+323) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (1*(n:ℤ)+27) (12*(n:ℤ)+323) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (1*(n:ℤ)+27) (12*(n:ℤ)+323) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (1*(n:ℤ)+27) (12*(n:ℤ)+323) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (1*(n:ℤ)+27) (12*(n:ℤ)+323) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_2 (n u : ℕ) (hu : (12*n+323) ≤ u ∧ u < (20*n+539)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (12*(n:ℤ)+323) (20*(n:ℤ)+539) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (12*(n:ℤ)+323) (20*(n:ℤ)+539) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (12*(n:ℤ)+323) (20*(n:ℤ)+539) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (12*(n:ℤ)+323) (20*(n:ℤ)+539) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (12*(n:ℤ)+323) (20*(n:ℤ)+539) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_3 (n u : ℕ) (hu : (20*n+539) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (20*(n:ℤ)+539) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (20*(n:ℤ)+539) (38*(n:ℤ)+1024) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (20*(n:ℤ)+539) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (20*(n:ℤ)+539) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (20*(n:ℤ)+539) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_4 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (39*n+1051)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (39*(n:ℤ)+1051) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (39*(n:ℤ)+1051) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (39*(n:ℤ)+1051) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (39*(n:ℤ)+1051) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (39*(n:ℤ)+1051) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_5 (n u : ℕ) (hu : (39*n+1051) ≤ u ∧ u < (58*n+1563)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (39*(n:ℤ)+1051) (58*(n:ℤ)+1563) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (39*(n:ℤ)+1051) (58*(n:ℤ)+1563) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (39*(n:ℤ)+1051) (58*(n:ℤ)+1563) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (39*(n:ℤ)+1051) (58*(n:ℤ)+1563) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (39*(n:ℤ)+1051) (58*(n:ℤ)+1563) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_6 (n u : ℕ) (hu : (58*n+1563) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (58*(n:ℤ)+1563) (76*(n:ℤ)+2048) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (58*(n:ℤ)+1563) (76*(n:ℤ)+2048) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (58*(n:ℤ)+1563) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (58*(n:ℤ)+1563) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (58*(n:ℤ)+1563) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (77*n+2075)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (77*(n:ℤ)+2075) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (77*(n:ℤ)+2075) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (77*(n:ℤ)+2075) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (77*(n:ℤ)+2075) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (77*(n:ℤ)+2075) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_8 (n u : ℕ) (hu : (77*n+2075) ≤ u ∧ u < (88*n+2371)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (77*(n:ℤ)+2075) (88*(n:ℤ)+2371) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (77*(n:ℤ)+2075) (88*(n:ℤ)+2371) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (77*(n:ℤ)+2075) (88*(n:ℤ)+2371) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (77*(n:ℤ)+2075) (88*(n:ℤ)+2371) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (77*(n:ℤ)+2075) (88*(n:ℤ)+2371) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_9 (n u : ℕ) (hu : (88*n+2371) ≤ u ∧ u < (96*n+2586)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (88*(n:ℤ)+2371) (96*(n:ℤ)+2586) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (88*(n:ℤ)+2371) (96*(n:ℤ)+2586) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (88*(n:ℤ)+2371) (96*(n:ℤ)+2586) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (88*(n:ℤ)+2371) (96*(n:ℤ)+2586) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (88*(n:ℤ)+2371) (96*(n:ℤ)+2586) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_10 (n u : ℕ) (hu : (96*n+2586) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (96*(n:ℤ)+2586) (114*(n:ℤ)+3071) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (96*(n:ℤ)+2586) (114*(n:ℤ)+3071) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (96*(n:ℤ)+2586) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (96*(n:ℤ)+2586) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (96*(n:ℤ)+2586) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_11 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (115*n+3098)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (115*(n:ℤ)+3098) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (115*(n:ℤ)+3098) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (115*(n:ℤ)+3098) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (115*(n:ℤ)+3098) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (115*(n:ℤ)+3098) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_12 (n u : ℕ) (hu : (115*n+3098) ≤ u ∧ u < (134*n+3610)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (115*(n:ℤ)+3098) (134*(n:ℤ)+3610) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (115*(n:ℤ)+3098) (134*(n:ℤ)+3610) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (115*(n:ℤ)+3098) (134*(n:ℤ)+3610) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (115*(n:ℤ)+3098) (134*(n:ℤ)+3610) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (115*(n:ℤ)+3098) (134*(n:ℤ)+3610) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_7_13 (n u : ℕ) (hu : (134*n+3610) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 7 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*7))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*7) (19*(152*((n:ℤ)+27)-8)) (134*(n:ℤ)+3610) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (134*(n:ℤ)+3610) (152*(n:ℤ)+4095) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (134*(n:ℤ)+3610) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (134*(n:ℤ)+3610) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*7*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (134*(n:ℤ)+3610) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_7 (n : ℕ) :
    rowZeroCount (n+27) 7 = 130*n+3503 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 7 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 7 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 7 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 7=0) = (((((((((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) ∪ (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (39*n+1051) (58*n+1563) : Finset ℕ)) ∪ (Finset.Ico (58*n+1563) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (77*n+2075) (88*n+2371) : Finset ℕ)) ∪ (Finset.Ico (96*n+2586) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (115*n+3098) (134*n+3610) : Finset ℕ)) ∪ (Finset.Ico (134*n+3610) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (1*n+27)
      · have hf := cell_7_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (12*n+323)
        · have hf := cell_7_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (20*n+539)
          · have hf := cell_7_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1024)
            · have hf := cell_7_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (39*n+1051)
              · have hf := cell_7_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (58*n+1563)
                · have hf := cell_7_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_7_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (77*n+2075)
                    · have hf := cell_7_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (88*n+2371)
                      · have hf := cell_7_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (96*n+2586)
                        · have hf := cell_7_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3071)
                          · have hf := cell_7_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (115*n+3098)
                            · have hf := cell_7_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (134*n+3610)
                              · have hf := cell_7_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_7_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) ∪ (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ)) (Finset.Ico (39*n+1051) (58*n+1563) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) ∪ (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (39*n+1051) (58*n+1563) : Finset ℕ)) (Finset.Ico (58*n+1563) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) ∪ (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (39*n+1051) (58*n+1563) : Finset ℕ)) ∪ (Finset.Ico (58*n+1563) (76*n+2048) : Finset ℕ)) (Finset.Ico (77*n+2075) (88*n+2371) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) ∪ (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (39*n+1051) (58*n+1563) : Finset ℕ)) ∪ (Finset.Ico (58*n+1563) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (77*n+2075) (88*n+2371) : Finset ℕ)) (Finset.Ico (96*n+2586) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) ∪ (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (39*n+1051) (58*n+1563) : Finset ℕ)) ∪ (Finset.Ico (58*n+1563) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (77*n+2075) (88*n+2371) : Finset ℕ)) ∪ (Finset.Ico (96*n+2586) (114*n+3071) : Finset ℕ)) (Finset.Ico (115*n+3098) (134*n+3610) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0*n+0) (1*n+27) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (20*n+539) : Finset ℕ)) ∪ (Finset.Ico (20*n+539) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (39*n+1051) (58*n+1563) : Finset ℕ)) ∪ (Finset.Ico (58*n+1563) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (77*n+2075) (88*n+2371) : Finset ℕ)) ∪ (Finset.Ico (96*n+2586) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (115*n+3098) (134*n+3610) : Finset ℕ)) (Finset.Ico (134*n+3610) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_8_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (12*n+323)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (12*(n:ℤ)+323) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (12*(n:ℤ)+323) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (12*(n:ℤ)+323) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (12*(n:ℤ)+323) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (12*(n:ℤ)+323) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_1 (n u : ℕ) (hu : (12*n+323) ≤ u ∧ u < (31*n+835)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (12*(n:ℤ)+323) (31*(n:ℤ)+835) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (12*(n:ℤ)+323) (31*(n:ℤ)+835) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (12*(n:ℤ)+323) (31*(n:ℤ)+835) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (12*(n:ℤ)+323) (31*(n:ℤ)+835) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (12*(n:ℤ)+323) (31*(n:ℤ)+835) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_2 (n u : ℕ) (hu : (31*n+835) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (31*(n:ℤ)+835) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (31*(n:ℤ)+835) (38*(n:ℤ)+1024) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (31*(n:ℤ)+835) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (31*(n:ℤ)+835) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (31*(n:ℤ)+835) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_3 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (50*n+1347)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (50*(n:ℤ)+1347) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (50*(n:ℤ)+1347) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (50*(n:ℤ)+1347) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (50*(n:ℤ)+1347) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (50*(n:ℤ)+1347) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_4 (n u : ℕ) (hu : (50*n+1347) ≤ u ∧ u < (68*n+1832)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (50*(n:ℤ)+1347) (68*(n:ℤ)+1832) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (50*(n:ℤ)+1347) (68*(n:ℤ)+1832) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (50*(n:ℤ)+1347) (68*(n:ℤ)+1832) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (50*(n:ℤ)+1347) (68*(n:ℤ)+1832) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (50*(n:ℤ)+1347) (68*(n:ℤ)+1832) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_5 (n u : ℕ) (hu : (68*n+1832) ≤ u ∧ u < (69*n+1859)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (68*(n:ℤ)+1832) (69*(n:ℤ)+1859) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (68*(n:ℤ)+1832) (69*(n:ℤ)+1859) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (68*(n:ℤ)+1832) (69*(n:ℤ)+1859) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (68*(n:ℤ)+1832) (69*(n:ℤ)+1859) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (68*(n:ℤ)+1832) (69*(n:ℤ)+1859) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_6 (n u : ℕ) (hu : (69*n+1859) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (69*(n:ℤ)+1859) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (69*(n:ℤ)+1859) (76*(n:ℤ)+2048) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (69*(n:ℤ)+1859) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (69*(n:ℤ)+1859) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (69*(n:ℤ)+1859) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (88*n+2371)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (88*(n:ℤ)+2371) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (88*(n:ℤ)+2371) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (88*(n:ℤ)+2371) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (88*(n:ℤ)+2371) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (88*(n:ℤ)+2371) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_8 (n u : ℕ) (hu : (88*n+2371) ≤ u ∧ u < (107*n+2883)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (88*(n:ℤ)+2371) (107*(n:ℤ)+2883) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (88*(n:ℤ)+2371) (107*(n:ℤ)+2883) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (88*(n:ℤ)+2371) (107*(n:ℤ)+2883) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (88*(n:ℤ)+2371) (107*(n:ℤ)+2883) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (88*(n:ℤ)+2371) (107*(n:ℤ)+2883) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_9 (n u : ℕ) (hu : (107*n+2883) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (107*(n:ℤ)+2883) (114*(n:ℤ)+3071) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (107*(n:ℤ)+2883) (114*(n:ℤ)+3071) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (107*(n:ℤ)+2883) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (107*(n:ℤ)+2883) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (107*(n:ℤ)+2883) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_10 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (126*n+3395)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (126*(n:ℤ)+3395) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (126*(n:ℤ)+3395) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (126*(n:ℤ)+3395) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (126*(n:ℤ)+3395) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (126*(n:ℤ)+3395) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_11 (n u : ℕ) (hu : (126*n+3395) ≤ u ∧ u < (144*n+3880)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (126*(n:ℤ)+3395) (144*(n:ℤ)+3880) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (126*(n:ℤ)+3395) (144*(n:ℤ)+3880) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (126*(n:ℤ)+3395) (144*(n:ℤ)+3880) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (126*(n:ℤ)+3395) (144*(n:ℤ)+3880) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (126*(n:ℤ)+3395) (144*(n:ℤ)+3880) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_12 (n u : ℕ) (hu : (144*n+3880) ≤ u ∧ u < (145*n+3906)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (144*(n:ℤ)+3880) (145*(n:ℤ)+3906) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (144*(n:ℤ)+3880) (145*(n:ℤ)+3906) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (144*(n:ℤ)+3880) (145*(n:ℤ)+3906) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (144*(n:ℤ)+3880) (145*(n:ℤ)+3906) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (144*(n:ℤ)+3880) (145*(n:ℤ)+3906) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_8_13 (n u : ℕ) (hu : (145*n+3906) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 8 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*8))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*8) (19*(152*((n:ℤ)+27)-8)) (145*(n:ℤ)+3906) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (145*(n:ℤ)+3906) (152*(n:ℤ)+4095) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (145*(n:ℤ)+3906) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (145*(n:ℤ)+3906) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*8*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (145*(n:ℤ)+3906) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_8 (n : ℕ) :
    rowZeroCount (n+27) 8 = 124*n+3342 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 8 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 8 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 8 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 8=0) = (((((((((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ)) ∪ (Finset.Ico (50*n+1347) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (69*n+1859) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (88*n+2371) (107*n+2883) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (126*n+3395) : Finset ℕ)) ∪ (Finset.Ico (126*n+3395) (144*n+3880) : Finset ℕ)) ∪ (Finset.Ico (145*n+3906) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (12*n+323)
      · have hf := cell_8_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (31*n+835)
        · have hf := cell_8_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1024)
          · have hf := cell_8_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (50*n+1347)
            · have hf := cell_8_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (68*n+1832)
              · have hf := cell_8_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (69*n+1859)
                · have hf := cell_8_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_8_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (88*n+2371)
                    · have hf := cell_8_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (107*n+2883)
                      · have hf := cell_8_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3071)
                        · have hf := cell_8_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (126*n+3395)
                          · have hf := cell_8_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (144*n+3880)
                            · have hf := cell_8_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (145*n+3906)
                              · have hf := cell_8_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_8_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ)) (Finset.Ico (50*n+1347) (68*n+1832) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ)) ∪ (Finset.Ico (50*n+1347) (68*n+1832) : Finset ℕ)) (Finset.Ico (69*n+1859) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ)) ∪ (Finset.Ico (50*n+1347) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (69*n+1859) (76*n+2048) : Finset ℕ)) (Finset.Ico (88*n+2371) (107*n+2883) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ)) ∪ (Finset.Ico (50*n+1347) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (69*n+1859) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (88*n+2371) (107*n+2883) : Finset ℕ)) (Finset.Ico (114*n+3071) (126*n+3395) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ)) ∪ (Finset.Ico (50*n+1347) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (69*n+1859) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (88*n+2371) (107*n+2883) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (126*n+3395) : Finset ℕ)) (Finset.Ico (126*n+3395) (144*n+3880) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0*n+0) (12*n+323) : Finset ℕ) ∪ (Finset.Ico (12*n+323) (31*n+835) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (50*n+1347) : Finset ℕ)) ∪ (Finset.Ico (50*n+1347) (68*n+1832) : Finset ℕ)) ∪ (Finset.Ico (69*n+1859) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (88*n+2371) (107*n+2883) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (126*n+3395) : Finset ℕ)) ∪ (Finset.Ico (126*n+3395) (144*n+3880) : Finset ℕ)) (Finset.Ico (145*n+3906) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_9_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (4*n+108)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (4*(n:ℤ)+108) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (4*(n:ℤ)+108) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (4*(n:ℤ)+108) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (4*(n:ℤ)+108) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (4*(n:ℤ)+108) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_1 (n u : ℕ) (hu : (4*n+108) ≤ u ∧ u < (23*n+620)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (4*(n:ℤ)+108) (23*(n:ℤ)+620) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (4*(n:ℤ)+108) (23*(n:ℤ)+620) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (4*(n:ℤ)+108) (23*(n:ℤ)+620) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (4*(n:ℤ)+108) (23*(n:ℤ)+620) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (4*(n:ℤ)+108) (23*(n:ℤ)+620) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_2 (n u : ℕ) (hu : (23*n+620) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (23*(n:ℤ)+620) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (23*(n:ℤ)+620) (38*(n:ℤ)+1024) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (23*(n:ℤ)+620) (38*(n:ℤ)+1024) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (23*(n:ℤ)+620) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (23*(n:ℤ)+620) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_3 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (42*n+1132)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (42*(n:ℤ)+1132) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (42*(n:ℤ)+1132) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (42*(n:ℤ)+1132) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (42*(n:ℤ)+1132) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (42*(n:ℤ)+1132) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_4 (n u : ℕ) (hu : (42*n+1132) ≤ u ∧ u < (48*n+1293)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (42*(n:ℤ)+1132) (48*(n:ℤ)+1293) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (42*(n:ℤ)+1132) (48*(n:ℤ)+1293) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (42*(n:ℤ)+1132) (48*(n:ℤ)+1293) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (42*(n:ℤ)+1132) (48*(n:ℤ)+1293) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (42*(n:ℤ)+1132) (48*(n:ℤ)+1293) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_5 (n u : ℕ) (hu : (48*n+1293) ≤ u ∧ u < (61*n+1643)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (48*(n:ℤ)+1293) (61*(n:ℤ)+1643) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (48*(n:ℤ)+1293) (61*(n:ℤ)+1643) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (48*(n:ℤ)+1293) (61*(n:ℤ)+1643) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (48*(n:ℤ)+1293) (61*(n:ℤ)+1643) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (48*(n:ℤ)+1293) (61*(n:ℤ)+1643) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_6 (n u : ℕ) (hu : (61*n+1643) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (61*(n:ℤ)+1643) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (61*(n:ℤ)+1643) (76*(n:ℤ)+2048) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (61*(n:ℤ)+1643) (76*(n:ℤ)+2048) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (61*(n:ℤ)+1643) (76*(n:ℤ)+2048) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (61*(n:ℤ)+1643) (76*(n:ℤ)+2048) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_7 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (80*n+2155)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (80*(n:ℤ)+2155) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (80*(n:ℤ)+2155) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (80*(n:ℤ)+2155) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (80*(n:ℤ)+2155) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (80*(n:ℤ)+2155) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_8 (n u : ℕ) (hu : (80*n+2155) ≤ u ∧ u < (99*n+2667)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (80*(n:ℤ)+2155) (99*(n:ℤ)+2667) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (80*(n:ℤ)+2155) (99*(n:ℤ)+2667) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (80*(n:ℤ)+2155) (99*(n:ℤ)+2667) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (80*(n:ℤ)+2155) (99*(n:ℤ)+2667) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (80*(n:ℤ)+2155) (99*(n:ℤ)+2667) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_9 (n u : ℕ) (hu : (99*n+2667) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (99*(n:ℤ)+2667) (114*(n:ℤ)+3071) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (99*(n:ℤ)+2667) (114*(n:ℤ)+3071) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (99*(n:ℤ)+2667) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (99*(n:ℤ)+2667) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (99*(n:ℤ)+2667) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_10 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (118*n+3179)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (118*(n:ℤ)+3179) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (118*(n:ℤ)+3179) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (118*(n:ℤ)+3179) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (118*(n:ℤ)+3179) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (118*(n:ℤ)+3179) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_11 (n u : ℕ) (hu : (118*n+3179) ≤ u ∧ u < (124*n+3341)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (118*(n:ℤ)+3179) (124*(n:ℤ)+3341) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (118*(n:ℤ)+3179) (124*(n:ℤ)+3341) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (118*(n:ℤ)+3179) (124*(n:ℤ)+3341) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (118*(n:ℤ)+3179) (124*(n:ℤ)+3341) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (118*(n:ℤ)+3179) (124*(n:ℤ)+3341) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_12 (n u : ℕ) (hu : (124*n+3341) ≤ u ∧ u < (137*n+3691)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (124*(n:ℤ)+3341) (137*(n:ℤ)+3691) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (124*(n:ℤ)+3341) (137*(n:ℤ)+3691) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (124*(n:ℤ)+3341) (137*(n:ℤ)+3691) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (124*(n:ℤ)+3341) (137*(n:ℤ)+3691) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (124*(n:ℤ)+3341) (137*(n:ℤ)+3691) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_9_13 (n u : ℕ) (hu : (137*n+3691) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 9 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*9))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*9) (19*(152*((n:ℤ)+27)-8)) (137*(n:ℤ)+3691) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (137*(n:ℤ)+3691) (152*(n:ℤ)+4095) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (137*(n:ℤ)+3691) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (137*(n:ℤ)+3691) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*9*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (137*(n:ℤ)+3691) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_9 (n : ℕ) :
    rowZeroCount (n+27) 9 = 92*n+2480 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 9 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 9 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 9 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 9=0) = (((((((((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ)) ∪ (Finset.Ico (42*n+1132) (48*n+1293) : Finset ℕ)) ∪ (Finset.Ico (61*n+1643) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (80*n+2155) (99*n+2667) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (118*n+3179) : Finset ℕ)) ∪ (Finset.Ico (118*n+3179) (124*n+3341) : Finset ℕ)) ∪ (Finset.Ico (137*n+3691) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (4*n+108)
      · have hf := cell_9_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (23*n+620)
        · have hf := cell_9_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1024)
          · have hf := cell_9_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (42*n+1132)
            · have hf := cell_9_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (48*n+1293)
              · have hf := cell_9_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (61*n+1643)
                · have hf := cell_9_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2048)
                  · have hf := cell_9_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (80*n+2155)
                    · have hf := cell_9_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (99*n+2667)
                      · have hf := cell_9_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3071)
                        · have hf := cell_9_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (118*n+3179)
                          · have hf := cell_9_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (124*n+3341)
                            · have hf := cell_9_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (137*n+3691)
                              · have hf := cell_9_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_9_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ)) (Finset.Ico (42*n+1132) (48*n+1293) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ)) ∪ (Finset.Ico (42*n+1132) (48*n+1293) : Finset ℕ)) (Finset.Ico (61*n+1643) (76*n+2048) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ)) ∪ (Finset.Ico (42*n+1132) (48*n+1293) : Finset ℕ)) ∪ (Finset.Ico (61*n+1643) (76*n+2048) : Finset ℕ)) (Finset.Ico (80*n+2155) (99*n+2667) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ)) ∪ (Finset.Ico (42*n+1132) (48*n+1293) : Finset ℕ)) ∪ (Finset.Ico (61*n+1643) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (80*n+2155) (99*n+2667) : Finset ℕ)) (Finset.Ico (114*n+3071) (118*n+3179) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ)) ∪ (Finset.Ico (42*n+1132) (48*n+1293) : Finset ℕ)) ∪ (Finset.Ico (61*n+1643) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (80*n+2155) (99*n+2667) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (118*n+3179) : Finset ℕ)) (Finset.Ico (118*n+3179) (124*n+3341) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0*n+0) (4*n+108) : Finset ℕ) ∪ (Finset.Ico (4*n+108) (23*n+620) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (42*n+1132) : Finset ℕ)) ∪ (Finset.Ico (42*n+1132) (48*n+1293) : Finset ℕ)) ∪ (Finset.Ico (61*n+1643) (76*n+2048) : Finset ℕ)) ∪ (Finset.Ico (80*n+2155) (99*n+2667) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (118*n+3179) : Finset ℕ)) ∪ (Finset.Ico (118*n+3179) (124*n+3341) : Finset ℕ)) (Finset.Ico (137*n+3691) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_10_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (15*n+404)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (15*(n:ℤ)+404) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (15*(n:ℤ)+404) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (15*(n:ℤ)+404) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (15*(n:ℤ)+404) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (15*(n:ℤ)+404) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_1 (n u : ℕ) (hu : (15*n+404) ≤ u ∧ u < (28*n+754)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (15*(n:ℤ)+404) (28*(n:ℤ)+754) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (15*(n:ℤ)+404) (28*(n:ℤ)+754) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (15*(n:ℤ)+404) (28*(n:ℤ)+754) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (15*(n:ℤ)+404) (28*(n:ℤ)+754) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (15*(n:ℤ)+404) (28*(n:ℤ)+754) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_2 (n u : ℕ) (hu : (28*n+754) ≤ u ∧ u < (34*n+916)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (28*(n:ℤ)+754) (34*(n:ℤ)+916) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (28*(n:ℤ)+754) (34*(n:ℤ)+916) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (28*(n:ℤ)+754) (34*(n:ℤ)+916) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (28*(n:ℤ)+754) (34*(n:ℤ)+916) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (28*(n:ℤ)+754) (34*(n:ℤ)+916) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_3 (n u : ℕ) (hu : (34*n+916) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (34*(n:ℤ)+916) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (34*(n:ℤ)+916) (38*(n:ℤ)+1024) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (34*(n:ℤ)+916) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (34*(n:ℤ)+916) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (34*(n:ℤ)+916) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_4 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (53*n+1428)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (53*(n:ℤ)+1428) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (53*(n:ℤ)+1428) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (53*(n:ℤ)+1428) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (53*(n:ℤ)+1428) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (53*(n:ℤ)+1428) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_5 (n u : ℕ) (hu : (53*n+1428) ≤ u ∧ u < (72*n+1940)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (53*(n:ℤ)+1428) (72*(n:ℤ)+1940) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (53*(n:ℤ)+1428) (72*(n:ℤ)+1940) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (53*(n:ℤ)+1428) (72*(n:ℤ)+1940) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (53*(n:ℤ)+1428) (72*(n:ℤ)+1940) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (53*(n:ℤ)+1428) (72*(n:ℤ)+1940) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_6 (n u : ℕ) (hu : (72*n+1940) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (72*(n:ℤ)+1940) (76*(n:ℤ)+2047) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (72*(n:ℤ)+1940) (76*(n:ℤ)+2047) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (72*(n:ℤ)+1940) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (72*(n:ℤ)+1940) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (72*(n:ℤ)+1940) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (91*n+2452)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (91*(n:ℤ)+2452) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (91*(n:ℤ)+2452) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (91*(n:ℤ)+2452) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (91*(n:ℤ)+2452) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (91*(n:ℤ)+2452) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_8 (n u : ℕ) (hu : (91*n+2452) ≤ u ∧ u < (104*n+2802)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (91*(n:ℤ)+2452) (104*(n:ℤ)+2802) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (91*(n:ℤ)+2452) (104*(n:ℤ)+2802) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (91*(n:ℤ)+2452) (104*(n:ℤ)+2802) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (91*(n:ℤ)+2452) (104*(n:ℤ)+2802) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (91*(n:ℤ)+2452) (104*(n:ℤ)+2802) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_9 (n u : ℕ) (hu : (104*n+2802) ≤ u ∧ u < (110*n+2963)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (104*(n:ℤ)+2802) (110*(n:ℤ)+2963) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (104*(n:ℤ)+2802) (110*(n:ℤ)+2963) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (104*(n:ℤ)+2802) (110*(n:ℤ)+2963) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (104*(n:ℤ)+2802) (110*(n:ℤ)+2963) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (104*(n:ℤ)+2802) (110*(n:ℤ)+2963) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_10 (n u : ℕ) (hu : (110*n+2963) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (110*(n:ℤ)+2963) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (110*(n:ℤ)+2963) (114*(n:ℤ)+3071) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (110*(n:ℤ)+2963) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (110*(n:ℤ)+2963) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (110*(n:ℤ)+2963) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_11 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (129*n+3475)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (129*(n:ℤ)+3475) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (129*(n:ℤ)+3475) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (129*(n:ℤ)+3475) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (129*(n:ℤ)+3475) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (129*(n:ℤ)+3475) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_12 (n u : ℕ) (hu : (129*n+3475) ≤ u ∧ u < (148*n+3987)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (129*(n:ℤ)+3475) (148*(n:ℤ)+3987) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (129*(n:ℤ)+3475) (148*(n:ℤ)+3987) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (129*(n:ℤ)+3475) (148*(n:ℤ)+3987) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (129*(n:ℤ)+3475) (148*(n:ℤ)+3987) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (129*(n:ℤ)+3475) (148*(n:ℤ)+3987) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_10_13 (n u : ℕ) (hu : (148*n+3987) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 10 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*10))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*10) (19*(152*((n:ℤ)+27)-8)) (148*(n:ℤ)+3987) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (148*(n:ℤ)+3987) (152*(n:ℤ)+4095) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (148*(n:ℤ)+3987) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (148*(n:ℤ)+3987) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*10*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (148*(n:ℤ)+3987) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_10 (n : ℕ) :
    rowZeroCount (n+27) 10 = 92*n+2480 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 10 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 10 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 10 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 10=0) = (((((((((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) ∪ (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (53*n+1428) (72*n+1940) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (91*n+2452) : Finset ℕ)) ∪ (Finset.Ico (104*n+2802) (110*n+2963) : Finset ℕ)) ∪ (Finset.Ico (110*n+2963) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (129*n+3475) (148*n+3987) : Finset ℕ)) ∪ (Finset.Ico (148*n+3987) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (15*n+404)
      · have hf := cell_10_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (28*n+754)
        · have hf := cell_10_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (34*n+916)
          · have hf := cell_10_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1024)
            · have hf := cell_10_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (53*n+1428)
              · have hf := cell_10_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (72*n+1940)
                · have hf := cell_10_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_10_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (91*n+2452)
                    · have hf := cell_10_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (104*n+2802)
                      · have hf := cell_10_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (110*n+2963)
                        · have hf := cell_10_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3071)
                          · have hf := cell_10_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (129*n+3475)
                            · have hf := cell_10_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (148*n+3987)
                              · have hf := cell_10_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_10_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) ∪ (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ)) (Finset.Ico (53*n+1428) (72*n+1940) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) ∪ (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (53*n+1428) (72*n+1940) : Finset ℕ)) (Finset.Ico (76*n+2047) (91*n+2452) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) ∪ (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (53*n+1428) (72*n+1940) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (91*n+2452) : Finset ℕ)) (Finset.Ico (104*n+2802) (110*n+2963) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) ∪ (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (53*n+1428) (72*n+1940) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (91*n+2452) : Finset ℕ)) ∪ (Finset.Ico (104*n+2802) (110*n+2963) : Finset ℕ)) (Finset.Ico (110*n+2963) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) ∪ (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (53*n+1428) (72*n+1940) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (91*n+2452) : Finset ℕ)) ∪ (Finset.Ico (104*n+2802) (110*n+2963) : Finset ℕ)) ∪ (Finset.Ico (110*n+2963) (114*n+3071) : Finset ℕ)) (Finset.Ico (129*n+3475) (148*n+3987) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0*n+0) (15*n+404) : Finset ℕ) ∪ (Finset.Ico (28*n+754) (34*n+916) : Finset ℕ)) ∪ (Finset.Ico (34*n+916) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (53*n+1428) (72*n+1940) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (91*n+2452) : Finset ℕ)) ∪ (Finset.Ico (104*n+2802) (110*n+2963) : Finset ℕ)) ∪ (Finset.Ico (110*n+2963) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (129*n+3475) (148*n+3987) : Finset ℕ)) (Finset.Ico (148*n+3987) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_11_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (7*n+189)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (7*(n:ℤ)+189) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (7*(n:ℤ)+189) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (7*(n:ℤ)+189) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (7*(n:ℤ)+189) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (7*(n:ℤ)+189) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_1 (n u : ℕ) (hu : (7*n+189) ≤ u ∧ u < (8*n+215)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 2 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (7*(n:ℤ)+189) (8*(n:ℤ)+215) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (7*(n:ℤ)+189) (8*(n:ℤ)+215) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (7*(n:ℤ)+189) (8*(n:ℤ)+215) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (7*(n:ℤ)+189) (8*(n:ℤ)+215) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (7*(n:ℤ)+189) (8*(n:ℤ)+215) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_2 (n u : ℕ) (hu : (8*n+215) ≤ u ∧ u < (26*n+700)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (8*(n:ℤ)+215) (26*(n:ℤ)+700) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (8*(n:ℤ)+215) (26*(n:ℤ)+700) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (8*(n:ℤ)+215) (26*(n:ℤ)+700) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (8*(n:ℤ)+215) (26*(n:ℤ)+700) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (8*(n:ℤ)+215) (26*(n:ℤ)+700) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_3 (n u : ℕ) (hu : (26*n+700) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (26*(n:ℤ)+700) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (26*(n:ℤ)+700) (38*(n:ℤ)+1024) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (26*(n:ℤ)+700) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (26*(n:ℤ)+700) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (26*(n:ℤ)+700) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_4 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (45*n+1212)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (45*(n:ℤ)+1212) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (45*(n:ℤ)+1212) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (45*(n:ℤ)+1212) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (45*(n:ℤ)+1212) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (45*(n:ℤ)+1212) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_5 (n u : ℕ) (hu : (45*n+1212) ≤ u ∧ u < (64*n+1724)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (45*(n:ℤ)+1212) (64*(n:ℤ)+1724) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (45*(n:ℤ)+1212) (64*(n:ℤ)+1724) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (45*(n:ℤ)+1212) (64*(n:ℤ)+1724) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (45*(n:ℤ)+1212) (64*(n:ℤ)+1724) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (45*(n:ℤ)+1212) (64*(n:ℤ)+1724) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_6 (n u : ℕ) (hu : (64*n+1724) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (64*(n:ℤ)+1724) (76*(n:ℤ)+2047) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (64*(n:ℤ)+1724) (76*(n:ℤ)+2047) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (64*(n:ℤ)+1724) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (64*(n:ℤ)+1724) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (64*(n:ℤ)+1724) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (83*n+2236)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (83*(n:ℤ)+2236) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (83*(n:ℤ)+2236) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (83*(n:ℤ)+2236) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (83*(n:ℤ)+2236) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (83*(n:ℤ)+2236) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_8 (n u : ℕ) (hu : (83*n+2236) ≤ u ∧ u < (84*n+2263)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (83*(n:ℤ)+2236) (84*(n:ℤ)+2263) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (83*(n:ℤ)+2236) (84*(n:ℤ)+2263) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (83*(n:ℤ)+2236) (84*(n:ℤ)+2263) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (83*(n:ℤ)+2236) (84*(n:ℤ)+2263) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (83*(n:ℤ)+2236) (84*(n:ℤ)+2263) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_9 (n u : ℕ) (hu : (84*n+2263) ≤ u ∧ u < (102*n+2748)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (84*(n:ℤ)+2263) (102*(n:ℤ)+2748) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (84*(n:ℤ)+2263) (102*(n:ℤ)+2748) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (84*(n:ℤ)+2263) (102*(n:ℤ)+2748) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (84*(n:ℤ)+2263) (102*(n:ℤ)+2748) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (84*(n:ℤ)+2263) (102*(n:ℤ)+2748) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_10 (n u : ℕ) (hu : (102*n+2748) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (102*(n:ℤ)+2748) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (102*(n:ℤ)+2748) (114*(n:ℤ)+3071) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (102*(n:ℤ)+2748) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (102*(n:ℤ)+2748) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (102*(n:ℤ)+2748) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_11 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (121*n+3260)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (121*(n:ℤ)+3260) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (121*(n:ℤ)+3260) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (121*(n:ℤ)+3260) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (121*(n:ℤ)+3260) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (121*(n:ℤ)+3260) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_12 (n u : ℕ) (hu : (121*n+3260) ≤ u ∧ u < (140*n+3772)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (121*(n:ℤ)+3260) (140*(n:ℤ)+3772) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (121*(n:ℤ)+3260) (140*(n:ℤ)+3772) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (121*(n:ℤ)+3260) (140*(n:ℤ)+3772) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (121*(n:ℤ)+3260) (140*(n:ℤ)+3772) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (121*(n:ℤ)+3260) (140*(n:ℤ)+3772) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_11_13 (n u : ℕ) (hu : (140*n+3772) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 11 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*11))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*11) (19*(152*((n:ℤ)+27)-8)) (140*(n:ℤ)+3772) (152*(n:ℤ)+4095) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (140*(n:ℤ)+3772) (152*(n:ℤ)+4095) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (140*(n:ℤ)+3772) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (140*(n:ℤ)+3772) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*11*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (140*(n:ℤ)+3772) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_11 (n : ℕ) :
    rowZeroCount (n+27) 11 = 124*n+3342 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 11 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 11 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 11 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 11=0) = (((((((((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) ∪ (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (45*n+1212) (64*n+1724) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (83*n+2236) : Finset ℕ)) ∪ (Finset.Ico (84*n+2263) (102*n+2748) : Finset ℕ)) ∪ (Finset.Ico (102*n+2748) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (121*n+3260) (140*n+3772) : Finset ℕ)) ∪ (Finset.Ico (140*n+3772) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (7*n+189)
      · have hf := cell_11_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (8*n+215)
        · have hf := cell_11_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (26*n+700)
          · have hf := cell_11_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1024)
            · have hf := cell_11_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (45*n+1212)
              · have hf := cell_11_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (64*n+1724)
                · have hf := cell_11_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_11_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (83*n+2236)
                    · have hf := cell_11_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (84*n+2263)
                      · have hf := cell_11_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (102*n+2748)
                        · have hf := cell_11_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3071)
                          · have hf := cell_11_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (121*n+3260)
                            · have hf := cell_11_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (140*n+3772)
                              · have hf := cell_11_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_11_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) ∪ (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ)) (Finset.Ico (45*n+1212) (64*n+1724) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) ∪ (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (45*n+1212) (64*n+1724) : Finset ℕ)) (Finset.Ico (76*n+2047) (83*n+2236) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) ∪ (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (45*n+1212) (64*n+1724) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (83*n+2236) : Finset ℕ)) (Finset.Ico (84*n+2263) (102*n+2748) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) ∪ (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (45*n+1212) (64*n+1724) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (83*n+2236) : Finset ℕ)) ∪ (Finset.Ico (84*n+2263) (102*n+2748) : Finset ℕ)) (Finset.Ico (102*n+2748) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) ∪ (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (45*n+1212) (64*n+1724) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (83*n+2236) : Finset ℕ)) ∪ (Finset.Ico (84*n+2263) (102*n+2748) : Finset ℕ)) ∪ (Finset.Ico (102*n+2748) (114*n+3071) : Finset ℕ)) (Finset.Ico (121*n+3260) (140*n+3772) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0*n+0) (7*n+189) : Finset ℕ) ∪ (Finset.Ico (8*n+215) (26*n+700) : Finset ℕ)) ∪ (Finset.Ico (26*n+700) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (45*n+1212) (64*n+1724) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (83*n+2236) : Finset ℕ)) ∪ (Finset.Ico (84*n+2263) (102*n+2748) : Finset ℕ)) ∪ (Finset.Ico (102*n+2748) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (121*n+3260) (140*n+3772) : Finset ℕ)) (Finset.Ico (140*n+3772) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_12_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (18*n+485)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (18*(n:ℤ)+485) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (18*(n:ℤ)+485) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (18*(n:ℤ)+485) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (18*(n:ℤ)+485) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (18*(n:ℤ)+485) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_1 (n u : ℕ) (hu : (18*n+485) ≤ u ∧ u < (37*n+997)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (18*(n:ℤ)+485) (37*(n:ℤ)+997) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (18*(n:ℤ)+485) (37*(n:ℤ)+997) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (18*(n:ℤ)+485) (37*(n:ℤ)+997) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (18*(n:ℤ)+485) (37*(n:ℤ)+997) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (18*(n:ℤ)+485) (37*(n:ℤ)+997) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_2 (n u : ℕ) (hu : (37*n+997) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (37*(n:ℤ)+997) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (37*(n:ℤ)+997) (38*(n:ℤ)+1024) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (37*(n:ℤ)+997) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (37*(n:ℤ)+997) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (37*(n:ℤ)+997) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_3 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (56*n+1509)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (56*(n:ℤ)+1509) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (56*(n:ℤ)+1509) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (56*(n:ℤ)+1509) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (56*(n:ℤ)+1509) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (56*(n:ℤ)+1509) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_4 (n u : ℕ) (hu : (56*n+1509) ≤ u ∧ u < (64*n+1724)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (56*(n:ℤ)+1509) (64*(n:ℤ)+1724) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (56*(n:ℤ)+1509) (64*(n:ℤ)+1724) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (56*(n:ℤ)+1509) (64*(n:ℤ)+1724) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (56*(n:ℤ)+1509) (64*(n:ℤ)+1724) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (56*(n:ℤ)+1509) (64*(n:ℤ)+1724) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_5 (n u : ℕ) (hu : (64*n+1724) ≤ u ∧ u < (75*n+2020)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (64*(n:ℤ)+1724) (75*(n:ℤ)+2020) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (64*(n:ℤ)+1724) (75*(n:ℤ)+2020) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (64*(n:ℤ)+1724) (75*(n:ℤ)+2020) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (64*(n:ℤ)+1724) (75*(n:ℤ)+2020) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (64*(n:ℤ)+1724) (75*(n:ℤ)+2020) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_6 (n u : ℕ) (hu : (75*n+2020) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (75*(n:ℤ)+2020) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (75*(n:ℤ)+2020) (76*(n:ℤ)+2047) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (75*(n:ℤ)+2020) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (75*(n:ℤ)+2020) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (75*(n:ℤ)+2020) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (94*n+2532)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (94*(n:ℤ)+2532) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (94*(n:ℤ)+2532) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (94*(n:ℤ)+2532) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (94*(n:ℤ)+2532) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (94*(n:ℤ)+2532) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_8 (n u : ℕ) (hu : (94*n+2532) ≤ u ∧ u < (113*n+3044)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (94*(n:ℤ)+2532) (113*(n:ℤ)+3044) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (94*(n:ℤ)+2532) (113*(n:ℤ)+3044) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (94*(n:ℤ)+2532) (113*(n:ℤ)+3044) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (94*(n:ℤ)+2532) (113*(n:ℤ)+3044) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (94*(n:ℤ)+2532) (113*(n:ℤ)+3044) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_9 (n u : ℕ) (hu : (113*n+3044) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (113*(n:ℤ)+3044) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (113*(n:ℤ)+3044) (114*(n:ℤ)+3071) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (113*(n:ℤ)+3044) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (113*(n:ℤ)+3044) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (113*(n:ℤ)+3044) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_10 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (132*n+3556)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (132*(n:ℤ)+3556) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (132*(n:ℤ)+3556) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (132*(n:ℤ)+3556) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (132*(n:ℤ)+3556) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (132*(n:ℤ)+3556) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_11 (n u : ℕ) (hu : (132*n+3556) ≤ u ∧ u < (140*n+3772)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (132*(n:ℤ)+3556) (140*(n:ℤ)+3772) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (132*(n:ℤ)+3556) (140*(n:ℤ)+3772) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (132*(n:ℤ)+3556) (140*(n:ℤ)+3772) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (132*(n:ℤ)+3556) (140*(n:ℤ)+3772) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (132*(n:ℤ)+3556) (140*(n:ℤ)+3772) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_12 (n u : ℕ) (hu : (140*n+3772) ≤ u ∧ u < (151*n+4068)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (140*(n:ℤ)+3772) (151*(n:ℤ)+4068) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (140*(n:ℤ)+3772) (151*(n:ℤ)+4068) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (140*(n:ℤ)+3772) (151*(n:ℤ)+4068) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (140*(n:ℤ)+3772) (151*(n:ℤ)+4068) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (140*(n:ℤ)+3772) (151*(n:ℤ)+4068) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_12_13 (n u : ℕ) (hu : (151*n+4068) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 12 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*12))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*12) (19*(152*((n:ℤ)+27)-8)) (151*(n:ℤ)+4068) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (151*(n:ℤ)+4068) (152*(n:ℤ)+4095) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (151*(n:ℤ)+4068) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (151*(n:ℤ)+4068) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*12*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (151*(n:ℤ)+4068) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_12 (n : ℕ) :
    rowZeroCount (n+27) 12 = 130*n+3503 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 12 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 12 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 12 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 12=0) = (((((((((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ)) ∪ (Finset.Ico (64*n+1724) (75*n+2020) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (94*n+2532) : Finset ℕ)) ∪ (Finset.Ico (94*n+2532) (113*n+3044) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (132*n+3556) : Finset ℕ)) ∪ (Finset.Ico (132*n+3556) (140*n+3772) : Finset ℕ)) ∪ (Finset.Ico (151*n+4068) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (18*n+485)
      · have hf := cell_12_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (37*n+997)
        · have hf := cell_12_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1024)
          · have hf := cell_12_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (56*n+1509)
            · have hf := cell_12_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (64*n+1724)
              · have hf := cell_12_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (75*n+2020)
                · have hf := cell_12_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_12_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (94*n+2532)
                    · have hf := cell_12_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (113*n+3044)
                      · have hf := cell_12_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3071)
                        · have hf := cell_12_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (132*n+3556)
                          · have hf := cell_12_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (140*n+3772)
                            · have hf := cell_12_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (151*n+4068)
                              · have hf := cell_12_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_12_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ)) (Finset.Ico (64*n+1724) (75*n+2020) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ)) ∪ (Finset.Ico (64*n+1724) (75*n+2020) : Finset ℕ)) (Finset.Ico (76*n+2047) (94*n+2532) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ)) ∪ (Finset.Ico (64*n+1724) (75*n+2020) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (94*n+2532) : Finset ℕ)) (Finset.Ico (94*n+2532) (113*n+3044) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ)) ∪ (Finset.Ico (64*n+1724) (75*n+2020) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (94*n+2532) : Finset ℕ)) ∪ (Finset.Ico (94*n+2532) (113*n+3044) : Finset ℕ)) (Finset.Ico (114*n+3071) (132*n+3556) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ)) ∪ (Finset.Ico (64*n+1724) (75*n+2020) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (94*n+2532) : Finset ℕ)) ∪ (Finset.Ico (94*n+2532) (113*n+3044) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (132*n+3556) : Finset ℕ)) (Finset.Ico (132*n+3556) (140*n+3772) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd8 : Disjoint ((((((((Finset.Ico (0*n+0) (18*n+485) : Finset ℕ) ∪ (Finset.Ico (18*n+485) (37*n+997) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (56*n+1509) : Finset ℕ)) ∪ (Finset.Ico (64*n+1724) (75*n+2020) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (94*n+2532) : Finset ℕ)) ∪ (Finset.Ico (94*n+2532) (113*n+3044) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (132*n+3556) : Finset ℕ)) ∪ (Finset.Ico (132*n+3556) (140*n+3772) : Finset ℕ)) (Finset.Ico (151*n+4068) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd8,Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_13_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (10*n+269)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (10*(n:ℤ)+269) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (10*(n:ℤ)+269) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (10*(n:ℤ)+269) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (10*(n:ℤ)+269) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (10*(n:ℤ)+269) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_1 (n u : ℕ) (hu : (10*n+269) ≤ u ∧ u < (29*n+781)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (10*(n:ℤ)+269) (29*(n:ℤ)+781) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (10*(n:ℤ)+269) (29*(n:ℤ)+781) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (10*(n:ℤ)+269) (29*(n:ℤ)+781) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (10*(n:ℤ)+269) (29*(n:ℤ)+781) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (10*(n:ℤ)+269) (29*(n:ℤ)+781) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_2 (n u : ℕ) (hu : (29*n+781) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (29*(n:ℤ)+781) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (29*(n:ℤ)+781) (38*(n:ℤ)+1024) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (29*(n:ℤ)+781) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (29*(n:ℤ)+781) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (29*(n:ℤ)+781) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_3 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (44*n+1185)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (44*(n:ℤ)+1185) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (44*(n:ℤ)+1185) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (44*(n:ℤ)+1185) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (44*(n:ℤ)+1185) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (44*(n:ℤ)+1185) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_4 (n u : ℕ) (hu : (44*n+1185) ≤ u ∧ u < (48*n+1293)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (44*(n:ℤ)+1185) (48*(n:ℤ)+1293) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (44*(n:ℤ)+1185) (48*(n:ℤ)+1293) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (44*(n:ℤ)+1185) (48*(n:ℤ)+1293) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (44*(n:ℤ)+1185) (48*(n:ℤ)+1293) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (44*(n:ℤ)+1185) (48*(n:ℤ)+1293) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_5 (n u : ℕ) (hu : (48*n+1293) ≤ u ∧ u < (67*n+1805)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (48*(n:ℤ)+1293) (67*(n:ℤ)+1805) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (48*(n:ℤ)+1293) (67*(n:ℤ)+1805) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (48*(n:ℤ)+1293) (67*(n:ℤ)+1805) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (48*(n:ℤ)+1293) (67*(n:ℤ)+1805) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (48*(n:ℤ)+1293) (67*(n:ℤ)+1805) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_6 (n u : ℕ) (hu : (67*n+1805) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (67*(n:ℤ)+1805) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (67*(n:ℤ)+1805) (76*(n:ℤ)+2047) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (67*(n:ℤ)+1805) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (67*(n:ℤ)+1805) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (67*(n:ℤ)+1805) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (86*n+2317)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (86*(n:ℤ)+2317) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (86*(n:ℤ)+2317) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (86*(n:ℤ)+2317) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (86*(n:ℤ)+2317) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (86*(n:ℤ)+2317) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_8 (n u : ℕ) (hu : (86*n+2317) ≤ u ∧ u < (105*n+2829)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (86*(n:ℤ)+2317) (105*(n:ℤ)+2829) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (86*(n:ℤ)+2317) (105*(n:ℤ)+2829) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (86*(n:ℤ)+2317) (105*(n:ℤ)+2829) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (86*(n:ℤ)+2317) (105*(n:ℤ)+2829) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (86*(n:ℤ)+2317) (105*(n:ℤ)+2829) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_9 (n u : ℕ) (hu : (105*n+2829) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (105*(n:ℤ)+2829) (114*(n:ℤ)+3071) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (105*(n:ℤ)+2829) (114*(n:ℤ)+3071) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (105*(n:ℤ)+2829) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (105*(n:ℤ)+2829) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (105*(n:ℤ)+2829) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_10 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (120*n+3233)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (120*(n:ℤ)+3233) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (120*(n:ℤ)+3233) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (120*(n:ℤ)+3233) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (120*(n:ℤ)+3233) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (120*(n:ℤ)+3233) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_11 (n u : ℕ) (hu : (120*n+3233) ≤ u ∧ u < (124*n+3340)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (120*(n:ℤ)+3233) (124*(n:ℤ)+3340) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (120*(n:ℤ)+3233) (124*(n:ℤ)+3340) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (120*(n:ℤ)+3233) (124*(n:ℤ)+3340) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (120*(n:ℤ)+3233) (124*(n:ℤ)+3340) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (120*(n:ℤ)+3233) (124*(n:ℤ)+3340) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_12 (n u : ℕ) (hu : (124*n+3340) ≤ u ∧ u < (143*n+3852)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (124*(n:ℤ)+3340) (143*(n:ℤ)+3852) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (124*(n:ℤ)+3340) (143*(n:ℤ)+3852) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (124*(n:ℤ)+3340) (143*(n:ℤ)+3852) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (124*(n:ℤ)+3340) (143*(n:ℤ)+3852) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (124*(n:ℤ)+3340) (143*(n:ℤ)+3852) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_13_13 (n u : ℕ) (hu : (143*n+3852) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 13 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*13))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*13) (19*(152*((n:ℤ)+27)-8)) (143*(n:ℤ)+3852) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (143*(n:ℤ)+3852) (152*(n:ℤ)+4095) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (143*(n:ℤ)+3852) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (143*(n:ℤ)+3852) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*13*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (143*(n:ℤ)+3852) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_13 (n : ℕ) :
    rowZeroCount (n+27) 13 = 98*n+2641 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 13 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 13 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 13 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 13=0) = ((((((((Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) ∪ (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1185) : Finset ℕ)) ∪ (Finset.Ico (48*n+1293) (67*n+1805) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (86*n+2317) : Finset ℕ)) ∪ (Finset.Ico (86*n+2317) (105*n+2829) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (120*n+3233) : Finset ℕ)) ∪ (Finset.Ico (143*n+3852) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (10*n+269)
      · have hf := cell_13_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (29*n+781)
        · have hf := cell_13_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1024)
          · have hf := cell_13_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (44*n+1185)
            · have hf := cell_13_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (48*n+1293)
              · have hf := cell_13_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (67*n+1805)
                · have hf := cell_13_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_13_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (86*n+2317)
                    · have hf := cell_13_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (105*n+2829)
                      · have hf := cell_13_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3071)
                        · have hf := cell_13_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (120*n+3233)
                          · have hf := cell_13_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (124*n+3340)
                            · have hf := cell_13_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (143*n+3852)
                              · have hf := cell_13_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_13_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) ∪ (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ)) (Finset.Ico (38*n+1024) (44*n+1185) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) ∪ (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1185) : Finset ℕ)) (Finset.Ico (48*n+1293) (67*n+1805) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) ∪ (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1185) : Finset ℕ)) ∪ (Finset.Ico (48*n+1293) (67*n+1805) : Finset ℕ)) (Finset.Ico (76*n+2047) (86*n+2317) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) ∪ (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1185) : Finset ℕ)) ∪ (Finset.Ico (48*n+1293) (67*n+1805) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (86*n+2317) : Finset ℕ)) (Finset.Ico (86*n+2317) (105*n+2829) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) ∪ (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1185) : Finset ℕ)) ∪ (Finset.Ico (48*n+1293) (67*n+1805) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (86*n+2317) : Finset ℕ)) ∪ (Finset.Ico (86*n+2317) (105*n+2829) : Finset ℕ)) (Finset.Ico (114*n+3071) (120*n+3233) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (10*n+269) : Finset ℕ) ∪ (Finset.Ico (10*n+269) (29*n+781) : Finset ℕ)) ∪ (Finset.Ico (38*n+1024) (44*n+1185) : Finset ℕ)) ∪ (Finset.Ico (48*n+1293) (67*n+1805) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (86*n+2317) : Finset ℕ)) ∪ (Finset.Ico (86*n+2317) (105*n+2829) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (120*n+3233) : Finset ℕ)) (Finset.Ico (143*n+3852) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_14_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (2*n+54)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (2*(n:ℤ)+54) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (2*(n:ℤ)+54) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (2*(n:ℤ)+54) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (2*(n:ℤ)+54) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (2*(n:ℤ)+54) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_1 (n u : ℕ) (hu : (2*n+54) ≤ u ∧ u < (21*n+566)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (2*(n:ℤ)+54) (21*(n:ℤ)+566) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (2*(n:ℤ)+54) (21*(n:ℤ)+566) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (2*(n:ℤ)+54) (21*(n:ℤ)+566) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (2*(n:ℤ)+54) (21*(n:ℤ)+566) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (2*(n:ℤ)+54) (21*(n:ℤ)+566) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_2 (n u : ℕ) (hu : (21*n+566) ≤ u ∧ u < (24*n+646)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (21*(n:ℤ)+566) (24*(n:ℤ)+646) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (21*(n:ℤ)+566) (24*(n:ℤ)+646) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (21*(n:ℤ)+566) (24*(n:ℤ)+646) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (21*(n:ℤ)+566) (24*(n:ℤ)+646) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (21*(n:ℤ)+566) (24*(n:ℤ)+646) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_3 (n u : ℕ) (hu : (24*n+646) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (24*(n:ℤ)+646) (38*(n:ℤ)+1024) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (24*(n:ℤ)+646) (38*(n:ℤ)+1024) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (24*(n:ℤ)+646) (38*(n:ℤ)+1024) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (24*(n:ℤ)+646) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (24*(n:ℤ)+646) (38*(n:ℤ)+1024) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_4 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (40*n+1077)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (40*(n:ℤ)+1077) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (40*(n:ℤ)+1077) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (40*(n:ℤ)+1077) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (40*(n:ℤ)+1077) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (40*(n:ℤ)+1077) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_5 (n u : ℕ) (hu : (40*n+1077) ≤ u ∧ u < (59*n+1589)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (40*(n:ℤ)+1077) (59*(n:ℤ)+1589) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (40*(n:ℤ)+1077) (59*(n:ℤ)+1589) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (40*(n:ℤ)+1077) (59*(n:ℤ)+1589) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (40*(n:ℤ)+1077) (59*(n:ℤ)+1589) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (40*(n:ℤ)+1077) (59*(n:ℤ)+1589) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_6 (n u : ℕ) (hu : (59*n+1589) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (59*(n:ℤ)+1589) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (59*(n:ℤ)+1589) (76*(n:ℤ)+2047) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (59*(n:ℤ)+1589) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (59*(n:ℤ)+1589) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (59*(n:ℤ)+1589) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (78*n+2101)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (78*(n:ℤ)+2101) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (78*(n:ℤ)+2101) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (78*(n:ℤ)+2101) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (78*(n:ℤ)+2101) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (78*(n:ℤ)+2101) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_8 (n u : ℕ) (hu : (78*n+2101) ≤ u ∧ u < (97*n+2613)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (78*(n:ℤ)+2101) (97*(n:ℤ)+2613) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (78*(n:ℤ)+2101) (97*(n:ℤ)+2613) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (78*(n:ℤ)+2101) (97*(n:ℤ)+2613) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (78*(n:ℤ)+2101) (97*(n:ℤ)+2613) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (78*(n:ℤ)+2101) (97*(n:ℤ)+2613) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_9 (n u : ℕ) (hu : (97*n+2613) ≤ u ∧ u < (100*n+2694)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (97*(n:ℤ)+2613) (100*(n:ℤ)+2694) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (97*(n:ℤ)+2613) (100*(n:ℤ)+2694) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (97*(n:ℤ)+2613) (100*(n:ℤ)+2694) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (97*(n:ℤ)+2613) (100*(n:ℤ)+2694) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (97*(n:ℤ)+2613) (100*(n:ℤ)+2694) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_10 (n u : ℕ) (hu : (100*n+2694) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_11 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (116*n+3125)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_12 (n u : ℕ) (hu : (116*n+3125) ≤ u ∧ u < (135*n+3637)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (116*(n:ℤ)+3125) (135*(n:ℤ)+3637) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (116*(n:ℤ)+3125) (135*(n:ℤ)+3637) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (116*(n:ℤ)+3125) (135*(n:ℤ)+3637) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (116*(n:ℤ)+3125) (135*(n:ℤ)+3637) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (116*(n:ℤ)+3125) (135*(n:ℤ)+3637) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_14_13 (n u : ℕ) (hu : (135*n+3637) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 14 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*14))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*14) (19*(152*((n:ℤ)+27)-8)) (135*(n:ℤ)+3637) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (135*(n:ℤ)+3637) (152*(n:ℤ)+4095) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (135*(n:ℤ)+3637) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (135*(n:ℤ)+3637) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*14*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (135*(n:ℤ)+3637) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_14 (n : ℕ) :
    rowZeroCount (n+27) 14 = 106*n+2857 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 14 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 14 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 14 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 14=0) = ((((((((Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) ∪ (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ)) ∪ (Finset.Ico (24*n+646) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (40*n+1077) (59*n+1589) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (78*n+2101) : Finset ℕ)) ∪ (Finset.Ico (78*n+2101) (97*n+2613) : Finset ℕ)) ∪ (Finset.Ico (100*n+2694) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (135*n+3637) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (2*n+54)
      · have hf := cell_14_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (21*n+566)
        · have hf := cell_14_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (24*n+646)
          · have hf := cell_14_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1024)
            · have hf := cell_14_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (40*n+1077)
              · have hf := cell_14_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (59*n+1589)
                · have hf := cell_14_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_14_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (78*n+2101)
                    · have hf := cell_14_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (97*n+2613)
                      · have hf := cell_14_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (100*n+2694)
                        · have hf := cell_14_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3071)
                          · have hf := cell_14_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (116*n+3125)
                            · have hf := cell_14_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (135*n+3637)
                              · have hf := cell_14_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_14_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) ∪ (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ)) (Finset.Ico (24*n+646) (38*n+1024) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) ∪ (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ)) ∪ (Finset.Ico (24*n+646) (38*n+1024) : Finset ℕ)) (Finset.Ico (40*n+1077) (59*n+1589) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) ∪ (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ)) ∪ (Finset.Ico (24*n+646) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (40*n+1077) (59*n+1589) : Finset ℕ)) (Finset.Ico (76*n+2047) (78*n+2101) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) ∪ (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ)) ∪ (Finset.Ico (24*n+646) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (40*n+1077) (59*n+1589) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (78*n+2101) : Finset ℕ)) (Finset.Ico (78*n+2101) (97*n+2613) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) ∪ (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ)) ∪ (Finset.Ico (24*n+646) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (40*n+1077) (59*n+1589) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (78*n+2101) : Finset ℕ)) ∪ (Finset.Ico (78*n+2101) (97*n+2613) : Finset ℕ)) (Finset.Ico (100*n+2694) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (2*n+54) : Finset ℕ) ∪ (Finset.Ico (2*n+54) (21*n+566) : Finset ℕ)) ∪ (Finset.Ico (24*n+646) (38*n+1024) : Finset ℕ)) ∪ (Finset.Ico (40*n+1077) (59*n+1589) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (78*n+2101) : Finset ℕ)) ∪ (Finset.Ico (78*n+2101) (97*n+2613) : Finset ℕ)) ∪ (Finset.Ico (100*n+2694) (114*n+3071) : Finset ℕ)) (Finset.Ico (135*n+3637) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_15_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (4*n+107)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 3 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (4*(n:ℤ)+107) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (4*(n:ℤ)+107) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (4*(n:ℤ)+107) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (4*(n:ℤ)+107) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (4*(n:ℤ)+107) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_1 (n u : ℕ) (hu : (4*n+107) ≤ u ∧ u < (13*n+350)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (4*(n:ℤ)+107) (13*(n:ℤ)+350) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (4*(n:ℤ)+107) (13*(n:ℤ)+350) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (4*(n:ℤ)+107) (13*(n:ℤ)+350) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (4*(n:ℤ)+107) (13*(n:ℤ)+350) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (4*(n:ℤ)+107) (13*(n:ℤ)+350) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_2 (n u : ℕ) (hu : (13*n+350) ≤ u ∧ u < (32*n+862)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (13*(n:ℤ)+350) (32*(n:ℤ)+862) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (13*(n:ℤ)+350) (32*(n:ℤ)+862) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (13*(n:ℤ)+350) (32*(n:ℤ)+862) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (13*(n:ℤ)+350) (32*(n:ℤ)+862) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (13*(n:ℤ)+350) (32*(n:ℤ)+862) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_3 (n u : ℕ) (hu : (32*n+862) ≤ u ∧ u < (38*n+1023)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (32*(n:ℤ)+862) (38*(n:ℤ)+1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (32*(n:ℤ)+862) (38*(n:ℤ)+1023) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (32*(n:ℤ)+862) (38*(n:ℤ)+1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (32*(n:ℤ)+862) (38*(n:ℤ)+1023) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (32*(n:ℤ)+862) (38*(n:ℤ)+1023) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_4 (n u : ℕ) (hu : (38*n+1023) ≤ u ∧ u < (51*n+1374)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1023) (51*(n:ℤ)+1374) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (51*(n:ℤ)+1374) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (51*(n:ℤ)+1374) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (51*(n:ℤ)+1374) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1023) (51*(n:ℤ)+1374) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_5 (n u : ℕ) (hu : (51*n+1374) ≤ u ∧ u < (70*n+1886)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (51*(n:ℤ)+1374) (70*(n:ℤ)+1886) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (51*(n:ℤ)+1374) (70*(n:ℤ)+1886) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (51*(n:ℤ)+1374) (70*(n:ℤ)+1886) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (51*(n:ℤ)+1374) (70*(n:ℤ)+1886) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (51*(n:ℤ)+1374) (70*(n:ℤ)+1886) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_6 (n u : ℕ) (hu : (70*n+1886) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (70*(n:ℤ)+1886) (76*(n:ℤ)+2047) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (70*(n:ℤ)+1886) (76*(n:ℤ)+2047) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (70*(n:ℤ)+1886) (76*(n:ℤ)+2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (70*(n:ℤ)+1886) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (70*(n:ℤ)+1886) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (80*n+2155)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (80*(n:ℤ)+2155) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (80*(n:ℤ)+2155) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (80*(n:ℤ)+2155) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (80*(n:ℤ)+2155) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (80*(n:ℤ)+2155) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_8 (n u : ℕ) (hu : (80*n+2155) ≤ u ∧ u < (89*n+2397)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (80*(n:ℤ)+2155) (89*(n:ℤ)+2397) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (80*(n:ℤ)+2155) (89*(n:ℤ)+2397) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (80*(n:ℤ)+2155) (89*(n:ℤ)+2397) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (80*(n:ℤ)+2155) (89*(n:ℤ)+2397) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (80*(n:ℤ)+2155) (89*(n:ℤ)+2397) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_9 (n u : ℕ) (hu : (89*n+2397) ≤ u ∧ u < (108*n+2909)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (89*(n:ℤ)+2397) (108*(n:ℤ)+2909) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (89*(n:ℤ)+2397) (108*(n:ℤ)+2909) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (89*(n:ℤ)+2397) (108*(n:ℤ)+2909) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (89*(n:ℤ)+2397) (108*(n:ℤ)+2909) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (89*(n:ℤ)+2397) (108*(n:ℤ)+2909) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_10 (n u : ℕ) (hu : (108*n+2909) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (108*(n:ℤ)+2909) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (108*(n:ℤ)+2909) (114*(n:ℤ)+3071) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (108*(n:ℤ)+2909) (114*(n:ℤ)+3071) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (108*(n:ℤ)+2909) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (108*(n:ℤ)+2909) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_11 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (127*n+3421)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (127*(n:ℤ)+3421) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (127*(n:ℤ)+3421) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (127*(n:ℤ)+3421) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (127*(n:ℤ)+3421) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (127*(n:ℤ)+3421) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_12 (n u : ℕ) (hu : (127*n+3421) ≤ u ∧ u < (146*n+3933)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (127*(n:ℤ)+3421) (146*(n:ℤ)+3933) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (127*(n:ℤ)+3421) (146*(n:ℤ)+3933) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (127*(n:ℤ)+3421) (146*(n:ℤ)+3933) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (127*(n:ℤ)+3421) (146*(n:ℤ)+3933) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (127*(n:ℤ)+3421) (146*(n:ℤ)+3933) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_15_13 (n u : ℕ) (hu : (146*n+3933) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 15 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*15))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*15) (19*(152*((n:ℤ)+27)-8)) (146*(n:ℤ)+3933) (152*(n:ℤ)+4095) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 14 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (146*(n:ℤ)+3933) (152*(n:ℤ)+4095) 14 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (146*(n:ℤ)+3933) (152*(n:ℤ)+4095) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (146*(n:ℤ)+3933) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*15*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (146*(n:ℤ)+3933) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_15 (n : ℕ) :
    rowZeroCount (n+27) 15 = 90*n+2426 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 15 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 15 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 15 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 15=0) = ((((((((Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) ∪ (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (51*n+1374) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (80*n+2155) : Finset ℕ)) ∪ (Finset.Ico (89*n+2397) (108*n+2909) : Finset ℕ)) ∪ (Finset.Ico (108*n+2909) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (127*n+3421) (146*n+3933) : Finset ℕ)) ∪ (Finset.Ico (146*n+3933) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (4*n+107)
      · have hf := cell_15_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (13*n+350)
        · have hf := cell_15_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (32*n+862)
          · have hf := cell_15_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1023)
            · have hf := cell_15_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (51*n+1374)
              · have hf := cell_15_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (70*n+1886)
                · have hf := cell_15_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_15_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (80*n+2155)
                    · have hf := cell_15_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (89*n+2397)
                      · have hf := cell_15_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (108*n+2909)
                        · have hf := cell_15_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3071)
                          · have hf := cell_15_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (127*n+3421)
                            · have hf := cell_15_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (146*n+3933)
                              · have hf := cell_15_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_15_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) ∪ (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ)) (Finset.Ico (38*n+1023) (51*n+1374) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) ∪ (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (51*n+1374) : Finset ℕ)) (Finset.Ico (76*n+2047) (80*n+2155) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) ∪ (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (51*n+1374) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (80*n+2155) : Finset ℕ)) (Finset.Ico (89*n+2397) (108*n+2909) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) ∪ (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (51*n+1374) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (80*n+2155) : Finset ℕ)) ∪ (Finset.Ico (89*n+2397) (108*n+2909) : Finset ℕ)) (Finset.Ico (108*n+2909) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) ∪ (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (51*n+1374) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (80*n+2155) : Finset ℕ)) ∪ (Finset.Ico (89*n+2397) (108*n+2909) : Finset ℕ)) ∪ (Finset.Ico (108*n+2909) (114*n+3071) : Finset ℕ)) (Finset.Ico (127*n+3421) (146*n+3933) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (4*n+107) : Finset ℕ) ∪ (Finset.Ico (13*n+350) (32*n+862) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (51*n+1374) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (80*n+2155) : Finset ℕ)) ∪ (Finset.Ico (89*n+2397) (108*n+2909) : Finset ℕ)) ∪ (Finset.Ico (108*n+2909) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (127*n+3421) (146*n+3933) : Finset ℕ)) (Finset.Ico (146*n+3933) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_16_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (5*n+134)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (5*(n:ℤ)+134) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (5*(n:ℤ)+134) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (5*(n:ℤ)+134) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (5*(n:ℤ)+134) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (5*(n:ℤ)+134) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_1 (n u : ℕ) (hu : (5*n+134) ≤ u ∧ u < (24*n+646)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (5*(n:ℤ)+134) (24*(n:ℤ)+646) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (5*(n:ℤ)+134) (24*(n:ℤ)+646) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (5*(n:ℤ)+134) (24*(n:ℤ)+646) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (5*(n:ℤ)+134) (24*(n:ℤ)+646) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (5*(n:ℤ)+134) (24*(n:ℤ)+646) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_2 (n u : ℕ) (hu : (24*n+646) ≤ u ∧ u < (38*n+1023)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (24*(n:ℤ)+646) (38*(n:ℤ)+1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (24*(n:ℤ)+646) (38*(n:ℤ)+1023) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (24*(n:ℤ)+646) (38*(n:ℤ)+1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (24*(n:ℤ)+646) (38*(n:ℤ)+1023) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (24*(n:ℤ)+646) (38*(n:ℤ)+1023) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_3 (n u : ℕ) (hu : (38*n+1023) ≤ u ∧ u < (43*n+1158)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1023) (43*(n:ℤ)+1158) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (43*(n:ℤ)+1158) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (43*(n:ℤ)+1158) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (43*(n:ℤ)+1158) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1023) (43*(n:ℤ)+1158) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_4 (n u : ℕ) (hu : (43*n+1158) ≤ u ∧ u < (60*n+1616)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (43*(n:ℤ)+1158) (60*(n:ℤ)+1616) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (43*(n:ℤ)+1158) (60*(n:ℤ)+1616) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (43*(n:ℤ)+1158) (60*(n:ℤ)+1616) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (43*(n:ℤ)+1158) (60*(n:ℤ)+1616) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (43*(n:ℤ)+1158) (60*(n:ℤ)+1616) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_5 (n u : ℕ) (hu : (60*n+1616) ≤ u ∧ u < (62*n+1670)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (60*(n:ℤ)+1616) (62*(n:ℤ)+1670) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (60*(n:ℤ)+1616) (62*(n:ℤ)+1670) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (60*(n:ℤ)+1616) (62*(n:ℤ)+1670) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (60*(n:ℤ)+1616) (62*(n:ℤ)+1670) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (60*(n:ℤ)+1616) (62*(n:ℤ)+1670) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_6 (n u : ℕ) (hu : (62*n+1670) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (62*(n:ℤ)+1670) (76*(n:ℤ)+2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (62*(n:ℤ)+1670) (76*(n:ℤ)+2047) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (62*(n:ℤ)+1670) (76*(n:ℤ)+2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (62*(n:ℤ)+1670) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (62*(n:ℤ)+1670) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (81*n+2182)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (81*(n:ℤ)+2182) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (81*(n:ℤ)+2182) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (81*(n:ℤ)+2182) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (81*(n:ℤ)+2182) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (81*(n:ℤ)+2182) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_8 (n u : ℕ) (hu : (81*n+2182) ≤ u ∧ u < (100*n+2694)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (81*(n:ℤ)+2182) (100*(n:ℤ)+2694) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (81*(n:ℤ)+2182) (100*(n:ℤ)+2694) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (81*(n:ℤ)+2182) (100*(n:ℤ)+2694) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (81*(n:ℤ)+2182) (100*(n:ℤ)+2694) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (81*(n:ℤ)+2182) (100*(n:ℤ)+2694) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_9 (n u : ℕ) (hu : (100*n+2694) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (100*(n:ℤ)+2694) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_10 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (119*n+3206)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (119*(n:ℤ)+3206) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (119*(n:ℤ)+3206) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (119*(n:ℤ)+3206) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (119*(n:ℤ)+3206) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (119*(n:ℤ)+3206) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_11 (n u : ℕ) (hu : (119*n+3206) ≤ u ∧ u < (136*n+3664)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (119*(n:ℤ)+3206) (136*(n:ℤ)+3664) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (119*(n:ℤ)+3206) (136*(n:ℤ)+3664) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (119*(n:ℤ)+3206) (136*(n:ℤ)+3664) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (119*(n:ℤ)+3206) (136*(n:ℤ)+3664) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (119*(n:ℤ)+3206) (136*(n:ℤ)+3664) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_12 (n u : ℕ) (hu : (136*n+3664) ≤ u ∧ u < (138*n+3717)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (136*(n:ℤ)+3664) (138*(n:ℤ)+3717) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (136*(n:ℤ)+3664) (138*(n:ℤ)+3717) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (136*(n:ℤ)+3664) (138*(n:ℤ)+3717) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (136*(n:ℤ)+3664) (138*(n:ℤ)+3717) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (136*(n:ℤ)+3664) (138*(n:ℤ)+3717) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_16_13 (n u : ℕ) (hu : (138*n+3717) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 16 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*16))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*16) (19*(152*((n:ℤ)+27)-8)) (138*(n:ℤ)+3717) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 14 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (138*(n:ℤ)+3717) (152*(n:ℤ)+4095) 14 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (138*(n:ℤ)+3717) (152*(n:ℤ)+4095) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (138*(n:ℤ)+3717) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*16*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (138*(n:ℤ)+3717) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_16 (n : ℕ) :
    rowZeroCount (n+27) 16 = 90*n+2425 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 16 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 16 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 16 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 16=0) = (((((((Finset.Ico (5*n+134) (24*n+646) : Finset ℕ) ∪ (Finset.Ico (38*n+1023) (43*n+1158) : Finset ℕ)) ∪ (Finset.Ico (60*n+1616) (62*n+1670) : Finset ℕ)) ∪ (Finset.Ico (62*n+1670) (76*n+2047) : Finset ℕ)) ∪ (Finset.Ico (81*n+2182) (100*n+2694) : Finset ℕ)) ∪ (Finset.Ico (100*n+2694) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (119*n+3206) (136*n+3664) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (5*n+134)
      · have hf := cell_16_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (24*n+646)
        · have hf := cell_16_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1023)
          · have hf := cell_16_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (43*n+1158)
            · have hf := cell_16_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (60*n+1616)
              · have hf := cell_16_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (62*n+1670)
                · have hf := cell_16_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_16_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (81*n+2182)
                    · have hf := cell_16_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (100*n+2694)
                      · have hf := cell_16_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3071)
                        · have hf := cell_16_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (119*n+3206)
                          · have hf := cell_16_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (136*n+3664)
                            · have hf := cell_16_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (138*n+3717)
                              · have hf := cell_16_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_16_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (5*n+134) (24*n+646) : Finset ℕ) (Finset.Ico (38*n+1023) (43*n+1158) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (5*n+134) (24*n+646) : Finset ℕ) ∪ (Finset.Ico (38*n+1023) (43*n+1158) : Finset ℕ)) (Finset.Ico (60*n+1616) (62*n+1670) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (5*n+134) (24*n+646) : Finset ℕ) ∪ (Finset.Ico (38*n+1023) (43*n+1158) : Finset ℕ)) ∪ (Finset.Ico (60*n+1616) (62*n+1670) : Finset ℕ)) (Finset.Ico (62*n+1670) (76*n+2047) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (5*n+134) (24*n+646) : Finset ℕ) ∪ (Finset.Ico (38*n+1023) (43*n+1158) : Finset ℕ)) ∪ (Finset.Ico (60*n+1616) (62*n+1670) : Finset ℕ)) ∪ (Finset.Ico (62*n+1670) (76*n+2047) : Finset ℕ)) (Finset.Ico (81*n+2182) (100*n+2694) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (5*n+134) (24*n+646) : Finset ℕ) ∪ (Finset.Ico (38*n+1023) (43*n+1158) : Finset ℕ)) ∪ (Finset.Ico (60*n+1616) (62*n+1670) : Finset ℕ)) ∪ (Finset.Ico (62*n+1670) (76*n+2047) : Finset ℕ)) ∪ (Finset.Ico (81*n+2182) (100*n+2694) : Finset ℕ)) (Finset.Ico (100*n+2694) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (5*n+134) (24*n+646) : Finset ℕ) ∪ (Finset.Ico (38*n+1023) (43*n+1158) : Finset ℕ)) ∪ (Finset.Ico (60*n+1616) (62*n+1670) : Finset ℕ)) ∪ (Finset.Ico (62*n+1670) (76*n+2047) : Finset ℕ)) ∪ (Finset.Ico (81*n+2182) (100*n+2694) : Finset ℕ)) ∪ (Finset.Ico (100*n+2694) (114*n+3071) : Finset ℕ)) (Finset.Ico (119*n+3206) (136*n+3664) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_17_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (16*n+431)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (16*(n:ℤ)+431) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (16*(n:ℤ)+431) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (16*(n:ℤ)+431) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (16*(n:ℤ)+431) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (16*(n:ℤ)+431) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_1 (n u : ℕ) (hu : (16*n+431) ≤ u ∧ u < (35*n+943)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (16*(n:ℤ)+431) (35*(n:ℤ)+943) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (16*(n:ℤ)+431) (35*(n:ℤ)+943) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (16*(n:ℤ)+431) (35*(n:ℤ)+943) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (16*(n:ℤ)+431) (35*(n:ℤ)+943) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (16*(n:ℤ)+431) (35*(n:ℤ)+943) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_2 (n u : ℕ) (hu : (35*n+943) ≤ u ∧ u < (38*n+1023)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 2 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (35*(n:ℤ)+943) (38*(n:ℤ)+1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (35*(n:ℤ)+943) (38*(n:ℤ)+1023) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (35*(n:ℤ)+943) (38*(n:ℤ)+1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (35*(n:ℤ)+943) (38*(n:ℤ)+1023) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (35*(n:ℤ)+943) (38*(n:ℤ)+1023) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_3 (n u : ℕ) (hu : (38*n+1023) ≤ u ∧ u < (40*n+1077)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1023) (40*(n:ℤ)+1077) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (40*(n:ℤ)+1077) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (40*(n:ℤ)+1077) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (40*(n:ℤ)+1077) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1023) (40*(n:ℤ)+1077) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_4 (n u : ℕ) (hu : (40*n+1077) ≤ u ∧ u < (54*n+1454)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (40*(n:ℤ)+1077) (54*(n:ℤ)+1454) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (40*(n:ℤ)+1077) (54*(n:ℤ)+1454) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (40*(n:ℤ)+1077) (54*(n:ℤ)+1454) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (40*(n:ℤ)+1077) (54*(n:ℤ)+1454) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (40*(n:ℤ)+1077) (54*(n:ℤ)+1454) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_5 (n u : ℕ) (hu : (54*n+1454) ≤ u ∧ u < (73*n+1966)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (54*(n:ℤ)+1454) (73*(n:ℤ)+1966) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (54*(n:ℤ)+1454) (73*(n:ℤ)+1966) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (54*(n:ℤ)+1454) (73*(n:ℤ)+1966) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (54*(n:ℤ)+1454) (73*(n:ℤ)+1966) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (54*(n:ℤ)+1454) (73*(n:ℤ)+1966) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_6 (n u : ℕ) (hu : (73*n+1966) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (73*(n:ℤ)+1966) (76*(n:ℤ)+2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (73*(n:ℤ)+1966) (76*(n:ℤ)+2047) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (73*(n:ℤ)+1966) (76*(n:ℤ)+2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (73*(n:ℤ)+1966) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (73*(n:ℤ)+1966) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (92*n+2478)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (92*(n:ℤ)+2478) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (92*(n:ℤ)+2478) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (92*(n:ℤ)+2478) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (92*(n:ℤ)+2478) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (92*(n:ℤ)+2478) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_8 (n u : ℕ) (hu : (92*n+2478) ≤ u ∧ u < (111*n+2990)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (92*(n:ℤ)+2478) (111*(n:ℤ)+2990) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (92*(n:ℤ)+2478) (111*(n:ℤ)+2990) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (92*(n:ℤ)+2478) (111*(n:ℤ)+2990) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (92*(n:ℤ)+2478) (111*(n:ℤ)+2990) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (92*(n:ℤ)+2478) (111*(n:ℤ)+2990) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_9 (n u : ℕ) (hu : (111*n+2990) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (111*(n:ℤ)+2990) (114*(n:ℤ)+3071) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (111*(n:ℤ)+2990) (114*(n:ℤ)+3071) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (111*(n:ℤ)+2990) (114*(n:ℤ)+3071) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (111*(n:ℤ)+2990) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (111*(n:ℤ)+2990) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_10 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (116*n+3125)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (116*(n:ℤ)+3125) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_11 (n u : ℕ) (hu : (116*n+3125) ≤ u ∧ u < (130*n+3502)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (116*(n:ℤ)+3125) (130*(n:ℤ)+3502) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (116*(n:ℤ)+3125) (130*(n:ℤ)+3502) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (116*(n:ℤ)+3125) (130*(n:ℤ)+3502) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (116*(n:ℤ)+3125) (130*(n:ℤ)+3502) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (116*(n:ℤ)+3125) (130*(n:ℤ)+3502) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_12 (n u : ℕ) (hu : (130*n+3502) ≤ u ∧ u < (149*n+4014)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (130*(n:ℤ)+3502) (149*(n:ℤ)+4014) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 14 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (130*(n:ℤ)+3502) (149*(n:ℤ)+4014) 14 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (130*(n:ℤ)+3502) (149*(n:ℤ)+4014) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (130*(n:ℤ)+3502) (149*(n:ℤ)+4014) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (130*(n:ℤ)+3502) (149*(n:ℤ)+4014) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_17_13 (n u : ℕ) (hu : (149*n+4014) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 17 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*17))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*17) (19*(152*((n:ℤ)+27)-8)) (149*(n:ℤ)+4014) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 15 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (149*(n:ℤ)+4014) (152*(n:ℤ)+4095) 15 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (149*(n:ℤ)+4014) (152*(n:ℤ)+4095) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (149*(n:ℤ)+4014) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*17*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (149*(n:ℤ)+4014) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_17 (n : ℕ) :
    rowZeroCount (n+27) 17 = 89*n+2398 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 17 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 17 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 17 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 17=0) = (((((((Finset.Ico (0*n+0) (16*n+431) : Finset ℕ) ∪ (Finset.Ico (40*n+1077) (54*n+1454) : Finset ℕ)) ∪ (Finset.Ico (54*n+1454) (73*n+1966) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (92*n+2478) : Finset ℕ)) ∪ (Finset.Ico (92*n+2478) (111*n+2990) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (116*n+3125) : Finset ℕ)) ∪ (Finset.Ico (149*n+4014) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (16*n+431)
      · have hf := cell_17_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (35*n+943)
        · have hf := cell_17_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (38*n+1023)
          · have hf := cell_17_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (40*n+1077)
            · have hf := cell_17_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (54*n+1454)
              · have hf := cell_17_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (73*n+1966)
                · have hf := cell_17_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_17_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (92*n+2478)
                    · have hf := cell_17_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (111*n+2990)
                      · have hf := cell_17_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (114*n+3071)
                        · have hf := cell_17_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (116*n+3125)
                          · have hf := cell_17_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (130*n+3502)
                            · have hf := cell_17_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (149*n+4014)
                              · have hf := cell_17_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_17_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (16*n+431) : Finset ℕ) (Finset.Ico (40*n+1077) (54*n+1454) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (16*n+431) : Finset ℕ) ∪ (Finset.Ico (40*n+1077) (54*n+1454) : Finset ℕ)) (Finset.Ico (54*n+1454) (73*n+1966) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (16*n+431) : Finset ℕ) ∪ (Finset.Ico (40*n+1077) (54*n+1454) : Finset ℕ)) ∪ (Finset.Ico (54*n+1454) (73*n+1966) : Finset ℕ)) (Finset.Ico (76*n+2047) (92*n+2478) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (16*n+431) : Finset ℕ) ∪ (Finset.Ico (40*n+1077) (54*n+1454) : Finset ℕ)) ∪ (Finset.Ico (54*n+1454) (73*n+1966) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (92*n+2478) : Finset ℕ)) (Finset.Ico (92*n+2478) (111*n+2990) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (16*n+431) : Finset ℕ) ∪ (Finset.Ico (40*n+1077) (54*n+1454) : Finset ℕ)) ∪ (Finset.Ico (54*n+1454) (73*n+1966) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (92*n+2478) : Finset ℕ)) ∪ (Finset.Ico (92*n+2478) (111*n+2990) : Finset ℕ)) (Finset.Ico (114*n+3071) (116*n+3125) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (16*n+431) : Finset ℕ) ∪ (Finset.Ico (40*n+1077) (54*n+1454) : Finset ℕ)) ∪ (Finset.Ico (54*n+1454) (73*n+1966) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (92*n+2478) : Finset ℕ)) ∪ (Finset.Ico (92*n+2478) (111*n+2990) : Finset ℕ)) ∪ (Finset.Ico (114*n+3071) (116*n+3125) : Finset ℕ)) (Finset.Ico (149*n+4014) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega

private theorem cell_18_0 (n u : ℕ) (hu : (0*n+0) ≤ u ∧ u < (8*n+215)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (0*(n:ℤ)+0) (8*(n:ℤ)+215) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (8*(n:ℤ)+215) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (8*(n:ℤ)+215) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (8*(n:ℤ)+215) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (8*(n:ℤ)+215) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_1 (n u : ℕ) (hu : (8*n+215) ≤ u ∧ u < (20*n+538)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 4 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (8*(n:ℤ)+215) (20*(n:ℤ)+538) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (8*(n:ℤ)+215) (20*(n:ℤ)+538) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (8*(n:ℤ)+215) (20*(n:ℤ)+538) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (8*(n:ℤ)+215) (20*(n:ℤ)+538) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (8*(n:ℤ)+215) (20*(n:ℤ)+538) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_2 (n u : ℕ) (hu : (20*n+538) ≤ u ∧ u < (27*n+727)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (20*(n:ℤ)+538) (27*(n:ℤ)+727) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 8 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (20*(n:ℤ)+538) (27*(n:ℤ)+727) 8 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (20*(n:ℤ)+538) (27*(n:ℤ)+727) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (20*(n:ℤ)+538) (27*(n:ℤ)+727) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (20*(n:ℤ)+538) (27*(n:ℤ)+727) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_3 (n u : ℕ) (hu : (27*n+727) ≤ u ∧ u < (38*n+1023)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (27*(n:ℤ)+727) (38*(n:ℤ)+1023) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (27*(n:ℤ)+727) (38*(n:ℤ)+1023) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (27*(n:ℤ)+727) (38*(n:ℤ)+1023) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (27*(n:ℤ)+727) (38*(n:ℤ)+1023) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (27*(n:ℤ)+727) (38*(n:ℤ)+1023) 0 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_4 (n u : ℕ) (hu : (38*n+1023) ≤ u ∧ u < (46*n+1239)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1023) (46*(n:ℤ)+1239) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 9 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (46*(n:ℤ)+1239) 9 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (46*(n:ℤ)+1239) 4 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1023) (46*(n:ℤ)+1239) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1023) (46*(n:ℤ)+1239) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_5 (n u : ℕ) (hu : (46*n+1239) ≤ u ∧ u < (65*n+1751)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (46*(n:ℤ)+1239) (65*(n:ℤ)+1751) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 10 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (46*(n:ℤ)+1239) (65*(n:ℤ)+1751) 10 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (46*(n:ℤ)+1239) (65*(n:ℤ)+1751) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (46*(n:ℤ)+1239) (65*(n:ℤ)+1751) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (46*(n:ℤ)+1239) (65*(n:ℤ)+1751) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_6 (n u : ℕ) (hu : (65*n+1751) ≤ u ∧ u < (76*n+2047)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (65*(n:ℤ)+1751) (76*(n:ℤ)+2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (65*(n:ℤ)+1751) (76*(n:ℤ)+2047) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (65*(n:ℤ)+1751) (76*(n:ℤ)+2047) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (65*(n:ℤ)+1751) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (65*(n:ℤ)+1751) (76*(n:ℤ)+2047) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_7 (n u : ℕ) (hu : (76*n+2047) ≤ u ∧ u < (84*n+2263)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2047) (84*(n:ℤ)+2263) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 11 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (84*(n:ℤ)+2263) 11 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (84*(n:ℤ)+2263) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2047) (84*(n:ℤ)+2263) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2047) (84*(n:ℤ)+2263) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_8 (n u : ℕ) (hu : (84*n+2263) ≤ u ∧ u < (96*n+2586)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 5 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (84*(n:ℤ)+2263) (96*(n:ℤ)+2586) 5 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (84*(n:ℤ)+2263) (96*(n:ℤ)+2586) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (84*(n:ℤ)+2263) (96*(n:ℤ)+2586) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (84*(n:ℤ)+2263) (96*(n:ℤ)+2586) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (84*(n:ℤ)+2263) (96*(n:ℤ)+2586) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_9 (n u : ℕ) (hu : (96*n+2586) ≤ u ∧ u < (103*n+2774)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (96*(n:ℤ)+2586) (103*(n:ℤ)+2774) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 12 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (96*(n:ℤ)+2586) (103*(n:ℤ)+2774) 12 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (96*(n:ℤ)+2586) (103*(n:ℤ)+2774) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (96*(n:ℤ)+2586) (103*(n:ℤ)+2774) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (96*(n:ℤ)+2586) (103*(n:ℤ)+2774) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_10 (n u : ℕ) (hu : (103*n+2774) ≤ u ∧ u < (114*n+3071)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (103*(n:ℤ)+2774) (114*(n:ℤ)+3071) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (103*(n:ℤ)+2774) (114*(n:ℤ)+3071) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (103*(n:ℤ)+2774) (114*(n:ℤ)+3071) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (103*(n:ℤ)+2774) (114*(n:ℤ)+3071) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (103*(n:ℤ)+2774) (114*(n:ℤ)+3071) 2 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_11 (n u : ℕ) (hu : (114*n+3071) ≤ u ∧ u < (122*n+3286)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3071) (122*(n:ℤ)+3286) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 13 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (122*(n:ℤ)+3286) 13 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (122*(n:ℤ)+3286) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3071) (122*(n:ℤ)+3286) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3071) (122*(n:ℤ)+3286) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_12 (n u : ℕ) (hu : (122*n+3286) ≤ u ∧ u < (141*n+3798)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (122*(n:ℤ)+3286) (141*(n:ℤ)+3798) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 14 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (122*(n:ℤ)+3286) (141*(n:ℤ)+3798) 14 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (122*(n:ℤ)+3286) (141*(n:ℤ)+3798) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (122*(n:ℤ)+3286) (141*(n:ℤ)+3798) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (122*(n:ℤ)+3286) (141*(n:ℤ)+3798) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_18_13 (n u : ℕ) (hu : (141*n+3798) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 18 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*18))/(19*(152*((n:ℤ)+27)-8)) = 6 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*18) (19*(152*((n:ℤ)+27)-8)) (141*(n:ℤ)+3798) (152*(n:ℤ)+4095) 6 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 15 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (141*(n:ℤ)+3798) (152*(n:ℤ)+4095) 15 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (141*(n:ℤ)+3798) (152*(n:ℤ)+4095) 7 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (141*(n:ℤ)+3798) (152*(n:ℤ)+4095) 1 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*18*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (141*(n:ℤ)+3798) (152*(n:ℤ)+4095) 3 u
    · ring_nf; positivity
    · ring_nf; positivity
    · apply sub_nonneg.mp
      ring_nf; positivity
    · apply sub_pos.mp
      ring_nf; positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  norm_num at h0 h1 h2 h3 h4 ⊢
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_18 (n : ℕ) :
    rowZeroCount (n+27) 18 = 84*n+2265 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 18 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 18 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero] using rowValue_normalized (n+27) 18 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u : ℕ => normalizedRow (152*((n:ℤ)+27)-8) u 18=0) = ((((((((Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) ∪ (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (46*n+1239) : Finset ℕ)) ∪ (Finset.Ico (46*n+1239) (65*n+1751) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (84*n+2263) : Finset ℕ)) ∪ (Finset.Ico (84*n+2263) (96*n+2586) : Finset ℕ)) ∪ (Finset.Ico (103*n+2774) (114*n+3071) : Finset ℕ)) ∪ (Finset.Ico (141*n+3798) (152*n+4095) : Finset ℕ)) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    by_cases hu : u < L (n+27)
    · have hub : u < (152*n+4095) := by dsimp [L] at hu; omega
      by_cases hc0 : u < (8*n+215)
      · have hf := cell_18_0 n u (by omega)
        rw [hf]
        norm_num
        dsimp [L] at *
        omega
      · by_cases hc1 : u < (20*n+538)
        · have hf := cell_18_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        · by_cases hc2 : u < (27*n+727)
          · have hf := cell_18_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          · by_cases hc3 : u < (38*n+1023)
            · have hf := cell_18_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            · by_cases hc4 : u < (46*n+1239)
              · have hf := cell_18_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              · by_cases hc5 : u < (65*n+1751)
                · have hf := cell_18_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                · by_cases hc6 : u < (76*n+2047)
                  · have hf := cell_18_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  · by_cases hc7 : u < (84*n+2263)
                    · have hf := cell_18_7 n u (by omega)
                      rw [hf]
                      norm_num
                      dsimp [L] at *
                      omega
                    · by_cases hc8 : u < (96*n+2586)
                      · have hf := cell_18_8 n u (by omega)
                        rw [hf]
                        norm_num
                        dsimp [L] at *
                        omega
                      · by_cases hc9 : u < (103*n+2774)
                        · have hf := cell_18_9 n u (by omega)
                          rw [hf]
                          norm_num
                          dsimp [L] at *
                          omega
                        · by_cases hc10 : u < (114*n+3071)
                          · have hf := cell_18_10 n u (by omega)
                            rw [hf]
                            norm_num
                            dsimp [L] at *
                            omega
                          · by_cases hc11 : u < (122*n+3286)
                            · have hf := cell_18_11 n u (by omega)
                              rw [hf]
                              norm_num
                              dsimp [L] at *
                              omega
                            · by_cases hc12 : u < (141*n+3798)
                              · have hf := cell_18_12 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
                              · have hf := cell_18_13 n u (by omega)
                                rw [hf]
                                norm_num
                                dsimp [L] at *
                                omega
    · dsimp [L] at *
      omega
  rw [heq]
  have hd1 : Disjoint (Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd2 : Disjoint ((Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) ∪ (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ)) (Finset.Ico (38*n+1023) (46*n+1239) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd3 : Disjoint (((Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) ∪ (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (46*n+1239) : Finset ℕ)) (Finset.Ico (46*n+1239) (65*n+1751) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd4 : Disjoint ((((Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) ∪ (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (46*n+1239) : Finset ℕ)) ∪ (Finset.Ico (46*n+1239) (65*n+1751) : Finset ℕ)) (Finset.Ico (76*n+2047) (84*n+2263) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd5 : Disjoint (((((Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) ∪ (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (46*n+1239) : Finset ℕ)) ∪ (Finset.Ico (46*n+1239) (65*n+1751) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (84*n+2263) : Finset ℕ)) (Finset.Ico (84*n+2263) (96*n+2586) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd6 : Disjoint ((((((Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) ∪ (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (46*n+1239) : Finset ℕ)) ∪ (Finset.Ico (46*n+1239) (65*n+1751) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (84*n+2263) : Finset ℕ)) ∪ (Finset.Ico (84*n+2263) (96*n+2586) : Finset ℕ)) (Finset.Ico (103*n+2774) (114*n+3071) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  have hd7 : Disjoint (((((((Finset.Ico (0*n+0) (8*n+215) : Finset ℕ) ∪ (Finset.Ico (20*n+538) (27*n+727) : Finset ℕ)) ∪ (Finset.Ico (38*n+1023) (46*n+1239) : Finset ℕ)) ∪ (Finset.Ico (46*n+1239) (65*n+1751) : Finset ℕ)) ∪ (Finset.Ico (76*n+2047) (84*n+2263) : Finset ℕ)) ∪ (Finset.Ico (84*n+2263) (96*n+2586) : Finset ℕ)) ∪ (Finset.Ico (103*n+2774) (114*n+3071) : Finset ℕ)) (Finset.Ico (141*n+3798) (152*n+4095) : Finset ℕ) := by
    simp only [Finset.disjoint_left,Finset.mem_union,Finset.mem_Ico]
    omega
  rw [Finset.card_union_of_disjoint hd7,Finset.card_union_of_disjoint hd6,Finset.card_union_of_disjoint hd5,Finset.card_union_of_disjoint hd4,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  simp only [Nat.card_Ico]
  omega
private theorem rowB_at_M (r : ℕ) : rowB (M r) = (B r : ℚ) := by
  have h : (B r : ℚ) + 8 = 152 * (M r : ℚ) := by exact_mod_cast b_add_eight r
  dsimp [rowB]
  linarith

/- Signed Int cuts avoid all accidental Nat subtraction/truncation. These are
   exactly the supplied Pro P/R/G formulas, including its v=9 and v=11 rows. -/
private def lint (m : ℕ) : ℤ := 152 * (m : ℤ) - 9
private theorem l_cast (m : ℕ) (hm : 27 ≤ m) : (L m : ℤ) = lint m := by
  have h : 9 ≤ 152 * m := by omega
  simp only [L, lint, Nat.cast_sub h, Nat.cast_mul, Nat.cast_ofNat]

private def pCut (m v j : ℕ) : ℤ :=
  (76 * (j : ℤ) - 20 * (v : ℤ)) * (m : ℤ) + (v : ℤ) - 4 * (j : ℤ)
private def rCut (m v j : ℕ) : ℤ :=
  38 * (j : ℤ) * (m : ℤ) - (171 * (j : ℤ) + 4 * (v : ℤ)) / 76
private def gCut (m v h : ℕ) : ℤ :=
  (19 * (h : ℤ) - 8 * (v : ℤ)) * (m : ℤ) -
    (171 * (h : ℤ) - 64 * (v : ℤ)) / 152

private def zeroIntervals (m v : ℕ) : List (ℤ × ℤ) :=
  let l := lint m
  let P := pCut m v
  let R := rCut m v
  let G := gCut m v
  match v with
  | 0 => [(0, G 1), (R 1, G 3), (G 5, R 3), (G 7, l)]
  | 1 => [(0, G 1), (R 1, G 3), (P 1, R 2), (G 5, R 3), (G 7, P 2), (G 8, l)]
  | 2 => [(0, G 1), (P 1, R 1), (G 3, R 2), (G 5, P 2), (G 8, l)]
  | 3 => [(P 1, G 3), (R 1, G 5), (R 2, P 2), (G 7, R 3), (G 8, G 9)]
  | 4 => [(0, G 3), (R 1, G 5), (P 2, R 2), (G 7, R 3), (G 8, G 9), (P 3, l)]
  | 5 => [(0, G 3), (R 1, P 2), (G 5, R 2), (G 7, G 8), (R 3, P 3), (G 9, l)]
  | 6 => [(0, G 3), (P 2, R 1), (G 5, R 2), (G 7, G 8), (P 3, R 3), (G 9, l)]
  | 7 => [(0, G 3), (P 2, R 1), (G 5, R 2), (G 7, P 3), (G 8, R 3), (G 9, l)]
  | 8 => [(0, G 5), (R 1, P 3), (G 7, R 2), (G 8, G 9), (R 3, P 4), (G 11, l)]
  | 9 => [(0, G 5), (R 1, P 3), (G 7, R 2), (G 8, G 9), (R 3, P 4), (G 11, l)]
  | 10 => [(0, G 5), (P 3, R 1), (G 7, G 8), (R 2, G 9), (P 4, R 3), (G 11, l)]
  | 11 => [(0, G 5), (P 3, R 1), (G 7, G 8), (R 2, G 9), (P 4, R 3), (G 11, l)]
  | 12 => [(0, G 7), (R 1, G 8), (P 4, G 9), (R 2, G 11), (R 3, P 5), (G 13, l)]
  | 13 => [(0, G 7), (R 1, P 4), (G 8, G 9), (R 2, G 11), (R 3, P 5), (G 13, l)]
  | 14 => [(0, G 7), (P 4, R 1), (G 8, G 9), (R 2, G 11), (P 5, R 3), (G 13, l)]
  | 15 => [(0, P 4), (G 7, G 8), (R 1, G 9), (R 2, P 5), (G 11, R 3), (G 13, l)]
  | 16 => [(G 7, G 8), (R 1, G 9), (P 5, R 2), (G 11, R 3), (G 13, P 6)]
  | 17 => [(0, G 8), (P 5, G 11), (R 2, G 13), (R 3, P 6), (G 15, l)]
  | 18 => [(0, G 8), (P 5, G 9), (R 1, G 11), (R 2, P 6), (G 13, R 3), (G 15, l)]
  | _ => []

private def intervalZeroSet (m v : ℕ) : Finset ℤ :=
  (zeroIntervals m v).foldl (fun s p => s ∪ Finset.Ico p.1 p.2) ∅
private def signedLength (m v : ℕ) : ℤ :=
  ((zeroIntervals m v).map (fun p => p.2 - p.1)).sum
private def rowAffine (m v : ℕ) : ℤ :=
  let n : ℤ := m
  match v with
  | 0 => 76 * n - 5
  | 1 | 18 => 84 * n - 3
  | 2 | 17 => 89 * n - 5
  | 3 | 16 => 90 * n - 5
  | 4 | 15 => 90 * n - 4
  | 5 | 14 => 106 * n - 5
  | 6 | 13 => 98 * n - 5
  | 7 | 12 => 130 * n - 7
  | 8 | 11 => 124 * n - 6
  | 9 | 10 => 92 * n - 4
  | _ => 0

/- This proves SIGNED interval-length arithmetic, not floor classification,
   positivity, disjointness, or actual row cardinality. -/
private theorem interval_lengths (m v : ℕ) (hv : v < 19) :
    signedLength m v = rowAffine m v := by
  interval_cases v <;>
    norm_num [signedLength, zeroIntervals, pCut, rCut, gCut, lint, rowAffine] <;> ring

private theorem all_interval_lengths (m : ℕ) :
    (∑ v ∈ Finset.range 19, signedLength m v) = 1882 * (m : ℤ) - 93 := by
  calc
    _ = ∑ v ∈ Finset.range 19, rowAffine m v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact interval_lengths m v (Finset.mem_range.mp hv)
    _ = _ := by norm_num [Finset.sum_range_succ, rowAffine]; ring

private theorem affine_total (r : ℕ) :
    76 * (1882 * M r - 92) = 941 * B r + 536 := by
  have := b_affine r
  have := m_lower r
  omega

set_option maxHeartbeats 1000000 in
private theorem physical_zero_card_reduction (r : ℕ) :
    (physicalZero r).card =
      (∑ v ∈ Finset.range 19, rowZeroCount (M r) v)+1 := by
  classical
  let s : Finset ℕ := (Finset.range (K r)).filter
    (fun k => sumAtMask r (k*Q r)=0)
  let t : Finset (ℕ×ℕ) := ((Finset.range (B r-1)) ×ˢ (Finset.range 19)).filter
    (fun p => rowValue (M r) p.2 p.1=0)
  have hzero (k : ℕ) (hk : k ≤ K r) :
      sumAtMask r (k*Q r)=0 ↔ f r k=0 := by
    rw [candidate_sum_formula r k hk]
    have hn : (N r : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt (n_positive r)
    simp only [mul_eq_zero,hn,false_or]
  have hend : sumAtMask r (K r*Q r)=0 := by
    rw [Nat.mul_comm,q_mul_k]
    exact sumAtMask_full r
  have hc : candidateMasks r = insert (K r) s := by
    ext k
    simp only [candidateMasks,s,Finset.mem_filter,Finset.mem_range,Finset.mem_insert]
    constructor
    · rintro ⟨hk,hz⟩
      by_cases he : k=K r
      · exact Or.inl he
      · exact Or.inr ⟨by omega,hz⟩
    · rintro (rfl | ⟨hk,hz⟩)
      · exact ⟨by omega,hend⟩
      · exact ⟨by omega,hz⟩
  have hknot : K r ∉ s := by simp [s]
  have hcard : s.card=t.card := by
    apply Finset.card_nbij (fun k : ℕ => (k/19,k%19))
    · intro k hk
      obtain ⟨hk,hz⟩ := Finset.mem_filter.mp hk
      have hlt := Finset.mem_range.mp hk
      have hu : k/19 < B r-1 := by dsimp [K] at hlt; omega
      have hv : k%19 < 19 := Nat.mod_lt _ (by norm_num)
      have hf := (hzero k (by omega)).mp hz
      have he : 19*(k/19)+k%19=k := by omega
      have hp := candidate_profile r (k/19) (k%19)
      rw [he] at hp
      dsimp only
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hu,Finset.mem_range.mpr hv⟩,hp.symm.trans hf⟩
    · intro a ha b hb he
      dsimp only at he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      dsimp only at h1 h2
      omega
    · intro p hp
      obtain ⟨hp,hz⟩ := Finset.mem_filter.mp hp
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
      have hu := Finset.mem_range.mp hu
      have hv := Finset.mem_range.mp hv
      have hk : 19*p.1+p.2 < K r := by dsimp [K]; omega
      refine ⟨19*p.1+p.2,?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,
          (hzero _ (by omega)).mpr ((candidate_profile r p.1 p.2).trans hz)⟩
      · dsimp only
        apply Prod.ext <;> dsimp only <;> omega
  have htcard : t.card=∑ v ∈ Finset.range 19, rowZeroCount (M r) v := by
    simp only [t,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
    rw [Finset.sum_comm]
    congr 1
    ext v
    simp only [rowZeroCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [physical_candidate_card,hc,Finset.card_insert_of_notMem hknot,hcard,htcard]
  omega

/-
OPEN mathematical boundaries. These are specifications, NOT assumed helpers,
and NOT Lean theorem declarations. See source-manifest.json for consumers.

1. six_actual_carries (r : ℕ) :
     ∀ i : Fin (3 * d r),
       2 * actualSource (3 * d r) (seed r) i -
         actualSource (3 * d r) (seed r) (finRotate (3 * d r) i) =
         modulus (3 * d r) * epsilon r i
   Derive the six branches from centered uniqueness/doubling (or the three
   actual phase representatives). The cyclic endpoint is included.

2. binary_subset_transport (r : ℕ) (A : Finset (Fin (3 * d r))) :
     (∑ i ∈ A, actualSource (3 * d r) (seed r) i) = binarySum r (mask A)
   carry_floor_identity (r m : ℕ) (hm : m ≤ N r) :
     binarySum r m = (seed r : ℤ) * (m : ℤ) - (N r : ℤ) * carryCorrection r m
   The latter must consume six_actual_carries, iterate the recurrence and
   prove the binary floor transport, including m=N. No Nat subtraction in
   carryCorrection is permitted. Then derive, rather than assume:
   candidate_sum_formula (r k : ℕ) (hk : k ≤ K r) :
     sumAtMask r (k * Q r) = (N r : ℤ) * f r k
   candidate_profile (r u v : ℕ) (hu : u < B r - 1) (hv : v < 19) :
     f r (19 * u + v) = rowValue (M r) v u
   This last step needs integer floor translations and the exact B^-2 term.

3. cut_order_and_floor_profile (m : ℕ) (hm : 27 ≤ m) :
     ∀ v < 19, ∀ u < L m,
       (u : ℤ) ∈ intervalZeroSet m v ↔ rowValue m v u = 0
   Prove the P/R/G threshold ceilings and exhaustive H jumps for ALL m>=27,
   not sampled m. The only coincident cuts are P1=R2 in row zero. Also prove
   the listed intervals disjoint, nonempty and inside [0,lint m). Combine
   their Ico cardinalities with all_interval_lengths to obtain:
   row_zero_count (m : ℕ) (hm : 27 ≤ m) :
     (∑ v ∈ Finset.range 19, rowZeroCount m v) = 1882 * m - 93

4. physical_zero_card_reduction (r : ℕ) :
     (physicalZero r).card =
       (∑ v ∈ Finset.range 19, rowZeroCount (M r) v) + 1
   Start with physical_candidate_card. Partition k<K uniquely by k=19u+v,
   u<B-1, v<19; use candidate_sum_formula/candidate_profile and N>0 for
   literal zero. The separate k=K endpoint uses q_mul_k and sumAtMask_full.
   This is still OPEN even though the physical-to-candidate sieve is written.

The SOLE intended public theorem, not yet declared, is exactly:

theorem actual_zero_subsets_card (r : ℕ) :
    let d := 18 * r + 12
    76 * (Finset.univ.filter (fun A : Finset (Fin (3 * d)) =>
      (∑ i ∈ A,
        SourceWidth.actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) = 0)).card =
      941 * 2 ^ d + 536 := by
  classical
  change 76 * (Finset.univ.filter (fun A : Finset (Fin (3 * d r)) =>
    (∑ i ∈ A, actualSource (3 * d r)
      ((2 ^ d r - 1) * (2 ^ (d r + 1) - 3)) i) = 0)).card = 941 * B r + 536
  rw [original_seed r]
  change 76 * (physicalZero r).card = 941 * B r + 536
  rw [physical_zero_card_reduction r, row_zero_count (M r) (m_lower r)]
  have hadd : (1882 * M r - 93) + 1 = 1882 * M r - 92 := by
    have := m_lower r
    omega
  rw [hadd]
  exact affine_total r

This composition genuinely uses both missing cardinality theorems, the seed
conversion and affine_total. Activating it before those proofs exist would
NOT be a complete candidate. No helper premise is added to the public type.
-/

end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
