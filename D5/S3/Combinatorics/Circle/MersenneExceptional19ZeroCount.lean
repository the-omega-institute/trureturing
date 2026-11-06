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
  norm_num at hz8 hz4 hz1
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
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (0*(n:ℤ)+0) (19*(n:ℤ)+512) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_1 (n u : ℕ) (hu : (19*n+512) ≤ u ∧ u < (38*n+1024)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 0 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (19*(n:ℤ)+512) (38*(n:ℤ)+1024) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_2 (n u : ℕ) (hu : (38*n+1024) ≤ u ∧ u < (57*n+1536)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 2 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (38*(n:ℤ)+1024) (57*(n:ℤ)+1536) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_3 (n u : ℕ) (hu : (57*n+1536) ≤ u ∧ u < (76*n+2048)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 0 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 3 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 1 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (57*(n:ℤ)+1536) (76*(n:ℤ)+2048) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_4 (n u : ℕ) (hu : (76*n+2048) ≤ u ∧ u < (95*n+2560)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 4 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 4 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 2 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (76*(n:ℤ)+2048) (95*(n:ℤ)+2560) 2 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_5 (n u : ℕ) (hu : (95*n+2560) ≤ u ∧ u < (114*n+3072)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 5 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 5 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 2 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 2 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (95*(n:ℤ)+2560) (114*(n:ℤ)+3072) 2 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_6 (n u : ℕ) (hu : (114*n+3072) ≤ u ∧ u < (133*n+3584)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = -1 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 6 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 6 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 3 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (114*(n:ℤ)+3072) (133*(n:ℤ)+3584) 3 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem cell_0_7 (n u : ℕ) (hu : (133*n+3584) ≤ u ∧ u < (152*n+4095)) :
    normalizedRow (152*((n:ℤ)+27)-8) u 0 = 0 := by
  have h0 : ((38)*(u:ℤ)+((5*(152*((n:ℤ)+27)-8)+2)*0))/(19*(152*((n:ℤ)+27)-8)) = 1 := by
    apply floor_on_cell (38) ((5*(152*((n:ℤ)+27)-8)+2)*0) (19*(152*((n:ℤ)+27)-8)) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 1 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h1 : ((152*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 7 := by
    apply floor_on_cell (152*((152*((n:ℤ)+27)-8)+1)) (8*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 7 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h2 : ((76*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 3 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h3 : ((19*((152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^2) = 0 := by
    apply floor_on_cell (19*((152*((n:ℤ)+27)-8)+1)) (0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^2) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 0 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  have h4 : ((76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1))*(u:ℤ)+(4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)))/(19*(152*((n:ℤ)+27)-8)^3) = 3 := by
    apply floor_on_cell (76*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (4*0*((152*((n:ℤ)+27)-8)^2+(152*((n:ℤ)+27)-8)+1)) (19*(152*((n:ℤ)+27)-8)^3) (133*(n:ℤ)+3584) (152*(n:ℤ)+4095) 3 u
    · ring_nf <;> positivity
    · ring_nf <;> positivity
    · apply sub_nonneg.mp
      ring_nf <;> positivity
    · apply sub_pos.mp
      ring_nf <;> positivity
    · exact_mod_cast hu
  dsimp [normalizedRow]
  rw [h0,h1,h2,h3,h4]
  norm_num

private theorem row_count_0 (n : ℕ) :
    rowZeroCount (n+27) 0 = 76*n+2047 := by
  classical
  have hval (u : ℕ) : rowValue (n+27) 0 u =
      normalizedRow (152*((n:ℤ)+27)-8) u 0 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using rowValue_normalized (n+27) 0 u (by omega)
  unfold rowZeroCount
  simp_rw [hval]
  have heq : (Finset.range (L (n+27))).filter
      (fun u => normalizedRow (152*((n:ℤ)+27)-8) u 0=0) = ((((Finset.Ico (0*n+0) (19*n+512) : Finset ℕ) ∪ (Finset.Ico (38*n+1024) (57*n+1536) : Finset ℕ)) ∪ (Finset.Ico (95*n+2560) (114*n+3072) : Finset ℕ)) ∪ (Finset.Ico (133*n+3584) (152*n+4095) : Finset ℕ)) := by
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
      ·
        by_cases hc1 : u < (38*n+1024)
        · have hf := cell_0_1 n u (by omega)
          rw [hf]
          norm_num
          dsimp [L] at *
          omega
        ·
          by_cases hc2 : u < (57*n+1536)
          · have hf := cell_0_2 n u (by omega)
            rw [hf]
            norm_num
            dsimp [L] at *
            omega
          ·
            by_cases hc3 : u < (76*n+2048)
            · have hf := cell_0_3 n u (by omega)
              rw [hf]
              norm_num
              dsimp [L] at *
              omega
            ·
              by_cases hc4 : u < (95*n+2560)
              · have hf := cell_0_4 n u (by omega)
                rw [hf]
                norm_num
                dsimp [L] at *
                omega
              ·
                by_cases hc5 : u < (114*n+3072)
                · have hf := cell_0_5 n u (by omega)
                  rw [hf]
                  norm_num
                  dsimp [L] at *
                  omega
                ·
                  by_cases hc6 : u < (133*n+3584)
                  · have hf := cell_0_6 n u (by omega)
                    rw [hf]
                    norm_num
                    dsimp [L] at *
                    omega
                  ·
                    have hf := cell_0_7 n u (by omega)
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
