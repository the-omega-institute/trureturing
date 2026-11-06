/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroCount
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Powerset]
   utility: none
   digest: Exact physical mask sieve and exceptional19 integer-floor count development.

-/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows.Basic
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer
public import D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
import all D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
public import D5.S3.Combinatorics.Circle.Orbit.MersennePhaseNoncyclicFamily
import all D5.S3.Combinatorics.Circle.Orbit.MersennePhaseNoncyclicFamily
public import Batteries.Tactic.OpenPrivate
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

/-! # Exact exceptional19 physical zero-subset counting

The physical mask sieve, integer block transport and universal row cardinalities
combine to count every original physical integer-zero subset. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount

open SourceWidth ZeroSumSubsets
open private rowB X Z Hjump rowValue rowZeroCount normalizedRow rowValue_normalized from D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows.Basic open private row_zero_count from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroCountRows open scoped BigOperators open private from D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
open D5.S3.Combinatorics.Circle.ZeroSumSubsets (mask_surjective) open private phase_scaled_gcd from D5.S3.Combinatorics.Circle.Orbit.MersennePhaseNoncyclicFamily private def d (r : ℕ) : ℕ := 18 * r + 12 private def B (r : ℕ) : ℕ := 2 ^ d r private def N (r : ℕ) : ℕ := B r ^ 3 - 1 private def (r : ℕ) : ℕ := (B r - 1) * (2 * B r - 3) private def C (b : ℕ) : ℕ := b ^ 2 + b + 1 private def Q (r : ℕ) : ℕ := C (B r) / 19 private def K (r : ℕ) : ℕ := 19 * (B r - 1) private def M (r : ℕ) : ℕ := (B r + 8) / 152 private def L (m : ℕ) : ℕ := 152 * m - 9 private def physicalZero (r : ℕ) : Finset (Finset (Fin (3 * d r))) := Finset.univ.filter (fun A => (∑ i ∈ A, actualSource (3 * d r) (seed r) i) = 0) private theorem d_lower (r : ℕ) : 3 ≤ d r := by dsimp [d]; omega private theorem d_positive (r : ℕ) : 0 < d r := by have := d_lower r omega private theorem b_lower (r : ℕ) : 4096 ≤ B r := by have he : 12 ≤ d r := by dsimp [d]; omega have hp : (2 : ℕ) ^ 12 ≤ 2 ^ d r := Nat.pow_le_pow_right (by decide) he norm_num at hp exact hp private theorem b_multiple_eight (r : ℕ) : 8 ∣ B r := by have hd := d_lower r refine ⟨2 ^ (d r - 3), ?_⟩ change 2 ^ d r = 8 * 2 ^ (d r - 3) calc 2 ^ d r = 2 ^ (3 + (d r - 3)) := by congr 1; omega _ = 8 * 2 ^ (d r - 3) := by rw [pow_add]; norm_num private theorem b_mod_nineteen (r : ℕ) : B r % 19 = 11 := by change (2 : ℕ) ^ (18 * r + 12) % 19 = 11 rw [pow_add, pow_mul, Nat.mul_mod] have hpow : ((2 : ℕ) ^ 18) ^ r % 19 = 1 := by rw [Nat.pow_mod] norm_num rw [hpow] norm_num private theorem b_add_eight (r : ℕ) : B r + 8 = 152 * M r := by have h8 : B r % 8 = 0 := Nat.mod_eq_zero_of_dvd (b_multiple_eight r) have h19 := b_mod_nineteen r have h152 : (B r + 8) % 152 = 0 := by omega have hdiv := Nat.mod_add_div (B r + 8) 152 dsimp [M] omega private theorem b_affine (r : ℕ) : B r = 152 * M r - 8 := by have := b_add_eight r omega private theorem m_lower (r : ℕ) : 27 ≤ M r := by have := b_add_eight r have := b_lower r omega private theorem original_seed (r : ℕ) : (2 ^ d r - 1) * (2 ^ (d r + 1) - 3) = r := by simp only [seed, B, pow_succ, Nat.mul_comm] private theorem n_pow (r : ℕ) : N r = 2 ^ (3 * d r) - 1 := by change ((2 : ℕ) ^ d r) ^ 3 - 1 = 2 ^ (3 * d r) - 1 rw [← pow_mul, Nat.mul_comm (d r) 3] private theorem n_positive (r : ℕ) : 0 < N r := by have hd := d_positive r have hp := Nat.one_lt_two_pow (show 3 * d r ≠ 0 by omega) rw [n_pow] omega private theorem n_factor (r : ℕ) : N r = (B r - 1) * C (B r) := by have hb : 1 ≤ B r := by have := b_lower r; omega have he : B r - 1 + 1 = B r := Nat.sub_add_cancel hb have hp : (B r - 1 + 1) ^ 3 = (B r - 1) * C (B r - 1 + 1) + 1 := by dsimp [C]; ring rw [he] at hp dsimp [N] omega private theorem gcd_exceptional (r : ℕ) : Nat.gcd (seed r) (N r) = K r := by have hb := b_lower r have hm := b_mod_nineteen r have hdiv : 19 ∣ 2 ^ (d r + 1) - 3 := by rw [pow_succ] change 19 ∣ B r * 2 - 3 omega have hg := phase_scaled_gcd (d r) (d_positive r) rw [Nat.gcd_eq_right hdiv, original_seed r, ← n_pow r] at hg simpa only [B, K, Nat.mul_comm] using hg private theorem q_eq_quotient (r : ℕ) : N r / Nat.gcd (seed r) (N r) = Q r := by rw [gcd_exceptional, n_factor] change (B r - 1) * C (B r) / (19 * (B r - 1)) = C (B r) / 19 rw [Nat.mul_comm 19 (B r - 1)] exact Nat.mul_div_mul_left _ _ (by have := b_lower r; omega) private theorem q_positive (r : ℕ) : 0 < Q r := by rw [← q_eq_quotient r] exact Nat.div_gcd_pos_of_pos_right (seed r) (n_positive r) private theorem q_mul_k (r : ℕ) : Q r * K r = N r := by have h := Nat.div_mul_cancel (Nat.gcd_dvd_right (seed r) (N r)) rw [q_eq_quotient r, gcd_exceptional r] at h exact h private theorem zero_sum_implies_candidate (r : ℕ) (A : Finset (Fin (3 * d r))) (hA : (∑ i ∈ A, actualSource (3 * d r) (seed r) i) = 0) : Q r ∣ mask A := by have hd := zero_mask_dvd A hA rw [← n_pow r] at hd have hq := quotient_dvd (n_positive r) hd rwa [q_eq_quotient r] at hq /- The inverse is selected from the SEALED physical mask bijection. This is not a new binary-set foundation; every physical label is retained. -/ private noncomputable def subsetOfMask (r m : ℕ) : Finset (Fin (3 * d r)) := if hm : m < 2 ^ (3 * d r) then (mask_surjective (3 * d r) m hm).choose else ∅ private theorem mask_subsetOfMask (r m : ℕ) (hm : m < 2 ^ (3 * d r)) : mask (subsetOfMask r m) = m := by simp only [subsetOfMask, dite_eq_left hm] exact (mask_surjective (3 * d r) m hm).choose_spec private theorem subsetOfMask_mask (r : ℕ) (A : Finset (Fin (3 * d r))) : subsetOfMask r (mask A) = A := by apply mask_injective (3 * d r) apply mask_subsetOfMask have hb := mask_bound A have hp : 1 ≤ (2 : ℕ) ^ (3 * d r) := Nat.one_le_two_pow omega private noncomputable def sumAtMask (r m : ℕ) : ℤ := ∑ i ∈ subsetOfMask r m, actualSource (3 * d r) (seed r) i private theorem sumAtMask_mask (r : ℕ) (A : Finset (Fin (3 * d r))) : sumAtMask r (mask A) = ∑ i ∈ A, actualSource (3 * d r) (seed r) i := by unfold sumAtMask rw [subsetOfMask_mask r A] private theorem full_mask_is_zero (r : ℕ) : (∑ i : Fin (3 * d r), actualSource (3 * d r) (seed r) i) = 0 := by exact (source_cycle (show 0 < 3 * d r by have := d_positive r; omega) (seed r)).2.1 private theorem sumAtMask_full (r : ℕ) : sumAtMask r (N r) = 0 := by have h := sumAtMask_mask r (Finset.univ : Finset (Fin (3 * d r))) rw [mask_full, ← n_pow r] at h exact h.trans (full_mask_is_zero r) private noncomputable def candidateMasks (r : ℕ) : Finset ℕ := (Finset.range (K r + 1)).filter (fun k => sumAtMask r (k * Q r) = 0) /- This sieve is an exact physical-cardinality reduction, BEFORE the open carry/profile computation. It does not replace literal zero by divisibility. -/ private theorem physical_candidate_card (r : ℕ) : (physicalZero r).card = (candidateMasks r).card := by classical unfold candidateMasks apply Finset.card_nbij (fun A : Finset (Fin (3 * d r)) => mask A / Q r) · intro A hA have hz := (Finset.mem_filter.mp hA).2 have hd := zero_sum_implies_candidate r A hz have hb := mask_bound A rw [← n_pow r] at hb have hu := Nat.div_le_div_right hb (c := Q r) rw [← q_mul_k r, Nat.mul_div_cancel_left _ (q_positive r)] at hu dsimp only refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩ rw [Nat.div_mul_cancel hd, sumAtMask_mask r A] exact hz · intro A hA D hD he dsimp only at he have hdA := zero_sum_implies_candidate r A (Finset.mem_filter.mp hA).2 have hdD := zero_sum_implies_candidate r D (Finset.mem_filter.mp hD).2 apply mask_injective (3 * d r) calc mask A = mask A / Q r * Q r := (Nat.div_mul_cancel hdA).symm _ = mask D / Q r * Q r := by rw [he] _ = mask D := Nat.div_mul_cancel hdD · intro k hk have hk' := Finset.mem_filter.mp hk have hkbound : k ≤ K r := by have := Finset.mem_range.mp hk'.1; omega have hm : k * Q r ≤ N r := by calc k * Q r ≤ K r * Q r := Nat.mul_le_mul_right _ hkbound _ = N r := by rw [Nat.mul_comm, q_mul_k r] have hm' : k * Q r < 2 ^ (3 * d r) := by rw [n_pow r] at hm have hp : 1 ≤ (2 : ℕ) ^ (3 * d r) := Nat.one_le_two_pow omega refine ⟨subsetOfMask r (k * Q r), ?_, ?_⟩ · apply Finset.mem_filter.mpr refine ⟨Finset.mem_univ _, ?_⟩ change sumAtMask r (k * Q r) = 0 exact hk'.2 · dsimp only rw [mask_subsetOfMask r _ hm', Nat.mul_div_cancel _ (q_positive r)] /- Correct five signed floors. EACH Nat quotient is cast BEFORE subtraction. -/ private def carryCorrection (r m : ℕ) : ℤ := ((2 * m / B r : ℕ) : ℤ) - ((8 * m / B r ^ 2 : ℕ) : ℤ) + ((4 * m / B r ^ 2 : ℕ) : ℤ) - ((m / B r ^ 2 : ℕ) : ℤ) + ((4 * m / B r ^ 3 : ℕ) : ℤ) open private from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer
open D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer (seed seed degree base total slice charge mask_slices actual_sum_blocks)

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
  change t*(19*(u:ℤ)+v) -
    (2*((19*(u:ℤ)+v)*q)/b-8*((19*(u:ℤ)+v)*q)/b^2+
      4*((19*(u:ℤ)+v)*q)/b^2-((19*(u:ℤ)+v)*q)/b^2+
      4*((19*(u:ℤ)+v)*q)/b^3) = _
  rw [hfirst,hother 8,hother 4,show ((19*(u:ℤ)+v)*q)/b^2 =
    u+(19*(b+1)*u+v*(b^2+b+1))/(19*b^2) by simpa using hother 1,hlast]
  dsimp [b] at *
  linear_combination (u:ℤ)*ht

private theorem candidate_profile (r u v : ℕ) :
    f r (19*u+v) = rowValue (M r) v u := by
  rw [candidate_normalized,rowValue_normalized _ _ _ (m_lower r)]
  congr 1
  have h := b_add_eight r
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

private theorem card_filter_product (a b : Finset ℕ) (P : ℕ × ℕ → Prop)
    [DecidablePred P] :
    ((a ×ˢ b).filter P).card = ∑ y ∈ b, (a.filter (fun x => P (x,y))).card := by
  simp only [Finset.card_filter,Finset.sum_product]
  rw [Finset.sum_comm]

set_option maxHeartbeats 1000000 in
private theorem physical_zero_card_reduction (r : ℕ) :
    (physicalZero r).card =
      (∑ v ∈ Finset.range 19, rowZeroCount (M r) v)+1 := by
  classical
  let s : Finset ℕ := (Finset.range (K r)).filter
    (fun k => sumAtMask r (k*Q r)=0)
  let t : Finset (ℕ × ℕ) := ((Finset.range (B r-1)) ×ˢ (Finset.range 19)).filter
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
  have hL : B r-1 = L (M r) := by
    have := b_add_eight r
    dsimp [L]
    omega
  have htcard : t.card=∑ v ∈ Finset.range 19, rowZeroCount (M r) v := by
    change (((Finset.range (B r-1)) ×ˢ (Finset.range 19)).filter
      (fun p => rowValue (M r) p.2 p.1=0)).card = _
    rw [card_filter_product]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hL]
    rfl
  rw [physical_candidate_card,hc,Finset.card_insert_of_notMem hknot,hcard,htcard]

/-- Exact cardinality of all physical integer-zero subsets, for every r. -/
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

#check @actual_zero_subsets_card
#print axioms actual_zero_subsets_card
end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCount
