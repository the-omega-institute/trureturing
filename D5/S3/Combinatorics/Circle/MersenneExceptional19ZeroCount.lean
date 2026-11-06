/-!
Exceptional 19: focused source repair, UNCOMPILED.

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
  simp only [subsetOfMask, dif_pos hm]
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
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.div_mul_cancel hd, sumAtMask_mask r A]
    exact hz
  · intro A hA D hD he
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
    · rw [mask_subsetOfMask r _ hm', Nat.mul_div_cancel _ (q_positive r)]

/- Correct five signed floors. EACH Nat quotient is cast BEFORE subtraction. -/
private def carryCorrection (r m : ℕ) : ℤ :=
  ((2 * m / B r : ℕ) : ℤ) - ((8 * m / B r ^ 2 : ℕ) : ℤ) +
  ((4 * m / B r ^ 2 : ℕ) : ℤ) - ((m / B r ^ 2 : ℕ) : ℤ) +
  ((4 * m / B r ^ 3 : ℕ) : ℤ)

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
