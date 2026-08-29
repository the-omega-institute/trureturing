/- GID: D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Least power depth meets both bit bounds; a 3-bit witness separates faults. -/

import D5.S3.Arith.Coding.HorizontalCompletenessDepth
import D5.S3.Arith.Coding.ResidueCodeDynamicRange
import D5.S3.Observer.ArithmeticTomography.FinitePrimeInformationBudget

/- Library-search audit trail (2026-08-25):
   * `Nat.primorial` is the product of primes at most a value, not the first `r` primes.
     `Nat.nth Nat.Prime` and the repository's `primePrefixProduct` are the exact prefix SSOT.
   * Exact Mathlib hits are `Nat.clog_le_iff_le_pow`, `Nat.clog_pow`,
     `Real.natCeil_logb_natCast`, `Real.logb_le_logb`, `Real.logb_pow`,
     `Real.logb_prod`, and `Nat.pow_le_pow_iff_right`; `Nat.log` is the floor analogue.
   * `HorizontalCompletenessDepth` uses `[0,N]`, hence `N < P_r`; the size-`N`
     threshold here is its `horizontalDepth (N - 1)` and is proved to mean `N <= P_r`.
   * `ResidueCodeDynamicRange.prefixProduct` is generic; at `m i = nth Prime i` it is
     `primePrefixProduct`. Its distance theorem supplies the concrete CRT distance witness.
   * `FinitePrimeInformationBudget` supplies the generic positive-precision logarithmic
     bound. It is applied to the vertical prime at `N >= 2`; the zero-depth cases are new.
   * Repository searches for vertical prime depth and equal-bit fault geometry found no
     declaration. `ExactResidueCodeMinimumDistance` concerns arbitrary bounded RRNS codes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ArithmeticTomography.PrimeObservationDepthGeometry

open D5.S3.Arith.Coding.HorizontalCompletenessDepth
open D5.S3.Arith.Coding.ResidueCodeDynamicRange
open D5.S3.Observer.ArithmeticTomography.FinitePrimeInformationBudget

/-- The horizontal depth for a window with cardinality `N`, derived from the canonical
inclusive-window depth by replacing its endpoint with `N - 1`. -/
def horizontalCardinalityDepth (N : Nat) : Nat :=
  horizontalDepth (N - 1)

/-- The least precision whose single prime power has capacity at least `N`. -/
def verticalDepth (p N : Nat) : Nat :=
  Nat.clog p N

/-- Exact real-valued bit cost of the first `r` prime channels. -/
def horizontalBitCost (r : Nat) : Real :=
  ∑ i ∈ Finset.range r, Real.logb 2 (Nat.nth Nat.Prime i)

/-- Exact real-valued bit cost of a depth-`k_p(N)` single-prime channel. -/
def verticalBitCost (p N : Nat) : Real :=
  verticalDepth p N * Real.logb 2 p

private theorem primePrefixProduct_pos (r : Nat) :
    0 < primePrefixProduct r := by
  rw [primePrefixProduct]
  apply Finset.prod_pos
  intro i hi
  exact (Nat.prime_nth_prime i).pos

/-- The cardinality-indexed horizontal depth is exactly the least `r` with `N <= P_r`. -/
theorem horizontal_cardinality_depth_isLeast (N : Nat) :
    IsLeast {r : Nat | N ≤ primePrefixProduct r} (horizontalCardinalityDepth N) := by
  have threshold_iff (r : Nat) :
      N ≤ primePrefixProduct r ↔ N - 1 < primePrefixProduct r := by
    have hpositive := primePrefixProduct_pos r
    omega
  constructor
  · apply (threshold_iff _).2
    simpa only [horizontalCardinalityDepth, horizontalDepth] using
      Nat.find_spec (exists_primePrefixProduct_gt (N - 1))
  · intro r hr
    rw [horizontalCardinalityDepth, horizontalDepth]
    apply Nat.find_min'
    exact (threshold_iff r).1 hr
#print axioms horizontal_cardinality_depth_isLeast

/-- For every base greater than one, `verticalDepth p N` is the least exponent whose
power has capacity at least `N`. -/
theorem vertical_depth_isLeast (p N : Nat) (hp : 1 < p) :
    IsLeast {k : Nat | N ≤ p ^ k} (verticalDepth p N) := by
  constructor
  · exact (Nat.clog_le_iff_le_pow hp).1 le_rfl
  · intro k hk
    exact (Nat.clog_le_iff_le_pow hp).2 hk
#print axioms vertical_depth_isLeast

/-- The least-power definition equals the natural ceiling of the real base-`p` logarithm. -/
theorem vertical_depth_eq_natCeil_logb (p N : Nat) :
    verticalDepth p N = ⌈Real.logb p N⌉₊ := by
  exact (Real.natCeil_logb_natCast p N).symm
#print axioms vertical_depth_eq_natCeil_logb

private theorem horizontal_bit_cost_eq_log_prefix (r : Nat) :
    horizontalBitCost r = Real.logb 2 (primePrefixProduct r) := by
  rw [horizontalBitCost, primePrefixProduct, Nat.cast_prod]
  symm
  apply Real.logb_prod
  intro i hi
  exact_mod_cast (Nat.prime_nth_prime i).ne_zero

/-- The selected horizontal and vertical schemes both meet the base-two capacity bound.
The first equality also identifies the horizontal sum with the logarithm of its product. -/
theorem horizontal_vertical_bit_cost_lower_bounds (p : Nat.Primes) (N : Nat) :
    horizontalBitCost (horizontalCardinalityDepth N) =
        Real.logb 2 (primePrefixProduct (horizontalCardinalityDepth N)) ∧
      Real.logb 2 N ≤ horizontalBitCost (horizontalCardinalityDepth N) ∧
      Real.logb 2 N ≤ verticalBitCost p N := by
  have hcost := horizontal_bit_cost_eq_log_prefix (horizontalCardinalityDepth N)
  refine ⟨hcost, ?_, ?_⟩
  · rw [hcost]
    by_cases hzero : N = 0
    · subst N
      simp only [Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by norm_num) (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (primePrefixProduct_pos (horizontalCardinalityDepth 0))))
    · apply (Real.logb_le_logb (b := 2) (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hzero)
          (by exact_mod_cast primePrefixProduct_pos (horizontalCardinalityDepth N))).2
      exact_mod_cast (horizontal_cardinality_depth_isLeast N).1
  · by_cases hsmall : N ≤ 1
    · have hcases : N = 0 ∨ N = 1 := by omega
      rcases hcases with (rfl | rfl) <;> simp [verticalBitCost, verticalDepth]
    · have hN : 0 < N := by omega
      have hNtwo : 1 < N := by omega
      have hk : 0 < verticalDepth p N := Nat.clog_pos p.2.one_lt hNtwo
      let precision : Nat.Primes → ℕ+ := fun _ => ⟨verticalDepth p N, hk⟩
      have hcapacity : N ≤ p.1 ^ verticalDepth p N :=
        (vertical_depth_isLeast p N p.2.one_lt).1
      have hbudget := finite_prime_information_budget ({p} : Finset Nat.Primes)
        precision N hN (by simpa [precision] using hcapacity)
      simpa [precision, verticalBitCost] using hbudget
#print axioms horizontal_vertical_bit_cost_lower_bounds

/-- At base one and `N = 2`, both the least-power and logarithmic conclusions fail. -/
theorem base_gt_one_is_necessary :
    (¬IsLeast {k : Nat | 2 ≤ 1 ^ k} (verticalDepth 1 2)) ∧
      ¬Real.logb 2 2 ≤ verticalBitCost 1 2 := by
  constructor
  · intro hleast
    have hmember := hleast.1
    norm_num [verticalDepth] at hmember
  · norm_num [verticalBitCost, verticalDepth, Real.logb]
#print axioms base_gt_one_is_necessary

/-- Rounded storage cost for a finite family of residue channels. -/
def storedChannelBitCost (m : Nat → Nat) (n : Nat) : Nat :=
  ∑ i : Fin n, Nat.clog 2 (m i)

/-- Two messages agree outside the coordinate that is unavailable. -/
def AgreeOutside (m : Nat → Nat) (n : Nat) (unavailable : Fin n) (x y : Nat) : Prop :=
  ∀ i : Fin n, i ≠ unavailable → residueWord m n x i = residueWord m n y i

/-- One three-bit residue channel. -/
def verticalExampleModuli (_ : Nat) : Nat :=
  8

/-- Two independent prime residue channels using moduli two and three. -/
def horizontalExampleModuli (i : Nat) : Nat :=
  if i = 0 then 2 else 3

/-- A modulus-eight channel and the modulus-two/modulus-three CRT pair both occupy three
rounded bits. Losing the only vertical coordinate hides zero from two, while losing the
modulus-two CRT coordinate does not; the CRT pair also has distance at least one on `X_6`. -/
theorem same_bit_cost_different_fault_geometry :
    storedChannelBitCost verticalExampleModuli 1 =
        storedChannelBitCost horizontalExampleModuli 2 ∧
      MinDistanceAtLeast horizontalExampleModuli 2 6 1 ∧
      AgreeOutside verticalExampleModuli 1 (0 : Fin 1) 0 2 ∧
      ¬AgreeOutside horizontalExampleModuli 2 (0 : Fin 2) 0 2 := by
  have hdistance : MinDistanceAtLeast horizontalExampleModuli 2 6 1 := by
    apply (maximum_dynamic_range_iff_min_distance horizontalExampleModuli 2 1 6
      (by omega) (by omega) (by
        intro i j hij hj
        simp only [horizontalExampleModuli]
        split <;> split <;> omega) (by
        intro i hi
        simp only [horizontalExampleModuli]
        split <;> omega) (by
        intro i j hi hj hij
        have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
        rcases hcases with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact (Nat.coprime_primes (by decide) (by decide)).2 (by decide)
        · exact (Nat.coprime_primes (by decide) (by decide)).2 (by decide))).2
    norm_num [prefixProduct, horizontalExampleModuli, Fin.prod_univ_succ]
  refine ⟨?_, hdistance, ?_, ?_⟩
  · norm_num [storedChannelBitCost, verticalExampleModuli, horizontalExampleModuli,
      Fin.sum_univ_succ]
  · intro i hi
    exact (hi (Fin.eq_zero i)).elim
  · intro hagree
    have h := hagree (1 : Fin 2) (by decide)
    norm_num [residueWord, horizontalExampleModuli] at h
#print axioms same_bit_cost_different_fault_geometry

example : verticalDepth 2 0 = 0 := by decide
example : verticalDepth 2 1 = 0 := by decide
example : verticalDepth 2 2 = 1 := by decide
example : verticalDepth 2 (2 ^ 3) = 3 := by decide

example : horizontalCardinalityDepth 1 = 0 := by
  apply (horizontal_cardinality_depth_isLeast 1).unique
  constructor
  · norm_num [primePrefixProduct]
  · intro r hr
    omega

example : horizontalCardinalityDepth 2 = 1 := by
  apply (horizontal_cardinality_depth_isLeast 2).unique
  constructor
  · norm_num [primePrefixProduct]
  · intro r hr
    by_contra hnot
    have : r = 0 := by omega
    subst r
    norm_num [primePrefixProduct] at hr

example : horizontalCardinalityDepth 6 = 2 := by
  apply (horizontal_cardinality_depth_isLeast 6).unique
  constructor
  · norm_num [primePrefixProduct, Finset.prod_range_succ,
      Nat.nth_prime_one_eq_three]
  · intro r hr
    by_contra hnot
    have hcases : r = 0 ∨ r = 1 := by omega
    rcases hcases with (rfl | rfl) <;> norm_num [primePrefixProduct] at hr

end D5.S3.Observer.ArithmeticTomography.PrimeObservationDepthGeometry
