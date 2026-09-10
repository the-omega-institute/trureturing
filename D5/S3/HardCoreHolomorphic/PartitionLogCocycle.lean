/- GID: D5/S3/HardCoreHolomorphic/PartitionLogCocycle
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/PartitionLogCocycle
   mirror-E: none(waiver:exact-actual-partition-logarithmic-square)
   anchors: []
   digest: Actual vertex-deletion increments have a branch-correct additive square identity. -/

import D5.S3.HardCoreHolomorphic.FiniteGridZeroFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.PartitionLogCocycle

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood
open D5.S3.HardCoreHolomorphic.FiniteGridZeroFree

/-- Actual insertion factor, inverse to the marked vacancy when the partitions
are nonzero. A missing vertex gives one on the established activity tube. -/
def increment (V : Finset Point) (v : Point) (z : ℂ) : ℂ :=
  gridPartition V z / gridPartition (V.erase v) z

/-- The actual finite independent-configuration sum is an entire function. -/
theorem grid_partition_differentiable (V : Finset Point) :
    Differentiable ℂ (fun z : ℂ => gridPartition V z) := by
  unfold gridPartition partition
  fun_prop

/-- The empty configuration is the only nonzero contribution at activity zero. -/
theorem grid_partition_zero (V : Finset Point) : gridPartition V (0 : ℂ) = 1 := by
  have hempty : (∅ : Finset Point) ∈ configurations squareGrid V := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset V), ?_⟩
    intro x hx
    exact False.elim (Finset.notMem_empty x hx)
  unfold gridPartition partition
  calc
    _ = ∑ S ∈ configurations squareGrid V, if S = ∅ then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases he : S = ∅
      · simp [he]
      · rw [if_neg he]
        obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
        exact Finset.prod_eq_zero hv rfl
    _ = 1 := by simp [hempty]

/-- The origin half-plane estimate transports to every marked vertex, including
an absent vertex. No direct bound on the argument of the whole partition is used. -/
theorem increment_halfplane (V : Finset Point) (v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) : (1 / 2 : ℝ) ≤ (increment V v z).re := by
  by_cases hv : v ∈ V
  · have h0 : (0, 0) ∈ V.image (shiftTo v) := by
      refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
      ext <;> simp [shiftTo]
    have he := congrArg (fun x : ℂ => x⁻¹) (vacancy_shift V v z)
    simp only [gridVacancy, inv_div] at he
    have h := finite_grid_origin_increment (V.image (shiftTo v)) h0 z hz
    rw [he] at h
    exact h
  · simp only [increment, Finset.erase_eq_of_notMem hv,
      div_self (finite_grid_zero_free V z hz), Complex.one_re]
    norm_num

/-- Each actual insertion factor is nonzero on the common tube. -/
theorem increment_ne_zero (V : Finset Point) (v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) : increment V v z ≠ 0 := by
  intro he
  have h := increment_halfplane V v z hz
  norm_num [he] at h

/-- Positivity of the real part bounds the imaginary part of the principal log.
This bound is what makes two successive log increments branch-compatible. -/
theorem increment_log_im (V : Finset Point) (v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    |(Complex.log (increment V v z)).im| < Real.pi / 2 := by
  rw [Complex.log_im, Complex.abs_arg_lt_pi_div_two_iff]
  exact Or.inl (lt_of_lt_of_le (by norm_num) (increment_halfplane V v z hz))

private theorem log_mul_right_halfplane (x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  exact Complex.log_mul hx0 hy0 ⟨by linarith, by linarith⟩

/-- Two ordered deletion steps have the same actual product after swapping
vertices. All denominator nonvanishing facts are supplied by the concrete grid theorem. -/
theorem increment_square (V : Finset Point) (u v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    increment V u z * increment (V.erase u) v z =
      increment V v z * increment (V.erase v) u z := by
  have he : (V.erase u).erase v = (V.erase v).erase u := by
    ext p
    simp only [Finset.mem_erase]
    tauto
  unfold increment
  rw [he]
  field_simp [finite_grid_zero_free (V.erase u) z hz,
    finite_grid_zero_free (V.erase v) z hz,
    finite_grid_zero_free ((V.erase v).erase u) z hz] <;> ring

/-- Exact additive flatness on every deletion square. The equality is in ℂ,
not merely modulo 2*pi*i; the individual right-half-plane bounds prove the branch choice. -/
theorem increment_log_square (V : Finset Point) (u v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    Complex.log (increment V u z) + Complex.log (increment (V.erase u) v z) =
      Complex.log (increment V v z) + Complex.log (increment (V.erase v) u z) := by
  have hp (W : Finset Point) (w : Point) : 0 < (increment W w z).re :=
    lt_of_lt_of_le (by norm_num) (increment_halfplane W w z hz)
  rw [← log_mul_right_halfplane _ _ (hp V u) (hp (V.erase u) v),
    ← log_mul_right_halfplane _ _ (hp V v) (hp (V.erase v) u),
    increment_square V u v z hz]

/-- The logarithmic derivative of the actual partition. It is finite
at z=0 and uses no logarithm branch in its definition. -/
def response (V : Finset Point) (z : ℂ) : ℂ :=
  deriv (fun w : ℂ => gridPartition V w) z / gridPartition V z

/-- Differentiate the actual local principal logarithm. Its derivative is the
exact difference of two actual logarithmic derivatives, enabling telescoping. -/
theorem increment_log_hasDerivAt (V : Finset Point) (v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    HasDerivAt (fun w : ℂ => Complex.log (increment V v w))
      (response V z - response (V.erase v) z) z := by
  have hf := (grid_partition_differentiable V z).hasDerivAt
  have hg := (grid_partition_differentiable (V.erase v) z).hasDerivAt
  have hn := finite_grid_zero_free V z hz
  have hn' := finite_grid_zero_free (V.erase v) z hz
  have hs : increment V v z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl
      (lt_of_lt_of_le (by norm_num) (increment_halfplane V v z hz)))
  have h := (hf.div hg hn').clog hs
  convert h using 1
  · rfl
  · dsimp [response, increment]
    field_simp [hn, hn'] <;> ring

/-- Direct configuration comparison gives a volume upper bound on the entire
complex plane. This does not use the recursion or the zero-free theorem. -/
theorem grid_partition_norm_upper (V : Finset Point) (z : ℂ) :
    ‖gridPartition V z‖ ≤ (1 + ‖z‖) ^ V.card := by
  unfold gridPartition partition
  calc
    _ ≤ ∑ S ∈ configurations squareGrid V, ‖∏ _v ∈ S, z‖ := norm_sum_le _ _
    _ = ∑ S ∈ configurations squareGrid V, ∏ _v ∈ S, ‖z‖ := by simp only [norm_prod]
    _ ≤ ∑ S ∈ V.powerset, ∏ _v ∈ S, ‖z‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro S _ _
        exact Finset.prod_nonneg (fun _ _ => norm_nonneg z)
    _ = ∏ _v ∈ V, (1 + ‖z‖) := (Finset.prod_one_add _).symm
    _ = _ := by simp

#print axioms grid_partition_norm_upper
#print axioms grid_partition_differentiable
#print axioms grid_partition_zero
#print axioms increment_halfplane
#print axioms increment_ne_zero
#print axioms increment_log_im
#print axioms increment_square
#print axioms increment_log_square
#print axioms increment_log_hasDerivAt

end D5.S3.HardCoreHolomorphic.PartitionLogCocycle
