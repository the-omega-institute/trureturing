import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis14

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality
open scoped BigOperators

noncomputable section

theorem native_frequency_one_le (D : LatticeData) (index : Index D) :
    1 ≤ frequencyWeight D index := by
  dsimp [frequencyWeight]
  omega

theorem native_index_auxiliary_bounds (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (index : Index D) :
    -(frequencyWeight D index : ℤ) ≤ auxiliaryWeight D xAxis yAxis index ∧
      auxiliaryWeight D xAxis yAxis index ≤ (frequencyWeight D index : ℤ) := by
  classical
  have frequencyBound : (1 : ℤ) ≤ (frequencyWeight D index : ℤ) := by
    exact_mod_cast native_frequency_one_le D index
  unfold auxiliaryWeight axisAuxDegree
  split_ifs <;> constructor <;> omega

theorem native_index_exponent_auxiliary_bounds (D : LatticeData)
    (xAxis yAxis : Fin D.rank) (powers : Index D →₀ ℕ) (index : Index D) :
    -((powers index * frequencyWeight D index : ℕ) : ℤ) ≤
        powers index • auxiliaryWeight D xAxis yAxis index ∧
      powers index • auxiliaryWeight D xAxis yAxis index ≤
        ((powers index * frequencyWeight D index : ℕ) : ℤ) := by
  obtain ⟨lower, upper⟩ := native_index_auxiliary_bounds D xAxis yAxis index
  have exponentNonnegative : 0 ≤ (powers index : ℤ) := Int.natCast_nonneg _
  constructor
  · simpa only [nsmul_eq_mul, Nat.cast_mul, mul_neg] using
      mul_le_mul_of_nonneg_left lower exponentNonnegative
  · simpa only [nsmul_eq_mul, Nat.cast_mul] using
      mul_le_mul_of_nonneg_left upper exponentNonnegative

theorem native_axisExponentCount_le_frequency (D : LatticeData) (axis : Fin D.rank)
    (powers : Index D →₀ ℕ) :
    axisExponentCount D axis powers ≤ Finsupp.weight (frequencyWeight D) powers := by
  classical
  unfold axisExponentCount
  rw [Finsupp.weight_apply]
  unfold Finsupp.sum
  apply Finset.sum_le_sum
  intro index indexMember
  have exponentCost : powers index ≤ powers index * frequencyWeight D index := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (native_frequency_one_le D index)
        (Nat.zero_le (powers index))
  by_cases onAxis : index.1 = axis
  · simpa [if_pos onAxis, nsmul_eq_mul] using exponentCost
  · simp only [if_neg onAxis]
    exact Nat.zero_le _

theorem native_signed_axis_count_bounds (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (distinct : xAxis ≠ yAxis) (powers : Index D →₀ ℕ) :
    -(Finsupp.weight (frequencyWeight D) powers : ℤ) ≤
        Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers ∧
      Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers ≤
        (Finsupp.weight (frequencyWeight D) powers : ℤ) := by
  have xBound : (axisExponentCount D xAxis powers : ℤ) ≤
      (Finsupp.weight (frequencyWeight D) powers : ℤ) := by
    exact_mod_cast native_axisExponentCount_le_frequency D xAxis powers
  have yBound : (axisExponentCount D yAxis powers : ℤ) ≤
      (Finsupp.weight (frequencyWeight D) powers : ℤ) := by
    exact_mod_cast native_axisExponentCount_le_frequency D yAxis powers
  have xNonnegative : 0 ≤ (axisExponentCount D xAxis powers : ℤ) := Int.natCast_nonneg _
  have yNonnegative : 0 ≤ (axisExponentCount D yAxis powers : ℤ) := Int.natCast_nonneg _
  simp only [signed_weight_axis_counts D xAxis yAxis distinct powers]
  constructor <;> omega

theorem native_matter_auxiliary_bounds (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) :
    -(Finsupp.weight (frequencyWeight D) powers : ℤ) ≤
        Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers ∧
      Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers ≤
        (Finsupp.weight (frequencyWeight D) powers : ℤ) := by
  classical
  by_cases distinct : xAxis ≠ yAxis
  · exact native_signed_axis_count_bounds D xAxis yAxis distinct powers
  · have lower := Finset.sum_le_sum (s := powers.support) (fun index _ =>
      (native_index_exponent_auxiliary_bounds D xAxis yAxis powers index).1)
    have upper := Finset.sum_le_sum (s := powers.support) (fun index _ =>
      (native_index_exponent_auxiliary_bounds D xAxis yAxis powers index).2)
    constructor
    · simpa [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum, nsmul_eq_mul,
        Nat.cast_mul, Finset.sum_neg_distrib] using lower
    · simpa [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum, nsmul_eq_mul,
        Nat.cast_mul] using upper

theorem native_polarizedLevel_nonnegative (subset : Finset ℕ) :
    0 ≤ polarizedLevel subset := by
  exact le_trans (Int.natCast_nonneg _) (ghost_excitation_bound subset)

theorem nativeLevel_nonnegative (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) : 0 ≤ nativeLevel D powers subset := by
  exact add_nonneg (Int.natCast_nonneg _) (native_polarizedLevel_nonnegative subset)

theorem nativeDegree_bounds (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) :
    -nativeLevel D powers subset ≤ nativeDegree D xAxis yAxis powers subset ∧
      nativeDegree D xAxis yAxis powers subset ≤ nativeLevel D powers subset + 1 := by
  obtain ⟨matterLower, matterUpper⟩ := native_matter_auxiliary_bounds D xAxis yAxis powers
  obtain ⟨ghostLower, ghostUpper⟩ := ghost_auxiliary_bounds subset
  unfold nativeLevel nativeDegree
  constructor <;> omega

theorem nativeDegree_upper_epsilon (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) :
    nativeDegree D xAxis yAxis powers subset ≤ nativeLevel D powers subset + epsilonCount subset := by
  have matterUpper := (native_matter_auxiliary_bounds D xAxis yAxis powers).2
  have excitationBound := ghost_excitation_bound subset
  have etaNonnegative : 0 ≤ (etaCount subset : ℤ) := Int.natCast_nonneg _
  unfold nativeLevel nativeDegree
  omega

theorem nativeDegree_relative_bounds (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) (relative : 3 ∉ subset) :
    -nativeLevel D powers subset ≤ nativeDegree D xAxis yAxis powers subset ∧
      nativeDegree D xAxis yAxis powers subset ≤ nativeLevel D powers subset := by
  have epsilonZero : epsilonCount subset = 0 := by simp [epsilonCount, relative]
  refine ⟨(nativeDegree_bounds D xAxis yAxis powers subset).1, ?_⟩
  simpa only [epsilonZero, add_zero] using
    nativeDegree_upper_epsilon D xAxis yAxis powers subset

theorem nativeLevel_negative_impossible (D : LatticeData) (powers : Index D →₀ ℕ)
    (subset : Finset ℕ) (negative : nativeLevel D powers subset < 0) : False := by
  have nonnegative : 0 ≤ nativeLevel D powers subset :=
    add_nonneg (Int.natCast_nonneg _) (native_polarizedLevel_nonnegative subset)
  omega

theorem nativeLevel_ne_of_negative (D : LatticeData) (powers : Index D →₀ ℕ)
    (subset : Finset ℕ) (level : ℤ) (negative : level < 0) :
    nativeLevel D powers subset ≠ level := by
  intro atLevel
  apply nativeLevel_negative_impossible D powers subset
  simpa only [atLevel] using negative

theorem nativeDegree_bounds_at_level (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) (level : ℤ)
    (atLevel : nativeLevel D powers subset = level) :
    -level ≤ nativeDegree D xAxis yAxis powers subset ∧
      nativeDegree D xAxis yAxis powers subset ≤ level + 1 := by
  simpa only [atLevel] using nativeDegree_bounds D xAxis yAxis powers subset

theorem nativeDegree_relative_bounds_at_level (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) (level : ℤ)
    (atLevel : nativeLevel D powers subset = level) (relative : 3 ∉ subset) :
    -level ≤ nativeDegree D xAxis yAxis powers subset ∧
      nativeDegree D xAxis yAxis powers subset ≤ level := by
  simpa only [atLevel] using nativeDegree_relative_bounds D xAxis yAxis powers subset relative

theorem nativeDegree_level_zero_eq_epsilon (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ)
    (levelZero : nativeLevel D powers subset = 0) :
    nativeDegree D xAxis yAxis powers subset = epsilonCount subset := by
  have matterNonnegative : 0 ≤ (Finsupp.weight (frequencyWeight D) powers : ℤ) :=
    Int.natCast_nonneg _
  have ghostNonnegative := native_polarizedLevel_nonnegative subset
  have excitationBound := ghost_excitation_bound subset
  have etaNonnegative : 0 ≤ (etaCount subset : ℤ) := Int.natCast_nonneg _
  have thetaNonnegative : 0 ≤ (thetaCount subset : ℤ) := Int.natCast_nonneg _
  obtain ⟨matterLower, matterUpper⟩ := native_matter_auxiliary_bounds D xAxis yAxis powers
  unfold nativeLevel at levelZero
  unfold nativeDegree
  omega

theorem nativeDegree_level_zero (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ)
    (levelZero : nativeLevel D powers subset = 0) :
    nativeDegree D xAxis yAxis powers subset = 0 ∨
      nativeDegree D xAxis yAxis powers subset = 1 := by
  simp only [nativeDegree_level_zero_eq_epsilon D xAxis yAxis powers subset levelZero]
  unfold epsilonCount
  split_ifs <;> omega

theorem nativeDegree_level_zero_relative (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ)
    (levelZero : nativeLevel D powers subset = 0) (relative : 3 ∉ subset) :
    nativeDegree D xAxis yAxis powers subset = 0 := by
  rw [nativeDegree_level_zero_eq_epsilon D xAxis yAxis powers subset levelZero]
  simp [epsilonCount, relative]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
