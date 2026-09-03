/- GID: D5/S3/Analytic/AllOrder/GoldenWeightCoordinates
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   digest: Beatty coordinates and injective weights for the golden Euler beta ledger. -/

import D5.S3.Analytic.GoldenEulerBetaZeckendorf
import Mathlib.Tactic

/-! SEARCH RECEIPT (2026-09-03, pinned repository and pinned mathlib):
Repository searches for `goldenBeattyQ`, `goldenBetaCoord`, `goldenWeight`,
`golden_beta_lattice_census`, and `GoldenWeightCoordinates` found no existing
declaration.  The frozen theorem
`GoldenEulerBetaZeckendorf.golden_euler_beta_zeckendorf` supplies exactly the
all-mode Beatty identity used below, so this module imports and specializes it
rather than reconstructing its Zeckendorf proof.  The supporting frozen
modules `GoldenEulerBeta` and `EulerGerm.GoldenLocalFactor` were also checked;
the latter's `o5_beta_zero` is not needed because the Beatty identity already
covers `v = 0`.

Pinned mathlib searches for floor bounds, natural conversion of nonnegative
integers, golden-ratio identities, and irrational linear combinations located
`Int.floor_nonneg`, `Int.floor_lt`, `Int.lt_floor_add_one`,
`Int.toNat_of_nonneg`, `Real.goldenRatio_sq`,
`Real.goldenRatio_irrational`, and `Irrational.ne_rational`.  These are used
directly below.  No third-party dependency is required. -/

/-! STOPPING JUSTIFICATION:
This first all-order module closes only the coordinate layer.  It exposes the
natural floor quotient, proves both bounds needed to remove truncated
subtractions, identifies the resulting weight with the frozen beta account,
and proves global injectivity by irrationality.  The coordinate reconstruction
and finite-range membership lemmas are interfaces for the next module, not a
claim that its census is already proved.  Strict growth, shifted lower bounds,
two-sided growth, divergence, and exact finite sublevel equality remain outside
this theorem and belong to `GoldenWeightCensus`. -/

namespace D5.S3.Analytic.AllOrder.GoldenWeightCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.GoldenEulerBetaZeckendorf

noncomputable section

/-- The Beatty quotient attached to the golden Euler mode `v`. -/
noncomputable def goldenBeattyQ (v : ℕ) : ℕ :=
  Int.toNat ⌊(((v : ℝ) + 1) / Real.goldenRatio)⌋

/-- The two nonnegative lattice coordinates attached to mode `v`. -/
def goldenBetaCoord (v : ℕ) : ℕ × ℕ :=
  (2 * goldenBeattyQ v - v, v - goldenBeattyQ v)

/-- The golden weight of a pair of lattice coordinates. -/
noncomputable def goldenWeight (m : ℕ × ℕ) : ℝ :=
  (m.1 : ℝ) * Real.goldenRatio ^ 2 +
    (m.2 : ℝ) * Real.goldenRatio ^ 3

private theorem beatty_argument_nonneg (v : ℕ) :
    0 ≤ ((v : ℝ) + 1) / Real.goldenRatio := by
  positivity

private theorem beatty_floor_nonneg (v : ℕ) :
    0 ≤ ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ := by
  exact Int.floor_nonneg.mpr (beatty_argument_nonneg v)

/-- The natural Beatty quotient casts back to the defining integer floor. -/
theorem goldenBeattyQ_intCast (v : ℕ) :
    (goldenBeattyQ v : ℤ) =
      ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ := by
  rw [goldenBeattyQ, Int.toNat_of_nonneg (beatty_floor_nonneg v)]

/-- Real coercion of the Beatty quotient is the defining floor. -/
theorem goldenBeattyQ_realCast (v : ℕ) :
    (goldenBeattyQ v : ℝ) =
      (⌊((v : ℝ) + 1) / Real.goldenRatio⌋ : ℝ) := by
  exact_mod_cast goldenBeattyQ_intCast v

private theorem beatty_argument_lt_succ (v : ℕ) :
    ((v : ℝ) + 1) / Real.goldenRatio < (v : ℝ) + 1 := by
  rw [div_lt_iff₀ Real.goldenRatio_pos]
  have hv : 0 ≤ (v : ℝ) := by positivity
  nlinarith [Real.one_lt_goldenRatio]

private theorem beatty_floor_lt_succ (v : ℕ) :
    ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ < (v : ℤ) + 1 := by
  apply Int.floor_lt.mpr
  push_cast
  exact beatty_argument_lt_succ v

/-- The Beatty quotient never exceeds its mode. -/
theorem goldenBeattyQ_le (v : ℕ) : goldenBeattyQ v ≤ v := by
  have hfloor :
      ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ ≤ (v : ℤ) := by
    have hlt := beatty_floor_lt_succ v
    omega
  rw [← goldenBeattyQ_intCast v] at hfloor
  exact_mod_cast hfloor

private theorem two_succ_goldenBeattyQ_le_of_not_le (v : ℕ)
    (h : ¬v ≤ 2 * goldenBeattyQ v) :
    2 * (goldenBeattyQ v + 1) ≤ v + 1 := by
  omega

private theorem goldenBeattyQ_succ_mul_phi_lt_succ (v : ℕ)
    (h : ¬v ≤ 2 * goldenBeattyQ v) :
    ((goldenBeattyQ v : ℝ) + 1) * Real.goldenRatio <
      (v : ℝ) + 1 := by
  have htwoNat := two_succ_goldenBeattyQ_le_of_not_le v h
  have htwoReal :
      2 * ((goldenBeattyQ v : ℝ) + 1) ≤ (v : ℝ) + 1 := by
    exact_mod_cast htwoNat
  have hpositive : 0 < (goldenBeattyQ v : ℝ) + 1 := by positivity
  have hphi :
      ((goldenBeattyQ v : ℝ) + 1) * Real.goldenRatio <
        ((goldenBeattyQ v : ℝ) + 1) * 2 :=
    mul_lt_mul_of_pos_left Real.goldenRatio_lt_two hpositive
  nlinarith

private theorem goldenBeattyQ_succ_lt_argument (v : ℕ)
    (h : ¬v ≤ 2 * goldenBeattyQ v) :
    (goldenBeattyQ v : ℝ) + 1 <
      ((v : ℝ) + 1) / Real.goldenRatio := by
  rw [lt_div_iff₀ Real.goldenRatio_pos]
  exact goldenBeattyQ_succ_mul_phi_lt_succ v h

private theorem beatty_argument_lt_goldenBeattyQ_succ (v : ℕ) :
    ((v : ℝ) + 1) / Real.goldenRatio <
      (goldenBeattyQ v : ℝ) + 1 := by
  have h := Int.lt_floor_add_one
    (((v : ℝ) + 1) / Real.goldenRatio)
  simpa only [goldenBeattyQ_realCast] using h

/-- Twice the Beatty quotient dominates its mode. -/
theorem le_two_goldenBeattyQ (v : ℕ) :
    v ≤ 2 * goldenBeattyQ v := by
  by_contra h
  have hlower := goldenBeattyQ_succ_lt_argument v h
  have hupper := beatty_argument_lt_goldenBeattyQ_succ v
  linarith

/-- The two inequalities which make the coordinate subtractions exact. -/
theorem goldenBeattyQ_bounds (v : ℕ) :
    goldenBeattyQ v ≤ v ∧ v ≤ 2 * goldenBeattyQ v :=
  ⟨goldenBeattyQ_le v, le_two_goldenBeattyQ v⟩

/-- Positive modes have a positive Beatty quotient. -/
theorem goldenBeattyQ_pos {v : ℕ} (hv : 0 < v) :
    0 < goldenBeattyQ v := by
  have htwo := le_two_goldenBeattyQ v
  omega

/-- The first coordinate unfolds to the bounded natural subtraction. -/
@[simp]
theorem goldenBetaCoord_fst (v : ℕ) :
    (goldenBetaCoord v).1 = 2 * goldenBeattyQ v - v := rfl

/-- The second coordinate unfolds to the bounded natural subtraction. -/
@[simp]
theorem goldenBetaCoord_snd (v : ℕ) :
    (goldenBetaCoord v).2 = v - goldenBeattyQ v := rfl

/-- Adding the two coordinates recovers the Beatty quotient. -/
theorem goldenBetaCoord_sum (v : ℕ) :
    (goldenBetaCoord v).1 + (goldenBetaCoord v).2 =
      goldenBeattyQ v := by
  have hq := goldenBeattyQ_le v
  have hv := le_two_goldenBeattyQ v
  simp only [goldenBetaCoord_fst, goldenBetaCoord_snd]
  omega

/-- Giving the second coordinate weight two recovers the original mode. -/
theorem goldenBetaCoord_weighted_sum (v : ℕ) :
    (goldenBetaCoord v).1 + 2 * (goldenBetaCoord v).2 = v := by
  have hq := goldenBeattyQ_le v
  have hv := le_two_goldenBeattyQ v
  simp only [goldenBetaCoord_fst, goldenBetaCoord_snd]
  omega

/-- The first coordinate is bounded by the Beatty quotient. -/
theorem goldenBetaCoord_fst_le_q (v : ℕ) :
    (goldenBetaCoord v).1 ≤ goldenBeattyQ v := by
  have hq := goldenBeattyQ_le v
  simp only [goldenBetaCoord_fst]
  omega

/-- The second coordinate is bounded by the mode. -/
theorem goldenBetaCoord_snd_le_v (v : ℕ) :
    (goldenBetaCoord v).2 ≤ v := by
  simp only [goldenBetaCoord_snd]
  omega

/-- Both coordinates are bounded by the mode that they encode. -/
theorem goldenBetaCoord_component_bounds (v : ℕ) :
    (goldenBetaCoord v).1 ≤ v ∧ (goldenBetaCoord v).2 ≤ v := by
  exact ⟨(goldenBetaCoord_fst_le_q v).trans (goldenBeattyQ_le v),
    goldenBetaCoord_snd_le_v v⟩

/-- A mode below `k` has both coordinates below `k`. -/
theorem goldenBetaCoord_components_lt {v k : ℕ} (hvk : v < k) :
    (goldenBetaCoord v).1 < k ∧ (goldenBetaCoord v).2 < k := by
  obtain ⟨hfst, hsnd⟩ := goldenBetaCoord_component_bounds v
  exact ⟨hfst.trans_lt hvk, hsnd.trans_lt hvk⟩

/-- A mode bound also bounds its Beatty quotient. -/
theorem goldenBeattyQ_lt_of_lt {v k : ℕ} (hvk : v < k) :
    goldenBeattyQ v < k :=
  (goldenBeattyQ_le v).trans_lt hvk

/-- The Beatty quotient of a bounded mode belongs to the same finite range. -/
theorem goldenBeattyQ_mem_range {v k : ℕ} (hvk : v < k) :
    goldenBeattyQ v ∈ Finset.range k := by
  simpa only [Finset.mem_range] using goldenBeattyQ_lt_of_lt hvk

/-- The coordinate pair of a bounded mode belongs to the finite product range. -/
theorem goldenBetaCoord_mem_product_range {v k : ℕ} (hvk : v < k) :
    goldenBetaCoord v ∈ (Finset.range k).product (Finset.range k) := by
  obtain ⟨hfst, hsnd⟩ := goldenBetaCoord_components_lt hvk
  change goldenBetaCoord v ∈ (Finset.range k ×ˢ Finset.range k)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hfst, Finset.mem_range.mpr hsnd⟩

/-- The two reconstruction equations characterize the coordinate pair. -/
theorem goldenBetaCoord_eq_iff {v a b : ℕ} :
    goldenBetaCoord v = (a, b) ↔
      a + b = goldenBeattyQ v ∧ a + 2 * b = v := by
  constructor
  · intro h
    have hsum := goldenBetaCoord_sum v
    have hweighted := goldenBetaCoord_weighted_sum v
    rw [h] at hsum hweighted
    simpa only using And.intro hsum hweighted
  · rintro ⟨hsum, hweighted⟩
    have hcoordSum := goldenBetaCoord_sum v
    have hcoordWeighted := goldenBetaCoord_weighted_sum v
    apply Prod.ext
    · change (goldenBetaCoord v).1 = a
      omega
    · change (goldenBetaCoord v).2 = b
      omega

/-- The coordinate map is injective: its weighted coordinate sum is `v`. -/
theorem goldenBetaCoord_injective : Function.Injective goldenBetaCoord := by
  intro v w h
  have hsum := congrArg (fun m : ℕ × ℕ => m.1 + 2 * m.2) h
  rw [goldenBetaCoord_weighted_sum, goldenBetaCoord_weighted_sum] at hsum
  exact hsum

/-- The first coordinate is the ordinary integer difference `2q-v`. -/
theorem goldenBetaCoord_fst_realCast (v : ℕ) :
    ((goldenBetaCoord v).1 : ℝ) =
      2 * (goldenBeattyQ v : ℝ) - (v : ℝ) := by
  rw [goldenBetaCoord]
  simp only
  rw [Nat.cast_sub (le_two_goldenBeattyQ v)]
  push_cast
  rfl

/-- The second coordinate is the ordinary integer difference `v-q`. -/
theorem goldenBetaCoord_snd_realCast (v : ℕ) :
    ((goldenBetaCoord v).2 : ℝ) =
      (v : ℝ) - (goldenBeattyQ v : ℝ) := by
  rw [goldenBetaCoord]
  simp only
  rw [Nat.cast_sub (goldenBeattyQ_le v)]

/-- The real coordinate sum still recovers the Beatty quotient. -/
theorem goldenBetaCoord_sum_real (v : ℕ) :
    ((goldenBetaCoord v).1 : ℝ) + ((goldenBetaCoord v).2 : ℝ) =
      (goldenBeattyQ v : ℝ) := by
  exact_mod_cast goldenBetaCoord_sum v

/-- The real weighted coordinate sum still recovers the mode. -/
theorem goldenBetaCoord_weighted_sum_real (v : ℕ) :
    ((goldenBetaCoord v).1 : ℝ) +
        2 * ((goldenBetaCoord v).2 : ℝ) = (v : ℝ) := by
  exact_mod_cast goldenBetaCoord_weighted_sum v

private theorem goldenRatio_cube :
    Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
  calc
    Real.goldenRatio ^ 3 =
        Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
    _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
      rw [Real.goldenRatio_sq]
    _ = 2 * Real.goldenRatio + 1 := by
      nlinarith [Real.goldenRatio_sq]

/-- Every golden weight has an affine normal form over `1` and `phi`. -/
theorem goldenWeight_affine (m : ℕ × ℕ) :
    goldenWeight m =
      ((m.1 + 2 * m.2 : ℕ) : ℝ) * Real.goldenRatio +
        ((m.1 + m.2 : ℕ) : ℝ) := by
  rw [goldenWeight, Real.goldenRatio_sq, goldenRatio_cube]
  push_cast
  ring

private theorem goldenWeight_coord_affine (v : ℕ) :
    goldenWeight (goldenBetaCoord v) =
      (goldenBeattyQ v : ℝ) + (v : ℝ) * Real.goldenRatio := by
  rw [goldenWeight]
  rw [goldenBetaCoord_fst_realCast, goldenBetaCoord_snd_realCast]
  rw [Real.goldenRatio_sq, goldenRatio_cube]
  ring

private theorem frozen_beta_beatty_form (v : ℕ) :
    o5Beta v =
      (⌊((v : ℝ) + 1) / Real.goldenRatio⌋ : ℝ) +
        (v : ℝ) * Real.goldenRatio := by
  exact golden_euler_beta_zeckendorf.1 v

/-- The frozen exponent account written directly in terms of the natural
Beatty quotient. -/
theorem o5Beta_eq_goldenBeattyQ_add (v : ℕ) :
    o5Beta v =
      (goldenBeattyQ v : ℝ) + (v : ℝ) * Real.goldenRatio := by
  rw [frozen_beta_beatty_form, goldenBeattyQ_realCast]

/-- The lattice coordinates have exactly the frozen golden Euler beta weight. -/
theorem goldenWeight_goldenBetaCoord (v : ℕ) :
    goldenWeight (goldenBetaCoord v) = o5Beta v := by
  rw [goldenWeight_coord_affine, frozen_beta_beatty_form,
    goldenBeattyQ_realCast]

private theorem goldenWeight_eq_affine_eq {m n : ℕ × ℕ}
    (h : goldenWeight m = goldenWeight n) :
    ((m.1 + 2 * m.2 : ℕ) : ℝ) * Real.goldenRatio +
        ((m.1 + m.2 : ℕ) : ℝ) =
      ((n.1 + 2 * n.2 : ℕ) : ℝ) * Real.goldenRatio +
        ((n.1 + n.2 : ℕ) : ℝ) := by
  simpa only [goldenWeight_affine] using h

private theorem affine_phi_coeff_eq {m n : ℕ × ℕ}
    (h : goldenWeight m = goldenWeight n) :
    m.1 + 2 * m.2 = n.1 + 2 * n.2 := by
  let a : ℤ := (m.1 : ℤ) + 2 * (m.2 : ℤ)
  let b : ℤ := (m.1 : ℤ) + (m.2 : ℤ)
  let c : ℤ := (n.1 : ℤ) + 2 * (n.2 : ℤ)
  let d : ℤ := (n.1 : ℤ) + (n.2 : ℤ)
  have haffine := goldenWeight_eq_affine_eq h
  push_cast at haffine
  have hacReal :
      ((a - c : ℤ) : ℝ) * Real.goldenRatio +
        ((b - d : ℤ) : ℝ) = 0 := by
    dsimp [a, b, c, d]
    push_cast
    nlinarith [haffine]
  have hac : a - c = 0 := by
    by_contra hne
    have hdenom : ((a - c : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast hne
    have hratio :
        Real.goldenRatio =
          ((d - b : ℤ) : ℝ) / ((a - c : ℤ) : ℝ) := by
      rw [eq_div_iff hdenom]
      push_cast at hacReal ⊢
      linear_combination hacReal
    exact (Real.goldenRatio_irrational.ne_rational
      (d - b) (a - c)) hratio
  have hac' : a = c := sub_eq_zero.mp hac
  dsimp [a, c] at hac'
  exact_mod_cast hac'

private theorem affine_constant_coeff_eq {m n : ℕ × ℕ}
    (h : goldenWeight m = goldenWeight n)
    (hphi : m.1 + 2 * m.2 = n.1 + 2 * n.2) :
    m.1 + m.2 = n.1 + n.2 := by
  have haffine := goldenWeight_eq_affine_eq h
  rw [hphi] at haffine
  exact_mod_cast (by linarith :
    (((m.1 + m.2 : ℕ) : ℝ) = ((n.1 + n.2 : ℕ) : ℝ)))

private theorem pair_eq_of_affine_coeffs_eq {m n : ℕ × ℕ}
    (hphi : m.1 + 2 * m.2 = n.1 + 2 * n.2)
    (hone : m.1 + m.2 = n.1 + n.2) : m = n := by
  apply Prod.ext
  · omega
  · omega

/-- Golden weights distinguish all natural lattice-coordinate pairs. -/
theorem goldenWeight_injective : Function.Injective goldenWeight := by
  intro m n h
  have hphi := affine_phi_coeff_eq h
  have hone := affine_constant_coeff_eq h hphi
  exact pair_eq_of_affine_coeffs_eq hphi hone

/-- Equality of golden weights is equivalent to equality of coordinates. -/
theorem goldenWeight_eq_iff {m n : ℕ × ℕ} :
    goldenWeight m = goldenWeight n ↔ m = n := by
  constructor
  · intro h
    exact goldenWeight_injective h
  · exact congrArg goldenWeight

/-- Every golden weight is nonnegative. -/
theorem goldenWeight_nonneg (m : ℕ × ℕ) : 0 ≤ goldenWeight m := by
  rw [goldenWeight]
  positivity

/-- The origin is the only lattice pair of golden weight zero. -/
theorem goldenWeight_eq_zero_iff (m : ℕ × ℕ) :
    goldenWeight m = 0 ↔ m = (0, 0) := by
  have hzero : goldenWeight (0, 0) = 0 := by
    simp [goldenWeight]
  constructor
  · intro h
    apply goldenWeight_injective
    simpa only [hzero] using h
  · intro h
    subst h
    exact hzero

/-- A golden weight is positive exactly away from the coordinate origin. -/
theorem goldenWeight_pos_iff (m : ℕ × ℕ) :
    0 < goldenWeight m ↔ m ≠ (0, 0) := by
  constructor
  · intro hpos hzero
    subst hzero
    simp [goldenWeight] at hpos
  · intro hnonzero
    have hweightNonzero : goldenWeight m ≠ 0 := by
      intro hweight
      exact hnonzero ((goldenWeight_eq_zero_iff m).mp hweight)
    exact lt_of_le_of_ne (goldenWeight_nonneg m) hweightNonzero.symm

/-- The Beatty quotient at the vacuum mode is zero. -/
theorem goldenBeattyQ_zero : goldenBeattyQ 0 = 0 := by
  have hfloor :
      ⌊1 / Real.goldenRatio⌋ = (0 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · have hpositive : 0 < 1 / Real.goldenRatio := by positivity
      simpa only [Int.cast_zero] using hpositive.le
    · have h := (div_lt_one Real.goldenRatio_pos).mpr
        Real.one_lt_goldenRatio
      simpa only [Int.cast_zero, zero_add] using h
  simp only [goldenBeattyQ, Nat.cast_zero, zero_add, hfloor,
    Int.toNat_zero]

/-- Concrete coordinate check at the vacuum mode. -/
theorem goldenBetaCoord_zero : goldenBetaCoord 0 = (0, 0) := by
  simp [goldenBetaCoord, goldenBeattyQ_zero]

/-- Concrete weight check at the vacuum mode. -/
theorem goldenWeight_goldenBetaCoord_zero :
    goldenWeight (goldenBetaCoord 0) = 0 := by
  rw [goldenBetaCoord_zero]
  simp [goldenWeight]

/-- The coordinate vector vanishes exactly at the vacuum mode. -/
theorem goldenBetaCoord_eq_zero_iff (v : ℕ) :
    goldenBetaCoord v = (0, 0) ↔ v = 0 := by
  constructor
  · intro h
    have hsum := congrArg (fun m : ℕ × ℕ => m.1 + 2 * m.2) h
    rw [goldenBetaCoord_weighted_sum] at hsum
    simpa using hsum
  · intro h
    subst h
    exact goldenBetaCoord_zero

/-- Positive modes have positive coordinate weights. -/
theorem goldenWeight_goldenBetaCoord_pos {v : ℕ} (hv : 0 < v) :
    0 < goldenWeight (goldenBetaCoord v) := by
  rw [goldenWeight_pos_iff]
  intro hzero
  have hvzero := (goldenBetaCoord_eq_zero_iff v).mp hzero
  omega

/-- The frozen beta exponent is positive at every positive mode. -/
theorem o5Beta_pos_of_pos {v : ℕ} (hv : 0 < v) : 0 < o5Beta v := by
  rw [← goldenWeight_goldenBetaCoord]
  exact goldenWeight_goldenBetaCoord_pos hv

/-- Composing the coordinate map with the weight map remains injective. -/
theorem goldenWeight_comp_goldenBetaCoord_injective :
    Function.Injective (fun v => goldenWeight (goldenBetaCoord v)) := by
  intro v w h
  apply goldenBetaCoord_injective
  exact goldenWeight_injective h

/-- Coordinate bounds and exact weights for every mode, together with global
injectivity of the weight map.  Growth, divergence, and the finite sublevel
census are deliberately left to the next all-order module. -/
theorem golden_weight_coordinates :
    (∀ v : ℕ,
      goldenBeattyQ v ≤ v ∧
        v ≤ 2 * goldenBeattyQ v ∧
          goldenWeight (goldenBetaCoord v) = o5Beta v) ∧
      Function.Injective goldenWeight := by
  constructor
  · intro v
    exact ⟨goldenBeattyQ_le v, le_two_goldenBeattyQ v,
      goldenWeight_goldenBetaCoord v⟩
  · exact goldenWeight_injective

#print axioms golden_weight_coordinates

end

end D5.S3.Analytic.AllOrder.GoldenWeightCoordinates
