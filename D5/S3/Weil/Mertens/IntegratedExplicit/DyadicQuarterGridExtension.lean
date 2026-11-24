import D5.S3.Weil.Mertens.IntegratedExplicit.DyadicActualHingeProbe
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
import D5.S3.Weil.Mertens.IntegratedExplicit.GaussianActualWindowAssembly
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

/-! Exact sampling for the triangular Mangoldt sum. -/

noncomputable section

open Filter Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass firstLiMass_lt_one)

namespace DyadicActualHingeProbe

private theorem ramp_unit_interpolation (n d k : ℕ) (hd : 0 < d)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    mangoldtRamp n (((k : ℝ) + r) / d) =
      (1 - r) * mangoldtRamp n ((k : ℝ) / d) +
        r * mangoldtRamp n (((k : ℝ) + 1) / d) := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldtRamp]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases h : n * d ≤ k
  · have hR : (n : ℝ) * d ≤ k := by exact_mod_cast h
    have hl : (n : ℝ) ≤ (k : ℝ) / d := (le_div_iff₀ hdR).mpr hR
    have hm : (n : ℝ) ≤ ((k : ℝ) + r) / d := (le_div_iff₀ hdR).mpr (by linarith)
    have hu : (n : ℝ) ≤ ((k : ℝ) + 1) / d := (le_div_iff₀ hdR).mpr (by linarith)
    rw [ramp_eq_affine (Nat.pos_of_ne_zero hn) hm,
      ramp_eq_affine (Nat.pos_of_ne_zero hn) hl, ramp_eq_affine (Nat.pos_of_ne_zero hn) hu]
    ring
  · have hN : k + 1 ≤ n * d := by omega
    have hR : (k : ℝ) + 1 ≤ (n : ℝ) * d := by exact_mod_cast hN
    have hu : ((k : ℝ) + 1) / d ≤ n := (div_le_iff₀ hdR).mpr hR
    have zeroBelow (t : ℝ) (ht : t ≤ n) : mangoldtRamp n t = 0 := by
      unfold mangoldtRamp
      rw [max_eq_right (show t / (n : ℝ) - 1 ≤ 0 by
        linarith [(div_le_one hnR).mpr ht]), mul_zero]
    rw [zeroBelow _ ((div_le_iff₀ hdR).mpr (by linarith)),
      zeroBelow _ ((div_le_iff₀ hdR).mpr (by linarith)), zeroBelow _ hu]
    ring

private theorem part_unit_interpolation (d k : ℕ) (hd : 0 < d)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    mangoldtPart (((k : ℝ) + r) / d) =
      (1 - r) * mangoldtPart ((k : ℝ) / d) +
        r * mangoldtPart (((k : ℝ) + 1) / d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) < d := by linarith
  have below {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
      ((k : ℝ) + u) / d < (↑(k + 2) : ℝ) := by
    have hle := div_le_self (show 0 ≤ (k : ℝ) + u by linarith) hdR
    push_cast
    linarith
  have hleft : (k : ℝ) / d < (↑(k + 2) : ℝ) := by simpa using below le_rfl zero_le_one
  rw [mangoldtPart_eq_range (div_nonneg (by linarith) hd0.le) (below hr hr'),
    mangoldtPart_eq_range (div_nonneg hk hd0.le) hleft,
    mangoldtPart_eq_range (div_nonneg (by linarith) hd0.le) (below zero_le_one le_rfl),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => ramp_unit_interpolation n d k hd hr hr'

private theorem hinge_eq_parts {x : ℝ} (hx : 0 < x) :
    hinge U x = mangoldtPart (4 * x) - 3 * mangoldtPart (2 * x) +
      2 * mangoldtPart x - 2 * x * Real.log 2 := by
  unfold hinge
  rw [U_eq_complete_ramps (by positivity : 0 ≤ 4 * x),
    U_eq_complete_ramps (by positivity : 0 ≤ 2 * x), U_eq_complete_ramps hx.le,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne',
    show Real.log 4 = Real.log 2 + Real.log 2 by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]]
  ring

/-- Every knot of the centered triangular Mangoldt sum lies on the quarter grid. -/
theorem hinge_quarter_interpolation {k : ℕ} (hk : 0 < k)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    hinge U (((k : ℝ) + r) / 4) =
      (1 - r) * hinge U ((k : ℝ) / 4) + r * hinge U (((k : ℝ) + 1) / 4) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [hinge_eq_parts (by linarith), hinge_eq_parts (by positivity),
    hinge_eq_parts (by positivity)]
  have h1 := part_unit_interpolation 1 k (by decide) hr hr'
  have h2 := part_unit_interpolation 2 k (by decide) hr hr'
  have h4 := part_unit_interpolation 4 k (by decide) hr hr'
  norm_num only [Nat.cast_one, div_one, Nat.cast_ofNat] at h1 h2 h4
  simp only [show ∀ t : ℝ, 4 * (t / 4) = t by intro t; ring,
    show ∀ t : ℝ, 2 * (t / 4) = t / 2 by intro t; ring, h1, h2, h4]
  ring

/-- The exact quarterly samples of the finite triangular sum control all
large real scales at the same exponent. -/
theorem eventually_hinge_lower_of_quarter_grid {θ A : ℝ} (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (hs : ∀ᶠ k : ℕ in atTop, -A * ((k : ℝ) / 4) ^ θ ≤ hinge U ((k : ℝ) / 4)) :
    ∀ᶠ x : ℝ in atTop, -(A * (2 : ℝ) ^ θ) * x ^ θ ≤ hinge U x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with x hx
  have hx1 := (le_max_left (1 : ℝ) N).trans hx
  have hxN := (le_max_right (1 : ℝ) N).trans hx
  let k := ⌊4 * x⌋₊
  have hx0 : 0 ≤ 4 * x := by linarith
  have hk_floor : (k : ℝ) ≤ 4 * x := Nat.floor_le hx0
  have hfloor_k : 4 * x < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkN : N ≤ k := (Nat.le_floor_iff hx0).mpr (by linarith)
  have hk : 0 < k := (Nat.le_floor_iff hx0).mpr (by norm_num; linarith)
  let r := 4 * x - (k : ℝ)
  have hr : 0 ≤ r := sub_nonneg.mpr hk_floor
  have hr' : r ≤ 1 := by dsimp [r]; linarith
  have hxgrid : ((k : ℝ) + r) / 4 = x := by dsimp [r]; ring
  have hleft : ((k : ℝ) / 4) ^ θ ≤ (2 * x) ^ θ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hθ
  have hright : (((k : ℝ) + 1) / 4) ^ θ ≤ (2 * x) ^ θ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hθ
  have hl := (mul_le_mul_of_nonpos_left hleft (neg_nonpos.mpr hA)).trans (hN k hkN)
  have hu := (mul_le_mul_of_nonpos_left hright (neg_nonpos.mpr hA)).trans (by
    simpa only [Nat.cast_succ] using hN (k + 1) (hkN.trans (Nat.le_succ k)))
  rw [← hxgrid, hinge_quarter_interpolation hk hr hr', hxgrid,
    ← neg_mul, mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ x)]
  have h := add_le_add (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hr'))
    (mul_le_mul_of_nonneg_left hu hr)
  convert h using 1
  ring

private theorem eventual_abs_U_le_sqrt (rh : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, |U x| ≤ Real.sqrt x := by
  have he := Real.tendsto_log_atTop.eventually ((RHSharpActualEnvelope.actual_G_control rh).1
    (1 - firstLiMass) (sub_pos.mpr firstLiMass_lt_one))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x h hx
  change |Real.exp (-Real.log x / 2) * U (Real.exp (Real.log x))| <
    firstLiMass + (1 - firstLiMass) at h
  have hinv : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_neg]
    congr 1
    ring
  rw [Real.exp_log hx, abs_mul, abs_of_pos (Real.exp_pos _), hinv, ← div_eq_inv_mul] at h
  exact (div_le_one (Real.sqrt_pos.mpr hx)).mp (by linarith)

private theorem eventual_hinge_lower_of_rh (rh : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, -(10 : ℝ) * Real.sqrt x ≤ hinge U x := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventual_abs_U_le_sqrt rh)
  filter_upwards [eventually_ge_atTop (max 1 T)] with x hx
  have hx1 := (le_max_left 1 T).trans hx
  have hxT := (le_max_right 1 T).trans hx
  have hxNonneg : 0 ≤ x := by linarith
  have h4 := abs_le.mp (hT (4 * x) (by linarith))
  have h2 := abs_le.mp (hT (2 * x) (by linarith))
  have h1 := abs_le.mp (hT x hxT)
  have hs4 : Real.sqrt (4 * x) = 2 * Real.sqrt x := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hs2 : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
    rw [← hs4]
    exact Real.sqrt_le_sqrt (by linarith)
  unfold hinge
  linarith [h4.1, h2.2, h1.1]

/-- RH is equivalent to an eventual square-root lower bound on only the
finite, nonnegative triangular Mangoldt sum at the exact quarter grid. -/
theorem rh_iff_eventual_quarter_triangular_lower :
    RiemannHypothesis ↔ ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k : ℕ in atTop,
      2 * ((k : ℝ) / 4) * Real.log 2 - A * Real.sqrt ((k : ℝ) / 4) ≤
        mangoldtHingeSum ((k : ℝ) / 4) := by
  constructor
  · intro rh
    have hlim : Tendsto (fun k : ℕ => (k : ℝ) / 4) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop
    refine ⟨10, by norm_num, ?_⟩
    filter_upwards [hlim.eventually (eventual_hinge_lower_of_rh rh),
      eventually_gt_atTop (0 : ℕ)] with k h hk
    rw [hinge_mangoldtRamp_eq (by positivity : 0 < (k : ℝ) / 4)] at h
    linarith
  · rintro ⟨A, hA, hs⟩
    have hg : ∀ᶠ k : ℕ in atTop, -A * ((k : ℝ) / 4) ^ (1 / 2 : ℝ) ≤
        hinge U ((k : ℝ) / 4) := by
      filter_upwards [hs, eventually_gt_atTop (0 : ℕ)] with k h hk
      rw [hinge_mangoldtRamp_eq (by positivity : 0 < (k : ℝ) / 4), ← Real.sqrt_eq_rpow]
      linarith
    let M := A * (2 : ℝ) ^ (1 / 2 : ℝ)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    obtain ⟨X, hX⟩ := eventually_atTop.mp
      (eventually_hinge_lower_of_quarter_grid (by norm_num : (0 : ℝ) ≤ 1 / 2) hA hg)
    obtain ⟨B, hB⟩ := mangoldt_ramp_upper_bound
      (X := max 1 X) (θ := 1 / 2) (A := M)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by norm_num) (by norm_num) hM
      (fun x hx => hX x ((le_max_right _ _).trans hx))
    let D := M / ((2 ^ (1 / 2 : ℝ) - 1) * (2 - 2 ^ (1 / 2 : ℝ)))
    let C := |B| + |D| + |firstLiMass| + 1
    have hC : firstLiMass < C := by
      dsimp [C]
      linarith [le_abs_self firstLiMass, abs_nonneg B, abs_nonneg D]
    apply (MangoldtPointwiseWindows.rh_iff_pointwise_sqrt_windows (b := 2) hC (by norm_num)).mpr
    intro R
    refine ⟨max (max R 2) (max 1 X), le_max_left _ _, ?_⟩
    intro x hx
    have hxX := (le_max_right (max R 2) (max 1 X)).trans hx.1
    have hxs : 1 ≤ Real.sqrt x := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ((le_max_left 1 X).trans hxX)
    have hb := hB x hxX
    change U x ≤ B + D * x ^ (1 / 2 : ℝ) at hb
    rw [← Real.sqrt_eq_rpow] at hb
    refine hb.trans ?_
    calc
      B + D * Real.sqrt x ≤ |B| * Real.sqrt x + |D| * Real.sqrt x := by
        have hb' := mul_le_mul_of_nonneg_left hxs (abs_nonneg B)
        have hd' := mul_le_mul_of_nonneg_right (le_abs_self D) (Real.sqrt_nonneg x)
        linarith [le_abs_self B]
      _ = (|B| + |D|) * Real.sqrt x := by ring
      _ ≤ C * Real.sqrt x :=
        mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [abs_nonneg firstLiMass])
          (Real.sqrt_nonneg x)

end DyadicActualHingeProbe

#print axioms DyadicActualHingeProbe.hinge_quarter_interpolation
#print axioms DyadicActualHingeProbe.eventually_hinge_lower_of_quarter_grid
#print axioms DyadicActualHingeProbe.rh_iff_eventual_quarter_triangular_lower

namespace DyadicActualHingeProbe

/-- The tent weight vanishes outside `(x, 4*x)` and takes the value `1` at `2*x`. -/
def triangleWeight (x n : ℝ) : ℝ :=
  max (4 * x / n - 1) 0 - 3 * max (2 * x / n - 1) 0 + 2 * max (x / n - 1) 0

theorem triangleWeight_bounds {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    triangleWeight x n ∈ Icc (0 : ℝ) 1 := by
  let t := x / n
  have ht : 0 ≤ t := div_nonneg hx hn.le
  unfold triangleWeight
  rw [mul_div_assoc, mul_div_assoc]
  change 0 ≤ max (4 * t - 1) 0 - 3 * max (2 * t - 1) 0 + 2 * max (t - 1) 0 ∧
    max (4 * t - 1) 0 - 3 * max (2 * t - 1) 0 + 2 * max (t - 1) 0 ≤ 1
  by_cases h1 : 1 ≤ t
  · rw [max_eq_left (by linarith : 0 ≤ 4 * t - 1),
      max_eq_left (by linarith : 0 ≤ 2 * t - 1), max_eq_left (by linarith : 0 ≤ t - 1)]
    constructor <;> linarith
  rw [max_eq_right (by linarith : t - 1 ≤ 0)]
  by_cases h2 : 1 / 2 ≤ t
  · rw [max_eq_left (by linarith : 0 ≤ 4 * t - 1), max_eq_left (by linarith : 0 ≤ 2 * t - 1)]
    constructor <;> linarith
  rw [max_eq_right (by linarith : 2 * t - 1 ≤ 0)]
  constructor
  · linarith [le_max_right (4 * t - 1) (0 : ℝ)]
  · linarith [max_le (show 4 * t - 1 ≤ 1 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)]

/-- Restrict the triangular sum to primes, with their literal logarithmic weights. -/
def primeTriangleSum (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊4 * x⌋₊).filter Nat.Prime, Real.log n * triangleWeight x n

private theorem triangleWeight_eq_zero_of_le {x n : ℝ} (hn : 0 < n) (h : n ≤ x) :
    triangleWeight x n = 0 := by
  have h1 : 1 ≤ x / n := (one_le_div hn).mpr h
  unfold triangleWeight
  rw [mul_div_assoc, mul_div_assoc, max_eq_left (by linarith : 0 ≤ 4 * (x / n) - 1),
    max_eq_left (by linarith : 0 ≤ 2 * (x / n) - 1),
    max_eq_left (by linarith : 0 ≤ x / n - 1)]
  ring

/-- The prime sum uses only the literal primes in `(x, 4*x]`. -/
theorem primeTriangleSum_eq_window {x : ℝ} (hx : 0 ≤ x) :
    primeTriangleSum x =
      ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊4 * x⌋₊).filter Nat.Prime, Real.log n * triangleWeight x n := by
  unfold primeTriangleSum
  symm
  apply Finset.sum_subset
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hI := Finset.mem_Ioc.mp hn'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hI.2⟩, hn'.2⟩
  · intro n hn hnot
    have hn' := Finset.mem_filter.mp hn
    have hI := Finset.mem_Ioc.mp hn'.1
    have hle : n ≤ ⌊x⌋₊ := by
      by_contra! hh
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hh, hI.2⟩, hn'.2⟩)
    rw [triangleWeight_eq_zero_of_le (by exact_mod_cast hI.1) ((Nat.le_floor_iff hx).mp hle),
      mul_zero]

theorem primeTriangle_comparison {x : ℝ} (hx : 0 ≤ x) :
    primeTriangleSum x ≤ mangoldtHingeSum x ∧
      mangoldtHingeSum x ≤ primeTriangleSum x +
        (Chebyshev.psi (4 * x) - Chebyshev.theta (4 * x)) := by
  let s := Finset.Ioc 0 ⌊4 * x⌋₊
  let f := fun n : ℕ => ArithmeticFunction.vonMangoldt n * triangleWeight x n
  have hp : ∑ n ∈ s.filter Nat.Prime, f n = primeTriangleSum x := by
    unfold primeTriangleSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [show f n = ArithmeticFunction.vonMangoldt n * triangleWeight x n from rfl,
      ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  have hsplit : mangoldtHingeSum x =
      primeTriangleSum x + ∑ n ∈ s.filter (fun n => ¬n.Prime), f n := by
    change ∑ n ∈ s, f n = _
    rw [← hp]
    exact (Finset.sum_filter_add_sum_filter_not s Nat.Prime f).symm
  have hnonneg : 0 ≤ ∑ n ∈ s.filter (fun n => ¬n.Prime), f n := by
    apply Finset.sum_nonneg
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (triangleWeight_bounds hx hn').1
  have hupper : (∑ n ∈ s.filter (fun n => ¬n.Prime), f n) ≤
      ∑ n ∈ s.filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (triangleWeight_bounds hx hn').2
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, hsplit]
  exact ⟨le_add_of_nonneg_right hnonneg, add_le_add_right hupper _⟩

/-- The prime-only triangle on `(k/4,k]` tests RH by one eventual lower bound. -/
theorem rh_iff_eventual_prime_triangle_lower :
    RiemannHypothesis ↔ ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k : ℕ in atTop,
      2 * ((k : ℝ) / 4) * Real.log 2 - A * Real.sqrt ((k : ℝ) / 4) ≤
        primeTriangleSum ((k : ℝ) / 4) := by
  rw [rh_iff_eventual_quarter_triangular_lower]
  constructor
  · rintro ⟨A, hA, hs⟩
    obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    refine ⟨A + 2 * max C 0, by positivity, ?_⟩
    filter_upwards [hs] with k hk
    let x : ℝ := (k : ℝ) / 4
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hc := (hC (4 * x)).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at hc
    change 2 * x * Real.log 2 - A * Real.sqrt x ≤ mangoldtHingeSum x at hk
    change 2 * x * Real.log 2 - (A + 2 * max C 0) * Real.sqrt x ≤ primeTriangleSum x
    linarith [(primeTriangle_comparison hx).2]
  · rintro ⟨A, hA, hs⟩
    exact ⟨A, hA, hs.mono fun k hk => hk.trans (primeTriangle_comparison (by positivity)).1⟩

/-- It suffices to bound the ordinary-prime triangle from below on arbitrarily
late power windows, with one fixed square-root error coefficient. -/
theorem rh_iff_frequently_prime_triangle_lower {B : ℝ} (hB : 1 < B) :
    RiemannHypothesis ↔ ∃ A : ℝ, 0 ≤ A ∧ ∃ᶠ X : ℝ in atTop,
      ∀ x ∈ Icc X (X ^ B), 2 * x * Real.log 2 - A * Real.sqrt x ≤ primeTriangleSum x := by
  constructor
  · intro rh
    obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    have he : ∀ᶠ x : ℝ in atTop,
        2 * x * Real.log 2 - (10 + 2 * max C 0) * Real.sqrt x ≤ primeTriangleSum x := by
      filter_upwards [eventual_hinge_lower_of_rh rh, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      have hc := (hC (4 * x)).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at hc
      rw [hinge_mangoldtRamp_eq hx0] at hx
      linarith only [hx, hc, (primeTriangle_comparison hx0.le).2]
    obtain ⟨T, hT⟩ := eventually_atTop.mp he
    exact ⟨10 + 2 * max C 0, by positivity,
      (eventually_ge_atTop T).frequently.mono fun X hX x hx => hT x (hX.trans hx.1)⟩
  · rintro ⟨A, hA, hwin⟩
    apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
    intro ρ hzero hhalf hone
    have hρ : Zeta23.IsNontrivialZero ρ := ⟨hzero, by linarith, hone⟩
    have hpeaks := GaussianActualWindowAssembly.signed_peaks_in_power_windows hρ hhalf hB hA
    obtain ⟨X, hX, hpeak, hX0⟩ := (hwin.and_eventually
      (hpeaks.and (eventually_gt_atTop (0 : ℝ)))).exists
    obtain ⟨x, hx, hdiscrepancy⟩ := hpeak (-1) (Or.inr rfl)
    have hx0 := hX0.trans_le hx.1
    have hh := hinge_mangoldtRamp_eq hx0
    unfold hinge at hh
    linarith only [hX x hx, hdiscrepancy, hh, (primeTriangle_comparison hx0.le).1]

end DyadicActualHingeProbe

#print axioms DyadicActualHingeProbe.rh_iff_eventual_prime_triangle_lower
#print axioms DyadicActualHingeProbe.primeTriangleSum_eq_window
#print axioms DyadicActualHingeProbe.rh_iff_frequently_prime_triangle_lower
