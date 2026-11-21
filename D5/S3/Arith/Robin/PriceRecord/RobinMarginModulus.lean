/- GID: D5/S3/Arith/Robin/PriceRecord/RobinMarginModulus
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RobinMarginModulus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-sided local interpolation of Robin margins on strict price records. -/

import D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Weil.GronwallLowerEnvelope
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff

/-! A local modulus and cell bound for the Robin margins of strict price records. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.PriceRecord.RobinMarginModulus

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.ActualTwoPriceDefect (clock integerAt price price_antitone price_pos
  clock_monotone strictInteger strictInteger_spec strictInteger_pos strictInteger_counts W)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open ActualBalancedCutoff (firstLayerPrice)

/-- The optimizer comparisons and log-log tangents bound the margin increment by
the two cross-price differences times the actual increment of the record clock. -/
theorem robin_margin_sub_bounds {u v : ℝ} (hu : 1 < u) (huv : u ≤ v)
    (hclock : 1 < clock u) :
    (price (clock v) - price u) * (clock v - clock u) ≤
        robinLogMargin (integerAt v) - robinLogMargin (integerAt u) ∧
      robinLogMargin (integerAt v) - robinLogMargin (integerAt u) ≤
        (price (clock u) - price v) * (clock v - clock u) := by
  have hv := hu.trans_le huv
  have hmon := clock_monotone hu hv huv
  obtain ⟨hNu, _, hoptu, _⟩ := strictInteger_spec (price_pos hu)
  obtain ⟨hNv, _, hoptv, _⟩ := strictInteger_spec (price_pos hv)
  change 1 ≤ integerAt u at hNu
  change 1 ≤ integerAt v at hNv
  have hupper := hoptu (integerAt v) hNv
  have hlower := hoptv (integerAt u) hNu
  change goldenResourceObjective (price u) (integerAt v) ≤
    goldenResourceObjective (price u) (integerAt u) at hupper
  change goldenResourceObjective (price v) (integerAt u) ≤
    goldenResourceObjective (price v) (integerAt v) at hlower
  rw [golden_resource_sigma_identity _ hNv, golden_resource_sigma_identity _ hNu] at hupper
  rw [golden_resource_sigma_identity _ hNu, golden_resource_sigma_identity _ hNv] at hlower
  change W (integerAt v) - price u * clock v ≤
    W (integerAt u) - price u * clock u at hupper
  change W (integerAt u) - price v * clock u ≤
    W (integerAt v) - price v * clock v at hlower
  have htangent {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
      Real.log (Real.log b) - Real.log (Real.log a) ≤ (b - a) * price a := by
    by_cases heq : a = b
    · simp [heq]
    · exact (RestrictedDivisorStrictInventory.loglog_tangent ha hb heq).le
  have hright := htangent hclock (hclock.trans_le hmon)
  have hleft := htangent (hclock.trans_le hmon) hclock
  change (price (clock v) - price u) * (clock v - clock u) ≤
      (Real.eulerMascheroniConstant + Real.log (Real.log (clock v)) - W (integerAt v)) -
        (Real.eulerMascheroniConstant + Real.log (Real.log (clock u)) - W (integerAt u)) ∧
    (Real.eulerMascheroniConstant + Real.log (Real.log (clock v)) - W (integerAt v)) -
        (Real.eulerMascheroniConstant + Real.log (Real.log (clock u)) - W (integerAt u)) ≤
      (price (clock u) - price v) * (clock v - clock u)
  exact ⟨by linarith only [hleft, hupper], by linarith only [hright, hlower]⟩

private lemma abs_price_sub_le {a x y : ℝ} (ha : 1 < a) (hlog : 1 ≤ Real.log a)
    (hax : a ≤ x) (hay : a ≤ y) :
    |price x - price y| ≤ 2 * |x - y| / (a ^ 2 * Real.log a) := by
  have ordered {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) :
      |price s - price t| ≤ 2 * |s - t| / (a ^ 2 * Real.log a) := by
    have hs1 := ha.trans_le hs
    rw [abs_of_nonneg (sub_nonneg.mpr (price_antitone hs1 hst)), abs_sub_comm s t,
      abs_of_nonneg (sub_nonneg.mpr hst)]
    calc
      _ ≤ 2 * (t - s) / (s ^ 2 * Real.log s) :=
        PolynomialMeshBounds.price_gap hs1 hst
          (hlog.trans (Real.log_le_log (by linarith) hs))
      _ ≤ _ := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        exact mul_le_mul (pow_le_pow_left₀ (by linarith) hs 2)
          (Real.log_le_log (by linarith) hs) (by positivity) (by positivity)
  rcases le_total x y with hxy | hyx
  · exact ordered hax hxy
  · rw [abs_sub_comm (price x) (price y), abs_sub_comm x y]
    exact ordered hay hyx

private lemma margin_modulus_of_price_bounds {u v K : ℝ} (hu : 1 < u) (huv : u ≤ v)
    (hclock : 1 < clock u) (hleft : |price (clock v) - price u| ≤ K)
    (hright : |price (clock u) - price v| ≤ K) :
    |robinLogMargin (integerAt v) - robinLogMargin (integerAt u)| ≤
      K * (clock v - clock u) := by
  have hinc := sub_nonneg.mpr (clock_monotone hu (hu.trans_le huv) huv)
  obtain ⟨hl, hr⟩ := robin_margin_sub_bounds hu huv hclock
  have hlow : -K ≤ price (clock v) - price u :=
    (neg_le_neg hleft).trans (neg_abs_le _)
  have hupp : price (clock u) - price v ≤ K := (le_abs_self _).trans hright
  apply abs_le.mpr
  rw [← neg_mul]
  exact ⟨(mul_le_mul_of_nonneg_right hlow hinc).trans hl,
    hr.trans (mul_le_mul_of_nonneg_right hupp hinc)⟩

/-- A common lower bound for the two parameters and their clocks gives a price
modulus from the cross-distances. The right side keeps the actual clock increment. -/
theorem robin_margin_modulus {a u v D : ℝ} (ha : 1 < a) (hlog : 1 ≤ Real.log a)
    (hau : a ≤ u) (huv : u ≤ v) (hac : a ≤ clock u)
    (hleft : |clock v - u| ≤ D) (hright : |clock u - v| ≤ D) :
    |robinLogMargin (integerAt v) - robinLogMargin (integerAt u)| ≤
      (2 * D / (a ^ 2 * Real.log a)) * (clock v - clock u) := by
  have hu := ha.trans_le hau
  have hcv := hac.trans (clock_monotone hu (hu.trans_le huv) huv)
  apply margin_modulus_of_price_bounds hu huv (ha.trans_le hac)
  · exact (abs_price_sub_le ha hlog hcv hau).trans
      (div_le_div_of_nonneg_right (by linarith only [hleft]) (by positivity))
  · exact (abs_price_sub_le ha hlog hac (hau.trans huv)).trans
      (div_le_div_of_nonneg_right (by linarith only [hright]) (by positivity))

/-- On a short price step, the clock discrepancy supplies the power saving,
while the actual clock increment is a separate factor that can telescope. -/
theorem robin_margin_local_power_bound {X u v C β : ℝ} (hX : 8 ≤ X) (hXu : X ≤ u)
    (huv : u ≤ v) (hstep : v - u ≤ 2) (hclock : X / 2 ≤ clock u) (hβ : 0 ≤ β)
    (hdu : |clock u - u| ≤ C * Real.rpow X β)
    (hdv : |clock v - v| ≤ C * Real.rpow X β) :
    |robinLogMargin (integerAt v) - robinLogMargin (integerAt u)| ≤
      (16 * (C + 2) * Real.rpow X (β - 2) / Real.log X) * (clock v - clock u) := by
  have hX0 : 0 < X := by linarith
  have ha : 1 < X / 2 := by linarith
  have hlog : 1 ≤ Real.log (X / 2) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hlogX : Real.log X ≤ 2 * Real.log (X / 2) := by
    rw [show 2 * Real.log (X / 2) = Real.log ((X / 2) ^ 2) by simp [Real.log_pow]]
    apply Real.log_le_log hX0
    nlinarith [mul_nonneg (show 0 ≤ X by linarith) (show 0 ≤ X - 4 by linarith)]
  have hone : 1 ≤ Real.rpow X β := Real.one_le_rpow (by linarith) hβ
  have hplus : C * Real.rpow X β + 2 ≤ (C + 2) * Real.rpow X β := by linarith
  have hdist : |v - u| ≤ 2 := by rwa [abs_of_nonneg (sub_nonneg.mpr huv)]
  have hleft : |clock v - u| ≤ (C + 2) * Real.rpow X β :=
    (abs_sub_le (clock v) v u).trans ((add_le_add hdv hdist).trans hplus)
  have hright : |clock u - v| ≤ (C + 2) * Real.rpow X β := by
    rw [abs_sub_comm v u] at hdist
    exact (abs_sub_le (clock u) u v).trans ((add_le_add hdu hdist).trans hplus)
  have hbound := robin_margin_modulus ha hlog (show X / 2 ≤ u by linarith)
    huv hclock hleft hright
  have hden : X ^ 2 * Real.log X / 8 ≤ (X / 2) ^ 2 * Real.log (X / 2) := by
    have h := mul_le_mul_of_nonneg_left hlogX (sq_nonneg X)
    linarith only [h]
  have hpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hscaled : 2 * ((C + 2) * Real.rpow X β) / ((X / 2) ^ 2 * Real.log (X / 2)) ≤
      16 * (C + 2) * Real.rpow X (β - 2) / Real.log X := calc
    _ ≤ 2 * ((C + 2) * Real.rpow X β) / (X ^ 2 * Real.log X / 8) :=
      div_le_div_of_nonneg_left (by linarith only [abs_nonneg (clock v - u), hleft])
        (by positivity) hden
    _ = _ := by
      rw [Real.rpow_eq_pow X β, Real.rpow_eq_pow X (β - 2), Real.rpow_sub hX0,
        show X ^ (2 : ℝ) = X ^ (2 : ℕ) from Real.rpow_natCast X 2]
      field_simp [hX0.ne', hpos.ne']
      ring
  exact hbound.trans (mul_le_mul_of_nonneg_right hscaled
    (sub_nonneg.mpr (clock_monotone (show 1 < u by linarith) (show 1 < v by linarith) huv)))

/-- Summing short price steps in an indexed cell keeps just the difference
of its endpoint clocks, even when consecutive records coincide. -/
theorem robin_margin_cell_power_bound {t : ℕ → ℝ} {i j : ℕ} {X C β : ℝ}
    (hij : i ≤ j) (hX : 8 ≤ X) (hβ : 0 ≤ β)
    (hgeom : ∀ k, i ≤ k → k ≤ j → X ≤ t k ∧
      X / 2 ≤ clock (t k) ∧ |clock (t k) - t k| ≤ C * Real.rpow X β)
    (hstep : ∀ k, i ≤ k → k < j → t k ≤ t (k + 1) ∧ t (k + 1) - t k ≤ 2) :
    |robinLogMargin (integerAt (t j)) - robinLogMargin (integerAt (t i))| ≤
      (16 * (C + 2) * Real.rpow X (β - 2) / Real.log X) *
        (clock (t j) - clock (t i)) := by
  let K := 16 * (C + 2) * Real.rpow X (β - 2) / Real.log X
  suffices ∀ m, i ≤ m → m ≤ j →
      |robinLogMargin (integerAt (t m)) - robinLogMargin (integerAt (t i))| ≤
        K * (clock (t m) - clock (t i)) from this j hij le_rfl
  intro m him
  induction m, him using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    intro hnext
    obtain ⟨hlo, hclock, herr⟩ := hgeom k hik (by omega)
    obtain ⟨_, _, herrnext⟩ := hgeom (k + 1) (by omega) hnext
    obtain ⟨hmono, hgap⟩ := hstep k hik (by omega)
    have hlocal := robin_margin_local_power_bound hX hlo hmono hgap hclock hβ herr herrnext
    calc
      _ ≤ |robinLogMargin (integerAt (t (k + 1))) - robinLogMargin (integerAt (t k))| +
          |robinLogMargin (integerAt (t k)) - robinLogMargin (integerAt (t i))| :=
        abs_sub_le _ _ _
      _ ≤ K * (clock (t (k + 1)) - clock (t k)) + K * (clock (t k) - clock (t i)) :=
        add_le_add hlocal (ih (by omega))
      _ = _ := by ring

private lemma psi_sub_le {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    Chebyshev.psi v - Chebyshev.psi u ≤ (v - u + 1) * Real.log v := by
  have hfloor : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
  have hv0 : 0 ≤ v := by linarith
  have hsize : (↑(⌊v⌋₊ - ⌊u⌋₊) : ℝ) ≤ v - u + 1 := by
    rw [Nat.cast_sub hfloor]
    linarith only [Nat.floor_le hv0, Nat.lt_floor_add_one u]
  have hsum := Finset.sum_Ioc_consecutive ArithmeticFunction.vonMangoldt
    (Nat.zero_le ⌊u⌋₊) hfloor
  calc
    _ = ∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, ArithmeticFunction.vonMangoldt n := by
      unfold Chebyshev.psi
      linarith only [hsum]
    _ ≤ ∑ _n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, Real.log v := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnv⟩ := Finset.mem_Ioc.mp hn
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hn0))
          ((show (n : ℝ) ≤ ⌊v⌋₊ by exact_mod_cast hnv).trans (Nat.floor_le hv0)))
    _ = (↑(⌊v⌋₊ - ⌊u⌋₊) : ℝ) * Real.log v := by
      simp [Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsize (Real.log_nonneg (by linarith))

/-- The change in the actual strict inventory clock is bounded by the local
von Mangoldt sum and two square-root inventory discrepancies. -/
theorem clock_sub_le : ∃ A : ℝ, 0 < A ∧ ∀ {u v : ℝ}, 2 ≤ u → u ≤ v →
    clock v - clock u ≤ (v - u + 1) * Real.log v + A * (Real.sqrt u + Real.sqrt v) := by
  obtain ⟨A, hA, hAinv⟩ := EulerLayerInventoryGrowth.strict_inventory_sqrt_discrepancy
  have hinv {s : ℝ} (hs : 2 ≤ s) : |clock s - Chebyshev.psi s| ≤ A * Real.sqrt s := by
    have hq := price_pos (show 1 < s by linarith)
    exact hAinv s hs (integerAt s) (strictInteger_pos hq) (fun p _ => strictInteger_counts hq p)
  refine ⟨A, hA, ?_⟩
  intro u v hu huv
  have hlo := (abs_le.mp (hinv hu)).1
  have hhi := (abs_le.mp (hinv (hu.trans huv))).2
  linarith only [hlo, hhi, psi_sub_le hu huv]

/-- The cell estimate written on the literal canonical strict record integers.
Any exact-price cutoffs within the half-unit windows give the same integers. -/
theorem canonical_robin_margin_cell_bound : ∃ A : ℝ, 0 < A ∧
    ∀ {t : ℕ → ℝ} {i j : ℕ} {X C β : ℝ}, i ≤ j → 8 ≤ X → 0 ≤ C → 0 ≤ β →
    (∀ k, i ≤ k → k ≤ j → (k : ℝ) + 1 ≤ t k ∧ t k ≤ (k : ℝ) + 1 + 1 / 2 ∧
      price (t k) = firstLayerPrice ((k : ℝ) + 1)) →
    (∀ k, i ≤ k → k ≤ j → X ≤ t k ∧ X / 2 ≤ clock (t k) ∧
      |clock (t k) - t k| ≤ C * Real.rpow X β) →
    |robinLogMargin (strictInteger (firstLayerPrice ((j : ℝ) + 1))) -
        robinLogMargin (strictInteger (firstLayerPrice ((i : ℝ) + 1)))| ≤
      (16 * (C + 2) * Real.rpow X (β - 2) / Real.log X) *
        ((t j - t i + 1) * Real.log (t j) + A * (Real.sqrt (t i) + Real.sqrt (t j))) := by
  obtain ⟨A, hA, hinc⟩ := clock_sub_le
  refine ⟨A, hA, ?_⟩
  intro t i j X C β hij hX hC hβ hcut hgeom
  have hstep (k : ℕ) (hik : i ≤ k) (hkj : k < j) :
      t k ≤ t (k + 1) ∧ t (k + 1) - t k ≤ 2 := by
    obtain ⟨hlo, hhi, _⟩ := hcut k hik hkj.le
    obtain ⟨hlonext, hhinext, _⟩ := hcut (k + 1) (by omega) (by omega)
    push_cast at hlonext hhinext
    constructor <;> linarith
  obtain ⟨_, hit, hip⟩ := hcut i le_rfl hij
  obtain ⟨hjt, _, hjp⟩ := hcut j hij le_rfl
  have htle : t i ≤ t j := by
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
      linarith
  have hti : 2 ≤ t i := by linarith only [hX, (hgeom i le_rfl hij).1]
  have hK : 0 ≤ 16 * (C + 2) * Real.rpow X (β - 2) / Real.log X := by
    have hlog : 0 < Real.log X := Real.log_pos (by linarith)
    have hX0 : 0 ≤ X := by linarith
    exact div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hX0 _)) hlog.le
  have hb := (robin_margin_cell_power_bound hij hX hβ hgeom hstep).trans
    (mul_le_mul_of_nonneg_left (hinc hti htle) hK)
  simpa only [integerAt, hip, hjp] using hb

#print axioms robin_margin_sub_bounds
#print axioms robin_margin_modulus
#print axioms robin_margin_local_power_bound
#print axioms robin_margin_cell_power_bound
#print axioms clock_sub_le
#print axioms canonical_robin_margin_cell_bound

end D5.S3.Arith.Robin.PriceRecord.RobinMarginModulus
