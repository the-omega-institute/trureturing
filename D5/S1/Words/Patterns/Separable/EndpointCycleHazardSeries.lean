/- GID: D5/S1/Words/Patterns/Separable/EndpointCycleHazardSeries
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointCycleHazardSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual next-cycle endpoint hazard is the occupied zero term plus the parity-regrouped geometric removal series. -/

import D5.S1.Words.Patterns.Separable.ActualCycleLaw
import D5.S1.Words.Patterns.Separable.OccupiedComparison
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The actual alternating endpoint-cycle hit law retains removal shapes and terminal type. -/

namespace D5.S1.Words.Patterns.Separable.EndpointCycleHazard

open D5.S1.Words.Patterns.Separable.ActualCycles
open D5.S1.Words.Patterns.Separable.ActualCycleLaw
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.OccupiedComparison
open MeasureTheory
open scoped BigOperators ENNReal

/-- At discrepancy e, a hit occurs precisely in a direct terminal's local diagonal. -/
def hit : {sign : Bool} → UnboundedCycle sign → ℤ → Prop
  | sign, .terminal _ shape, e => sign = false ∧ hitsDiagonal shape.val.val e
  | sign, .discard n _ tail, e =>
      hit tail (e + if sign then (n : ℤ) + 1 else 0)

noncomputable def nextHazard (e : ℤ) : ℝ≥0∞ :=
  cyclePMF.toMeasure {c : MarkedCycle | hit c.2 e}

private theorem fixed_decode_size {s : Bool} {r : ℕ} (c : Fixed s r) :
    c.decode.size = c.size := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih => simp only [Fixed.decode, UnboundedCycle.size, Fixed.size, ih]

/-- Actual cycle weight respects the fixed-count reindexing without any independence
assumption about number of removals and terminal type. -/
private theorem fixed_cycle_weight {s : Bool} {r : ℕ} (c : Fixed s r) :
    cyclePMF (⟨s, c.decode⟩ : MarkedCycle) = ENNReal.ofReal (rho ^ c.size) := by
  change ENNReal.ofReal (rho ^ c.decode.size) = _
  rw [fixed_decode_size]

/-- Weighted hit mass for actual cycles retaining the starting sign and discard count. -/
private noncomputable def fixedHitMass (s : Bool) (k : ℕ) (e : ℤ) : ℝ≥0∞ := by
  classical
  exact ∑' c : Fixed s k, if hit c.decode e then ENNReal.ofReal (rho ^ c.size) else 0

/-- Remove the first actual discard, shifting the offset only at a skew cut. -/
private theorem fixedHitMass_succ (s : Bool) (k : ℕ) (e : ℤ) :
    fixedHitMass s (k + 1) e =
      ∑' c : Removal, ENNReal.ofReal (rho ^ (c.1 + 1)) *
        fixedHitMass (!s) k (e + (if s then (c.1 : ℤ) + 1 else 0)) := by
  classical
  have hrho : 0 ≤ rho := by unfold rho; exact sq_nonneg _
  change (∑' p : Removal × Fixed (!s) k,
      if hit p.2.decode (e + (if s then (p.1.1 : ℤ) + 1 else 0))
      then ENNReal.ofReal (rho ^ (p.1.1 + 1 + p.2.size)) else 0) = _
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro c
  unfold fixedHitMass
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro tail
  by_cases h : hit tail.decode (e + (if s then (c.1 : ℤ) + 1 else 0))
  · simp only [if_pos h]
    rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hrho _)]
  · simp only [if_neg h, mul_zero]

/-- Keep both actual starting signs and the common discard count. -/
private noncomputable def hitMassAtCount (e : ℤ) (k : ℕ) : ℝ≥0∞ :=
  ∑ s : Bool, fixedHitMass s k e

private theorem signed_hit_mass (e : ℤ) (s : Bool) :
    (∑' c : UnboundedCycle s,
      ({d : MarkedCycle | hit d.2 e} : Set MarkedCycle).indicator cyclePMF ⟨s, c⟩) =
      ∑' k, fixedHitMass s k e := by
  classical
  rw [← (enumeration s).symm.tsum_eq, ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  unfold fixedHitMass
  apply tsum_congr
  intro c
  change (({d : MarkedCycle | hit d.2 e} : Set MarkedCycle).indicator
    cyclePMF ⟨s, c.decode⟩) = _
  simp only [Set.indicator_apply, Set.mem_setOf_eq, fixed_cycle_weight]

/-- Reindex the actual hit, not an independent model, by exact discard count. -/
private theorem nextHazard_eq_tsum_hitMassAtCount (e : ℤ) :
    nextHazard e = ∑' k, hitMassAtCount e k := by
  classical
  rw [nextHazard, PMF.toMeasure_apply_eq_tsum, ENNReal.tsum_sigma']
  simp_rw [signed_hit_mass]
  calc
    (∑' (s : Bool) (k : ℕ), fixedHitMass s k e) =
        ∑' p : Bool × ℕ, fixedHitMass p.1 p.2 e := (ENNReal.tsum_prod' (f := fun p : Bool × ℕ => fixedHitMass p.1 p.2 e)).symm
    _ = ∑' p : ℕ × Bool, fixedHitMass p.2 p.1 e :=
        ((Equiv.prodComm ℕ Bool).tsum_eq
          (fun p : Bool × ℕ => fixedHitMass p.1 p.2 e)).symm
    _ = ∑' k, hitMassAtCount e k := by
      rw [ENNReal.tsum_prod']
      simp only [hitMassAtCount, tsum_fintype]

private theorem removal_weight_sum :
    (∑' c : Removal, ENNReal.ofReal (rho ^ (c.1 + 1))) = ENNReal.ofReal b := by
  classical
  have hrho : 0 ≤ rho := by unfold rho; exact sq_nonneg _
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have cast (n : ℕ) : (Nat.card (Avoider (n + 1)) : ℝ≥0∞) *
      ENNReal.ofReal (rho ^ (n + 1)) = ENNReal.ofReal (shapeWeight n) := by
    rw [shapeWeight, ENNReal.ofReal_mul (pow_nonneg hrho _)]
    simp only [ENNReal.ofReal_natCast, mul_comm]
  simp_rw [cast]
  have nonneg (n : ℕ) : 0 ≤ shapeWeight n :=
    mul_nonneg (pow_nonneg hrho _) (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_tsum_of_nonneg nonneg critical_shape_masses.1,
    critical_shape_masses.2.1]

private noncomputable def skewKernel (f : ℤ → ℝ≥0∞) (e : ℤ) : ℝ≥0∞ :=
  ∑' c : Removal, ENNReal.ofReal (rho ^ (c.1 + 1)) * f (e + (c.1 : ℤ) + 1)

private theorem skewKernel_mul (a : ℝ≥0∞) (f : ℤ → ℝ≥0∞) (e : ℤ) :
    skewKernel (fun x => a * f x) e = a * skewKernel f e := by
  unfold skewKernel
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun _ => mul_left_comm _ _ _

private theorem fixed_false_succ (k : ℕ) (e : ℤ) :
    fixedHitMass false (k+1) e = ENNReal.ofReal b * fixedHitMass true k e := by
  rw [fixedHitMass_succ]
  simp only [Bool.false_eq_true, if_false, add_zero, Bool.not_false]
  rw [ENNReal.tsum_mul_right, removal_weight_sum]

private theorem fixed_true_succ (k : ℕ) (e : ℤ) :
    fixedHitMass true (k+1) e = skewKernel (fixedHitMass false k) e := by
  rw [fixedHitMass_succ]
  simp only [if_true, Bool.not_true, skewKernel, add_assoc]

/-- Iterate the unnormalized skew removal kernel starting at the direct terminal. -/
private noncomputable def skewIterate : ℕ → ℤ → ℝ≥0∞
  | 0 => fixedHitMass false 0
  | k+1 => skewKernel (skewIterate k)

private theorem fixed_false_even (r : ℕ) (e : ℤ) :
    fixedHitMass false (2*r) e = ENNReal.ofReal b ^ r * skewIterate r e := by
  induction r generalizing e with
  | zero => simp [skewIterate]
  | succ r ih =>
    have h : 2*(r+1) = (2*r+1)+1 := by omega
    rw [h, fixed_false_succ, fixed_true_succ]
    have hf : fixedHitMass false (2*r) =
        fun x => ENNReal.ofReal b ^ r * skewIterate r x := funext ih
    rw [hf, skewKernel_mul, pow_succ]
    simp only [skewIterate]
    ac_rfl

/-- The two direct-terminal patterns for r+1 skew discards combine to the
coefficient b^r(1+b) against the unnormalized skew-iterate mass. -/
private theorem direct_patterns_succ (r : ℕ) (e : ℤ) :
    fixedHitMass true (2*r+1) e + fixedHitMass false (2*(r+1)) e =
      ENNReal.ofReal b ^ r * (1 + ENNReal.ofReal b) * skewIterate (r+1) e := by
  rw [fixed_true_succ (2*r) e, fixed_false_even (r+1) e]
  have hf : fixedHitMass false (2*r) =
      fun x => ENNReal.ofReal b ^ r * skewIterate r x := funext (fixed_false_even r)
  rw [hf, skewKernel_mul, pow_succ, mul_add, add_mul, mul_one]
  simp only [skewIterate]

private theorem b_pos_local : 0 < b := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  unfold b
  nlinarith

private noncomputable def normalizedSkewKernel (f : ℤ → ℝ≥0∞) (e : ℤ) : ℝ≥0∞ :=
  ∑' c : Removal, ENNReal.ofReal (rho ^ (c.1 + 1) / b) * f (e + (c.1 : ℤ) + 1)

private theorem skewKernel_eq_normalized (f : ℤ → ℝ≥0∞) (e : ℤ) :
    skewKernel f e = ENNReal.ofReal b * normalizedSkewKernel f e := by
  unfold skewKernel normalizedSkewKernel
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro c
  rw [← mul_assoc, ← ENNReal.ofReal_mul b_pos_local.le]
  have h : b * (rho ^ (c.1 + 1) / b) = rho ^ (c.1 + 1) := by
    field_simp [ne_of_gt b_pos_local]
  rw [h]

noncomputable def normalizedSkewIterate : ℕ → ℤ → ℝ≥0∞
  | 0 => fixedHitMass false 0
  | k+1 => normalizedSkewKernel (normalizedSkewIterate k)

private theorem skewIterate_eq_normalized (k : ℕ) (e : ℤ) :
    skewIterate k e = ENNReal.ofReal b ^ k * normalizedSkewIterate k e := by
  induction k generalizing e with
  | zero => simp [skewIterate, normalizedSkewIterate]
  | succ k ih =>
    change skewKernel (skewIterate k) e =
      ENNReal.ofReal b ^ (k+1) * normalizedSkewKernel (normalizedSkewIterate k) e
    have hf : skewIterate k =
        fun x => ENNReal.ofReal b ^ k * normalizedSkewIterate k x := funext ih
    rw [hf]
    calc
      _ = ENNReal.ofReal b ^ k * skewKernel (normalizedSkewIterate k) e := by
        unfold skewKernel
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun _ => mul_left_comm _ _ _
      _ = _ := by rw [skewKernel_eq_normalized, pow_succ, mul_assoc]

/-- The normalized coefficient for r+1 skew discards is b^(2r+1)(1+b). -/
private theorem direct_patterns_succ_normalized (r : ℕ) (e : ℤ) :
    fixedHitMass true (2*r+1) e + fixedHitMass false (2*(r+1)) e =
      ENNReal.ofReal b ^ (2*r+1) * (1 + ENNReal.ofReal b) *
        normalizedSkewIterate (r+1) e := by
  rw [direct_patterns_succ, skewIterate_eq_normalized]
  have h : 2*r+1 = r+(r+1) := by omega
  rw [h, pow_add (ENNReal.ofReal b) r (r + 1)]
  ac_rfl

private abbrev OccupiedTerminal (e : ℤ) :=
  Σ n : ℕ, {π : Indecomposable false (n + 1) // hitsDiagonal π.val.val e}

private theorem occupiedTerminal_weight_sum (e : ℤ) :
    (∑' z : OccupiedTerminal e, ENNReal.ofReal (rho ^ (z.1 + 1))) =
      ENNReal.ofReal (rawOccupation e) := by
  classical
  have hrho : 0 ≤ rho := by unfold rho; exact sq_nonneg _
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have cast (n : ℕ) :
      (Nat.card {π : Indecomposable false (n + 1) // hitsDiagonal π.val.val e} : ℝ≥0∞) *
          ENNReal.ofReal (rho ^ (n + 1)) =
      ENNReal.ofReal (rho ^ (n + 1) * (occupiedCount (n + 1) e : ℝ)) := by
    change _ = ENNReal.ofReal (rho ^ (n + 1) *
      (Nat.card {π : Indecomposable false (n + 1) // hitsDiagonal π.val.val e} : ℝ))
    rw [ENNReal.ofReal_mul (pow_nonneg hrho _), ENNReal.ofReal_natCast, mul_comm]
  simp_rw [cast]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (pow_nonneg hrho (n + 1)) (Nat.cast_nonneg _))
    (actual_occupation_subsolution_comparison.2.2.2.1 e)).symm

/-- The direct zero-discard part of the recurrence uses raw, not normalized,
occupation. Count the actual occupied terminal shapes by length. -/
private theorem fixedHitMass_false_zero (e : ℤ) :
    fixedHitMass false 0 e = ENNReal.ofReal (rawOccupation e) := by
  classical
  calc
    fixedHitMass false 0 e =
        ∑' z : OccupiedTerminal e, ENNReal.ofReal (rho ^ (z.1 + 1)) := by
      unfold fixedHitMass
      simp only [Fixed.decode, hit, Fixed.size, eq_self, true_and]
      change (∑' c : Σ n : ℕ, Indecomposable false (n + 1),
        if hitsDiagonal c.2.val.val e then ENNReal.ofReal (rho ^ (c.1 + 1)) else 0) = _
      rw [ENNReal.tsum_sigma', ENNReal.tsum_sigma']
      apply tsum_congr
      intro n
      change (∑' c : Indecomposable false (n + 1),
          if hitsDiagonal c.val.val e then ENNReal.ofReal (rho ^ (n + 1)) else 0) =
        ∑' c : {π : Indecomposable false (n + 1) | hitsDiagonal π.val.val e},
          ENNReal.ofReal (rho ^ (n + 1))
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
        (tsum_subtype {c : Indecomposable false (n + 1) | hitsDiagonal c.val.val e}
          (fun _ => ENNReal.ofReal (rho ^ (n + 1)))).symm
    _ = _ := occupiedTerminal_weight_sum e

/-- The wrong parity leaves a skew terminal, which cannot hit. -/
private theorem wrong_parity (r : ℕ) :
    (∀ e, fixedHitMass true (2*r) e = 0) ∧
      (∀ e, fixedHitMass false (2*r+1) e = 0) := by
  have direct_step (k : ℕ) (h : ∀ e, fixedHitMass true k e = 0) :
      ∀ e, fixedHitMass false (k+1) e = 0 := by
    intro e
    rw [fixedHitMass_succ]
    simp [h]
  induction r with
  | zero =>
    have base : ∀ e, fixedHitMass true (2*0) e = 0 := by
      intro e
      classical
      unfold fixedHitMass
      simp [Fixed.decode, hit]
    exact ⟨base, direct_step _ base⟩
  | succ r ih =>
    have heven : ∀ e, fixedHitMass true (2*(r+1)) e = 0 := by
      intro e
      have hidx : 2*(r+1) = (2*r+1)+1 := by omega
      rw [hidx, fixedHitMass_succ]
      simp [ih.2]
    exact ⟨heven, direct_step _ heven⟩

private theorem hitMassAtCount_even (r : ℕ) (e : ℤ) :
    hitMassAtCount e (2*r) = fixedHitMass false (2*r) e := by
  simp [hitMassAtCount, Fintype.sum_bool, (wrong_parity r).1]

private theorem hitMassAtCount_odd (r : ℕ) (e : ℤ) :
    hitMassAtCount e (2*r+1) = fixedHitMass true (2*r+1) e := by
  simp [hitMassAtCount, Fintype.sum_bool, (wrong_parity r).2]

/-- Actual hazard as the raw zero term and the normalized positive-count
series. Occupied-mass or discrepancy-tail premises are not asserted here. -/
theorem nextHazard_eq_normalized_series (e : ℤ) :
    nextHazard e = ENNReal.ofReal (rawOccupation e) +
      ∑' r : ℕ, ENNReal.ofReal b ^ (2*r+1) * (1 + ENNReal.ofReal b) *
        normalizedSkewIterate (r+1) e := by
  rw [nextHazard_eq_tsum_hitMassAtCount, tsum_eq_zero_add' ENNReal.summable]
  have hz : hitMassAtCount e 0 = ENNReal.ofReal (rawOccupation e) :=
    (hitMassAtCount_even 0 e).trans (fixedHitMass_false_zero e)
  rw [hz]
  congr 1
  have split := tsum_even_add_odd (f := fun k : ℕ => hitMassAtCount e (k+1))
    ENNReal.summable ENNReal.summable
  rw [← split, ← ENNReal.tsum_add]
  apply tsum_congr
  intro r
  have hidx : (2*r+1)+1 = 2*(r+1) := by omega
  rw [hidx, hitMassAtCount_odd, hitMassAtCount_even, direct_patterns_succ_normalized]

end D5.S1.Words.Patterns.Separable.EndpointCycleHazard
