/- GID: D5/S3/Arith/Robin/PriceRecord/CanonicalRecordPowerDefect
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CanonicalRecordPowerDefect
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Complete defect bounds for canonical strict records at real references. -/
import D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
import D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceGeometry
import Mathlib.Tactic

/-! Bounds for the higher inventory and the complete first-layer loss of a strict record. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect

open Finset Real
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization (FullRecord)
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open D5.S3.Arith.Robin.PriceRecord.ActualHigherMassResponse

/-- Total logarithmic weight of the higher coordinates present in exactly one
of the actual and reference inventories. -/
def higherInventoryMismatch (X : ℝ) (n : ℕ) : ℝ :=
  ∑ c ∈ (coordinates n \ coordinates (strictInteger (referencePrice X))) ∪
      (coordinates (strictInteger (referencePrice X)) \ coordinates n),
    coordinateWeight c

private theorem threshold_bounds {X : ℝ} (hX : exp 4 ≤ X) :
    16 < X ∧ 4 ≤ log X ∧ exp 2 ≤ X := by
  have he1 : 2 < exp 1 := by
    have hh := add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have he2 : exp (2 : ℝ) = exp 1 ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    ring
  have he2lo : 4 < exp 2 := by
    rw [he2]
    nlinarith [sq_nonneg (exp 1 - 2)]
  have he4 : exp (4 : ℝ) = exp 2 ^ 2 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, exp_add]
    ring
  have he4lo : 16 < exp 4 := by
    rw [he4]
    nlinarith [sq_nonneg (exp 2 - 4)]
  have hX0 : 0 < X := (exp_pos 4).trans_le hX
  exact ⟨he4lo.trans_le hX, (le_log_iff_exp_le hX0).mpr hX,
    (exp_le_exp.mpr (by norm_num : (2 : ℝ) ≤ 4)).trans hX⟩

/- A scalar proof, with no prime-distribution input. The deliberately coarse
   numerator 1/(X+2) is sufficient for the coefficient 3. -/
private theorem deterministic_cutoff_bracket {X : ℝ} (hX : exp 4 ≤ X) :
    0 < firstLayerPrice (X + 1) ∧
    (1 - 3 / X) * referencePrice X ≤ firstLayerPrice (X + 1) ∧
    firstLayerPrice (X + 1) < referencePrice X := by
  obtain ⟨hX16, hL4, _⟩ := threshold_bounds hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hL0 : 0 < log X := by linarith
  have hN0 : 0 < X + 1 := by linarith
  have hLN0 : 0 < log (X + 1) := log_pos (by linarith)
  have hinv : 0 < 1 / X := one_div_pos.mpr hX0
  have hinvN : 0 < 1 / (X + 1) := one_div_pos.mpr hN0
  have hpos : 0 < firstLayerPrice (X + 1) :=
    div_pos (log_pos (by linarith)) hLN0
  have hloghi : log (1 + 1 / X) < 1 / X := by
    have hh := log_lt_sub_one_of_pos (show 0 < 1 + 1 / X by positivity)
      (show 1 + 1 / X ≠ 1 by linarith)
    linarith only [hh]
  have hmul : X * (1 + 1 / X) = X + 1 := by
    field_simp [hX0.ne']
  have hlogN : log (X + 1) ≤ log X + 1 / X := by
    rw [← hmul, log_mul hX0.ne' (by positivity : 1 + 1 / X ≠ 0)]
    linarith only [hloghi]
  have hrat : 2 * (1 / (X + 1)) / (1 / (X + 1) + 2) =
      2 / (2 * X + 3) := by
    field_simp [hN0.ne', (show 1 / (X + 1) + 2 ≠ 0 by positivity),
      (show 2 * X + 3 ≠ 0 by linarith)]
    ring
  have hnum : 1 / (X + 2) ≤ log (1 + 1 / (X + 1)) := by
    have hh := lt_log_one_add_of_pos hinvN
    rw [hrat] at hh
    have hc : 1 / (X + 2) ≤ 2 / (2 * X + 3) := by
      apply (div_le_div_iff₀ (by linarith : 0 < X + 2)
        (by linarith : 0 < 2 * X + 3)).mpr
      linarith
    exact hc.trans hh.le
  let a := (1 - 3 / X) * referencePrice X
  have h3 : 3 / X < 1 := (div_lt_one hX0).mpr (by linarith)
  have ha : 0 ≤ a := by
    exact mul_nonneg (by linarith : 0 ≤ 1 - 3 / X) (reference_price_pos hX1).le
  have hproduct : a * (log X + 1 / X) ≤ 1 / (X + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < X + 2)).mpr
    have hid : a * (log X + 1 / X) * (X + 2) =
        ((X - 3) * (X + 2) * (X * log X + 1)) / (X ^ 3 * log X) := by
      dsimp [a, referencePrice]
      field_simp [hX0.ne', hL0.ne']
    rw [hid]
    apply (div_le_one (by positivity : 0 < X ^ 3 * log X)).mpr
    nlinarith [mul_nonneg (sq_nonneg X) (show 0 ≤ log X - 1 by linarith),
      mul_nonneg hX0.le hL0.le]
  have hlower : a ≤ firstLayerPrice (X + 1) := by
    apply (le_div_iff₀ hLN0).mpr
    exact (mul_le_mul_of_nonneg_left hlogN ha).trans (hproduct.trans hnum)
  have hprice : firstLayerPrice X < referencePrice X := by
    change log (1 + 1 / X) / log X < 1 / (X * log X)
    rw [← div_div]
    exact div_lt_div_of_pos_right hloghi hL0
  exact ⟨hpos, hlower,
    (firstLayerPrice_strictAnti hX1 (by linarith : 1 < X + 1)
      (by linarith : X < X + 1)).trans hprice⟩

/- Strict support at every real reference; p = X+1 is excluded literally. -/
private theorem deterministic_first_count {X : ℝ} (hX : exp 4 ≤ X)
    {p : ℕ} (hp : p.Prime) :
    1 ≤ (strictInteger (firstLayerPrice (X + 1))).factorization p ↔
      (p : ℝ) < X + 1 := by
  have hX16 := (threshold_bounds hX).1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hN1 : 1 < X + 1 := by linarith
  rw [strict_layer_iff (deterministic_cutoff_bracket hX).1 hp (by norm_num),
    golden_layer_marginal_one_eq_log_one_add_inv hp]
  change firstLayerPrice (X + 1) < firstLayerPrice (p : ℝ) ↔ (p : ℝ) < X + 1
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (firstLayerPrice_strictAnti.antitoneOn hN1 hp1
      (le_of_not_gt hn))) h
  · exact firstLayerPrice_strictAnti hp1 hN1

/- Original objective and minimal optimizer, with no prime reference premise. -/
private theorem deterministic_record_support {X : ℝ} (hX : exp 4 ≤ X) :
    let mu := firstLayerPrice (X + 1)
    let m := strictInteger mu
    0 < mu ∧ 2 ≤ m ∧ FullRecord m mu ∧
      (∀ p : ℕ, p ∈ m.primeFactors ↔ p.Prime ∧ (p : ℝ) < X + 1) := by
  classical
  let mu := firstLayerPrice (X + 1)
  let m := strictInteger mu
  have hmu : 0 < mu := (deterministic_cutoff_bracket hX).1
  have hm : 1 ≤ m := strictInteger_pos hmu
  have h2 : 1 ≤ m.factorization 2 :=
    (deterministic_first_count hX Nat.prime_two).mpr (by
      change (2 : ℝ) < X + 1
      have := (threshold_bounds hX).1
      linarith)
  have h2dvd : 2 ∣ m := (Nat.prime_two.dvd_iff_one_le_factorization
    (by omega : m ≠ 0)).mpr h2
  have hm2 : 2 ≤ m := Nat.le_of_dvd (by omega : 0 < m) h2dvd
  have hrecord : FullRecord m mu := by
    intro n hn hnm
    have hopt := (strictInteger_spec hmu).2.2.1
    have hle := hopt n (by omega : 1 ≤ n)
    by_contra! hnot
    have heq := le_antisymm hle hnot
    have hnopt : IsGoldenResourceOptimal mu n := by
      intro k hk
      rw [heq]
      exact hopt k hk
    have hdvd := (strictInteger_spec hmu).2.2.2 n (by omega) hnopt
    exact (Nat.le_of_dvd hn hdvd).not_gt hnm
  refine ⟨hmu, hm2, hrecord, ?_⟩
  intro p
  have hf : p ∈ m.primeFactors ↔ 1 ≤ m.factorization p := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  constructor
  · intro hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact ⟨hprime, (deterministic_first_count hX hprime).mp (hf.mp hp)⟩
  · rintro ⟨hp, hpX⟩
    exact hf.mpr ((deterministic_first_count hX hp).mpr hpX)

private theorem log_reciprocal_endpoint_bounds {X : ℝ} (hX : 0 < X) :
    0 < 1 / X - log (1 + 1 / X) ∧
      1 / X - log (1 + 1 / X) < 1 / (2 * X ^ 2) := by
  let x := 1 / X
  have hx : 0 < x := one_div_pos.mpr hX
  have hhi : log (1 + x) < x := by
    have hh := log_lt_sub_one_of_pos (show 0 < 1 + x by linarith)
      (show 1 + x ≠ 1 by linarith)
    linarith only [hh]
  have hquad : x - x ^ 2 / 2 ≤ 2 * x / (x + 2) := by
    apply (le_div_iff₀ (show 0 < x + 2 by linarith)).mpr
    nlinarith only [mul_nonneg (sq_nonneg x) hx.le]
  have hlo := hquad.trans_lt (lt_log_one_add_of_pos hx)
  have hsquare : x ^ 2 / 2 = 1 / (2 * X ^ 2) := by
    dsimp [x]
    field_simp [hX.ne']
  change 0 < x - log (1 + x) ∧ x - log (1 + x) < _
  constructor
  · linarith only [hhi]
  · rw [← hsquare]
    linarith only [hlo]

/- Complete weighted inventory estimate. The surrounding inventories are
   canonical, but the mismatch being bounded is the literal full mismatch. -/
private theorem deterministic_inventory_bound {X : ℝ} (hX : exp 4 ≤ X) :
    let mu := firstLayerPrice (X + 1)
    let m := strictInteger mu
    higherInventoryMismatch X m ≤ 800 * log X ^ 2 := by
  classical
  obtain ⟨hX16, hL4, hXe2⟩ := threshold_bounds hX
  obtain ⟨hmu, hlower, hupper⟩ := deterministic_cutoff_bracket hX
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hq := reference_price_pos hX1
  let s := 3 / X
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ≤ 1 / 2 := by
    dsimp [s]
    apply (div_le_iff₀ hX0).mpr
    linarith
  have hlo : 0 < (1 - s) * referencePrice X := mul_pos (by linarith) hq
  have hhi : 0 < (1 + s) * referencePrice X := mul_pos (by linarith) hq
  let A := coordinates (strictInteger (firstLayerPrice (X + 1)))
  let B := coordinates (strictInteger (referencePrice X))
  let C := coordinates (strictInteger ((1 - s) * referencePrice X))
  let E := coordinates (strictInteger ((1 + s) * referencePrice X))
  have hBA : B ⊆ A := canonical_coordinates_antitone hmu hq hupper.le
  have hAC : A ⊆ C := canonical_coordinates_antitone hlo hmu hlower
  have hEB : E ⊆ B := canonical_coordinates_antitone hq hhi (by
    nlinarith [mul_nonneg hs.le hq.le])
  have hEC : E ⊆ C := fun c hc => hAC (hBA (hEB hc))
  have hdiff : B \ A = ∅ := sdiff_eq_empty_iff_subset.mpr hBA
  have hM : higherInventoryMismatch X (strictInteger (firstLayerPrice (X + 1))) =
      ∑ c ∈ A \ B, coordinateWeight c := by
    change (∑ c ∈ (A \ B) ∪ (B \ A), coordinateWeight c) = _
    rw [hdiff, union_empty]
  have hsub : A \ B ⊆ C \ E := by
    intro c hc
    obtain ⟨hcA, hcB⟩ := mem_sdiff.mp hc
    exact mem_sdiff.mpr ⟨hAC hcA, fun hcE => hcB (hEB hcE)⟩
  have hsum : (∑ c ∈ A \ B, coordinateWeight c) ≤
      ∑ c ∈ C \ E, coordinateWeight c := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro c hc _
    have hp := ((canonical_mem hlo).mp (mem_sdiff.mp hc).1).1
    exact hp.log_pos.le
  have hmass : (∑ c ∈ C \ E, coordinateWeight c) =
      higherMass (strictInteger ((1 - s) * referencePrice X)) -
        higherMass (strictInteger ((1 + s) * referencePrice X)) := by
    simpa only [higherMass_eq_coordinate_sum, coordinateWeight] using
      (sum_sdiff_eq_sub (f := fun c : ℕ × ℕ => log (c.1 : ℝ)) hEC)
  have hresponse := (actual_higher_mass_response hXe2 hs hs2).2
  have hsqrt : sqrt X ≤ X := by
    have hh : 1 ≤ sqrt X := (le_sqrt (by norm_num) hX0.le).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_right hh (sqrt_nonneg X)
    rw [one_mul, ← pow_two, sq_sqrt hX0.le] at hm
    exact hm
  have hsmall : s * sqrt X * log X ≤ log X ^ 2 := by
    have hnum : 3 * sqrt X ≤ X * log X := by
      nlinarith [mul_nonneg hX0.le (show 0 ≤ log X - 3 by linarith)]
    have hh : s * sqrt X ≤ log X := by
      dsimp [s]
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hX0).mpr (by nlinarith only [hnum])
    nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ log X by linarith)]
  change higherInventoryMismatch X (strictInteger (firstLayerPrice (X + 1))) ≤ _
  rw [hM]
  exact hsum.trans (hmass.le.trans (hresponse.trans (by nlinarith only [hsmall])))

/- This is the missing complete-loss inference: use the literal dual identity
   on ALL coordinates of m. At the reference price, canonical coordinates
   have zero loss; each extra coordinate has marginal in (mu,q], including
   the strict-reference tie case marginal=q. -/
private theorem one_sided_complete_loss {X mu : ℝ} (hX : 1 < X)
    (hmu : 0 < mu) (hmuq : mu ≤ referencePrice X) :
    let m := strictInteger mu
    0 ≤ actualDefect X m - completeFirstLayerLoss X m ∧
      actualDefect X m - completeFirstLayerLoss X m ≤
        (referencePrice X - mu) * higherInventoryMismatch X m := by
  classical
  let m := strictInteger mu
  let A := coordinates m
  let B := coordinates (strictInteger (referencePrice X))
  let q := referencePrice X
  let f := fun c : ℕ × ℕ =>
    max (coordinateGain c - q * coordinateWeight c) 0 -
      (coordinateGain c - q * coordinateWeight c)
  have hq : 0 < q := reference_price_pos hX
  have hBA : B ⊆ A := canonical_coordinates_antitone hmu hq hmuq
  have hprime (c : ℕ × ℕ) (hc : c ∈ A) : c.1.Prime ∧ 2 ≤ c.2 :=
    ⟨((canonical_mem hmu).mp hc).1, ((canonical_mem hmu).mp hc).2.1⟩
  have hU : B ∪ A ⊆ A := by
    intro c hc
    exact (mem_union.mp hc).elim (fun h => hBA h) id
  have hid := literal_loss_identity hX (strictInteger_pos hmu) A hprime hU
  have hsum : actualDefect X m - completeFirstLayerLoss X m = ∑ c ∈ A, f c := by
    rw [hid]
    change (∑ c ∈ A, max (coordinateGain c - q * coordinateWeight c) 0) -
      (∑ c ∈ A, coordinateGain c) + q * higherMass m = _
    rw [higherMass_eq_coordinate_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro c _
    dsimp [f, coordinateWeight]
    ring
  have hzero (c : ℕ × ℕ) (hc : c ∈ B) : f c = 0 := by
    obtain ⟨hp, _, hg⟩ := (canonical_mem hq).mp hc
    have hh : 0 < coordinateGain c - q * coordinateWeight c :=
      (positive_coordinate hp).mpr hg
    dsimp [f]
    rw [max_eq_left hh.le, sub_self]
  have hsdiff : (∑ c ∈ A, f c) = ∑ c ∈ A \ B, f c := by
    symm
    apply sum_subset sdiff_subset
    intro c hc hnot
    apply hzero
    by_contra hcB
    exact hnot (mem_sdiff.mpr ⟨hc, hcB⟩)
  have hdiff : B \ A = ∅ := sdiff_eq_empty_iff_subset.mpr hBA
  have hM : higherInventoryMismatch X m = ∑ c ∈ A \ B, coordinateWeight c := by
    change (∑ c ∈ (A \ B) ∪ (B \ A), coordinateWeight c) = _
    rw [hdiff, union_empty]
  have hpoint (c : ℕ × ℕ) (hc : c ∈ A \ B) :
      f c ≤ (q - mu) * coordinateWeight c := by
    obtain ⟨hcA, hcB⟩ := mem_sdiff.mp hc
    obtain ⟨hp, hj, hgm⟩ := (canonical_mem hmu).mp hcA
    have hgq : goldenLayerMarginal c.1 c.2 ≤ q := by
      apply le_of_not_gt
      intro hh
      exact hcB ((canonical_mem hq).mpr ⟨hp, hj, hh⟩)
    have hz : coordinateGain c - q * coordinateWeight c ≤ 0 := by
      dsimp [coordinateGain, coordinateWeight]
      nlinarith [mul_nonneg hp.log_pos.le (sub_nonneg.mpr hgq)]
    dsimp [f]
    rw [max_eq_right hz]
    dsimp [coordinateGain, coordinateWeight]
    nlinarith [mul_le_mul_of_nonneg_right hgm.le hp.log_pos.le]
  constructor
  · rw [hsum]
    exact sum_nonneg (fun c _ => sub_nonneg.mpr (le_max_left _ _))
  · rw [hsum, hsdiff, hM, mul_sum]
    exact sum_le_sum hpoint

/- At an unoccupied first coordinate the reference gain cannot be positive:
   mu < q, and the strict specification excludes marginal = mu as well. -/
private theorem unoccupied_first_loss_zero {X : ℝ} (hX : exp 4 ≤ X)
    {p : ℕ} (hp : p.Prime)
    (hv : ¬ 1 ≤ (strictInteger (firstLayerPrice (X + 1))).factorization p) :
    layerLoss X (strictInteger (firstLayerPrice (X + 1))) p 1 = 0 := by
  obtain ⟨hmu, _, hmuq⟩ := deterministic_cutoff_bracket hX
  have hgm : goldenLayerMarginal p 1 ≤ firstLayerPrice (X + 1) := by
    apply le_of_not_gt
    intro hg
    exact hv ((strict_layer_iff hmu hp (by norm_num : 1 ≤ (1 : ℕ))).mpr hg)
  have hraw : rawLayerMargin X p 1 ≤ 0 := by
    unfold rawLayerMargin
    exact mul_nonpos_of_nonneg_of_nonpos hp.log_pos.le (by linarith)
  simp only [layerLoss, ite_eq_right hv, max_eq_right hraw, sub_self]

/- The actual public cutoff says X-rho is positive and less than 1/2.
   Nonzero first loss is strictly above rho (the rho equality has zero loss).
   In particular it lies in (X-1/2, X+1), hence also in (X-1, X+1). -/
private theorem first_loss_localized {X : ℝ} (hX : exp 4 ≤ X)
    {p : ℕ} (hp : p.Prime)
    (hnz : layerLoss X (strictInteger (firstLayerPrice (X + 1))) p 1 ≠ 0) :
    X - 1 / 2 < (p : ℝ) ∧ (p : ℝ) < X + 1 := by
  have hX16 := (threshold_bounds hX).1
  have hv : 1 ≤ (strictInteger (firstLayerPrice (X + 1))).factorization p := by
    by_contra hv
    exact hnz (unoccupied_first_loss_zero hX hp hv)
  have hpX := (deterministic_first_count hX hp).mp hv
  obtain ⟨rho, hr11, _, hhalf, hroot, _⟩ :=
    half_shift_cutoff (by linarith : (12 : ℝ) < X)
  have hr1 : 1 < rho := by linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hroot' : firstLayerPrice rho = referencePrice X := by
    simpa only [price, referencePrice] using hroot
  have hrp : rho < (p : ℝ) := by
    by_contra hn
    have hprice : referencePrice X ≤ firstLayerPrice (p : ℝ) := by
      rw [← hroot']
      exact firstLayerPrice_strictAnti.antitoneOn hp1 hr1 (le_of_not_gt hn)
    have hmargin : 0 ≤ rawLayerMargin X p 1 := by
      unfold rawLayerMargin
      apply mul_nonneg hp.log_pos.le
      rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
      change 0 ≤ firstLayerPrice (p : ℝ) - referencePrice X
      exact sub_nonneg.mpr hprice
    exact hnz (by simp only [layerLoss, ite_eq_left hv, max_eq_left hmargin, sub_self])
  exact ⟨by linarith only [hhalf, hrp], hpX⟩

/- At most two NATURAL integers in an open interval of length two.
   No parity, prime-gap or prime-distribution estimate occurs. -/
private theorem two_integer_card (S : Finset ℕ) (X : ℝ)
    (hS : ∀ p ∈ S, X - 1 < (p : ℝ) ∧ (p : ℝ) < X + 1) :
    S.card ≤ 2 := by
  have hgap (p q : ℕ) (hp : p ∈ S) (hq : q ∈ S) : p < q + 2 := by
    have hh : (p : ℝ) < (q : ℝ) + 2 := by
      linarith only [(hS p hp).2, (hS q hq).1]
    exact_mod_cast hh
  by_contra hn
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    two_lt_card_iff.mp (by omega : 2 < S.card)
  have hab' := hgap a b ha hb
  have hba' := hgap b a hb ha
  have hac' := hgap a c ha hc
  have hca' := hgap c a hc ha
  have hbc' := hgap b c hb hc
  have hcb' := hgap c b hc hb
  omega

private theorem losing_first_coordinate_bound {X : ℝ} (hX : exp 4 ≤ X)
    {p : ℕ} (hp : p.Prime)
    (hnz : layerLoss X (strictInteger (firstLayerPrice (X + 1))) p 1 ≠ 0) :
    layerLoss X (strictInteger (firstLayerPrice (X + 1))) p 1 ≤ 9 / (4 * X ^ 2) := by
  obtain ⟨hX16, hL4, _⟩ := threshold_bounds hX
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < log X := by linarith
  have hN0 : 0 < X + 1 := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpX := (first_loss_localized hX hp hnz).2
  have hv := (deterministic_first_count hX hp).mpr hpX
  have hnegative : rawLayerMargin X p 1 < 0 := by
    by_contra hn
    have hh : 0 ≤ rawLayerMargin X p 1 := le_of_not_gt hn
    exact hnz (by simp only [layerLoss, ite_eq_left hv, max_eq_left hh, sub_self])
  have hraw : rawLayerMargin X p 1 =
      log (1 + 1 / (p : ℝ)) - referencePrice X * log (p : ℝ) := by
    rw [rawLayerMargin, golden_layer_marginal_one_eq_log_one_add_inv hp]
    field_simp [hp.log_pos.ne']
  have hterm : layerLoss X (strictInteger (firstLayerPrice (X + 1))) p 1 =
      referencePrice X * log (p : ℝ) - log (1 + 1 / (p : ℝ)) := by
    rw [layerLoss, ite_eq_left hv, max_eq_right hnegative.le, hraw]
    ring
  have hloghi : log (1 + 1 / X) < 1 / X := by
    have hh := log_lt_sub_one_of_pos (show 0 < 1 + 1 / X by positivity)
      (show 1 + 1 / X ≠ 1 by have := one_div_pos.mpr hX0; linarith)
    linarith only [hh]
  have hmul : X * (1 + 1 / X) = X + 1 := by
    field_simp [hX0.ne']
  have hlogN : log (X + 1) ≤ log X + 1 / X := by
    rw [← hmul, log_mul hX0.ne' (by positivity : 1 + 1 / X ≠ 0)]
    linarith only [hloghi]
  have hlogp : log (p : ℝ) ≤ log X + 1 / X :=
    (log_le_log hp0 hpX.le).trans hlogN
  have hrat : 2 * (1 / (X + 1)) / (1 / (X + 1) + 2) =
      2 / (2 * X + 3) := by
    field_simp [hN0.ne', (show 1 / (X + 1) + 2 ≠ 0 by positivity),
      (show 2 * X + 3 ≠ 0 by linarith)]
    ring
  have hnum : 1 / (X + 2) ≤ log (1 + 1 / (X + 1)) := by
    have hh := lt_log_one_add_of_pos (one_div_pos.mpr hN0)
    rw [hrat] at hh
    have hc : 1 / (X + 2) ≤ 2 / (2 * X + 3) := by
      apply (div_le_div_iff₀ (by linarith : 0 < X + 2)
        (by linarith : 0 < 2 * X + 3)).mpr
      linarith
    exact hc.trans hh.le
  have hnumP : 1 / (X + 2) ≤ log (1 + 1 / (p : ℝ)) := by
    apply hnum.trans
    apply log_le_log (by positivity : 0 < 1 + 1 / (X + 1))
    have hh := one_div_le_one_div_of_le hp0 hpX.le
    linarith only [hh]
  have hq : 0 ≤ referencePrice X := (reference_price_pos (by linarith)).le
  have hscalar : referencePrice X * (log X + 1 / X) - 1 / (X + 2) =
      2 / (X * (X + 2)) + 1 / (X ^ 2 * log X) := by
    dsimp [referencePrice]
    field_simp [hX0.ne', hL0.ne', (show X + 2 ≠ 0 by linarith)]
    ring
  have hA : 2 / (X * (X + 2)) ≤ 2 / X ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (sq_pos_of_pos hX0)
      (by nlinarith : X ^ 2 ≤ X * (X + 2))
  have hB : 1 / (X ^ 2 * log X) ≤ 1 / (4 * X ^ 2) :=
    one_div_le_one_div_of_le (by positivity : 0 < 4 * X ^ 2)
      (by nlinarith [mul_le_mul_of_nonneg_left hL4 (sq_nonneg X)])
  have hsum : 2 / X ^ 2 + 1 / (4 * X ^ 2) = 9 / (4 * X ^ 2) := by
    field_simp [hX0.ne']
    ring
  rw [hterm]
  calc
    _ ≤ referencePrice X * (log X + 1 / X) - 1 / (X + 2) := by
      have hh := mul_le_mul_of_nonneg_left hlogp hq
      linarith only [hh, hnumP]
    _ = 2 / (X * (X + 2)) + 1 / (X ^ 2 * log X) := hscalar
    _ ≤ 2 / X ^ 2 + 1 / (4 * X ^ 2) := add_le_add hA hB
    _ = _ := hsum

/- The filtered set is precisely the nonzero summands of the ORIGINAL full
   finite union. It is not a cap imposed on lossPrimes or on the integer. -/
private theorem complete_first_loss_bound {X : ℝ} (hX : exp 4 ≤ X) :
    let m := strictInteger (firstLayerPrice (X + 1))
    (∀ p ∈ lossPrimes X m, layerLoss X m p 1 ≠ 0 →
      X - 1 / 2 < (p : ℝ) ∧ (p : ℝ) < X + 1) ∧
    0 ≤ completeFirstLayerLoss X m ∧ completeFirstLayerLoss X m ≤ 5 / X ^ 2 := by
  classical
  let m := strictInteger (firstLayerPrice (X + 1))
  let S := (lossPrimes X m).filter (fun p => layerLoss X m p 1 ≠ 0)
  have hprime (p : ℕ) (hp : p ∈ lossPrimes X m) : p.Prime := by
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hloc (p : ℕ) (hp : p ∈ lossPrimes X m) (hnz : layerLoss X m p 1 ≠ 0) :
      X - 1 / 2 < (p : ℝ) ∧ (p : ℝ) < X + 1 :=
    first_loss_localized hX (hprime p hp) hnz
  have hcard : S.card ≤ 2 := by
    apply two_integer_card S X
    intro p hp
    obtain ⟨hpmem, hnz⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := hloc p hpmem hnz
    exact ⟨by linarith only [hlo], hhi⟩
  have hsum : completeFirstLayerLoss X m = ∑ p ∈ S, layerLoss X m p 1 := by
    symm
    apply sum_subset (filter_subset _ _)
    intro p hp hnot
    by_contra hnz
    exact hnot (mem_filter.mpr ⟨hp, hnz⟩)
  have hX0 : 0 < X := (exp_pos 4).trans_le hX
  have hhalf : 2 * (9 / (4 * X ^ 2)) = (9 / 2) / X ^ 2 := by
    field_simp [hX0.ne']
    ring
  refine ⟨hloc, ?_, ?_⟩
  · unfold completeFirstLayerLoss
    exact sum_nonneg (fun p _ => layer_loss_nonneg X m p 1)
  · rw [hsum]
    calc
      _ ≤ ∑ _p ∈ S, 9 / (4 * X ^ 2) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpmem, hnz⟩ := mem_filter.mp hp
        exact losing_first_coordinate_bound hX (hprime p hpmem) hnz
      _ = (S.card : ℝ) * (9 / (4 * X ^ 2)) := by simp
      _ ≤ 2 * (9 / (4 * X ^ 2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = (9 / 2) / X ^ 2 := hhalf
      _ ≤ 5 / X ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num : (9 / 2 : ℝ) ≤ 5) (sq_nonneg X)

/-- Every real reference at least exp(4) supplies the deterministic ORIGINAL
strict record with complete power-scale defect. No integrality, primality,
prime distribution or clock-closeness hypothesis is present. -/
theorem canonical_record_power_defect (X : ℝ) (hX : exp 4 ≤ X) :
    let q := referencePrice X
    let mu := firstLayerPrice (X + 1)
    let m := strictInteger mu
    let M := higherInventoryMismatch X m
    let R := actualDefect X m - completeFirstLayerLoss X m
    let D := actualDefect X m
    0 < mu ∧ 2 ≤ m ∧ FullRecord m mu ∧
      (∀ p : ℕ, p ∈ m.primeFactors ↔ p.Prime ∧ (p : ℝ) < X + 1) ∧
      (1 - 3 / X) * q ≤ mu ∧ mu < q ∧
      M ≤ 800 * log X ^ 2 ∧
      0 ≤ R ∧ R ≤ 2400 * log X / X ^ 2 ∧
      (∀ p ∈ lossPrimes X m, layerLoss X m p 1 ≠ 0 →
        X - 1 / 2 < (p : ℝ) ∧ (p : ℝ) < X + 1) ∧
      0 ≤ completeFirstLayerLoss X m ∧ completeFirstLayerLoss X m ≤ 5 / X ^ 2 ∧
      0 ≤ D ∧ D ≤ (2400 * log X + 5) / X ^ 2 := by
  classical
  dsimp only
  let mu := firstLayerPrice (X + 1)
  let m := strictInteger mu
  obtain ⟨hX16, hL4, _⟩ := threshold_bounds hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hL0 : 0 < log X := by linarith
  obtain ⟨hmu, hm2, hrecord, hsupport⟩ := deterministic_record_support hX
  obtain ⟨_, hlow, hhigh⟩ := deterministic_cutoff_bracket hX
  have hM := deterministic_inventory_bound hX
  have hR := one_sided_complete_loss hX1 hmu hhigh.le
  have hM0 : 0 ≤ higherInventoryMismatch X m := by
    unfold higherInventoryMismatch
    apply sum_nonneg
    intro c hc
    have hp : c.1.Prime := by
      rcases mem_union.mp hc with hc | hc
      · exact (mem_coordinates.mp (mem_sdiff.mp hc).1).1
      · exact (mem_coordinates.mp (mem_sdiff.mp hc).1).1
    exact hp.log_pos.le
  have hgap : referencePrice X - mu ≤ (3 / X) * referencePrice X := by
    dsimp [mu]
    nlinarith only [hlow]
  have hbound : actualDefect X m - completeFirstLayerLoss X m ≤
      2400 * log X / X ^ 2 := by
    calc
      _ ≤ (referencePrice X - mu) * higherInventoryMismatch X m := hR.2
      _ ≤ ((3 / X) * referencePrice X) * higherInventoryMismatch X m :=
        mul_le_mul_of_nonneg_right hgap hM0
      _ ≤ ((3 / X) * referencePrice X) * (800 * log X ^ 2) :=
        mul_le_mul_of_nonneg_left hM (by dsimp [referencePrice]; positivity)
      _ = _ := by
        dsimp [referencePrice]
        field_simp [hX0.ne', hL0.ne']
        ring
  obtain ⟨hloc, hfirst0, hfirst5⟩ := complete_first_loss_bound hX
  have hD0 : 0 ≤ actualDefect X m := by linarith only [hR.1, hfirst0]
  have hDhi : actualDefect X m ≤ (2400 * log X + 5) / X ^ 2 := by
    rw [add_div]
    linarith only [hbound, hfirst5]
  exact ⟨hmu, hm2, hrecord, hsupport, hlow, hhigh, hM, hR.1, hbound,
    hloc, hfirst0, hfirst5, hD0, hDhi⟩

/-- At an integer reference, the complete first loss has only the possible
coordinate N. Composite N gives zero, and prime N gives the exact endpoint
loss. The original complete finite sum and strict endpoint convention remain. -/
theorem canonical_integer_first_loss (N : ℕ) (hN : exp 4 ≤ (N : ℝ)) :
    let mu := firstLayerPrice ((N : ℝ) + 1)
    let m := strictInteger mu
    completeFirstLayerLoss (N : ℝ) m =
      if N.Prime then 1 / (N : ℝ) - log (1 + 1 / (N : ℝ)) else 0 := by
  classical
  dsimp only
  let m := strictInteger (firstLayerPrice ((N : ℝ) + 1))
  have hprime (p : ℕ) (hp : p ∈ lossPrimes (N : ℝ) m) : p.Prime := by
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hzero (p : ℕ) (hp : p ∈ lossPrimes (N : ℝ) m) (hne : p ≠ N) :
      layerLoss (N : ℝ) m p 1 = 0 := by
    by_contra hnz
    obtain ⟨hlo, hhi⟩ := first_loss_localized hN (hprime p hp) hnz
    have hlowR : (N : ℝ) < (p : ℝ) + 1 := by linarith only [hlo]
    have hlowN : N < p + 1 := by exact_mod_cast hlowR
    have hhighN : p < N + 1 := by exact_mod_cast hhi
    omega
  by_cases hpN : N.Prime
  · rw [ite_eq_left hpN]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hpN.pos
    have hLN : 0 < log (N : ℝ) := hpN.log_pos
    have hv : 1 ≤ m.factorization N :=
      (deterministic_first_count hN hpN).mpr (by linarith)
    have hmem : N ∈ lossPrimes (N : ℝ) m := by
      apply mem_union_right
      have hf : N ∈ m.primeFactors ↔ m.factorization N ≠ 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact hf.mpr (by omega)
    have hraw : rawLayerMargin (N : ℝ) N 1 =
        log (1 + 1 / (N : ℝ)) - 1 / (N : ℝ) := by
      rw [rawLayerMargin, golden_layer_marginal_one_eq_log_one_add_inv hpN]
      dsimp [referencePrice]
      field_simp [hN0.ne', hLN.ne']
    have hnegative : rawLayerMargin (N : ℝ) N 1 < 0 := by
      rw [hraw]
      linarith only [(log_reciprocal_endpoint_bounds hN0).1]
    calc
      completeFirstLayerLoss (N : ℝ) m = layerLoss (N : ℝ) m N 1 := by
        unfold completeFirstLayerLoss
        exact sum_eq_single N hzero (fun hnot => (hnot hmem).elim)
      _ = _ := by
        rw [layerLoss, ite_eq_left hv, max_eq_right hnegative.le, hraw]
        ring
  · rw [ite_eq_right hpN]
    unfold completeFirstLayerLoss
    apply sum_eq_zero
    intro p hp
    apply hzero p hp
    intro heq
    subst p
    exact hpN (hprime N hp)

end D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect
