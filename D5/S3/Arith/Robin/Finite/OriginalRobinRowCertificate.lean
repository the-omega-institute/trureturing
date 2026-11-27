/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinRowCertificate
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Finite/OriginalRobinRowCertificate
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: A rational checker for original Robin intervals, with the verified Row 05 data. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinFiniteRows

/-! A rational checker at the original Robin row prices. The analytic
soundness lemmas are reused from the already verified native finite rows.
The row data are from Jonas Whidden's Robin1984 at
5ce18bf3487c68d9353276ef5811057f60d17808. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open Finset
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Weil.GronwallLowerEnvelope
open private layerRatio from D5.S3.Arith.Robin.Finite.RobinRow01
open private optimal_of_cuts fixed_price_interval sigma_roster
  from D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows
open private mantissa logLower logUpper cut_above cut_below row_factorization
  objectiveUpper objective_le endpoint_gap
  from D5.S3.Arith.Robin.Finite.OriginalRobinFiniteRows

def ratScale (x : ℚ) : ℕ := Nat.log2 (x.num.natAbs / x.den)

def ratMantissa (x : ℚ) (s : ℕ) : ℚ := x / 2 ^ s

def ratParameter (x : ℚ) : ℚ := (x - 1) / (x + 1)

def ratPartial (t : ℚ) : ℚ :=
  2 * ∑ j ∈ range 10, t ^ (2 * j + 1) / (2 * j + 1)

def ratLower (x : ℚ) (s : ℕ) : ℚ :=
  s * (6931471803 / 10000000000) + ratPartial (ratParameter (ratMantissa x s))

def ratUpper (x : ℚ) (s : ℕ) : ℚ :=
  let t := ratParameter (ratMantissa x s)
  s * (6931471808 / 10000000000) + ratPartial t + 2 * t ^ 21 / (21 * (1 - t ^ 2))

def ratLayerRatio (p k : ℕ) : ℚ :=
  (1 - (p : ℚ)⁻¹ ^ (k + 1)) / (1 - (p : ℚ)⁻¹ ^ k)

private theorem cast_mantissa (x : ℚ) (s : ℕ) :
    (ratMantissa x s : ℝ) = mantissa (x : ℝ) s := by
  unfold ratMantissa mantissa
  push_cast
  rfl

private theorem cast_lower (x : ℚ) (s : ℕ) :
    (ratLower x s : ℝ) = logLower (x : ℝ) s := by
  unfold ratLower ratPartial ratParameter logLower atanhPartial atanhParameter
  simp [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, cast_mantissa]

private theorem cast_upper (x : ℚ) (s : ℕ) :
    (ratUpper x s : ℝ) = logUpper (x : ℝ) s := by
  unfold ratUpper ratPartial ratParameter logUpper atanhPartial atanhParameter
  simp [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, cast_mantissa]

private theorem cast_layer_ratio (p k : ℕ) :
    (ratLayerRatio p k : ℝ) = layerRatio p k := by
  unfold ratLayerRatio layerRatio
  push_cast
  rfl

def Normalized (x : ℚ) (s : ℕ) : Prop :=
  1 ≤ ratMantissa x s ∧ ratMantissa x s < 2

instance (x : ℚ) (s : ℕ) : Decidable (Normalized x s) := by
  unfold Normalized
  infer_instance

private theorem Normalized.sound {x : ℚ} {s : ℕ} (h : Normalized x s) :
    1 ≤ mantissa (x : ℝ) s ∧ mantissa (x : ℝ) s < 2 := by
  rw [← cast_mantissa]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

def TopCheck (q : ℚ) (p k : ℕ) : Prop :=
  2 ≤ p ∧ Normalized (p : ℚ) (Nat.log2 p) ∧ Normalized (ratLayerRatio p k) 0 ∧
    q * ratUpper p (Nat.log2 p) < ratLower (ratLayerRatio p k) 0

def NextCheck (q : ℚ) (p k : ℕ) : Prop :=
  2 ≤ p ∧ Normalized (p : ℚ) (Nat.log2 p) ∧ Normalized (ratLayerRatio p k) 0 ∧
    ratUpper (ratLayerRatio p k) 0 < q * ratLower p (Nat.log2 p)

instance (q : ℚ) (p k : ℕ) : Decidable (TopCheck q p k) := by
  unfold TopCheck
  infer_instance

instance (q : ℚ) (p k : ℕ) : Decidable (NextCheck q p k) := by
  unfold NextCheck
  infer_instance

private theorem TopCheck.sound {q : ℚ} {p k : ℕ} (hq : 0 < (q : ℝ))
    (h : TopCheck q p k) : (q : ℝ) < goldenLayerMarginal p k := by
  have hp := h.2.1.sound
  have hr := h.2.2.1.sound
  rw [Rat.cast_natCast] at hp
  rw [cast_layer_ratio] at hr
  have hc : (q : ℝ) * (ratUpper p (Nat.log2 p) : ℝ) <
      (ratLower (ratLayerRatio p k) 0 : ℝ) := by exact_mod_cast h.2.2.2
  rw [cast_upper, cast_lower, Rat.cast_natCast, cast_layer_ratio] at hc
  exact cut_above (Nat.log2 p) hq (by have := h.1; omega) hp.1 hp.2 hr.1 hr.2 hc

private theorem NextCheck.sound {q : ℚ} {p k : ℕ} (hq : 0 < (q : ℝ))
    (h : NextCheck q p k) : goldenLayerMarginal p k < (q : ℝ) := by
  have hp := h.2.1.sound
  have hr := h.2.2.1.sound
  rw [Rat.cast_natCast] at hp
  rw [cast_layer_ratio] at hr
  have hc : (ratUpper (ratLayerRatio p k) 0 : ℝ) <
      (q : ℝ) * (ratLower p (Nat.log2 p) : ℝ) := by exact_mod_cast h.2.2.2
  rw [cast_upper, cast_lower, Rat.cast_natCast, cast_layer_ratio] at hc
  exact cut_below (Nat.log2 p) hq (by have := h.1; omega) hp.1 hp.2 hr.1 hr.2 hc

structure Row where
  lo : ℚ
  hi : ℚ
  price : ℚ
  cuts : List ℕ
  gainUpper : ℚ
  heightExponent : ℕ
  heightMantissa : ℚ
  logLoLower : ℚ
  logHiLower : ℚ

def Row.cut (r : Row) (k : ℕ) : ℕ := r.cuts[k - 1]!

def Row.layers (r : Row) (p : ℕ) : Finset ℕ :=
  (range r.cuts.length).filter (fun i => p ≤ r.cuts[i]!)

def Row.exponent (r : Row) (p : ℕ) : ℕ := (r.layers p).card

def Row.primes (r : Row) : Finset ℕ := Nat.primesLE r.cuts[0]!

def Row.optimizer (r : Row) : ℕ := ∏ p ∈ r.primes, p ^ r.exponent p

def Row.sigmaProduct (r : Row) : ℕ :=
  ∏ p ∈ r.primes, ∑ j ∈ range (r.exponent p + 1), p ^ j

def CutOrder (r : Row) : Prop :=
  ∀ i j : Fin r.cuts.length, i.val ≤ j.val → r.cuts[j.val]! ≤ r.cuts[i.val]!

instance (r : Row) : Decidable (CutOrder r) := by
  unfold CutOrder
  infer_instance

private theorem CutOrder.le {r : Row} (h : CutOrder r) {i j : ℕ}
    (hij : i ≤ j) (hj : j < r.cuts.length) : r.cuts[j]! ≤ r.cuts[i]! :=
  h ⟨i, hij.trans_lt hj⟩ ⟨j, hj⟩ hij

private theorem exponent_le (r : Row) (p : ℕ) : r.exponent p ≤ r.cuts.length := by
  simpa [Row.exponent, Row.layers] using
    card_filter_le (range r.cuts.length) (fun i => p ≤ r.cuts[i]!)

private theorem exponent_member {r : Row} (h : CutOrder r) (p i : ℕ)
    (hi : i < r.cuts.length) : p ≤ r.cuts[i]! ↔ i < r.exponent p := by
  constructor
  · intro hp
    have hs : range (i + 1) ⊆ r.layers p := by
      intro j hj
      have hji : j ≤ i := by have := mem_range.mp hj; omega
      exact mem_filter.mpr ⟨mem_range.mpr (hji.trans_lt hi), hp.trans (h.le hji hi)⟩
    have hc := card_le_card hs
    rw [card_range] at hc
    change i < (r.layers p).card
    omega
  · intro he
    by_contra hp
    have hs : r.layers p ⊆ range i := by
      intro j hj
      obtain ⟨hj, hpj⟩ := mem_filter.mp hj
      apply mem_range.mpr
      by_contra hji
      exact hp (hpj.trans (h.le (le_of_not_gt hji) (mem_range.mp hj)))
    have hc := card_le_card hs
    rw [card_range] at hc
    change i < (r.layers p).card at he
    omega

private theorem exponent_outside {r : Row} (h : CutOrder r) {p : ℕ}
    (hp : r.cuts[0]! < p) : r.exponent p = 0 := by
  have he : r.layers p = ∅ := by
    unfold Row.layers
    apply filter_eq_empty_iff.mpr
    intro i hi hpi
    exact (not_le_of_gt hp) (hpi.trans (h.le (Nat.zero_le i) (mem_range.mp hi)))
  simp [Row.exponent, he]

private theorem row_primes (r : Row) : ∀ p ∈ r.primes, p.Prime :=
  fun _ hp => (Nat.mem_primesLE.mp hp).2

private theorem optimizer_pos (r : Row) : 1 ≤ r.optimizer := by
  unfold Row.optimizer
  exact one_le_prod (fun p hp => one_le_pow₀ (row_primes r p hp).one_le)

private theorem optimizer_factorization {r : Row} (h : CutOrder r) (p : ℕ) (hp : p.Prime) :
    r.optimizer.factorization p = r.exponent p :=
  row_factorization (row_primes r) rfl rfl
    (fun _ hout => exponent_outside h hout) hp

private theorem optimizer_sigma (r : Row) :
    ArithmeticFunction.sigma 1 r.optimizer = r.sigmaProduct := by
  unfold Row.optimizer Row.sigmaProduct
  exact sigma_roster _ (row_primes r) _

def Row.objectiveBound (r : Row) : ℚ :=
  ratUpper r.gainUpper (ratScale r.gainUpper) -
    r.price * (r.heightExponent * (6931471803 / 10000000000) + ratLower r.heightMantissa 0)

def EndpointCheck (q H ell upper : ℚ) : Prop :=
  1 < H ∧ 0 < ell ∧ Normalized H (ratScale H) ∧ Normalized ell (ratScale ell) ∧
    ell ≤ ratLower H (ratScale H) ∧
    upper < 5772155 / 10000000 + ratLower ell (ratScale ell) - q * H

instance (q H ell upper : ℚ) : Decidable (EndpointCheck q H ell upper) := by
  unfold EndpointCheck
  infer_instance

private theorem EndpointCheck.sound {q H ell upper : ℚ} {m : ℕ}
    (h : EndpointCheck q H ell upper)
    (hobj : goldenResourceObjective (q : ℝ) m ≤ (upper : ℝ)) :
    0 < robinThreshold (H : ℝ) - (q : ℝ) * (H : ℝ) -
      goldenResourceObjective (q : ℝ) m := by
  have hH := h.2.2.1.sound
  have hE := h.2.2.2.1.sound
  have hEll : (ell : ℝ) ≤ (ratLower H (ratScale H) : ℝ) := by
    exact_mod_cast h.2.2.2.2.1
  rw [cast_lower] at hEll
  have hc : (upper : ℝ) <
      (5772155 / 10000000 : ℝ) + (ratLower ell (ratScale ell) : ℝ) -
        (q : ℝ) * (H : ℝ) := by
    have hcast := Rat.cast_lt (K := ℝ).mpr h.2.2.2.2.2
    convert hcast using 1
    push_cast
    norm_num
  rw [cast_lower] at hc
  exact endpoint_gap hobj hH.1 hH.2 hE.1 hE.2
    (by exact_mod_cast h.2.1) hEll hc

/-- Every field is a finite comparison of natural numbers or rationals.
The last two checks use the published endpoint log bounds weakened by
10⁻⁸, as in the verified native Row 04. -/
structure Checks (r : Row) : Prop where
  price_pos : 0 < r.price
  interval : r.lo < r.hi
  descending : CutOrder r
  top : ∀ i : Fin r.cuts.length, TopCheck r.price r.cuts[i.val]! (i.val + 1)
  next : ∀ i : Fin r.cuts.length, NextCheck r.price (r.cuts[i.val]! + 1) (i.val + 1)
  stop : NextCheck r.price 2 (r.cuts.length + 1)
  gain_normalized : Normalized r.gainUpper (ratScale r.gainUpper)
  height_normalized : Normalized r.heightMantissa 0
  gain : (r.sigmaProduct : ℚ) ≤ r.gainUpper * (r.optimizer : ℚ)
  height : (2 : ℚ) ^ r.heightExponent * r.heightMantissa ≤ (r.optimizer : ℚ)
  left : EndpointCheck r.price r.lo (r.logLoLower - 1 / 100000000) r.objectiveBound
  right : EndpointCheck r.price r.hi (r.logHiLower - 1 / 100000000) r.objectiveBound

theorem Checks.optimal {r : Row} (h : Checks r) :
    IsGoldenResourceOptimal (r.price : ℝ) r.optimizer := by
  have hq : 0 < (r.price : ℝ) := by exact_mod_cast h.price_pos
  apply optimal_of_cuts hq (optimizer_pos r) r.cuts.length r.cut
  · intro k hk hK
    have hi : k - 1 < r.cuts.length := by omega
    exact (h.top ⟨k - 1, hi⟩).1
  · intro k hk hK
    have hi : k - 1 < r.cuts.length := by omega
    simpa [Row.cut, show k - 1 + 1 = k by omega] using
      And.intro ((h.top ⟨k - 1, hi⟩).sound hq) ((h.next ⟨k - 1, hi⟩).sound hq)
  · exact h.stop.sound hq
  · intro p hp
    rw [optimizer_factorization h.descending p hp]
    exact exponent_le r p
  · intro p k hp hk hK
    rw [optimizer_factorization h.descending p hp]
    have hm := exponent_member h.descending p (k - 1) (by omega)
    unfold Row.cut
    exact hm.trans (by omega)

theorem Checks.objective {r : Row} (h : Checks r) :
    goldenResourceObjective (r.price : ℝ) r.optimizer ≤ (r.objectiveBound : ℝ) := by
  have hq : 0 < (r.price : ℝ) := by exact_mod_cast h.price_pos
  have hm : (0 : ℝ) < r.optimizer := Nat.cast_pos.mpr (by have := optimizer_pos r; omega)
  have hg := h.gain_normalized.sound
  have ht := h.height_normalized.sound
  have hgain : (r.sigmaProduct : ℝ) ≤ (r.gainUpper : ℝ) * (r.optimizer : ℝ) := by
    exact_mod_cast h.gain
  have hheight : (2 : ℝ) ^ r.heightExponent * (r.heightMantissa : ℝ) ≤
      (r.optimizer : ℝ) := by exact_mod_cast h.height
  have hsigma : (ArithmeticFunction.sigma 1 r.optimizer : ℝ) / (r.optimizer : ℝ) ≤
      (r.gainUpper : ℝ) := by
    rw [optimizer_sigma]
    exact (div_le_iff₀ hm).mpr hgain
  have hObj := objective_le hq (optimizer_pos r) hg.1 hg.2 ht.1 ht.2 hsigma hheight
  have hc : (r.objectiveBound : ℝ) =
      objectiveUpper (r.price : ℝ) (r.gainUpper : ℝ) (r.heightMantissa : ℝ)
        r.heightExponent (ratScale r.gainUpper) := by
    unfold Row.objectiveBound objectiveUpper
    simp [Rat.cast_natCast, Rat.cast_div, cast_lower, cast_upper]
  rw [hc]
  exact hObj

/-- A checked row proves the native Robin log margin on its complete interval. -/
theorem Checks.sound {r : Row} (h : Checks r) {n : ℕ} (hn : 1 ≤ n)
    (hlo : (r.lo : ℝ) ≤ Real.log (n : ℝ))
    (hhi : Real.log (n : ℝ) ≤ (r.hi : ℝ)) : 0 < robinLogMargin n := by
  exact fixed_price_interval (optimizer_pos r) hn h.optimal
    (by exact_mod_cast h.left.1) (by exact_mod_cast h.interval) hlo hhi
    (h.left.sound h.objective) (h.right.sound h.objective)

/-- Extend a previously proved height range with a checked adjacent row. -/
theorem Checks.extend {r : Row} (h : Checks r) {n : ℕ} (hn : 1 ≤ n)
    (hprefix : Real.log (n : ℝ) ≤ (r.lo : ℝ) → 0 < robinLogMargin n)
    (hhi : Real.log (n : ℝ) ≤ (r.hi : ℝ)) : 0 < robinLogMargin n := by
  by_cases hlo : Real.log (n : ℝ) ≤ (r.lo : ℝ)
  · exact hprefix hlo
  · exact h.sound hn (le_of_lt (lt_of_not_ge hlo)) hhi

def pinnedRow05 : Row where
  lo := (146801491 / 1000000)
  hi := (111686563 / 500000)
  price := (8278925801 / 8000000000000)
  gainUpper := (4630388083099 / 500000000000)
  heightMantissa := (12659228613027413269 / 9223372036854775808)
  logLoLower := (4989081271 / 1000000000)
  logHiLower := (2704421791 / 500000000)
  heightExponent := 277
  cuts := [184, 17, 7, 4, 3, 2, 2, 2, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- The finite checker reduces all primes up to 184 and both rational endpoint gaps.
theorem pinnedRow05_checks : Checks pinnedRow05 := by
  constructor <;> decide +kernel

theorem pinned_row05_margin {n : ℕ} (hn : 1 ≤ n)
    (hlo : (146801491 / 1000000 : ℝ) ≤ Real.log (n : ℝ))
    (hhi : Real.log (n : ℝ) ≤ (111686563 / 500000 : ℝ)) :
    0 < robinLogMargin n := by
  apply pinnedRow05_checks.sound hn
  · convert hlo using 1
    norm_num [pinnedRow05]
  · convert hhi using 1
    norm_num [pinnedRow05]

theorem robin_margin_through_pinned_row05 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (pinnedRow05.hi : ℝ)) : 0 < robinLogMargin n := by
  apply pinnedRow05_checks.extend (by omega) ?_ hhi
  intro h
  apply D5.S3.Arith.Robin.Finite.OriginalRobinFiniteRows.robin_margin_through_pinned_row04 hn
  convert h using 1
  norm_num [pinnedRow05]

/-- The native certificate proves the original inequality through the Row 05 endpoint. -/
theorem original_robin_through_pinned_row05 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ (111686563 / 500000 : ℝ)) :
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  apply original_robin_of_margin (by omega)
  apply robin_margin_through_pinned_row05 hn
  convert hhi using 1
  norm_num [pinnedRow05]

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
