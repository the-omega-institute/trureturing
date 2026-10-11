/- GID: D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedOptimality/ExitGeometry
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedOptimality/ExitGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite first-exit partitions retain survivor mass and recover complete-word distances under common continuations. -/

import D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import D5.S3.Entropy.Forgetting.CapacityMonotone

namespace D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedOptimality.ExitGeometry

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Equality.DataProcessingEquality
open D5.S3.TotalVariation.DataProcessing
open D5.S3.Divergence.ClassicalDPI (channelOutput)
open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)
open scoped BigOperators

noncomputable section

/-- `none` records survival through the entire horizon. A recorded exit keeps its
first time and symbol; no infinite history is added to the observer's input. -/
def firstExitIndex : {H : Nat} → (Fin H → Visible) → Option (Fin H × Visible)
  | 0, _ => none
  | H+1, w => if w 0 = B then
      (firstExitIndex (fun i : Fin H => w i.succ)).map (fun a => (a.1.succ, a.2))
    else some (0, w 0)

/-- An exit coefficient at time `n` uses the same normalized continuation for its
symbol. The residual coefficient `s H` is assigned to the all-B word. -/
def exitExpansion (s : Nat → ℝ) (e : Nat → Visible → ℝ)
    (R : Visible → LawProfile) : LawProfile
  | 0, _ => s 0
  | H+1, w => if w 0 = B then
      exitExpansion (fun n => s (n+1)) (fun n => e (n+1)) R H (fun i => w i.succ)
    else e 0 (w 0) * R (w 0) H (fun i => w i.succ)

private lemma symbol_split (f : Visible → ℝ) (x : ℝ) :
    (∑ y, if y = B then x else f y) = x + ∑ y, if y = B then 0 else f y := by
  simp [B, Fin.sum_univ_succ]
  ring

private lemma range_shift (f : Nat → ℝ) (H : Nat) :
    (∑ n ∈ Finset.range (H+1), f n) = f 0 + ∑ n ∈ Finset.range H, f (n+1) := by
  simpa only [add_comm] using Finset.sum_range_succ' f H

/-- Every finite exit partition includes its survivor coefficient. -/
private theorem expansion_mass (s : Nat → ℝ) (e : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hR : ∀ y, ProbabilityProfile (R y)) (H : Nat) :
    (∑ w, exitExpansion s e R H w) =
      s H + ∑ n ∈ Finset.range H, ∑ y, if y = B then 0 else e n y := by
  induction H generalizing s e with
  | zero => simp [exitExpansion]
  | succ H ih =>
    rw [sum_words_succ]
    simp only [exitExpansion, Fin.cons_zero, Fin.cons_succ]
    have he (y : Visible) :
        (∑ w : Fin H → Visible, if y = B then
          exitExpansion (fun n => s (n+1)) (fun n => e (n+1)) R H w
          else e 0 y * R y H w) =
        if y = B then (s (H+1) +
          ∑ n ∈ Finset.range H, ∑ a, if a = B then 0 else e (n+1) a) else e 0 y := by
      by_cases hy : y = B
      · simp only [hy, ite_true]; exact ih _ _
      · simp only [hy, ite_false, ← Finset.mul_sum, (hR y H).2, mul_one]
    simp_rw [he]
    rw [symbol_split, range_shift]
    ring

/-- With common conditional continuations, the complete finite-word L1 distance
is exactly the first-exit L1 distance, including the survivor difference. -/
private theorem expansion_abs_difference (s t : Nat → ℝ)
    (e f : Nat → Visible → ℝ) (R : Visible → LawProfile)
    (hR : ∀ y, ProbabilityProfile (R y)) (H : Nat) :
    (∑ w, |exitExpansion s e R H w - exitExpansion t f R H w|) =
      |s H - t H| + ∑ n ∈ Finset.range H,
        ∑ y, if y = B then 0 else |e n y - f n y| := by
  induction H generalizing s t e f with
  | zero => simp [exitExpansion]
  | succ H ih =>
    rw [sum_words_succ]
    simp only [exitExpansion, Fin.cons_zero, Fin.cons_succ]
    have he (y : Visible) :
        (∑ w : Fin H → Visible, |(if y = B then
          exitExpansion (fun n => s (n+1)) (fun n => e (n+1)) R H w
          else e 0 y * R y H w) - (if y = B then
          exitExpansion (fun n => t (n+1)) (fun n => f (n+1)) R H w
          else f 0 y * R y H w)|) =
        if y = B then (|s (H+1)-t (H+1)| +
          ∑ n ∈ Finset.range H, ∑ a, if a = B then 0 else |e (n+1) a-f (n+1) a|)
        else |e 0 y-f 0 y| := by
      by_cases hy : y = B
      · simp only [hy, ite_true]; exact ih _ _ _ _
      · simp only [hy, ite_false, ← sub_mul, abs_mul]
        simp_rw [abs_of_nonneg ((hR y H).1 _)]
        rw [← Finset.mul_sum, (hR y H).2, mul_one]
    simp_rw [he]
    rw [symbol_split, range_shift]
    ring

/-- A deterministic finite first-exit observation contracts the original word TV.
The survivor cell is present even for a law that never exits. -/
private theorem first_exit_contraction (F G : LawProfile) (H : Nat) :
    totalVariation (pushforward (@firstExitIndex H) (F H))
      (pushforward (@firstExitIndex H) (G H)) ≤ totalVariation (F H) (G H) := by
  classical
  let W : (Fin H → Visible) → Option (Fin H × Visible) → ℝ :=
    fun w a => if firstExitIndex w = a then 1 else 0
  have hW : (∀ w a, 0 ≤ W w a) ∧ ∀ w, (∑ a, W w a) = 1 := by
    constructor
    · intro w a; dsimp [W]; split_ifs <;> norm_num
    · intro w; simp [W]
  have he (P : (Fin H → Visible) → ℝ) : channelOutput W P =
      pushforward (@firstExitIndex H) P := by
    funext a
    simp only [channelOutput, pushforward, W, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : firstExitIndex w = a <;> simp only [hw, ite_true, ite_false]
  simpa only [he] using total_variation_channel_le (F H) (G H) W hW

/-- Conditional continuation mass of a word after its first non-B symbol. -/
def continuationWeight (R : Visible → LawProfile) : LawProfile
  | 0, _ => 1
  | H+1, w => if w 0 = B then continuationWeight R H (fun i => w i.succ)
    else R (w 0) H (fun i => w i.succ)

private def cellCoefficient (s : Nat → ℝ) (e : Nat → Visible → ℝ)
    (H : Nat) : Option (Fin H × Visible) → ℝ
  | none => s H
  | some (n, y) => e n.val y

private lemma continuation_nonnegative (R : Visible → LawProfile)
    (hR : ∀ y, ProbabilityProfile (R y)) (H : Nat) (w : Fin H → Visible) :
    0 ≤ continuationWeight R H w := by
  induction H with
  | zero => exact zero_le_one
  | succ H ih =>
    dsimp [continuationWeight]
    split_ifs
    · exact ih _
    · exact (hR _ H).1 _

private lemma expansion_factor (s : Nat → ℝ) (e : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (H : Nat) (w : Fin H → Visible) :
    exitExpansion s e R H w =
      cellCoefficient s e H (firstExitIndex w) * continuationWeight R H w := by
  induction H generalizing s e with
  | zero => simp [exitExpansion, cellCoefficient, firstExitIndex, continuationWeight]
  | succ H ih =>
    by_cases hy : w 0 = B
    · simp only [exitExpansion, firstExitIndex, continuationWeight, hy, ite_true]
      rw [ih]
      cases hc : firstExitIndex (fun i : Fin H => w i.succ) with
      | none => simp [cellCoefficient]
      | some a => simp [cellCoefficient]
    · simp [exitExpansion, firstExitIndex, continuationWeight, hy, cellCoefficient]

/-- The actual time-and-symbol partition preserves TV for standard common
continuations. This applies without any assumption that the survivor mass vanishes. -/
theorem first_exit_tv_exact (s t : Nat → ℝ) (e f : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hR : ∀ y, ProbabilityProfile (R y)) (H : Nat) :
    totalVariation (pushforward (@firstExitIndex H) (exitExpansion s e R H))
      (pushforward (@firstExitIndex H) (exitExpansion t f R H)) =
      totalVariation (exitExpansion s e R H) (exitExpansion t f R H) := by
  classical
  let W := D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel
    (@firstExitIndex H)
  have hW : (∀ w a, 0 ≤ W w a) ∧ ∀ w, (∑ a, W w a) = 1 := by
    constructor
    · intro w a; dsimp [W,
        D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel]
      split_ifs <;> norm_num
    · intro w; simp [W,
        D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel]
  have he (P : (Fin H → Visible) → ℝ) : channelOutput W P =
      pushforward (@firstExitIndex H) P := by
    funext a
    simp only [channelOutput, pushforward, W,
      D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel,
      mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : firstExitIndex w = a <;> simp only [hw, ite_true, ite_false]
  rw [← he, ← he]
  apply (total_variation_channel_eq_iff_no_sign_mixing _ _ W hW).mpr
  intro a
  by_cases hle : cellCoefficient s e H a ≤ cellCoefficient t f H a
  · right
    intro w hw
    dsimp [W, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel]
    apply if_neg
    intro ha
    rw [expansion_factor, expansion_factor, ha] at hw
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hle
      (continuation_nonnegative R hR H w))) hw
  · left
    intro w hw
    dsimp [W, D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel]
    apply if_neg
    intro ha
    rw [expansion_factor, expansion_factor, ha] at hw
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right (le_of_not_ge hle)
      (continuation_nonnegative R hR H w))) hw

/-- Complete-word TV can be computed from the finite first-exit coefficients,
with the residual all-B mass retained. -/
theorem common_continuation_tv (s t : Nat → ℝ) (e f : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hR : ∀ y, ProbabilityProfile (R y)) (H : Nat) :
    totalVariation (exitExpansion s e R H) (exitExpansion t f R H) =
      (1/2:ℝ) * (|s H-t H| + ∑ n ∈ Finset.range H,
        ∑ y, if y = B then 0 else |e n y-f n y|) := by
  rw [totalVariation, expansion_abs_difference s t e f R hR H]

private theorem expansion_overlap (s t : Nat → ℝ) (e f : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hR : ∀ y, ProbabilityProfile (R y)) (H : Nat) :
    (∑ w, min (exitExpansion s e R H w) (exitExpansion t f R H w)) =
      min (s H) (t H) + ∑ n ∈ Finset.range H,
        ∑ y, if y = B then 0 else min (e n y) (f n y) := by
  induction H generalizing s t e f with
  | zero => simp [exitExpansion]
  | succ H ih =>
    rw [sum_words_succ]
    simp only [exitExpansion, Fin.cons_zero, Fin.cons_succ]
    have he (y : Visible) :
        (∑ w : Fin H → Visible, min (if y = B then
          exitExpansion (fun n => s (n+1)) (fun n => e (n+1)) R H w
          else e 0 y * R y H w) (if y = B then
          exitExpansion (fun n => t (n+1)) (fun n => f (n+1)) R H w
          else f 0 y * R y H w)) =
        if y = B then (min (s (H+1)) (t (H+1)) +
          ∑ n ∈ Finset.range H, ∑ a, if a = B then 0 else min (e (n+1) a) (f (n+1) a))
        else min (e 0 y) (f 0 y) := by
      by_cases hy : y = B
      · simp only [hy, ite_true]; exact ih _ _ _ _
      · simp only [hy, ite_false]
        have hm (w : Fin H → Visible) :
            min (e 0 y * R y H w) (f 0 y * R y H w) = min (e 0 y) (f 0 y) * R y H w := by
          rcases le_total (e 0 y) (f 0 y) with h | h
          · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h ((hR y H).1 w))]
          · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h ((hR y H).1 w))]
        simp_rw [hm]
        rw [← Finset.mul_sum, (hR y H).2, mul_one]
    simp_rw [he]
    rw [symbol_split, range_shift]
    ring

/-- The complete-word overlap is the overlap of all finite exits and the
remaining survivor atom, provided both reconstructed laws are normalized. -/
theorem common_continuation_overlap (s t : Nat → ℝ) (e f : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hR : ∀ y, ProbabilityProfile (R y))
    (hP : ProbabilityProfile (exitExpansion s e R))
    (hQ : ProbabilityProfile (exitExpansion t f R)) (H : Nat) :
    totalVariation (exitExpansion s e R H) (exitExpansion t f R H) =
      1 - (min (s H) (t H) + ∑ n ∈ Finset.range H,
        ∑ y, if y = B then 0 else min (e n y) (f n y)) := by
  rw [finite_overlap_identity _ _ (hP H) (hQ H), expansion_overlap s t e f R hR H]

private lemma source_exit_expansion (p q r x z : ℝ) (n H : Nat)
    (w : Fin H → Visible) :
    exitExpansion (fun m => x*(a p q)^(n+m)+z*(b r)^(n+m))
      (fun m y => x*(a p q)^(n+m)*pureRow p q r 2 y +
        z*(b r)^(n+m)*pureRow p q r 4 y)
      (fun y => pureLaw p q r (singletonState y)) H w =
      x*(a p q)^n*pureLaw p q r 2 H w + z*(b r)^n*pureLaw p q r 4 H w := by
  induction H generalizing n with
  | zero => simp [exitExpansion, pure_zero]
  | succ H ih =>
    by_cases hy : w 0 = B
    · simp only [exitExpansion, hy, ite_true]
      have hs : (fun m => x*(a p q)^(n+(m+1))+z*(b r)^(n+(m+1))) =
          (fun m => x*(a p q)^(n+1+m)+z*(b r)^(n+1+m)) := by
        funext m; rw [show n+(m+1)=n+1+m by omega]
      have he : (fun m y => x*(a p q)^(n+(m+1))*pureRow p q r 2 y +
          z*(b r)^(n+(m+1))*pureRow p q r 4 y) =
          (fun m y => x*(a p q)^(n+1+m)*pureRow p q r 2 y +
            z*(b r)^(n+1+m)*pureRow p q r 4 y) := by
        funext m y; rw [show n+(m+1)=n+1+m by omega]
      rw [hs, he, ih]
      rw [pure_cons, pure_cons]
      simp only [hy, nextPure, ite_true, pureBSuccessor]
      simp [pureRow, B, pow_succ]
      ring
    · simp only [exitExpansion, hy, ite_false, Nat.add_zero]
      rw [pure_cons, pure_cons]
      simp only [nextPure, hy, ite_false]
      ring

/-- The original source mixture has the standard exact continuation after every
individual first-exit symbol. Its all-B mass remains part of the finite partition. -/
theorem source_first_exit_expansion (p q r x : ℝ) :
    mixtureLaw p q r x = exitExpansion
      (fun H => x*(a p q)^H+(1-x)*(b r)^H)
      (fun n y => x*(a p q)^n*pureRow p q r 2 y +
        (1-x)*(b r)^n*pureRow p q r 4 y)
      (fun y => pureLaw p q r (singletonState y)) := by
  funext H w
  simpa only [Nat.zero_add, pow_zero, mul_one, mixtureLaw] using
    (source_exit_expansion p q r x (1-x) 0 H w).symm

private lemma expansion_nonnegative (s : Nat → ℝ) (e : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hs : ∀ n, 0 ≤ s n) (he : ∀ n y, 0 ≤ e n y)
    (hR : ∀ y, ProbabilityProfile (R y)) (H : Nat) (w : Fin H → Visible) :
    0 ≤ exitExpansion s e R H w := by
  induction H generalizing s e with
  | zero => exact hs 0
  | succ H ih =>
    dsimp [exitExpansion]
    split_ifs
    · exact ih _ _ (fun n => hs (n+1)) (fun n y => he (n+1) y) _
    · exact mul_nonneg (he 0 _) ((hR _ H).1 _)

/-- A standard geometric tail law: hold with probability `t`, then emit an
individual exit symbol with row `alpha` and continue in its exact pure source law. -/
def geometricLaw (p q r t : ℝ) (alpha : Visible → ℝ) : LawProfile :=
  exitExpansion (fun H => t^H) (fun n y => t^n*alpha y)
    (fun y => pureLaw p q r (singletonState y))

private lemma geometric_mass (t : ℝ) (alpha : Visible → ℝ)
    (ha : (∑ y, if y = B then 0 else alpha y) = 1-t) (H : Nat) :
    t^H + (∑ n ∈ Finset.range H, ∑ y, if y = B then 0 else t^n*alpha y) = 1 := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ y, if y = B then 0 else t^H*alpha y) = t^H*(1-t) := by
      rw [← ha, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    rw [he, pow_succ]
    nlinarith

private theorem geometric_probability {p q r t : ℝ} (hp : admissible p q r)
    (ht : 0 ≤ t) (alpha : Visible → ℝ) (hα : ∀ y, 0 ≤ alpha y)
    (ha : (∑ y, if y = B then 0 else alpha y) = 1-t) :
    ProbabilityProfile (geometricLaw p q r t alpha) := by
  intro H
  refine ⟨expansion_nonnegative _ _ _ (fun n => pow_nonneg ht n)
    (fun n y => mul_nonneg (pow_nonneg ht n) (hα y))
    (fun y => pure_probability hp _) H, ?_⟩
  rw [geometricLaw, expansion_mass _ _ _ (fun y => pure_probability hp _) H]
  exact geometric_mass t alpha ha H

private lemma expansion_tv_monotone (s t : Nat → ℝ) (e f : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hR : ∀ y, ProbabilityProfile (R y))
    (hP : ProbabilityProfile (exitExpansion s e R))
    (hQ : ProbabilityProfile (exitExpansion t f R)) :
    Monotone (fun H => totalVariation (exitExpansion s e R H) (exitExpansion t f R H)) := by
  apply monotone_nat_of_le_succ
  intro H
  have hs0 := expansion_mass s e R hR H
  have hs1 := expansion_mass s e R hR (H+1)
  have ht0 := expansion_mass t f R hR H
  have ht1 := expansion_mass t f R hR (H+1)
  rw [(hP H).2] at hs0
  rw [(hP (H+1)).2, Finset.sum_range_succ] at hs1
  rw [(hQ H).2] at ht0
  rw [(hQ (H+1)).2, Finset.sum_range_succ] at ht1
  have he : s H-t H = (s (H+1)-t (H+1)) +
      ∑ y, if y = B then 0 else e H y-f H y := by
    have hd : (∑ y, if y = B then 0 else e H y-f H y) =
        (∑ y, if y = B then 0 else e H y)-(∑ y, if y = B then 0 else f H y) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    rw [hd]
    linarith
  have ha := abs_add_le (s (H+1)-t (H+1))
    (∑ y, if y = B then 0 else e H y-f H y)
  have hb := Finset.abs_sum_le_sum_abs
    (fun y : Visible => if y = B then 0 else e H y-f H y) Finset.univ
  have hc : (∑ y, |if y = B then 0 else e H y-f H y|) =
      ∑ y, if y = B then 0 else |e H y-f H y| := by
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  rw [hc] at hb
  rw [common_continuation_tv s t e f R hR H,
    common_continuation_tv s t e f R hR (H+1), Finset.sum_range_succ]
  rw [← he] at ha
  linarith

/-- Almost-sure exit and common conditional continuations identify the original
profile distance with the countable first-exit overlap. Finite survivors are kept
throughout the limiting argument. -/
theorem profile_from_exit_overlap (s t : Nat → ℝ) (e f : Nat → Visible → ℝ)
    (R : Visible → LawProfile) (hR : ∀ y, ProbabilityProfile (R y))
    (hP : ProbabilityProfile (exitExpansion s e R))
    (hQ : ProbabilityProfile (exitExpansion t f R))
    (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (hc : Summable (fun n => ∑ y, if y = B then 0 else min (e n y) (f n y))) :
    profileDistance (exitExpansion s e R) (exitExpansion t f R) =
      1-∑' n, ∑ y, if y = B then 0 else min (e n y) (f n y) := by
  have hlim : Filter.Tendsto (fun H =>
      totalVariation (exitExpansion s e R H) (exitExpansion t f R H))
      Filter.atTop (nhds (1-∑' n, ∑ y, if y = B then 0 else min (e n y) (f n y))) := by
    simp_rw [common_continuation_overlap s t e f R hR hP hQ]
    have hm := hs.min ht
    have hsum := hc.hasSum.tendsto_sum_nat
    simpa using tendsto_const_nhds.sub (hm.add hsum)
  apply le_antisymm
  · apply profile_le
    intro H
    exact (expansion_tv_monotone s t e f R hR hP hQ).ge_of_tendsto hlim H
  · exact le_of_tendsto' hlim (fun H => finite_le_profile hP hQ H)

/-- Countable overlap of scaled geometric exit laws, with holding parameters. -/
def geometricOverlap (A x C y : ℝ) : ℝ :=
  ∑' n : Nat, min (A*(1-x)*x^n) (C*(1-y)*y^n)

/-- Exit emission row with branch-2 fraction `z`; branch-2 singleton proportions
are those of the original source. -/
def tailExitRow (p q t z : ℝ) (y : Visible) : ℝ :=
  if y = 0 then (1-z)*(1-t) else if y = 1 then z*(1-t)*q/(p+q)
  else if y = 3 then z*(1-t)*p/(p+q) else 0

private lemma tail_exit_probability {p q t z : ℝ} (hp : 0 < p) (hq : 0 < q)
    (ht : t ≤ 1) (hz : z ∈ Set.Icc 0 1) :
    (∀ y, 0 ≤ tailExitRow p q t z y) ∧
      (∑ y, if y = B then 0 else tailExitRow p q t z y) = 1-t := by
  have hs : 0 < p+q := add_pos hp hq
  have hzn := sub_nonneg.mpr hz.2
  have htn := sub_nonneg.mpr ht
  have hz0 := hz.1
  constructor
  · intro y
    fin_cases y <;> simp [tailExitRow] <;> positivity
  · simp [tailExitRow, B, Fin.sum_univ_succ]
    field_simp
    ring

private lemma min_scale (A C w : ℝ) (hw : 0 ≤ w) :
    min (A*w) (C*w) = min A C*w := by
  rcases le_total A C with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h hw)]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h hw)]

private lemma exit_overlap_symbols {p q r : ℝ} (hp : admissible p q r)
    (x z t : ℝ) (n : Nat) :
    (∑ y, if y = B then 0 else min
      (x*(a p q)^n*pureRow p q r 2 y+(1-x)*(b r)^n*pureRow p q r 4 y)
      (t^n*tailExitRow p q t z y)) =
      min (x*(1-a p q)*(a p q)^n) (z*(1-t)*t^n) +
      min ((1-x)*(1-b r)*(b r)^n) ((1-z)*(1-t)*t^n) := by
  have hs : p+q ≠ 0 := ne_of_gt (add_pos hp.1 hp.2.1)
  have h1 : x*(a p q)^n*q = (x*(1-a p q)*(a p q)^n)*(q/(p+q)) := by
    unfold a; field_simp; ring
  have h3 : x*(a p q)^n*p = (x*(1-a p q)*(a p q)^n)*(p/(p+q)) := by
    unfold a; field_simp; ring
  have ht1 : t^n*(z*(1-t)*q/(p+q)) = (z*(1-t)*t^n)*(q/(p+q)) := by ring
  have ht3 : t^n*(z*(1-t)*p/(p+q)) = (z*(1-t)*t^n)*(p/(p+q)) := by ring
  simp only [B, Fin.sum_univ_succ, pureRow, tailExitRow]
  norm_num
  rw [h1, h3, ht1, ht3,
    min_scale _ _ _ (div_nonneg hp.2.1.le (add_pos hp.1 hp.2.1).le),
    min_scale _ _ _ (div_nonneg hp.1.le (add_pos hp.1 hp.2.1).le)]
  have hr : (1-x)*(b r)^n*r = (1-x)*(1-b r)*(b r)^n := by unfold b; ring
  have htt : t^n*((1-z)*(1-t)) = (1-z)*(1-t)*t^n := by ring
  rw [hr, htt]
  field_simp
  ring

private lemma overlap_summable {A C x y : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hx : x ∈ Set.Ico 0 1) (hy : y ∈ Set.Ico 0 1) :
    Summable (fun n : Nat => min (A*(1-x)*x^n) (C*(1-y)*y^n)) := by
  apply Summable.of_nonneg_of_le
    (fun n => le_min (by positivity) (by positivity)) (fun n => min_le_left _ _)
  exact (summable_geometric_of_lt_one hx.1 hx.2).mul_left (A*(1-x))

/-- The standard geometric tail and the original five-mode source mixture have
exactly the two-category geometric overlap of Definition 5.4. -/
theorem mixture_geometric_distance {p q r t x z : ℝ} (hp : admissible p q r)
    (ht : t ∈ Set.Ico 0 1) (hx : x ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    profileDistance (mixtureLaw p q r x) (geometricLaw p q r t (tailExitRow p q t z)) =
      1-geometricOverlap x (a p q) z t-
        geometricOverlap (1-x) (b r) (1-z) t := by
  let s := fun H => x*(a p q)^H+(1-x)*(b r)^H
  let e := fun n y => x*(a p q)^n*pureRow p q r 2 y +
    (1-x)*(b r)^n*pureRow p q r 4 y
  let f := fun n y => t^n*tailExitRow p q t z y
  let R := fun y => pureLaw p q r (singletonState y)
  have hsource : mixtureLaw p q r x = exitExpansion s e R :=
    source_first_exit_expansion p q r x
  have hP : ProbabilityProfile (exitExpansion s e R) := by
    rw [← hsource]; exact mixture_probability hp hx
  have htail := tail_exit_probability hp.1 hp.2.1 ht.2.le hz
  have hQ := geometric_probability hp ht.1 (tailExitRow p q t z) htail.1 htail.2
  have ha := holding_bounds hp
  have hc1 := overlap_summable hx.1 hz.1 ⟨ha.1.le, ha.2.1⟩ ht
  have hc2 := overlap_summable (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hz.2)
    ⟨ha.2.2.1.le, ha.2.2.2.1⟩ ht
  have hc : Summable (fun n => ∑ y, if y = B then 0 else min (e n y) (f n y)) := by
    simp only [e, f, exit_overlap_symbols hp]
    exact hc1.add hc2
  have hs : Filter.Tendsto s Filter.atTop (nhds 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2.1).const_mul x).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one ha.2.2.1.le ha.2.2.2.1).const_mul (1-x))
    simpa [s] using h
  rw [hsource, geometricLaw]
  have he := profile_from_exit_overlap s (fun H => t^H) e f R
    (fun y => pure_probability hp _) hP hQ hs
    (tendsto_pow_atTop_nhds_zero_of_lt_one ht.1 ht.2) hc
  rw [he]
  simp only [e, f, exit_overlap_symbols hp]
  rw [hc1.tsum_add hc2]
  simp only [geometricOverlap]
  ring

/-- Parameters of the source's dominant/minority geometric tail. -/
def Q (p q r t beta : ℝ) : LawProfile :=
  geometricLaw p q r t (tailExitRow p q t (if b r < a p q then 1-beta else beta))

/-- The original arbitrary-holding criterion, including non-strict endpoint ties. -/
def GeometricallyFeasible (p q r epsilon D : ℝ) : Prop :=
  D ∈ Set.Icc 0 (1/2:ℝ) ∧ ∃ t ∈ Set.Ico (0:ℝ) 1, ∃ beta ∈ Set.Icc (0:ℝ) 1,
    1-geometricOverlap 1 (max (a p q) (b r)) (1-beta) t ≤ epsilon ∧
    1-geometricOverlap (1-D) (max (a p q) (b r)) (1-beta) t -
      geometricOverlap D (min (a p q) (b r)) beta t ≤ epsilon

/-- The existential geometric criterion is equivalent to both complete-profile
endpoint bounds for the same tail law and the same two parameters. -/
theorem geometric_feasible_iff {p q r epsilon D : ℝ} (hp : admissible p q r) :
    GeometricallyFeasible p q r epsilon D ↔
      D ∈ Set.Icc 0 (1/2:ℝ) ∧ ∃ t ∈ Set.Ico (0:ℝ) 1, ∃ beta ∈ Set.Icc (0:ℝ) 1,
        profileDistance (dominantLaw p q r) (Q p q r t beta) ≤ epsilon ∧
        profileDistance (orientedMixture p q r D) (Q p q r t beta) ≤ epsilon := by
  have hz {C t : ℝ} (hC : 0 ≤ C) (ht : t ∈ Set.Ico 0 1) (y : ℝ) :
      geometricOverlap 0 y C t = 0 := by
    unfold geometricOverlap
    apply tsum_eq_zero
    intro n
    simp only [zero_mul]
    exact min_eq_left (mul_nonneg (mul_nonneg hC (sub_nonneg.mpr ht.2.le))
      (pow_nonneg ht.1 n))
  have hmetric (hD : D ∈ Set.Icc 0 (1/2:ℝ)) (t beta : ℝ)
      (ht : t ∈ Set.Ico 0 1) (hb : beta ∈ Set.Icc 0 1) :
      profileDistance (dominantLaw p q r) (Q p q r t beta) =
        1-geometricOverlap 1 (max (a p q) (b r)) (1-beta) t ∧
      profileDistance (orientedMixture p q r D) (Q p q r t beta) =
        1-geometricOverlap (1-D) (max (a p q) (b r)) (1-beta) t -
          geometricOverlap D (min (a p q) (b r)) beta t := by
    have hb' : 1-beta ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
    have hD0 : D ∈ Set.Icc (0:ℝ) 1 := ⟨hD.1, hD.2.trans (by norm_num)⟩
    have hD' : 1-D ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hD.2], by linarith [hD.1]⟩
    by_cases hab : b r < a p q
    · simp only [dominantLaw, orientedMixture, Q, if_pos hab, max_eq_left hab.le,
        min_eq_right hab.le]
      have he0 := mixture_geometric_distance hp ht (x := 1) (by norm_num) hb'
      have heD := mixture_geometric_distance hp ht hD' hb'
      rw [(mixture_endpoints p q r).2] at he0
      simp only [sub_self, sub_sub_cancel, hz hb.1 ht, sub_zero] at he0 heD
      exact ⟨he0, heD⟩
    · have hba := le_of_not_gt hab
      simp only [dominantLaw, orientedMixture, Q, if_neg hab, max_eq_right hba,
        min_eq_left hba]
      have he0 := mixture_geometric_distance hp ht (x := 0) (by norm_num) hb
      have heD := mixture_geometric_distance hp ht hD0 hb
      rw [(mixture_endpoints p q r).1] at he0
      simp only [hz hb.1 ht, sub_zero, zero_sub] at he0
      constructor
      · simpa only [sub_zero] using he0
      · linarith [heD]
  unfold GeometricallyFeasible
  constructor
  · rintro ⟨hD, t, ht, beta, hb, h0, h1⟩
    exact ⟨hD, t, ht, beta, hb, (hmetric hD t beta ht hb).1.symm ▸ h0,
      (hmetric hD t beta ht hb).2.symm ▸ h1⟩
  · rintro ⟨hD, t, ht, beta, hb, h0, h1⟩
    exact ⟨hD, t, ht, beta, hb, (hmetric hD t beta ht hb).1 ▸ h0,
      (hmetric hD t beta ht hb).2 ▸ h1⟩

end

end D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedOptimality.ExitGeometry
