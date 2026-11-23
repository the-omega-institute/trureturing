/- GID: D5/S3/Quantum/Entanglement/SectorChannels/SchmidtPartitionStability
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/SchmidtPartitionStability
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Labeled Schmidt partition distance from sorted spectral caps. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Lattice.Fold

/-! # Quantitative rounding from a prefix - majorized spectrum
Pure finite scalar inequalities; not a Schur–Horn or channel formalization.
-/

namespace D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability

set_option autoImplicit false
open scoped BigOperators



namespace RTMajorizationRound

def preSum (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, x i

/-- A decreasing nonnegative coefficient vector pairs nonnegatively with every
vector whose prefixes are nonnegative. No equality of the final sums is
required. This is finite Abel summation in a form convenient for majorization. -/
private theorem weighted_nonneg (n : ℕ) (d w : ℕ → ℝ)
    (hp : ∀ k ≤ n, 0 ≤ preSum d k)
    (hw : ∀ i < n, 0 ≤ w i)
    (hd : ∀ i j, i ≤ j → j < n → w j ≤ w i) :
    0 ≤ preSum (fun i => d i * w i) n := by
  induction n generalizing w with
  | zero => simp [preSum]
  | succ n ih =>
    have ha : 0 ≤ preSum (fun i => d i * (w i - w n)) n := by
      exact ih _ (fun k hk => hp k (Nat.le_trans hk (Nat.le_succ _)))
        (fun i hi => sub_nonneg.mpr (hd i n hi.le (Nat.lt_succ_self n)))
        (fun i j hij hj => sub_le_sub_right
          (hd i j hij (Nat.lt_trans hj (Nat.lt_succ_self n))) _)
    have hb : 0 ≤ preSum d (n + 1) * w n :=
      mul_nonneg (hp (n + 1) le_rfl) (hw n (Nat.lt_succ_self n))
    calc
      0 ≤ preSum (fun i => d i * (w i - w n)) n + preSum d (n + 1) * w n :=
        add_nonneg ha hb
      _ = preSum (fun i => d i * w i) (n + 1) := by
        unfold preSum
        simp only [Finset.sum_range_succ, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring

/-- The correlation dominates the squared norm of the decreasing,
prefix - majorized vector. Only the second vector needs to be decreasing. -/
private theorem correlation_ge (n : ℕ) (s l : ℕ → ℝ)
    (hp : ∀ k ≤ n, preSum l k ≤ preSum s k)
    (hl : ∀ i < n, 0 ≤ l i)
    (hd : ∀ i j, i ≤ j → j < n → l j ≤ l i) :
    preSum (fun i => (l i)^2) n ≤ preSum (fun i => s i * l i) n := by
  have h := weighted_nonneg n (fun i => s i - l i) l
    (fun k hk => by
      simpa only [preSum,Finset.sum_sub_distrib] using sub_nonneg.mpr (hp k hk)) hl hd
  have e : preSum (fun i => (s i - l i) * l i) n =
      preSum (fun i => s i * l i) n - preSum (fun i => (l i)^2) n := by
    unfold preSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rwa [e, sub_nonneg] at h


private theorem cauchy (n : ℕ) (a b : ℕ → ℝ) :
    preSum (fun i => a i * b i) n ^ 2 ≤
      preSum (fun i => (a i)^2) n * preSum (fun i => (b i)^2) n := by
  exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) a b

private theorem square_expansion (n : ℕ) (s l : ℕ → ℝ) :
    (preSum (fun i => (s i - l i)^2) n = preSum (fun i => (s i)^2) n +
      preSum (fun i => (l i)^2) n - 2 * preSum (fun i => s i * l i) n) ∧
    (preSum (fun i => (s i + l i)^2) n = preSum (fun i => (s i)^2) n +
      preSum (fun i => (l i)^2) n + 2 * preSum (fun i => s i * l i) n) := by
  constructor
  · unfold preSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · unfold preSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Quantitative rounding of the coordinate squares, with the sharper
4η - 3η² radicand. The correlation, not separate norm estimates, enters
through the product (2 - η - 2c)(2 - η + 2c). -/
private theorem square_l1_rounding (n : ℕ) (s l : ℕ → ℝ) (η : ℝ)
    (hs : preSum (fun i => (s i)^2) n = 1)
    (hl : preSum (fun i => (l i)^2) n = 1 - η)
    (hc : preSum (fun i => (l i)^2) n ≤ preSum (fun i => s i * l i) n) :
    0 ≤ η ∧ preSum (fun i => |(s i)^2 - (l i)^2|) n ≤ Real.sqrt (4 * η - 3 * η^2) := by
  obtain ⟨hm,hp⟩ := square_expansion n s l
  let c := preSum (fun i => s i * l i) n
  have hln : 0 ≤ preSum (fun i => (l i)^2) n := Finset.sum_nonneg (fun i _ => sq_nonneg (l i))
  have hmn : 0 ≤ preSum (fun i => (s i - l i)^2) n :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (s i - l i))
  rw [hl] at hln
  rw [hl] at hc
  change 1 - η ≤ c at hc
  change preSum (fun i => (s i - l i)^2) n = _ + _ - 2 * c at hm
  change preSum (fun i => (s i + l i)^2) n = _ + _ + 2 * c at hp
  rw [hs,hl] at hm hp
  have hη : 0 ≤ η := by linarith
  refine ⟨hη, ?_⟩
  have hcSq : (1 - η)^2 ≤ c^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ c + (1 - η) by linarith)]
  have hCS := cauchy n (fun i => |s i - l i|) (fun i => |s i + l i|)
  simp only [sq_abs] at hCS
  have he : preSum (fun i => |s i - l i| * |s i + l i|) n =
      preSum (fun i => |(s i)^2 - (l i)^2|) n := by
    apply Finset.sum_congr rfl
    intro i _
    change |s i - l i| * |s i + l i| = |(s i)^2 - (l i)^2|
    rw [← abs_mul]
    congr 1
    ring
  rw [he,hm,hp] at hCS
  have hb : preSum (fun i => |(s i)^2 - (l i)^2|) n ^2 ≤ 4 * η - 3 * η^2 := by
    nlinarith
  exact (Real.le_sqrt (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (le_trans (sq_nonneg _) hb)).2 hb

/-- Squared masses of a fixed grouping, used both for the spectral values and
the corresponding Schmidt coefficients. -/
def grouped {L : Type*} [DecidableEq L] (n : ℕ) (tag : ℕ → L) (s : ℕ → ℝ) (a : L) : ℝ :=
  preSum (fun i => if tag i = a then (s i)^2 else 0) n

private theorem grouped_l1_le {L : Type*} [Fintype L] [DecidableEq L]
    (n : ℕ) (tag : ℕ → L) (s l : ℕ → ℝ) :
    ∑ a : L, |grouped n tag s a - grouped n tag l a| ≤
      preSum (fun i => |(s i)^2 - (l i)^2|) n := by
  calc
    _ = ∑ a : L, |∑ i ∈ Finset.range n, if tag i = a then (s i)^2 - (l i)^2 else 0| := by
      apply Finset.sum_congr rfl
      intro a _
      unfold grouped preSum
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : tag i = a <;> simp [h]
    _ ≤ ∑ a : L, ∑ i ∈ Finset.range n, (if tag i = a then |(s i)^2 - (l i)^2| else 0) := by
      apply Finset.sum_le_sum
      intro a _
      have h := Finset.abs_sum_le_sum_abs
        (fun i => if tag i = a then (s i)^2 - (l i)^2 else 0) (Finset.range n)
      simpa only [apply_ite abs,abs_zero] using h
    _ = _ := by
      unfold preSum
      rw [Finset.sum_comm]
      simp [eq_comm]

/-- The spectral and Schmidt masses share labels. A subnormalized spectral
error E - η therefore gives an actual Schmidt grouping within E - η + sqrt(4η - 3η²). -/
private theorem sorted_group_rounding {L : Type*} [Fintype L] [DecidableEq L]
    (n : ℕ) (tag : ℕ → L) (s l : ℕ → ℝ) (w : L → ℝ) (η E : ℝ)
    (hs : preSum (fun i => (s i)^2) n = 1)
    (hl : preSum (fun i => (l i)^2) n = 1 - η)
    (hf : ∀ k ≤ n, preSum l k ≤ preSum s k)
    (hn : ∀ i < n, 0 ≤ l i)
    (hd : ∀ i j, i ≤ j → j < n → l j ≤ l i)
    (hE : ∑ a : L, |w a - grouped n tag l a| ≤ E - η) :
    0 ≤ η ∧ ∑ a : L, |w a - grouped n tag s a| ≤ E - η + Real.sqrt (4 * η - 3 * η^2) := by
  obtain ⟨hη,hr⟩ := square_l1_rounding n s l η hs hl (correlation_ge n s l hf hn hd)
  refine ⟨hη, ?_⟩
  calc
    _ ≤ (∑ a : L, |w a - grouped n tag l a|) +
        ∑ a : L, |grouped n tag s a - grouped n tag l a| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      rw [abs_sub_comm (grouped n tag s a) (grouped n tag l a)]
      exact abs_sub_le (w a) (grouped n tag l a) (grouped n tag s a)
    _ ≤ _ := add_le_add hE ((grouped_l1_le n tag s l).trans hr)

private theorem total_grouped {L : Type*} [Fintype L] [DecidableEq L]
    (n : ℕ) (tag : ℕ → L) (s : ℕ → ℝ) :
    (∑ a : L, grouped n tag s a) = preSum (fun i => (s i)^2) n := by
  unfold grouped preSum
  rw [Finset.sum_comm]
  simp [eq_comm]

private theorem abs_sub_min_identity (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  by_cases h : a ≤ b
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have h' : b ≤ a := (lt_of_not_ge h).le
    rw [min_eq_right h',abs_of_nonneg (sub_nonneg.mpr h')]
    ring

/-- A cap - overlap assertion is sufficient: the deficit η is forced to lie
in [0,E / 2], with no need for a separate bound on its sign. -/
private theorem cap_rounding {L : Type*} [Fintype L] [DecidableEq L]
    (n : ℕ) (tag : ℕ → L) (s l : ℕ → ℝ) (w : L → ℝ) (η E : ℝ)
    (hs : preSum (fun i => (s i)^2) n = 1)
    (hl : preSum (fun i => (l i)^2) n = 1 - η)
    (hf : ∀ k ≤ n, preSum l k ≤ preSum s k)
    (hn : ∀ i < n, 0 ≤ l i)
    (hd : ∀ i j, i ≤ j → j < n → l j ≤ l i)
    (hw : ∑ a : L, w a = 1)
    (hcap : 1 - E / 2 ≤ ∑ a : L, min (w a) (grouped n tag l a)) :
    0 ≤ η ∧ η ≤ E / 2 ∧
      ∑ a : L, |w a - grouped n tag s a| ≤ E - η + Real.sqrt (4 * η - 3 * η^2) := by
  have hsum := total_grouped n tag l
  rw [hl] at hsum
  have hca : (∑ a : L, min (w a) (grouped n tag l a)) ≤ 1 - η := by
    rw [← hsum]
    exact Finset.sum_le_sum fun _ _ => min_le_right _ _
  have he : ∑ a : L, |w a - grouped n tag l a| ≤ E - η := by
    simp only [abs_sub_min_identity,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum,hw,hsum]
    linarith
  obtain ⟨he0, hr⟩ := sorted_group_rounding n tag s l w η E hs hl hf hn hd he
  exact ⟨he0,by linarith,hr⟩

end RTMajorizationRound


namespace RoundingEnvelope
noncomputable def rad (t : ℝ) := 4 * t - 3 * t^2
noncomputable def lift (t : ℝ) := Real.sqrt (rad t) - t

private theorem rad_nonneg (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) : 0 ≤ rad t := by
  unfold rad
  nlinarith [mul_nonneg ht (show 0 ≤ 4 - 3 * t by linarith)]

private theorem universal_turn (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) : lift t ≤ 2 / 3 := by
  have hs := Real.sq_sqrt (rad_nonneg t ht ht')
  have hs0 := Real.sqrt_nonneg (rad t)
  unfold lift
  by_contra! h
  have hp := mul_pos (show 0 < Real.sqrt (rad t) - (t + 2 / 3) by linarith)
    (show 0 < Real.sqrt (rad t) + (t + 2 / 3) by linarith)
  change Real.sqrt (rad t)^2 = 4 * t - 3 * t^2 at hs
  nlinarith [sq_nonneg (t - 1 / 3)]

private theorem increasing_to_turn (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 3) :
    lift x ≤ lift y := by
  have hx1 : x ≤ 1 := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hA := Real.sq_sqrt (rad_nonneg x hx hx1)
  have hB := Real.sq_sqrt (rad_nonneg y hy0 hy1)
  have hA0 := Real.sqrt_nonneg (rad x)
  have hB0 := Real.sqrt_nonneg (rad y)
  have ht := universal_turn x hx hx1
  unfold lift at ht ⊢
  have hfactor : 0 ≤ 4 - 2 * x - 4 * y - 2 * Real.sqrt (rad x) := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hxy) hfactor
  by_contra! hh
  have hpos := mul_pos (show 0 < (Real.sqrt (rad x) + (y - x)) - Real.sqrt (rad y) by linarith)
    (show 0 < (Real.sqrt (rad x) + (y - x)) + Real.sqrt (rad y) by linarith)
  change Real.sqrt (rad x)^2 = 4 * x - 3 * x^2 at hA
  change Real.sqrt (rad y)^2 = 4 * y - 3 * y^2 at hB
  nlinarith

/-- Eliminate the unknown spectral deficit over the entire physical error range. -/
private theorem exact_envelope (E D t : ℝ) (hE : E ≤ 2)
    (ht : 0 ≤ t) (hte : t ≤ E / 2) (hD : D ≤ E + lift t) :
    (D ≤ E + 2 / 3) ∧ (E ≤ 2 / 3 → D ≤ E / 2 + Real.sqrt (2 * E - 3 * E^2 / 4)) := by
  refine ⟨by linarith [universal_turn t ht (show t ≤ 1 by linarith)], ?_⟩
  intro hs
  have hm := increasing_to_turn t (E / 2) ht hte (by linarith)
  unfold lift at hm
  have hr : rad (E / 2) = 2 * E - 3 * E^2 / 4 := by unfold rad; ring
  rw [hr] at hm
  unfold lift at hD
  linarith

/-- Rational algebraic form of the small - error branch, convenient for promise gaps. -/
private theorem small_error_quadratic (E D t : ℝ) (hE : 0 ≤ E) (hE' : E ≤ 2 / 3)
    (hD0 : 0 ≤ D) (ht : 0 ≤ t) (hte : t ≤ E / 2) (hD : D ≤ E + lift t) :
    D^2 ≤ (2 + D) * E - E^2 := by
  have h := (exact_envelope E D t (by linarith) ht hte hD).2 hE'
  have hR : 0 ≤ 2 * E - 3 * E^2 / 4 := by
    nlinarith [mul_nonneg hE (show 0 ≤ 2 - 3 * E / 4 by linarith)]
  by_cases hp : D ≤ E / 2
  · have h0 := mul_nonneg hD0 (show 0 ≤ E - D by linarith)
    have h1 := mul_nonneg hE (show 0 ≤ 2 - E by linarith)
    nlinarith
  · have hs := Real.sq_sqrt hR
    have hs0 := Real.sqrt_nonneg (2 * E - 3 * E^2 / 4)
    have h0 := mul_nonneg (show 0 ≤ Real.sqrt (2 * E - 3 * E^2 / 4) - (D - E / 2) by linarith)
      (show 0 ≤ Real.sqrt (2 * E - 3 * E^2 / 4) + (D - E / 2) by linarith)
    nlinarith

/-- A no - partition spacing 2 / T implies a stronger inverse - polynomial gap
than the coarse square - root estimate alone. -/
private theorem strong_spacing_gap (T E D t : ℝ) (hT : 2 ≤ T)
    (hE : 0 ≤ E) (hD0 : 0 ≤ D)
    (hDmin : 2 / T ≤ D) (ht : 0 ≤ t) (hte : t ≤ E / 2)
    (hD : D ≤ E + lift t) : 2 / (T * (T + 1)) < E := by
  by_contra! hsmall
  have hTpos : 0 < T := by linarith
  have hTP : 0 < T * (T + 1) := by positivity
  have hm := (le_div_iff₀ hTP).mp hsmall
  have hE1 : E ≤ 2 / 3 := by
    have hF : 6 ≤ T * (T + 1) := by nlinarith [sq_nonneg (T - 2)]
    have hF' := mul_le_mul_of_nonneg_left hF hE
    nlinarith
  have hs := small_error_quadratic E D t hE hE1 hD0 ht hte hD
  have hMin := (div_le_iff₀ hTpos).mp hDmin
  have hz : 0 < D := by nlinarith
  have hDE : E ≤ D := by
    have hEt : E * T ≤ 2 := by
      have hn := mul_nonneg hE (show 0 ≤ T^2 by positivity)
      nlinarith
    exact le_of_mul_le_mul_right (le_trans hEt hMin) hTpos
  have h1 := mul_nonneg (sub_nonneg.mpr hsmall) (show 0 ≤ (2 + D) by linarith)
  have hdiv : 0 < 2 / T := by positivity
  have hs0 : (2 / T)^2 ≤ (2 + 2 / T) * E - E^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hDmin) (show 0 ≤ D + 2 / T - E by linarith)
    nlinarith
  have hB : (2 + 2 / T) * (2 / (T * (T + 1))) = (2 / T)^2 := by
    field_simp
  have hA := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (2 + 2 / T) by linarith)
  rw [hB] at hA
  have hepos : 0 < E := by nlinarith [sq_pos_of_pos hdiv]
  nlinarith [sq_pos_of_pos hepos]

noncomputable def lower (D : ℝ) :=
  (D + 2 - Real.sqrt (4 + 4 * D - 3 * D^2)) / 2

/-- Inverse form over the complete physical range, with the large - error branch
kept distinct from the sharp small - error branch. -/
private theorem inverse_envelope (E D t : ℝ) (hE : E ≤ 2) (hD0 : 0 ≤ D)
    (ht : 0 ≤ t) (hte : t ≤ E / 2) (hD : D ≤ E + lift t) :
    (D ≤ 4 / 3 → lower D ≤ E) ∧ (4 / 3 ≤ D → D - 2 / 3 ≤ E) := by
  refine ⟨?_, fun _ => by linarith [(exact_envelope E D t hE ht hte hD).1]⟩
  intro hD'
  have hE0 : 0 ≤ E := by linarith
  have hR : 0 ≤ 4 + 4 * D - 3 * D^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - D by linarith) (show 0 ≤ 3 * D + 2 by linarith)]
  have hs := Real.sq_sqrt hR
  have hs0 := Real.sqrt_nonneg (4 + 4 * D - 3 * D^2)
  unfold lower
  by_cases hsmall : E ≤ 2 / 3
  · have hq := small_error_quadratic E D t hE0 hsmall hD0 ht hte hD
    by_contra! hn
    have H := mul_pos (show 0 < (D + 2 - 2 * E) - Real.sqrt (4 + 4 * D - 3 * D^2) by linarith)
      (show 0 < (D + 2 - 2 * E) + Real.sqrt (4 + 4 * D - 3 * D^2) by linarith)
    nlinarith
  · by_contra! hn
    have hp := mul_nonneg (show 0 ≤ 4 / 3 - D by linarith) (show 0 ≤ 4 * D + 8 / 3 by linarith)
    have H := mul_pos (show 0 < (D + 2 / 3) - Real.sqrt (4 + 4 * D - 3 * D^2) by linarith)
      (show 0 < (D + 2 / 3) + Real.sqrt (4 + 4 * D - 3 * D^2) by linarith)
    nlinarith

noncomputable def curve (E : ℝ) := E / 2 + Real.sqrt (2 * E - 3 * E^2 / 4)
end RoundingEnvelope


open scoped BigOperators

namespace RTPartitionEnvelope
open RTMajorizationRound RoundingEnvelope

noncomputable def partitionError {L : Type*} [Fintype L] [DecidableEq L]
    (n : ℕ) (s : ℕ → ℝ) (w : L → ℝ) (f : Fin n → L) : ℝ :=
  ∑ a : L, |w a - ∑ i : Fin n, if f i = a then (s i)^2 else 0|

noncomputable def partitionDistance {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (n : ℕ) (s : ℕ → ℝ) (w : L → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n → L)).inf' Finset.univ_nonempty (partitionError n s w)

private theorem distance_nonneg {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (n : ℕ) (s : ℕ → ℝ) (w : L → ℝ) : 0 ≤ partitionDistance n s w := by
  classical
  apply Finset.le_inf'
  intro f _
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem distance_le_tag {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (n : ℕ) (tag : ℕ → L) (s : ℕ → ℝ) (w : L → ℝ) :
    partitionDistance n s w ≤ ∑ a : L, |w a - grouped n tag s a| := by
  have h := Finset.inf'_le (partitionError n s w)
    (Finset.mem_univ (fun i : Fin n => tag i))
  have hg : partitionError n s w (fun i : Fin n => tag i) =
      ∑ a : L, |w a - grouped n tag s a| := by
    unfold partitionError
    apply Finset.sum_congr rfl
    intro a _
    unfold grouped preSum
    rw [Fin.sum_univ_eq_sum_range fun i : ℕ => if tag i = a then (s i)^2 else 0]
  rw [← hg]
  exact h

/-- The literal finite partition - distance readout, uniform in the label count. -/
noncomputable def readPartition (n m : ℕ) (s : ℕ → ℝ) (w : Fin (m + 1) → ℝ) : ℝ :=
  partitionDistance n s w

end RTPartitionEnvelope

open RTPartitionEnvelope RoundingEnvelope RTMajorizationRound

/-- The scalar stage of fixed - Schmidt matched - label stability, from sorted
spectral observations to the nearest exact labeled Schmidt partition. -/
theorem sorted_partition_inverse (n : ℕ) :
    let observed := readPartition n
    ∀ (m : ℕ) (s : ℕ → ℝ) (w : Fin (m + 1) → ℝ),
    let D := observed m s w
    ∀ (tag : ℕ → Fin (m + 1)) (l : ℕ → ℝ) (eta E : ℝ),
      E ≤ 2 →
      preSum (fun i => (s i)^2) n = 1 →
      preSum (fun i => (l i)^2) n = 1 - eta →
      (∀ k ≤ n, preSum l k ≤ preSum s k) →
      (∀ i < n, 0 ≤ l i) →
      (∀ i j, i ≤ j → j < n → l j ≤ l i) →
      (∑ a : Fin (m + 1), w a = 1) →
      (1 - E / 2 ≤ ∑ a : Fin (m + 1), min (w a) (grouped n tag l a)) →
      (D ≤ 4 / 3 → lower D ≤ E) ∧ (4 / 3 ≤ D → D - 2 / 3 ≤ E) ∧
      (E ≤ 2 / 3 → D ≤ curve E) ∧
      ∀ T : ℝ, 2 ≤ T → 2 / T ≤ D → 2 / (T * (T + 1)) < E := by
  intro observed m s w D tag l eta E hE hs hl hf hn hd hw hc
  have rr := cap_rounding n tag s l w eta E hs hl hf hn hd hw hc
  have hB := (distance_le_tag n tag s w).trans rr.2.2
  change D ≤ E - eta + Real.sqrt (4 * eta - 3 * eta^2) at hB
  have hb : D ≤ E + lift eta := by unfold lift rad; linarith
  have hD : 0 ≤ D := distance_nonneg n s w
  have i := inverse_envelope E D eta hE hD rr.1 rr.2.1 hb
  refine ⟨i.1,i.2,(exact_envelope E D eta hE rr.1 rr.2.1 hb).2,?_⟩
  intro T hT hDmin
  exact strong_spacing_gap T E D eta hT (by linarith [rr.1,rr.2.1]) hD hDmin rr.1 rr.2.1 hb
end D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability
