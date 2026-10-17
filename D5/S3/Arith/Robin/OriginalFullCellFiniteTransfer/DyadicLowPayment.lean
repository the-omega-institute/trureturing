/- GID: D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer/DyadicLowPayment
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalFullCellFiniteTransfer/DyadicLowPayment
   mirror-E: none(waiver:finite-analytic-inequality)
   anchors: []
   utility: none
   digest: Disjoint actual Mobius dyadic pairs reduce the entire finite low payment and feed the unchanged full-positive transfer with its complete mean and high terms. -/

import D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment

open D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer
open D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
  (centered variation variation_nonneg centered_pair_variation_sharp_bound log_bounds)
open D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.DyadicPrimitive
  (radius centered_pair_bound)
open D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
  (mobiusPrefix oddCoefficient twice_coefficient)

/-- Only internal odd pairs at scales at least three are selected. -/
def pairs (q : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 q).filter (fun d => Odd d ∧ 3 ≤ d ∧ 2*d ≤ q)

/-- The literal finite complement includes scales one and two and every upper singleton. -/
def unpaired (q : ℕ) : Finset ℕ :=
  Ioc 0 q \ (pairs q ∪ (pairs q).image (fun d => 2*d))

/-- Scale one costs exactly zero; every other scale uses the same real d/16 price. -/
def singlePrice (N d : ℕ) : ℝ :=
  if d = 1 then 0 else Real.log ((N : ℝ)/d)*(d : ℝ)/16

def jointPrice (N d : ℕ) : ℝ :=
  radius d (Real.log ((N : ℝ)/d)) (Real.log ((N : ℝ)/(2*d : ℕ)))

/-- The unchanged literal h=q+1 boundary price. -/
def boundaryPrice (N q : ℕ) : ℝ := |mobiusPrefix q+2|*singlePrice N (q+1)

/-- Actual magnitudes are retained, including vanishing Mobius coefficients. -/
def pairedCoefficient (N q : ℕ) : ℝ :=
  (∑ d ∈ pairs q, |(ArithmeticFunction.moebius d : ℝ)|*jointPrice N d)+
    (∑ k ∈ unpaired q, |(ArithmeticFunction.moebius k : ℝ)|*singlePrice N k)+
      boundaryPrice N q

/-- The identical actual-coefficient benchmark with separate single-scale payments. -/
def termwiseCoefficient (N q : ℕ) : ℝ :=
  (∑ k ∈ Ioc 0 q, |(ArithmeticFunction.moebius k : ℝ)|*singlePrice N k)+
    boundaryPrice N q

private theorem pair_properties {q d : ℕ} (hd : d ∈ pairs q) :
    Odd d ∧ 3 ≤ d ∧ 2*d ≤ q := (mem_filter.mp hd).2

private theorem paired_subset (q : ℕ) :
    pairs q ∪ (pairs q).image (fun d => 2*d) ⊆ Ioc 0 q := by
  intro k hk
  rcases mem_union.mp hk with hk | hk
  · exact (mem_filter.mp hk).1
  · obtain ⟨d, hd, rfl⟩ := mem_image.mp hk
    have hp := pair_properties hd
    exact mem_Ioc.mpr ⟨by omega, hp.2.2⟩

private theorem paired_disjoint (q : ℕ) :
    Disjoint (pairs q) ((pairs q).image (fun d => 2*d)) := by
  apply disjoint_left.mpr
  intro k hk he
  obtain ⟨d, _, rfl⟩ := mem_image.mp he
  obtain ⟨t, ht⟩ := (pair_properties hk).1
  omega

private theorem finite_split (q : ℕ) (F : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 q, F k) =
      (∑ d ∈ pairs q, (F d+F (2*d)))+∑ k ∈ unpaired q, F k := by
  classical
  have he := sum_sdiff (paired_subset q) (f := F)
  rw [sum_union (paired_disjoint q), sum_image (by
    intro d _ e _ h
    omega), ← sum_add_distrib] at he
  change (∑ k ∈ unpaired q, F k)+(∑ d ∈ pairs q, (F d+F (2*d))) = _ at he
  linarith

private theorem actual_twice {q d : ℕ} (hd : d ∈ pairs q) :
    (ArithmeticFunction.moebius (2*d) : ℝ) = -(ArithmeticFunction.moebius d : ℝ) := by
  simpa only [oddCoefficient, if_pos (pair_properties hd).1] using twice_coefficient d

private theorem log_parameters {N q d : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (hd : d ∈ pairs q) :
    0 < Real.log ((N : ℝ)/(2*d : ℕ)) ∧
      Real.log ((N : ℝ)/(2*d : ℕ)) < Real.log ((N : ℝ)/d) := by
  have hp := pair_properties hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2d0 : (0 : ℝ) < (2*d : ℕ) := by exact_mod_cast (show 0 < 2*d by omega)
  have hdN : ((2*d : ℕ) : ℝ) < N := by exact_mod_cast (show 2*d < N by omega)
  constructor
  · exact Real.log_pos ((one_lt_div h2d0).mpr hdN)
  · apply Real.log_lt_log (by positivity)
    apply div_lt_div_of_pos_left hN0 hd0
    push_cast
    linarith

private theorem single_bound {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hkN : k ≤ N) (b : ℕ → ℝ) :
    |centeredLogPair N b k| ≤ singlePrice N k*variation N b := by
  by_cases hk1 : k = 1
  · subst k
    simp [centeredLogPair, centeredPair, centered, singlePrice]
  · have hl := (log_bounds hk hkN).1
    rw [singlePrice, if_neg hk1, centeredLogPair, abs_mul, abs_of_nonneg hl]
    have hp := mul_le_mul_of_nonneg_left (centered_pair_variation_sharp_bound hN b hk) hl
    change Real.log ((N : ℝ)/k)*|centeredPair N b k| ≤ _ at hp
    convert hp using 1 <;> ring

private theorem joint_bound {N q d : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (hd : d ∈ pairs q) (b : ℕ → ℝ) :
    |centeredLogPair N b d-centeredLogPair N b (2*d)| ≤
      jointPrice N d*variation N b := by
  have hp := pair_properties hd
  have hl := log_parameters hN hq hd
  have he : centeredLogPair N b d-centeredLogPair N b (2*d) =
      ∑ m ∈ Ico N (2*N), b m*(Real.log ((N : ℝ)/d)*centered d m-
        Real.log ((N : ℝ)/(2*d : ℕ))*centered (2*d) m) := by
    unfold centeredLogPair centeredPair
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    ring
  rw [he]
  exact centered_pair_bound (by omega) (by omega) b (lt_trans hl.1 hl.2)
    (Real.log ((N : ℝ)/(2*d : ℕ)))


private theorem price_gap {N q d : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (hd : d ∈ pairs q) :
    singlePrice N d+singlePrice N (2*d)-jointPrice N d =
      (d : ℝ)*Real.log ((N : ℝ)/(2*d : ℕ))*
        (3*Real.log ((N : ℝ)/d)-2*Real.log ((N : ℝ)/(2*d : ℕ)))/
          (16*(2*Real.log ((N : ℝ)/d)-Real.log ((N : ℝ)/(2*d : ℕ)))) := by
  have hp := pair_properties hd
  have hl := log_parameters hN hq hd
  have hD : 0 < 2*Real.log ((N : ℝ)/d)-Real.log ((N : ℝ)/(2*d : ℕ)) := by linarith
  simp only [singlePrice, if_neg (by omega : d ≠ 1), if_neg (by omega : 2*d ≠ 1),
    jointPrice, radius, if_neg (not_le.mpr hl.1), if_pos hl.2]
  push_cast at hD ⊢
  field_simp [ne_of_gt hD]
  <;> ring

private theorem price_gap_pos {N q d : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2)
    (hd : d ∈ pairs q) : 0 < singlePrice N d+singlePrice N (2*d)-jointPrice N d := by
  rw [price_gap hN hq hd]
  have hp := pair_properties hd
  have hl := log_parameters hN hq hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply div_pos
  · exact mul_pos (mul_pos hd0 hl.1) (by linarith)
  · linarith

private theorem coefficient_difference {N q : ℕ} :
    termwiseCoefficient N q-pairedCoefficient N q =
      ∑ d ∈ pairs q, |(ArithmeticFunction.moebius d : ℝ)|*
        (singlePrice N d+singlePrice N (2*d)-jointPrice N d) := by
  have hs := finite_split q (fun k => |(ArithmeticFunction.moebius k : ℝ)|*singlePrice N k)
  have hp : (∑ d ∈ pairs q,
      (|(ArithmeticFunction.moebius d : ℝ)|*singlePrice N d+
        |(ArithmeticFunction.moebius (2*d) : ℝ)|*singlePrice N (2*d))) =
      ∑ d ∈ pairs q, |(ArithmeticFunction.moebius d : ℝ)|*(singlePrice N d+singlePrice N (2*d)) := by
    apply sum_congr rfl
    intro d hd
    rw [actual_twice hd, abs_neg]
    ring
  rw [hp] at hs
  unfold termwiseCoefficient pairedCoefficient
  rw [hs]
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  ring

/-- The d=3 pair strictly saves coefficient throughout the complete legal growing range. -/
theorem coefficient_saving {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2) (h6 : 6 ≤ q) :
    pairedCoefficient N q < termwiseCoefficient N q := by
  have h3 : 3 ∈ pairs q := by
    have ho : Odd (3 : ℕ) := ⟨1, by omega⟩
    simp only [pairs, mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, ho, by omega, by omega⟩
  have hpos : 0 < termwiseCoefficient N q-pairedCoefficient N q := by
    rw [coefficient_difference]
    apply sum_pos'
    · intro d hd
      exact mul_nonneg (abs_nonneg _) (price_gap_pos hN hq hd).le
    · refine ⟨3, h3, ?_⟩
      have hmu : (ArithmeticFunction.moebius 3 : ℝ) = -1 := by
        norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
      rw [hmu]
      norm_num only [abs_neg, abs_one, one_mul]
      exact price_gap_pos hN hq h3
  linarith

/-- The entire signed low bound and its consumption by the original full-positive transfer. -/
theorem full_positive_transfer {N q : ℕ} (hN : 3 ≤ N) (hq : q ≤ N-2) (b : ℕ → ℝ) :
    (|lowError N q b| ≤ pairedCoefficient N q*variation N b/Real.log N) ∧
    ∀ (F : ℕ → ℝ) (ε c : ℝ), 0 ≤ ε → 0 ≤ c →
      (∀ m ∈ Ico N (2*N), 0 ≤ b m) →
      (∀ k ∈ Ico (q+1) N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) →
      |pairing N b-replacement N q b F-meanCorrection N q b| ≤
        (ε+c/(q+1 : ℕ))/Real.log N*((N : ℝ)*totalMass N b*
          (1+2*Real.log ((N : ℝ)/(q+1 : ℕ))^2+
            2*Real.log ((N : ℝ)/(q+1 : ℕ))*(1+Real.log (2*(N : ℝ)/(q+1 : ℕ)))))+
        pairedCoefficient N q*variation N b/Real.log N := by
  have hlow : |lowError N q b| ≤ pairedCoefficient N q*variation N b/Real.log N := by
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hs := finite_split q (fun k => (ArithmeticFunction.moebius k : ℝ)*centeredLogPair N b k)
    have hpair : (∑ d ∈ pairs q,
        ((ArithmeticFunction.moebius d : ℝ)*centeredLogPair N b d+
          (ArithmeticFunction.moebius (2*d) : ℝ)*centeredLogPair N b (2*d))) =
        ∑ d ∈ pairs q, (ArithmeticFunction.moebius d : ℝ)*
          (centeredLogPair N b d-centeredLogPair N b (2*d)) := by
      apply sum_congr rfl
      intro d hd
      rw [actual_twice hd]
      ring
    rw [hpair] at hs
    have hp : |∑ d ∈ pairs q, (ArithmeticFunction.moebius d : ℝ)*
        (centeredLogPair N b d-centeredLogPair N b (2*d))| ≤
        (∑ d ∈ pairs q, |(ArithmeticFunction.moebius d : ℝ)|*jointPrice N d)*variation N b := by
      calc
        _ ≤ ∑ d ∈ pairs q, |(ArithmeticFunction.moebius d : ℝ)*
            (centeredLogPair N b d-centeredLogPair N b (2*d))| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ pairs q, (|(ArithmeticFunction.moebius d : ℝ)|*jointPrice N d)*variation N b := by
          apply sum_le_sum
          intro d hd
          rw [abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (joint_bound hN hq hd b) (abs_nonneg _)
        _ = _ := (sum_mul _ _ _).symm
    have hu : |∑ k ∈ unpaired q, (ArithmeticFunction.moebius k : ℝ)*centeredLogPair N b k| ≤
        (∑ k ∈ unpaired q, |(ArithmeticFunction.moebius k : ℝ)|*singlePrice N k)*variation N b := by
      calc
        _ ≤ ∑ k ∈ unpaired q, |(ArithmeticFunction.moebius k : ℝ)*centeredLogPair N b k| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ unpaired q, (|(ArithmeticFunction.moebius k : ℝ)|*singlePrice N k)*variation N b := by
          apply sum_le_sum
          intro k hk
          have hk' := mem_Ioc.mp (mem_sdiff.mp hk).1
          rw [abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (single_bound (by omega) hk'.1 (by omega) b) (abs_nonneg _)
        _ = _ := (sum_mul _ _ _).symm
    have hb : |(mobiusPrefix q+2)*centeredLogPair N b (q+1)| ≤
        boundaryPrice N q*variation N b := by
      rw [abs_mul, boundaryPrice, mul_assoc]
      exact mul_le_mul_of_nonneg_left (single_bound (by omega) (by omega) (by omega) b) (abs_nonneg _)
    unfold lowError
    rw [abs_div, abs_of_pos hL, hs]
    apply div_le_div_of_nonneg_right _ hL.le
    calc
      _ ≤ |∑ d ∈ pairs q, (ArithmeticFunction.moebius d : ℝ)*
            (centeredLogPair N b d-centeredLogPair N b (2*d))|+
          |∑ k ∈ unpaired q, (ArithmeticFunction.moebius k : ℝ)*centeredLogPair N b k|+
            |(mobiusPrefix q+2)*centeredLogPair N b (q+1)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hp hu) hb
      _ = _ := by unfold pairedCoefficient; ring
  refine ⟨hlow, ?_⟩
  intro F ε c hε hc hb herr
  exact transfer_of_low_bound hN hq b F ε c hε hc hb herr _ hlow

#print axioms coefficient_saving
#print axioms full_positive_transfer

end D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer.DyadicLowPayment
