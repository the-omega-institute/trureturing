/- GID: D5/S3/Arith/FactorialRatio/Weighted/CompactBudget
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/Weighted/CompactBudget
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Padics.PadicVal.Basic]
   utility: none
   digest: Prime-power weighted products over the actual legal compact parameters. -/

import D5.S3.Arith.FactorialRatio.Compression.SharpLoss
import D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
import Mathlib.Tactic

/-!
The weighted factorial is evaluated at each actual compact argument before
taking its quotient and the gcd over legal parameters.  The exact valuation
bridge identifies that gcd quotient with the shared floor-defect budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Weighted.CompactBudget

open Finset
open scoped Nat
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open D5.S3.Arith.FactorialRatio.Compression.SharpLoss
open D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd

/-- The actual legal compact parameters, including b=0. -/
def compactParameters (r s : ℕ) : Finset ℕ := range (s / r + 1)

/-- The composition head associated with rank r and window s. -/
def compactHeight (r s : ℕ) : ℕ := r * s + r - 1

/-- Convert the positive-power convention to CompositionGcd's zero-based index. -/
def shiftedWeights (c : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ := fun p j => c p (j + 1)

/-- The actual weighted compact product, with the same parameter in every factor. -/
def compactWeightedProduct (r s : ℕ) (c : ℕ → ℕ → ℕ) (b : ℕ) : ℕ :=
  ∏ i ∈ range r,
    weightedValue (compactHeight r s) (shiftedWeights c) ((i + 1) * b) /
      weightedValue (compactHeight r s) (shiftedWeights c) b *
        weightedValue (compactHeight r s) (shiftedWeights c) (s - i * b)

/-- The gcd over the actual legal compact products. -/
def compactWeightedGcd (r s : ℕ) (c : ℕ → ℕ → ℕ) : ℕ :=
  (compactParameters r s).gcd (compactWeightedProduct r s c)

/-- The full-composition weighted gcd at the same head and number of parts. -/
def compositionWeightedTail (r s : ℕ) (c : ℕ → ℕ → ℕ) : ℕ :=
  (Finset.Nat.antidiagonalTuple ((r - 1) + 1) (compactHeight r s - (r - 1))).gcd
    (weightedProduct (compactHeight r s) (shiftedWeights c))

private theorem compositionWeightedTail_eq (r s : ℕ) (c : ℕ → ℕ → ℕ) :
    compositionWeightedTail r s c =
      weightedTail (compactHeight r s) (r - 1) (shiftedWeights c) := by
  apply weighted_composition_gcd
  unfold compactHeight
  omega

/-- The actual integer quotient of the compact gcd by the full-composition gcd. -/
def compactWeightedExcess (r s : ℕ) (c : ℕ → ℕ → ℕ) : ℕ :=
  compactWeightedGcd r s c / compositionWeightedTail r s c

private theorem legal_parameter_bound {r s b : ℕ} (hr : 0 < r)
    (hb : b ∈ compactParameters r s) : r * b ≤ s := by
  have h := mem_range.mp hb
  have := (Nat.le_div_iff_mul_le hr).mp (show b ≤ s / r by omega)
  simpa [mul_comm] using this

private theorem height_eq {r s : ℕ} (hr : 1 ≤ r) :
    compactHeight r s = r * s + (r - 1) := by
  unfold compactHeight
  omega

private theorem value_mono_dvd (H : ℕ) (c : ℕ → ℕ → ℕ)
    {m n : ℕ} (h : m ≤ n) : weightedValue H c m ∣ weightedValue H c n := by
  unfold weightedValue
  apply prod_dvd_prod_of_dvd
  intro p _
  apply pow_dvd_pow
  unfold weightedExponent
  exact sum_le_sum fun j _ => Nat.mul_le_mul_left _ (Nat.div_le_div_right h)

private theorem value_factorization (H : ℕ) (c : ℕ → ℕ → ℕ) (n p : ℕ) :
    (weightedValue H c n).factorization p =
      if p ∈ Nat.primesLE H then weightedExponent H c p n else 0 := by
  unfold weightedValue
  exact prime_product_factorization _ _ (fun p hp => (Nat.mem_primesLE.mp hp).2) p

private theorem product_ne_zero (r s : ℕ) (c : ℕ → ℕ → ℕ) (b : ℕ) :
    compactWeightedProduct r s c b ≠ 0 := by
  unfold compactWeightedProduct
  apply prod_ne_zero_iff.mpr
  intro i _
  apply mul_ne_zero _ (weightedValue_ne_zero _ _ _)
  exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))
    (value_mono_dvd _ _ (b_le_index_mul i b)))
      (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))).ne'

private theorem gcd_ne_zero (r s : ℕ) (c : ℕ → ℕ → ℕ) :
    compactWeightedGcd r s c ≠ 0 :=
  gcd_ne_zero_iff.mpr ⟨0, mem_range.mpr (Nat.zero_lt_succ _), product_ne_zero _ _ _ _⟩

private theorem tail_ne_zero (r s : ℕ) (c : ℕ → ℕ → ℕ) :
    compositionWeightedTail r s c ≠ 0 := by
  rw [compositionWeightedTail_eq]
  exact weightedTail_ne_zero _ _ _

private theorem product_factorization (r s : ℕ) (c : ℕ → ℕ → ℕ)
    (b p : ℕ) (hp : p ∈ Nat.primesLE (compactHeight r s)) :
    (compactWeightedProduct r s c b).factorization p =
      ∑ j ∈ range (compactHeight r s + 1),
        c p (j + 1) * floorSum (p ^ (j + 1)) r s b := by
  unfold compactWeightedProduct
  rw [Nat.factorization_prod_apply]
  · calc
      _ = ∑ i ∈ range r, ∑ j ∈ range (compactHeight r s + 1),
          c p (j + 1) * pairedFloor (p ^ (j + 1)) s b i := by
        apply sum_congr rfl
        intro i _
        have hd := value_mono_dvd (compactHeight r s) (shiftedWeights c)
          (b_le_index_mul i b)
        have hquot : weightedValue (compactHeight r s) (shiftedWeights c)
              ((i + 1) * b) / weightedValue (compactHeight r s) (shiftedWeights c) b ≠ 0 :=
          (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _)) hd)
            (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))).ne'
        rw [Nat.factorization_mul hquot (weightedValue_ne_zero _ _ _), Finsupp.add_apply,
          Nat.factorization_div hd, Finsupp.tsub_apply]
        simp only [value_factorization, if_pos hp, weightedExponent, shiftedWeights]
        have hle (j : ℕ) : b / p ^ (j + 1) ≤ (i + 1) * b / p ^ (j + 1) :=
          Nat.div_le_div_right (b_le_index_mul i b)
        rw [← sum_tsub_distrib _ (fun j _ => Nat.mul_le_mul_left _ (hle j)),
          ← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        unfold pairedFloor
        rw [← Nat.mul_sub_left_distrib, ← Nat.mul_add]
        rw [Nat.sub_add_comm (hle j)]
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro j _
        rw [floorSum, mul_sum]
  · intro i _
    exact mul_ne_zero
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))
        (value_mono_dvd _ _ (b_le_index_mul i b)))
          (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))).ne'
      (weightedValue_ne_zero _ _ _)

private theorem tail_factorization (r s : ℕ) (c : ℕ → ℕ → ℕ)
    {p : ℕ} (hp : p ∈ Nat.primesLE (compactHeight r s)) :
    (compositionWeightedTail r s c).factorization p =
      ∑ j ∈ range (compactHeight r s + 1),
        c p (j + 1) * floorMinimum (compactHeight r s) (r - 1) (p ^ (j + 1)) := by
  rw [compositionWeightedTail_eq]
  exact weightedTail_factorization _ _ _ hp

private theorem product_factorization_outside (r s : ℕ) (c : ℕ → ℕ → ℕ)
    (b p : ℕ) (hp : p ∉ Nat.primesLE (compactHeight r s)) :
    (compactWeightedProduct r s c b).factorization p = 0 := by
  unfold compactWeightedProduct
  rw [Nat.factorization_prod_apply]
  · apply sum_eq_zero
    intro i _
    rw [Nat.factorization_mul, Finsupp.add_apply,
      Nat.factorization_div (value_mono_dvd _ _ (b_le_index_mul i b)),
      Finsupp.tsub_apply]
    · simp only [value_factorization, if_neg hp, Nat.sub_self, zero_add]
    · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))
        (value_mono_dvd _ _ (b_le_index_mul i b)))
          (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))).ne'
    · exact weightedValue_ne_zero _ _ _
  · intro i _
    exact mul_ne_zero
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))
        (value_mono_dvd _ _ (b_le_index_mul i b)))
          (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))).ne' (weightedValue_ne_zero _ _ _)

private theorem tail_factorization_outside (r s : ℕ) (c : ℕ → ℕ → ℕ)
    (p : ℕ) (hp : p ∉ Nat.primesLE (compactHeight r s)) :
    (compositionWeightedTail r s c).factorization p = 0 := by
  rw [compositionWeightedTail_eq]
  unfold weightedTail
  rw [prime_product_factorization _ _ (fun p hp => (Nat.mem_primesLE.mp hp).2), if_neg hp]

private theorem tail_dvd_product {r s b : ℕ} (hr : 2 ≤ r)
    (hb : b ∈ compactParameters r s) (c : ℕ → ℕ → ℕ) :
    compositionWeightedTail r s c ∣ compactWeightedProduct r s c b := by
  apply (Nat.factorization_prime_le_iff_dvd (tail_ne_zero _ _ _) (product_ne_zero _ _ _ _)).mp
  intro p hp
  by_cases hpin : p ∈ Nat.primesLE (compactHeight r s)
  · rw [tail_factorization r s c hpin, product_factorization r s c b p hpin]
    apply sum_le_sum
    intro j _
    apply Nat.mul_le_mul_left
    rw [floorMinimum, height_eq (by omega : 1 ≤ r)]
    apply selberg_floor_lower _ (by omega : 1 ≤ r) (legal_parameter_bound (by omega) hb)
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (j + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  · rw [tail_factorization_outside r s c p hpin]
    exact Nat.zero_le _

private theorem tail_dvd_gcd {r s : ℕ} (hr : 2 ≤ r) (c : ℕ → ℕ → ℕ) :
    compositionWeightedTail r s c ∣ compactWeightedGcd r s c := by
  exact dvd_gcd fun b hb => tail_dvd_product hr hb c

private theorem floors_above_window {r s b q : ℕ} (hb : r * b ≤ s) (hq : s < q) :
    floorSum q r s b = 0 := by
  unfold floorSum
  apply sum_eq_zero
  intro i hi
  have hib : (i + 1) * b ≤ s :=
    (Nat.mul_le_mul_right b (show i + 1 ≤ r from mem_range.mp hi)).trans hb
  have hbb : b ≤ s := (b_le_index_mul i b).trans hib
  simp only [pairedFloor, Nat.div_eq_of_lt (hib.trans_lt hq),
    Nat.div_eq_of_lt ((Nat.sub_le s _).trans_lt hq),
    Nat.div_eq_of_lt (hbb.trans_lt hq), zero_add, Nat.sub_self]

private theorem defect_cutoff {r s b p : ℕ} (hp : p.Prime)
    (hb : r * b ≤ s) (c : ℕ → ℕ → ℕ) (hr : 2 ≤ r) :
    (∑ j ∈ range (compactHeight r s + 1), c p (j + 1) * floorDefect (p ^ (j + 1)) r s b) =
      ∑ j ∈ Ico 1 (Nat.log p s + 1), c p j * floorDefect (p ^ j) r s b := by
  have hsH : s ≤ compactHeight r s := by
    rw [height_eq (by omega : 1 ≤ r)]
    have := Nat.le_mul_of_pos_left s (by omega : 0 < r)
    omega
  have hlog : Nat.log p s + 1 ≤ compactHeight r s + 2 := by
    have := Nat.log_le_self p s
    omega
  have hsub : Ico 1 (Nat.log p s + 1) ⊆ Ico 1 (compactHeight r s + 2) :=
    fun j hj => mem_Ico.mpr ⟨(mem_Ico.mp hj).1, lt_of_lt_of_le (mem_Ico.mp hj).2 hlog⟩
  have hz : ∀ j ∈ Ico 1 (compactHeight r s + 2), j ∉ Ico 1 (Nat.log p s + 1) →
      c p j * floorDefect (p ^ j) r s b = 0 := by
    intro j hj hn
    have hK : Nat.log p s + 1 ≤ j := by
      have := mem_Ico.mp hj
      simp only [mem_Ico, not_and, not_lt] at hn
      exact hn (by omega)
    have hq : s < p ^ j := (Nat.lt_pow_succ_log_self hp.one_lt s).trans_le
      (Nat.pow_le_pow_right hp.pos hK)
    rw [floorDefect, floors_above_window hb hq, Nat.zero_sub, mul_zero]
  have h := (sum_subset hsub hz).symm
  rw [sum_Ico_eq_sum_range] at h
  have hlen : compactHeight r s + 2 - 1 = compactHeight r s + 1 := by omega
  simpa only [hlen, add_comm 1] using h

private theorem product_minus_tail {r s b p : ℕ} (hr : 2 ≤ r)
    (hb : b ∈ compactParameters r s) (hp : p ∈ Nat.primesLE (compactHeight r s))
    (c : ℕ → ℕ → ℕ) :
    (compactWeightedProduct r s c b).factorization p -
        (compositionWeightedTail r s c).factorization p =
      ∑ j ∈ Ico 1 (Nat.log p s + 1), c p j * floorDefect (p ^ j) r s b := by
  rw [product_factorization r s c b p hp, tail_factorization r s c hp]
  have hlow (j : ℕ) :
      floorMinimum (compactHeight r s) (r - 1) (p ^ (j + 1)) ≤ floorSum (p ^ (j + 1)) r s b := by
    rw [floorMinimum, height_eq (by omega : 1 ≤ r)]
    apply selberg_floor_lower _ (by omega : 1 ≤ r) (legal_parameter_bound (by omega) hb)
    have hpprime := (Nat.mem_primesLE.mp hp).2
    calc
      2 ≤ p := hpprime.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (j + 1) := Nat.pow_le_pow_right hpprime.pos (by omega)
  rw [← sum_tsub_distrib _ (fun j _ => Nat.mul_le_mul_left _ (hlow j))]
  calc
    _ = ∑ j ∈ range (compactHeight r s + 1),
        c p (j + 1) * floorDefect (p ^ (j + 1)) r s b := by
      apply sum_congr rfl
      intro j _
      rw [← Nat.mul_sub_left_distrib]
      rw [floorMinimum, height_eq (by omega : 1 ≤ r)]
      rfl
    _ = _ := defect_cutoff (Nat.mem_primesLE.mp hp).2 (legal_parameter_bound (by omega) hb) c hr

/-- The actual compact gcd quotient has precisely the weighted floor-defect minima. -/
theorem compactWeightedExcess_factorization {r s p : ℕ} (hr : 2 ≤ r)
    (c : ℕ → ℕ → ℕ) (hp : p ∈ Nat.primesLE (compactHeight r s)) :
    (compactWeightedExcess r s c).factorization p =
      weightedPrimeLoss r s p (Nat.log p s + 1) (c p) := by
  let T := compositionWeightedTail r s c
  let G := compactWeightedGcd r s c
  let L := weightedPrimeLoss r s p (Nat.log p s + 1) (c p)
  have hpprime := (Nat.mem_primesLE.mp hp).2
  have hG : G ≠ 0 := gcd_ne_zero _ _ _
  have hT : T ≠ 0 := tail_ne_zero _ _ _
  have hTd : T ∣ G := tail_dvd_gcd hr c
  have hgmin : T.factorization p + L ≤ G.factorization p := by
    apply (hpprime.pow_dvd_iff_le_factorization hG).mp
    apply Finset.dvd_gcd
    intro b hb
    have hd : T ∣ compactWeightedProduct r s c b := tail_dvd_product hr hb c
    have hle := (Nat.factorization_prime_le_iff_dvd hT (product_ne_zero _ _ _ _)).mpr hd p hpprime
    have hlo := minimum_le
      (fun b => ∑ j ∈ Ico 1 (Nat.log p s + 1), c p j * floorDefect (p ^ j) r s b) hb
    change L ≤ ∑ j ∈ Ico 1 (Nat.log p s + 1), c p j * floorDefect (p ^ j) r s b at hlo
    rw [← product_minus_tail hr hb hp c] at hlo
    exact (hpprime.pow_dvd_iff_le_factorization (product_ne_zero _ _ _ _)).mpr (by
      dsimp only [T, L] at hle ⊢
      omega)
  obtain ⟨b, hb, heq⟩ := minimum_attained r s
    (fun b => ∑ j ∈ Ico 1 (Nat.log p s + 1), c p j * floorDefect (p ^ j) r s b)
  change (∑ j ∈ Ico 1 (Nat.log p s + 1), c p j * floorDefect (p ^ j) r s b) = L at heq
  have hGle := (Nat.factorization_prime_le_iff_dvd hG (product_ne_zero _ _ _ _)).mpr
    (gcd_dvd hb) p hpprime
  have hcost := product_minus_tail hr hb hp c
  rw [heq] at hcost
  unfold compactWeightedExcess
  rw [Nat.factorization_div (tail_dvd_gcd hr c), Finsupp.tsub_apply]
  change G.factorization p - T.factorization p = L
  dsimp only [G, T, L] at hgmin hGle ⊢
  omega

private theorem excess_ne_zero {r s : ℕ} (hr : 2 ≤ r) (c : ℕ → ℕ → ℕ) :
    compactWeightedExcess r s c ≠ 0 := by
  unfold compactWeightedExcess
  exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (gcd_ne_zero _ _ _))
    (tail_dvd_gcd hr c)) (Nat.pos_of_ne_zero (tail_ne_zero _ _ _))).ne'

/-- The floor-defect product is the actual compact gcd divided by its full-composition gcd. -/
theorem compactWeightedExcess_eq_weightedExcess {r s : ℕ} (hr : 2 ≤ r)
    (c : ℕ → ℕ → ℕ) :
    compactWeightedExcess r s c =
      weightedExcess r s (Nat.primesLE (compactHeight r s)) c := by
  have hP : ∀ p ∈ Nat.primesLE (compactHeight r s), p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp hp).2
  have hW : weightedExcess r s (Nat.primesLE (compactHeight r s)) c ≠ 0 := by
    unfold weightedExcess
    exact prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hP p hp).ne_zero
  apply Nat.eq_of_factorization_eq (excess_ne_zero hr c) hW
  intro p
  unfold weightedExcess
  rw [prime_product_factorization _ _ hP p]
  by_cases hp : p ∈ Nat.primesLE (compactHeight r s)
  · rw [if_pos hp, compactWeightedExcess_factorization hr c hp]
  · rw [if_neg hp]
    have hprod := product_factorization_outside r s c 0 p hp
    have hg := (Nat.factorization_prime_le_iff_dvd (gcd_ne_zero _ _ _)
      (product_ne_zero _ _ _ _)).mpr
      (gcd_dvd (f := compactWeightedProduct r s c)
        (show 0 ∈ compactParameters r s from mem_range.mpr (Nat.zero_lt_succ _)))
    have hpprime : p.Prime ∨ ¬p.Prime := Classical.em _
    rcases hpprime with hpprime | hpprime
    · have hz := hg p hpprime
      rw [hprod] at hz
      unfold compactWeightedExcess
      rw [Nat.factorization_div (tail_dvd_gcd hr c), Finsupp.tsub_apply]
      omega
    · exact Nat.factorization_eq_zero_of_not_prime _ hpprime

/-- The shared budget, and the exact quotient chain when the two weights partition C. -/
theorem actual_weighted_shared_budget {r s C : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2)
    (c d : ℕ → ℕ → ℕ)
    (hc : ∀ p ∈ Nat.primesLE (compactHeight r s),
      ∀ j ∈ Ico 1 (Nat.log p s + 1), c p j + d p j ≤ C) :
    (compactWeightedExcess r s c * compactWeightedExcess r s d ∣ compactExcess r s ^ C) ∧
    ((∀ p ∈ Nat.primesLE (compactHeight r s),
      ∀ j ∈ Ico 1 (compactHeight r s + 2), c p j + d p j = C) →
      compactWeightedGcd r s c ≠ 0 ∧
      compactWeightedGcd r s c ∣ selbergGcd r s ^ C ∧
      selbergGcd r s ^ C / compactWeightedGcd r s c ≠ 0 ∧
      compositionWeightedTail r s d ∣ compactWeightedGcd r s d ∧
      compactWeightedGcd r s d ∣ selbergGcd r s ^ C / compactWeightedGcd r s c ∧
      selbergGcd r s ^ C / compactWeightedGcd r s c ∣
        compositionWeightedTail r s d * compactExcess r s ^ C) := by
  have hbudget : compactWeightedExcess r s c * compactWeightedExcess r s d ∣
      compactExcess r s ^ C := by
    rw [compactWeightedExcess_eq_weightedExcess hr c,
      compactWeightedExcess_eq_weightedExcess hr d]
    exact weighted_shared_budget hr hs _ (fun p hp => (Nat.mem_primesLE.mp hp).2) c d hc
  refine ⟨hbudget, ?_⟩
  intro hpartition
  have htprod : compositionWeightedTail r s c * compositionWeightedTail r s d =
      tailLCM (compactHeight r s) (r - 1) ^ C := by
    rw [compositionWeightedTail_eq, compositionWeightedTail_eq, weightedTail_add,
      ← weightedTail_constant (compactHeight r s) (r - 1) C]
    unfold weightedTail
    apply prod_congr rfl
    intro p hp
    congr 1
    apply sum_congr rfl
    intro j hj
    exact congrArg
      (· * floorMinimum (compactHeight r s) (r - 1) (p ^ (j + 1)))
      (hpartition p hp (j + 1)
        (mem_Ico.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩))
  have hdec (w : ℕ → ℕ → ℕ) :
      compositionWeightedTail r s w * compactWeightedExcess r s w =
        compactWeightedGcd r s w := Nat.mul_div_cancel' (tail_dvd_gcd hr w)
  have ht : tailLCM (compactHeight r s) (r - 1) ∣ selbergGcd r s :=
    (compact_factorial_gcd r s hr hs).1
  have hordinary : tailLCM (compactHeight r s) (r - 1) * compactExcess r s =
      selbergGcd r s := Nat.mul_div_cancel' ht
  have hpair : compactWeightedGcd r s c * compactWeightedGcd r s d ∣
      selbergGcd r s ^ C := by
    obtain ⟨k, hk⟩ := hbudget
    refine ⟨k, ?_⟩
    rw [← hordinary, mul_pow, hk, ← htprod, ← hdec c, ← hdec d]
    ring
  have hdiv : compactWeightedGcd r s c ∣ selbergGcd r s ^ C :=
    (dvd_mul_right _ _).trans hpair
  refine ⟨gcd_ne_zero _ _ _, hdiv, ?_, tail_dvd_gcd hr d, ?_, ?_⟩
  · exact (Nat.div_pos (Nat.le_of_dvd
      (pow_pos (Nat.pos_of_ne_zero (selbergGcd_ne_zero r s)) C) hdiv)
      (Nat.pos_of_ne_zero (gcd_ne_zero _ _ _))).ne'
  · exact (Nat.dvd_div_iff_mul_dvd hdiv).mpr hpair
  · have hq := Nat.div_dvd_div_left hdiv (tail_dvd_gcd hr c)
    have heq : selbergGcd r s ^ C / compositionWeightedTail r s c =
        compositionWeightedTail r s d * compactExcess r s ^ C := by
      rw [← hordinary, mul_pow, ← htprod, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (tail_ne_zero _ _ _))]
    exact hq.trans (dvd_of_eq heq)

/-- Bounded weights give the exact ordinary compact compression budget to the same power. -/
theorem actual_weighted_budget {r s C : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2)
    (c : ℕ → ℕ → ℕ)
    (hc : ∀ p ∈ Nat.primesLE (compactHeight r s),
      ∀ j ∈ Ico 1 (Nat.log p s + 1), c p j ≤ C) :
    compactWeightedExcess r s c ∣ compactExcess r s ^ C := by
  have h := (actual_weighted_shared_budget hr hs c (fun _ _ => 0)
    (by simpa only [add_zero] using hc)).1
  exact (dvd_mul_right (compactWeightedExcess r s c)
    (compactWeightedExcess r s (fun _ _ => 0))).trans h

end D5.S3.Arith.FactorialRatio.Weighted.CompactBudget
