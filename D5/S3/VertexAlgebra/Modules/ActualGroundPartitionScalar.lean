/-
SOURCE_ONLY_UNCOMPILED.

Finite occupation counting for the ACTUAL opposite-charge Taylor scalar.
The recurrence is obtained by removing one occupied oscillator. In
particular neither the binomial coefficient nor its recurrence is a
representation hypothesis. All sums below are finite, including rank zero.
-/
import D5.S3.VertexAlgebra.Modules.ActualGroundTaylorCoefficients
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Modules.ActualGroundPartitionScalar

open LatticeGeneratingFieldLocality ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction ActualGroundTaylorCoefficients
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

variable {D : LatticeData}

def oscillatorBox (k : ℕ) : Finset (Index D) :=
  Finset.univ ×ˢ Finset.range k

theorem support_subset_oscillatorBox (k : ℕ) (d : Index D →₀ ℕ)
    (hd : occupationWeight d ≤ k) : d.support ⊆ oscillatorBox k := by
  intro x hx
  have h := Finsupp.le_weight_of_ne_zero'
    (w := fun y : Index D => y.2 + 1) (Finsupp.mem_support_iff.mp hx)
  change x.2 + 1 ≤ occupationWeight d at h
  simp only [oscillatorBox, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_range]
  omega

theorem occupationWeight_zero_iff (d : Index D →₀ ℕ) :
    occupationWeight d = 0 ↔ d = 0 := by
  constructor
  · intro h
    ext x
    have hx := Finsupp.le_weight (fun y : Index D => y.2 + 1)
      (s := x) (by omega) d
    change d x ≤ occupationWeight d at hx
    simp only [Finsupp.zero_apply]
    omega
  · rintro rfl
    exact occupationWeight_zero

theorem weightedLevel_zero : weightedLevel (D := D) 0 = {0} := by
  ext d
  simp [occupationWeight_zero_iff]

@[simp] theorem weightedScalarSum_zero (α : Charge D) : weightedScalarSum α 0 = 1 := by
  simp [weightedScalarSum, weightedLevel_zero, oppositeTaylorScalar]

/-- The scalar for one oscillator is exactly the contraction produced by
the normalized positive current and the opposite negative current. -/
def contractionAtom (α : Charge D) (x : Index D) : ℂ :=
  normalizedCharge α x * -(bilinear D (unitCharge D x.1) (-α) : ℂ)

theorem frequency_mul_atom (α : Charge D) (x : Index D) :
    (x.2 + 1 : ℂ) * contractionAtom α x =
      (α x.1 : ℂ) * (bilinear D (unitCharge D x.1) α : ℂ) := by
  have hb : bilinear D (unitCharge D x.1) (-α) =
      -bilinear D (unitCharge D x.1) α := by
    simp [bilinear, mul_neg, Finset.sum_neg_distrib]
  rw [contractionAtom, normalizedCharge, hb, Int.cast_neg, neg_neg]
  have hn : (x.2 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero x.2
  field_simp [hn]
  <;> ring

/-- Removing one occupation cancels precisely its factorial. -/
theorem occupation_remove_factor (α : Charge D) (d : Index D →₀ ℕ) (x : Index D) :
    (d x + 1 : ℂ) * oppositeTaylorScalar α (d + Finsupp.single x 1) =
      contractionAtom α x * oppositeTaylorScalar α d := by
  rw [oppositeTaylorScalar, WeylData.factorial_add_single,
    derivativeScalar_add_single, occupationScalar_add_single]
  push_cast
  have hd := WeylData.factorial_cast_ne_zero (K := ℂ) d
  have hx : (d x + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d x)
  dsimp only [oppositeTaylorScalar, contractionAtom]
  field_simp [hd, hx]
  <;> ring

/-- The removal bijection is between finite sets at the two indicated
weights. Its inverse ADDS one occupation; no formal infinite sum is used. -/
theorem sum_occupied_coordinate (α : Charge D) (k : ℕ) (x : Index D)
    (hx : x ∈ oscillatorBox k) :
    (∑ d ∈ weightedLevel k, (d x : ℂ) * oppositeTaylorScalar α d) =
      contractionAtom α x * weightedScalarSum α (k - (x.2 + 1)) := by
  classical
  have hfreq : x.2 + 1 ≤ k := by
    have := (Finset.mem_product.mp hx).2
    exact Nat.succ_le_of_lt (Finset.mem_range.mp this)
  let occupied := (weightedLevel (D := D) k).filter (fun d => d x ≠ 0)
  have hfilter : (∑ d ∈ weightedLevel k, (d x : ℂ) * oppositeTaylorScalar α d) =
      ∑ d ∈ occupied, (d x : ℂ) * oppositeTaylorScalar α d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hn
    have hz : d x = 0 := by
      by_contra hne
      exact hn (Finset.mem_filter.mpr ⟨hd, hne⟩)
    simp [hz]
  rw [hfilter, weightedScalarSum, Finset.mul_sum]
  apply Finset.sum_bij (fun d _ => d - Finsupp.single x 1)
  · intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hd, hdx⟩
    have hw := Finsupp.weight_sub_single_add
      (w := fun y : Index D => y.2 + 1) hdx
    have hk := (mem_weightedLevel k d).mp hd
    rw [mem_weightedLevel]
    change occupationWeight (d - Finsupp.single x 1) + (x.2 + 1) =
      occupationWeight d at hw
    omega
  · intro d hd e he hde
    have hdpos : 0 < d x := Nat.pos_of_ne_zero (Finset.mem_filter.mp hd).2
    have hepos : 0 < e x := Nat.pos_of_ne_zero (Finset.mem_filter.mp he).2
    have h := congrArg (fun f : Index D →₀ ℕ => f + Finsupp.single x 1) hde
    simpa only [WeylData.restore_sub_single d x hdpos,
      WeylData.restore_sub_single e x hepos] using h
  · intro e he
    refine ⟨e + Finsupp.single x 1, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_weightedLevel, occupationWeight_add_single]
      have hew := (mem_weightedLevel _ e).mp he
      constructor
      · omega
      · simp
    · ext y
      by_cases hy : y = x
      · subst y
        simp
      · simp [Finsupp.single_apply, hy]
  · intro d hd
    have hdpos : 0 < d x := Nat.pos_of_ne_zero (Finset.mem_filter.mp hd).2
    have hr := WeylData.restore_sub_single d x hdpos
    have hs := occupation_remove_factor α (d - Finsupp.single x 1) x
    rw [hr] at hs
    have hc : (((d - Finsupp.single x 1 : Index D →₀ ℕ) x : ℂ) + 1) = (d x : ℂ) := by
      have hnat : (d - Finsupp.single x 1 : Index D →₀ ℕ) x + 1 = d x := by
        simpa using congrArg (fun f : Index D →₀ ℕ => f x) hr
      exact_mod_cast hnat
    rwa [hc] at hs

/-- Multiplying an actual summand by its total oscillator weight counts
each occupied oscillator with its frequency. -/
theorem occupation_mass (k : ℕ) (d : Index D →₀ ℕ)
    (hd : occupationWeight d = k) :
    (k : ℂ) = ∑ x ∈ oscillatorBox k, (x.2 + 1 : ℂ) * (d x : ℂ) := by
  have hs := support_subset_oscillatorBox k d hd.le
  calc
    (k : ℂ) = ∑ x ∈ d.support, (x.2 + 1 : ℂ) * (d x : ℂ) := by
      rw [← hd]
      simp only [occupationWeight, Finsupp.weight_apply, Finsupp.sum,
        nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      apply Finset.sum_congr rfl
      intro x hx
      push_cast
      ring
    _ = _ := by
      apply Finset.sum_subset hs
      intro x hx hnot
      simp [Finsupp.notMem_support_iff.mp hnot]

/-- The genuine partition recurrence, deduced from the defined factorial
products and the ORIGINAL Gram contraction. No recurrence is a premise. -/
theorem weightedScalarSum_recurrence (α : Charge D) (k : ℕ) :
    (k : ℂ) * weightedScalarSum α k =
      (bilinear D α α : ℂ) *
        ∑ n ∈ Finset.range k, weightedScalarSum α (k - (n + 1)) := by
  classical
  calc
    _ = ∑ d ∈ weightedLevel k,
        ∑ x ∈ oscillatorBox k,
          (x.2 + 1 : ℂ) * ((d x : ℂ) * oppositeTaylorScalar α d) := by
      rw [weightedScalarSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [occupation_mass k d ((mem_weightedLevel k d).mp hd), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ x ∈ oscillatorBox k,
        (x.2 + 1 : ℂ) * (contractionAtom α x *
          weightedScalarSum α (k - (x.2 + 1))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.mul_sum, sum_occupied_coordinate α k x hx]
    _ = ∑ x ∈ oscillatorBox k,
        ((α x.1 : ℂ) * (bilinear D (unitCharge D x.1) α : ℂ)) *
          weightedScalarSum α (k - (x.2 + 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← mul_assoc, frequency_mul_atom]
    _ = _ := by
      rw [oscillatorBox, Finset.sum_product, Finset.sum_comm]
      simp_rw [← Finset.sum_mul, weighted_unit_pairing]
      rw [Finset.mul_sum]

/-- An elementary finite hockey-stick calculation for the comparison
binomial. It is independent of the module and its spectral questions. -/
theorem choose_recurrence (q k : ℕ) (hq : 0 < q) :
    (k : ℂ) * ((q + k - 1).choose k : ℂ) =
      (q : ℂ) * ∑ n ∈ Finset.range k, ((q + (k - (n + 1)) - 1).choose
        (k - (n + 1)) : ℂ) := by
  cases k with
  | zero => simp
  | succ k =>
    have hsum : (∑ n ∈ Finset.range (k + 1),
        ((q + (k + 1 - (n + 1)) - 1).choose (k + 1 - (n + 1)) : ℂ)) =
        ((q + k).choose q : ℂ) := by
      have hrew : (fun n : ℕ =>
          ((q + (k + 1 - (n + 1)) - 1).choose (k + 1 - (n + 1)) : ℂ)) =
          (fun n => ((k - n + (q - 1)).choose (q - 1) : ℂ)) := by
        funext n
        have hs : q + (k + 1 - (n + 1)) - 1 = (q - 1) + (k - n) := by omega
        rw [hs, Nat.add_comm (q - 1) (k - n),
          show k + 1 - (n + 1) = k - n by omega, Nat.choose_symm_add]
      have href := Finset.sum_range_reflect
        (fun n : ℕ => ((n + (q - 1)).choose (q - 1) : ℂ)) (k + 1)
      simp only [Nat.add_sub_cancel] at href
      rw [hrew, href]
      have h := congrArg (fun n : ℕ => (n : ℂ)) (Nat.sum_range_add_choose k (q - 1))
      simpa only [Nat.cast_sum, show k + (q - 1) + 1 = q + k by omega,
        show q - 1 + 1 = q by omega] using h
    rw [hsum, show q + (k + 1) - 1 = q + k by omega]
    have h := congrArg (fun n : ℕ => (n : ℂ)) (Nat.choose_succ_right_eq (q + k) k)
    have hs : (q + k).choose k = (q + k).choose q := Nat.choose_symm_add.symm
    rw [hs, show q + k - k = q by omega] at h
    push_cast at h
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- Exact coefficient of the ACTUAL opposite-charge Taylor expansion.
The initial value and recurrence were both proved above from that scalar. -/
theorem weightedScalarSum_eq_choose (α : Charge D) (q : ℕ)
    (hq : (q : ℤ) = bilinear D α α) (hqpos : 0 < q) (k : ℕ) :
    weightedScalarSum α k = ((q + k - 1).choose k : ℂ) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      simp
    · have hr := weightedScalarSum_recurrence α k
      have hqc : (bilinear D α α : ℂ) = (q : ℂ) := by exact_mod_cast hq.symm
      rw [hqc] at hr
      have hsum : (∑ n ∈ Finset.range k, weightedScalarSum α (k - (n + 1))) =
          ∑ n ∈ Finset.range k,
            ((q + (k - (n + 1)) - 1).choose (k - (n + 1)) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact ih (k - (n + 1)) (by omega)
      rw [hsum] at hr
      exact mul_left_cancel₀ (by exact_mod_cast hk)
        (hr.trans (choose_recurrence q k hqpos).symm)

theorem weightedScalarSum_eq_rising (α : Charge D) (q : ℕ)
    (hq : (q : ℤ) = bilinear D α α) (hqpos : 0 < q) (k : ℕ) :
    weightedScalarSum α k = risingCoefficient q k := by
  rw [weightedScalarSum_eq_choose α q hq hqpos,
    risingCoefficient_eq_choose q k hqpos]

end D5.S3.VertexAlgebra.Modules.ActualGroundPartitionScalar
