/- GID: D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation
   generality: G
   mirror-B: none(waiver:literal-interval-autocorrelation)
   mirror-E: none(waiver:literal-interval-autocorrelation)
   anchors: []
   utility: none
   digest: Literal integer interval differences give the actual triangular autocorrelation weights. -/

import D5.S3.FiniteGroups.RegularRepresentation.CentralAutocorrelation
import Mathlib.Data.Int.Interval

namespace D5.S3.Arith.CharacterSums

open scoped BigOperators
open D5.S3.FiniteGroups.RegularRepresentation.CentralAutocorrelation

noncomputable section

def symmetricIntegerInterval (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

private theorem difference_fiber_card (N : ℕ) (n : ℤ) (hn : |n| ≤ 2 * N) :
    (((symmetricIntegerInterval N ×ˢ symmetricIntegerInterval N).filter
      (fun ab => ab.1 - ab.2 = n)).card : ℤ) = 2 * N + 1 - |n| := by
  classical
  have hnlo := (abs_le.mp hn).1
  have hnhi := (abs_le.mp hn).2
  let I := symmetricIntegerInterval N
  let F := (I ×ˢ I).filter (fun ab => ab.1 - ab.2 = n)
  let J := I.filter (fun a => a - n ∈ I)
  have hbij : F.card = J.card := by
    apply Finset.card_nbij' Prod.fst (fun a => (a, a - n))
    · intro ab hab
      obtain ⟨hab, he⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact Finset.mem_filter.mpr ⟨ha, by convert hb using 1 <;> omega⟩
    · intro a ha
      obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, by dsimp; omega⟩
    · intro ab hab
      have he := (Finset.mem_filter.mp hab).2
      apply Prod.ext <;> dsimp <;> omega
    · intro a _
      rfl
  change (F.card : ℤ) = _
  rw [hbij]
  by_cases hn0 : 0 ≤ n
  · have hJ : J = Finset.Icc (n - N) N := by
      ext a
      simp only [J, I, symmetricIntegerInterval, Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hJ, Int.card_Icc_of_le (a := n - N) (b := (N : ℤ)) (by omega),
      abs_of_nonneg hn0]
    omega
  · have hJ : J = Finset.Icc (-(N : ℤ)) (n + N) := by
      ext a
      simp only [J, I, symmetricIntegerInterval, Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hJ, Int.card_Icc_of_le (a := -(N : ℤ)) (b := n + N) (by omega),
      abs_of_neg (lt_of_not_ge hn0)]
    omega

variable {G : Type*} [Group G] [Fintype G]

/-- The actual pushforward of a literal integer interval, retaining all
multiplicities even when its residues wrap around the finite group. -/
def integerIntervalMeasure (u : Multiplicative ℤ →* G) (N : ℕ) : MonoidAlgebra ℝ G :=
  ∑ n ∈ symmetricIntegerInterval N, MonoidAlgebra.single (u (.ofAdd n)) 1

/-- The normalized actual interval autocorrelation. -/
def integerIntervalFejer (u : Multiplicative ℤ →* G) (N : ℕ) : MonoidAlgebra ℝ G :=
  ((2 * (N : ℝ) + 1)⁻¹) •
    (integerIntervalMeasure u N * reverseCoefficients (integerIntervalMeasure u N))

theorem integerIntervalMeasure_coeff_nonneg (u : Multiplicative ℤ →* G) (N : ℕ) (g : G) :
    0 ≤ (integerIntervalMeasure u N).coeff g := by
  classical
  simp only [integerIntervalMeasure, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro n _
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split <;> positivity

/-- The literal triangular weights, with all residue collisions still summed. -/
theorem integerInterval_autocorrelation_coeff (u : Multiplicative ℤ →* G) (N : ℕ) (g : G) :
    (integerIntervalMeasure u N * reverseCoefficients (integerIntervalMeasure u N)).coeff g =
      ∑ n ∈ symmetricIntegerInterval (2 * N),
        ((2 * (N : ℤ) + 1 - |n| : ℤ) : ℝ) *
          (MonoidAlgebra.single (u (.ofAdd n)) (1 : ℝ)).coeff g := by
  classical
  let I := symmetricIntegerInterval N
  let J := symmetricIntegerInterval (2 * N)
  let E := I ×ˢ I
  have hdiff (a b : ℤ) : u (.ofAdd (a - b)) = u (.ofAdd a) * (u (.ofAdd b))⁻¹ := by
    simp [ofAdd_sub, map_div, div_eq_mul_inv]
  have hexpand : integerIntervalMeasure u N * reverseCoefficients (integerIntervalMeasure u N) =
      ∑ ab ∈ E, MonoidAlgebra.single (u (.ofAdd (ab.1 - ab.2))) (1 : ℝ) := by
    simp only [integerIntervalMeasure, reverse_sum, reverse_single,
      Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.single_mul_single, mul_one,
      E, I, Finset.sum_product, hdiff]
    rw [Finset.sum_comm]
  have hmap : ∀ ab ∈ E, ab.1 - ab.2 ∈ J := by
    intro ab hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    simp only [I, symmetricIntegerInterval, Finset.mem_Icc] at ha hb
    simp only [J, symmetricIntegerInterval, Finset.mem_Icc]
    push_cast
    omega
  rw [hexpand, ← Finset.sum_fiberwise_of_maps_to' hmap
    (fun n => MonoidAlgebra.single (u (.ofAdd n)) (1 : ℝ))]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : |n| ≤ 2 * (N : ℤ) := by
    have hh := Finset.mem_Icc.mp hn
    dsimp [J, symmetricIntegerInterval] at hh
    rw [abs_le]
    push_cast at hh
    omega
  have hc := difference_fiber_card N n hn'
  have hcR : (((E.filter (fun ab => ab.1 - ab.2 = n)).card : ℕ) : ℝ) =
      ((2 * (N : ℤ) + 1 - |n| : ℤ) : ℝ) := by exact_mod_cast hc
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hcR]

/-- The actual triangular measure lies between half the original interval
measure and the doubled interval measure, coefficient by coefficient. -/
theorem integerIntervalFejer_sandwich (u : Multiplicative ℤ →* G) (N : ℕ) (g : G) :
    (integerIntervalMeasure u N).coeff g ≤ 2 * (integerIntervalFejer u N).coeff g ∧
      (integerIntervalFejer u N).coeff g ≤ (integerIntervalMeasure u (2 * N)).coeff g := by
  classical
  let I := symmetricIntegerInterval N
  let J := symmetricIntegerInterval (2 * N)
  let w := fun n : ℤ => ((2 * (N : ℤ) + 1 - |n| : ℤ) : ℝ)
  let e := fun n : ℤ => (MonoidAlgebra.single (u (.ofAdd n)) (1 : ℝ)).coeff g
  let d := 2 * (N : ℝ) + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have he (n : ℤ) : 0 ≤ e n := by
    dsimp [e]
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split <;> positivity
  have hmem (n : ℤ) (hn : n ∈ J) : |n| ≤ 2 * (N : ℤ) := by
    simp only [J, symmetricIntegerInterval, Finset.mem_Icc] at hn
    push_cast at hn
    rw [abs_le]
    omega
  have hw0 (n : ℤ) (hn : n ∈ J) : 0 ≤ w n := by
    dsimp [w]
    exact_mod_cast (show (0 : ℤ) ≤ 2 * N + 1 - |n| by have := hmem n hn; omega)
  have hwu (n : ℤ) : w n ≤ d := by
    dsimp [w, d]
    push_cast
    linarith [abs_nonneg (n : ℝ)]
  have hwl (n : ℤ) (hn : n ∈ I) : d / 2 ≤ w n := by
    have hab : |n| ≤ (N : ℤ) := by
      simpa only [I, symmetricIntegerInterval, Finset.mem_Icc, ← abs_le] using hn
    have habR : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hab
    dsimp [w, d]
    push_cast
    linarith
  have hsub : I ⊆ J := by
    intro n hn
    simp only [I, J, symmetricIntegerInterval, Finset.mem_Icc] at hn ⊢
    push_cast
    omega
  have hformula : (integerIntervalFejer u N).coeff g = d⁻¹ * ∑ n ∈ J, w n * e n := by
    simp only [integerIntervalFejer, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, integerInterval_autocorrelation_coeff]
    rfl
  have hi : (integerIntervalMeasure u N).coeff g = ∑ n ∈ I, e n := by
    simp only [integerIntervalMeasure, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rfl
  have hj : (integerIntervalMeasure u (2 * N)).coeff g = ∑ n ∈ J, e n := by
    simp only [integerIntervalMeasure, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rfl
  have hlo : (d / 2) * (∑ n ∈ I, e n) ≤ ∑ n ∈ J, w n * e n := by
    calc
      _ = ∑ n ∈ I, (d / 2) * e n := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ I, w n * e n :=
        Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (hwl n hn) (he n))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n hn _ => mul_nonneg (hw0 n hn) (he n))
  have hup : (∑ n ∈ J, w n * e n) ≤ d * (∑ n ∈ J, e n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (hwu n) (he n))
  rw [hformula, hi, hj]
  constructor
  · have hh : (∑ n ∈ I, e n) / 2 ≤ d⁻¹ * ∑ n ∈ J, w n * e n := by
      calc
        _ = d⁻¹ * ((d / 2) * (∑ n ∈ I, e n)) := by field_simp [hd.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left hlo (inv_pos.mpr hd).le
    linarith
  · have hh := mul_le_mul_of_nonneg_left hup (inv_pos.mpr hd).le
    simpa only [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul] using hh

theorem integerIntervalFejer_coeff_nonneg (u : Multiplicative ℤ →* G) (N : ℕ) (g : G) :
    0 ≤ (integerIntervalFejer u N).coeff g := by
  have hlo := (integerIntervalFejer_sandwich u N g).1
  have hh := integerIntervalMeasure_coeff_nonneg u N g
  linarith

/-- Six actual alternating interval letters at an arbitrary central group
element are bounded by 64 times their doubled-interval identity count. -/
theorem alternating_integer_interval_center_le
    (u v : Multiplicative ℤ →* G) (N M : ℕ) (z : G)
    (hz : z ∈ Subgroup.center G) :
    ((integerIntervalMeasure u N * integerIntervalMeasure v M) ^ 3).coeff z ≤
      64 * ((integerIntervalMeasure u (2 * N) * integerIntervalMeasure v (2 * M)) ^ 3).coeff 1 := by
  let A := integerIntervalMeasure u N
  let B := integerIntervalMeasure v M
  let F := integerIntervalFejer u N
  let H := integerIntervalFejer v M
  have hA := integerIntervalMeasure_coeff_nonneg u N
  have hB := integerIntervalMeasure_coeff_nonneg v M
  have hF := integerIntervalFejer_coeff_nonneg u N
  have hH := integerIntervalFejer_coeff_nonneg v M
  have hlower : ∀ g, (A * B).coeff g ≤ ((2 : ℝ) • F * (2 : ℝ) • H).coeff g := by
    apply coeff_mul_mono
    · intro g
      simpa only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] using
        (integerIntervalFejer_sandwich u N g).1
    · intro g
      simpa only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] using
        (integerIntervalFejer_sandwich v M g).1
    · exact hB
    · intro g
      simpa only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hF g)
  have hFG : ∀ g, 0 ≤ (F * H).coeff g := coeff_mul_nonneg hF hH
  have hscaled : ∀ g, 0 ≤ ((2 : ℝ) • F * (2 : ℝ) • H).coeff g := by
    intro g
    simpa only [smul_mul_assoc, mul_smul_comm, smul_smul,
      MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 * 2) (hFG g)
  have hlo := coeff_pow_mono (coeff_mul_nonneg hA hB) hscaled hlower 3 z
  have hnormalized (g : G) : ((F * H) ^ 3).coeff g =
      (((2 * (N : ℝ) + 1)⁻¹ * (2 * (M : ℝ) + 1)⁻¹) ^ 3) *
        (((A * reverseCoefficients A) * (B * reverseCoefficients B)) ^ 3).coeff g := by
    dsimp [F, H, integerIntervalFejer, A, B]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_pow,
      MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
    ring
  have hcenter : ((F * H) ^ 3).coeff z ≤ ((F * H) ^ 3).coeff 1 := by
    rw [hnormalized, hnormalized]
    exact mul_le_mul_of_nonneg_left (central_alternating_autocorrelation_le A B z hz)
      (by positivity)
  have hu := integerIntervalMeasure_coeff_nonneg u (2 * N)
  have hv := integerIntervalMeasure_coeff_nonneg v (2 * M)
  have hupper := coeff_pow_mono hFG (coeff_mul_nonneg hu hv)
    (coeff_mul_mono (fun g => (integerIntervalFejer_sandwich u N g).2)
      (fun g => (integerIntervalFejer_sandwich v M g).2) hH hu) 3 (1 : G)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_pow,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hlo
  norm_num at hlo
  change ((A * B) ^ 3).coeff z ≤ _
  nlinarith [hlo, hcenter, hupper]

end

end D5.S3.Arith.CharacterSums
