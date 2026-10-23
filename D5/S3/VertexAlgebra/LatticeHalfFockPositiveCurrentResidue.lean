/- GID: D5/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete positive-current residue and original-source unweighted tail. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard

/-! Positive-current residues on the actual tensor module, with the original source cutoff. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators

noncomputable section

/- proof_shape: positive_pascal_difference: content
   admission_basis: escape-witness
   escape_witness: Pascal cancellation lowers the binomial degree once for
   each difference, with a genuine zero branch below the difference order.
   consumer: correctedField_positive_current_residue. -/
private theorem positive_pascal_difference (a : ℂ) (s n : ℕ) :
    (∑ l ∈ Finset.range (s + 1), (s.choose l : ℂ) *
      ((-1 : ℂ) ^ l * Ring.choose ((s : ℂ) - l + a) n)) =
      if s ≤ n then Ring.choose a (n - s) else 0 := by
  induction s generalizing n with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + 1 = s + 2 by omega, Finset.sum_choose_succ_mul
      (fun l _ => (-1 : ℂ) ^ l * Ring.choose (((s + 1 : ℕ) : ℂ) - l + a) n) s,
      ← Finset.sum_add_distrib]
    cases n with
    | zero =>
      rw [ite_eq_right (by omega)]
      apply Finset.sum_eq_zero
      intro l _
      simp only [Ring.choose_zero_right, mul_one, pow_succ]
      ring
    | succ n =>
      calc
        _ = ∑ l ∈ Finset.range (s + 1), (s.choose l : ℂ) *
            ((-1 : ℂ) ^ l * Ring.choose ((s : ℂ) - l + a) n) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one,
            show (s : ℂ) + 1 - ((l : ℂ) + 1) + a = (s : ℂ) - l + a by ring,
            show (s : ℂ) + 1 - l + a = ((s : ℂ) - l + a) + 1 by ring,
            Ring.choose_succ_succ, pow_succ]
          ring
        _ = _ := by simpa only [Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub] using ih n

/- proof_shape: positive_residue_commutators: bind-only
   consumer: correctedField_positive_current_residue uses this finite
   reflection of the complete ordered residue before applying actual Ward. -/
private theorem positive_residue_commutators
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (F : NativeField D hu) (gamma t : ℤ) (s : ℕ) (x : ActualTensor D hu) :
    currentResidue D hu i F gamma (s : ℤ) t x =
      ∑ l ∈ Finset.range (s + 1), ((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i ((s : ℤ) - l)
            (F.coeff (-2 * (t + l) - gamma - 2) x) -
          F.coeff (-2 * (t + l) - gamma - 2)
            (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i ((s : ℤ) - l) x)) := by
  classical
  have trunc (f : ℕ → ActualTensor D hu) (hf : Function.HasFiniteSupport
      (fun l => ((-1 : ℂ) ^ l * Ring.choose (s : ℂ) l) • f l)) :
      (∑ᶠ l : ℕ, ((-1 : ℂ) ^ l * Ring.choose (s : ℂ) l) • f l) =
      ∑ l ∈ Finset.range (s + 1), ((-1 : ℂ) ^ l * (s.choose l : ℂ)) • f l := by
    rw [finsum_eq_sum_of_support_toFinset_subset _ hf (s := Finset.range (s + 1)) (by
      intro l hl
      have member := hf.mem_toFinset.mp hl
      by_contra outside
      have zero : s.choose l = 0 := Nat.choose_eq_zero_of_lt (by
        simp only [Finset.mem_range] at outside
        omega)
      exact member (by simp [Ring.choose_natCast, zero]))]
    simp only [Ring.choose_natCast]
  have left := trunc (fun l =>
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i ((s : ℤ) - l)
      (F.coeff (-2 * (t + l) - gamma - 2) x))
    (current_residue_left_finite D hu i F gamma s t x)
  have right := trunc (fun l => F.coeff (-2 * ((s : ℤ) + t - l) - gamma - 2)
    (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i l x))
    (current_residue_right_finite D hu i F gamma s t x)
  rw [currentResidue]
  simp only [Int.cast_natCast]
  rw [left, right, zpow_natCast, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  have reflect :
      (∑ l ∈ Finset.range (s + 1), (-1 : ℂ) ^ s •
        (((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
          F.coeff (-2 * ((s : ℤ) + t - l) - gamma - 2)
            (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i l x))) =
      ∑ l ∈ Finset.range (s + 1), ((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
        F.coeff (-2 * (t + l) - gamma - 2)
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i ((s : ℤ) - l) x) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro l hl
    have within : l ≤ s := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul]
    have signs : (-1 : ℂ) ^ s * ((-1 : ℂ) ^ (s - l) * (s.choose l : ℂ)) =
        (-1 : ℂ) ^ l * (s.choose l : ℂ) := by
      have split : (-1 : ℂ) ^ s = (-1 : ℂ) ^ l * (-1 : ℂ) ^ (s - l) := by
        rw [← pow_add, Nat.add_sub_of_le within]
      have square : ((-1 : ℂ) ^ (s - l)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [split]
      calc
        _ = (-1 : ℂ) ^ l * ((-1 : ℂ) ^ (s - l)) ^ 2 * (s.choose l : ℂ) := by ring
        _ = _ := by rw [square]; ring
    rw [signs, Int.natCast_sub within,
      show (s : ℤ) + t - ((s : ℤ) - l) = t + l by ring]
  rw [Finset.sum_sub_distrib, reflect, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_sub]

/- proof_shape: correctedField_positive_current_residue: content
   admission_basis: escape-witness
   escape_witness: The full reflected ordered residue consumes unrestricted
   actual Ward and finite Pascal differences, retaining the original source
   cutoff and the zero branch when the difference order exceeds n. -/
set_option maxHeartbeats 2000000 in
-- The dependent actual-tensor coefficient rewrites retain both finite Ward sums.
/-- The complete nonnegative current residue, on arbitrary actual tensor inputs. -/
theorem correctedField_positive_current_residue
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (b : Carrier D) (gamma t : ℤ) (s : ℕ) (x : ActualTensor D hu) :
    currentResidue D hu i (correctedField D hu b) gamma (s : ℤ) t x =
      ∑ n ∈ Finset.range (vectorFrequencyBound D b + 1),
        if s ≤ n then Ring.choose (1 / 2 : ℂ) (n - s) •
          (correctedField D hu (neutralMode D i (n : ℤ) b)).coeff
            (-2 * (t + (s : ℤ) - (n : ℤ)) - gamma - 3) x
        else 0 := by
  classical
  rw [positive_residue_commutators]
  simp_rw [correctedField_current_ward, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have exponent (l : ℕ) :
      -2 * (t + l) - gamma - 2 - (2 * ((s : ℤ) - l) + 1) + 2 * (n : ℤ) =
        -2 * (t + (s : ℤ) - n) - gamma - 3 := by ring
  simp_rw [exponent, smul_smul]
  have frequency (l : ℕ) : LatticeHalfFock.frequency ((s : ℤ) - l) =
      (s : ℂ) - l + 1 / 2 := by
    simp only [LatticeHalfFock.frequency, Int.cast_sub, Int.cast_natCast]
  simp_rw [frequency]
  rw [← Finset.sum_smul]
  have difference := positive_pascal_difference (1 / 2 : ℂ) s n
  have reorder : (∑ l ∈ Finset.range (s + 1),
      ((-1 : ℂ) ^ l * (s.choose l : ℂ)) *
        Ring.choose ((s : ℂ) - l + 1 / 2) n) =
      if s ≤ n then Ring.choose (1 / 2 : ℂ) (n - s) else 0 := by
    convert difference using 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [reorder]
  split_ifs <;> simp only [zero_smul]

/- proof_shape: correctedField_positive_current_residue_tail: content
   admission_basis: escape-witness
   escape_witness: Every summand in the full residue's source-bounded Ward
   difference has n < N ≤ s, so the explicit zero branch kills the complete
   unweighted residue, independently of gamma,t and the actual input. -/
/-- The unweighted complete residue vanishes beyond the original source cutoff. -/
theorem correctedField_positive_current_residue_tail
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (b : Carrier D) (gamma t : ℤ) (s : ℕ) (x : ActualTensor D hu)
    (hs : vectorFrequencyBound D b + 1 ≤ s) :
    currentResidue D hu i (correctedField D hu b) gamma (s : ℤ) t x = 0 := by
  rw [correctedField_positive_current_residue]
  apply Finset.sum_eq_zero
  intro n hn
  exact ite_eq_right (by have := Finset.mem_range.mp hn; omega)

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
