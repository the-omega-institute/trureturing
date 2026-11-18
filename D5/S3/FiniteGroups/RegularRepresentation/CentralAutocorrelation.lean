/- GID: D5/S3/FiniteGroups/RegularRepresentation/CentralAutocorrelation
   generality: G
   mirror-B: none(waiver:actual-central-coefficient-comparison)
   mirror-E: none(waiver:actual-central-coefficient-comparison)
   anchors: []
   utility: none
   digest: Actual autocorrelation products have maximal central coefficient at the identity. -/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic

/-! The coefficient proof is the finite regular-trace argument without a
spectral square root: actual autocorrelation factors produce a Gram cube.
The regular trace convention agrees with RegularTrace.trace_lmul_list_prod. -/

namespace D5.S3.FiniteGroups.RegularRepresentation.CentralAutocorrelation

open scoped BigOperators

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

/-- Reverse an actual real group-algebra coefficient function. -/
def reverseCoefficients (a : MonoidAlgebra ℝ G) : MonoidAlgebra ℝ G :=
  ∑ g : G, MonoidAlgebra.single g (a.coeff g⁻¹)

@[simp] theorem coeff_reverse (a : MonoidAlgebra ℝ G) (g : G) :
    (reverseCoefficients a).coeff g = a.coeff g⁻¹ := by
  classical
  simp [reverseCoefficients, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

@[simp] private theorem reverse_zero : reverseCoefficients (0 : MonoidAlgebra ℝ G) = 0 := by
  ext g
  simp

@[simp] private theorem reverse_add (a b : MonoidAlgebra ℝ G) :
    reverseCoefficients (a + b) = reverseCoefficients a + reverseCoefficients b := by
  ext g
  simp

@[simp] theorem reverse_single (g : G) (r : ℝ) :
    reverseCoefficients (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
  classical
  ext h
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, inv_eq_iff_eq_inv]

@[simp] theorem reverse_reverse (a : MonoidAlgebra ℝ G) :
    reverseCoefficients (reverseCoefficients a) = a := by
  ext g
  simp

@[simp] theorem reverse_sum {ι : Type*} (s : Finset ι) (f : ι → MonoidAlgebra ℝ G) :
    reverseCoefficients (∑ i ∈ s, f i) = ∑ i ∈ s, reverseCoefficients (f i) := by
  ext g
  simp [MonoidAlgebra.coeff_sum]

/-- Coefficient reversal is the actual anti-involution of the real group algebra. -/
theorem reverse_mul (a b : MonoidAlgebra ℝ G) :
    reverseCoefficients (a * b) = reverseCoefficients b * reverseCoefficients a := by
  induction a using MonoidAlgebra.induction_linear generalizing b with
  | zero => simp
  | add a a' ha ha' => simp [add_mul, ha, ha', mul_add]
  | single g r =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp [mul_add, hb, hb', add_mul]
    | single h s => simp [MonoidAlgebra.single_mul_single, mul_comm]

theorem coeff_mul_fintype (a b : MonoidAlgebra ℝ G) (z : G) :
    (a * b).coeff z = ∑ g : G, a.coeff g * b.coeff (g⁻¹ * z) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  exact Finsupp.sum_fintype _ _ (by simp)

theorem coeff_mul_nonneg {a b : MonoidAlgebra ℝ G}
    (ha : ∀ g, 0 ≤ a.coeff g) (hb : ∀ g, 0 ≤ b.coeff g) (z : G) :
    0 ≤ (a * b).coeff z := by
  rw [coeff_mul_fintype]
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (ha _) (hb _))

theorem coeff_mul_mono {a a' b b' : MonoidAlgebra ℝ G}
    (ha : ∀ g, a.coeff g ≤ a'.coeff g) (hb : ∀ g, b.coeff g ≤ b'.coeff g)
    (hb0 : ∀ g, 0 ≤ b.coeff g) (ha'0 : ∀ g, 0 ≤ a'.coeff g) (z : G) :
    (a * b).coeff z ≤ (a' * b').coeff z := by
  simp only [coeff_mul_fintype]
  exact Finset.sum_le_sum (fun g _ => mul_le_mul (ha g) (hb _) (hb0 _) (ha'0 g))

theorem coeff_pow_nonneg {a : MonoidAlgebra ℝ G} (ha : ∀ g, 0 ≤ a.coeff g)
    (n : ℕ) (z : G) : 0 ≤ (a ^ n).coeff z := by
  classical
  induction n generalizing z with
  | zero =>
    simp only [pow_zero, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    split <;> norm_num
  | succ n ih => rw [pow_succ]; exact coeff_mul_nonneg ih ha z

theorem coeff_pow_mono {a b : MonoidAlgebra ℝ G}
    (ha : ∀ g, 0 ≤ a.coeff g) (hb : ∀ g, 0 ≤ b.coeff g)
    (hab : ∀ g, a.coeff g ≤ b.coeff g) (n : ℕ) (z : G) :
    (a ^ n).coeff z ≤ (b ^ n).coeff z := by
  classical
  induction n generalizing z with
  | zero => exact le_rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact coeff_mul_mono ih hab ha (coeff_pow_nonneg hb n) z

/-- A central coefficient is cyclic, just as the normalized regular trace. -/
theorem central_coeff_mul_comm (a b : MonoidAlgebra ℝ G) (z : G)
    (hz : z ∈ Subgroup.center G) : (a * b).coeff z = (b * a).coeff z := by
  classical
  have hswitch (g h : G) : g * h = z ↔ h * g = z := by
    constructor
    · intro he
      have hc := Subgroup.mem_center_iff.mp hz h
      rw [← he] at hc
      have hh : (h * g) * h = (g * h) * h := by simpa only [mul_assoc] using hc
      exact (mul_right_cancel hh).trans he
    · intro he
      have hc := Subgroup.mem_center_iff.mp hz g
      rw [← he] at hc
      have hh : (g * h) * g = (h * g) * g := by simpa only [mul_assoc] using hc
      exact (mul_right_cancel hh).trans he
  induction a using MonoidAlgebra.induction_linear generalizing b with
  | zero => simp
  | add a a' ha ha' => simp [add_mul, mul_add, ha, ha']
  | single g r =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp [add_mul, mul_add, hb, hb']
    | single h s =>
      simp only [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [hswitch]
      simp only [mul_comm]

/-- Every coefficient of an actual autocorrelation is bounded by its identity
coefficient. The proof is the finite sum of the corresponding square differences. -/
theorem autocorrelation_coeff_le (a : MonoidAlgebra ℝ G) (z : G) :
    (a * reverseCoefficients a).coeff z ≤ (a * reverseCoefficients a).coeff 1 := by
  classical
  simp only [coeff_mul_fintype, coeff_reverse, mul_inv_rev, inv_inv, inv_one, one_mul,
    mul_one]
  have hsum : (∑ g : G, (a.coeff (z⁻¹ * g)) ^ 2) = ∑ g : G, (a.coeff g) ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft z⁻¹) _ _ (fun _ => rfl)
  have hh : 2 * (∑ g : G, a.coeff g * a.coeff (z⁻¹ * g)) ≤
      (∑ g : G, (a.coeff g) ^ 2) + ∑ g : G, (a.coeff (z⁻¹ * g)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g _
    nlinarith [sq_nonneg (a.coeff g - a.coeff (z⁻¹ * g))]
  rw [hsum] at hh
  simp only [pow_two] at hh
  linarith

/-- The cube of two actual autocorrelations has maximal central coefficient
at the identity. This requires no abstract positivity supplier. -/
theorem central_alternating_autocorrelation_le (a b : MonoidAlgebra ℝ G) (z : G)
    (hz : z ∈ Subgroup.center G) :
    (((a * reverseCoefficients a) * (b * reverseCoefficients b)) ^ 3).coeff z ≤
      (((a * reverseCoefficients a) * (b * reverseCoefficients b)) ^ 3).coeff 1 := by
  let P := reverseCoefficients b * a
  let T := P * reverseCoefficients P
  let K := T * P
  let D := a * reverseCoefficients a * b * reverseCoefficients b * a *
    reverseCoefficients a * b * reverseCoefficients b * a * reverseCoefficients a * b
  have hrotate (g : G) (hg : g ∈ Subgroup.center G) :
      (((a * reverseCoefficients a) * (b * reverseCoefficients b)) ^ 3).coeff g =
        (T ^ 3).coeff g := by
    have hleft : ((a * reverseCoefficients a) * (b * reverseCoefficients b)) ^ 3 =
        D * reverseCoefficients b := by
      dsimp [D]
      simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
    have hright : reverseCoefficients b * D = T ^ 3 := by
      dsimp [D, T, P]
      simp only [reverse_mul, reverse_reverse, pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
    rw [hleft, central_coeff_mul_comm D (reverseCoefficients b) g hg, hright]
  have hgram : T ^ 3 = K * reverseCoefficients K := by
    dsimp [K]
    rw [reverse_mul]
    have hT : reverseCoefficients T = T := by simp [T, reverse_mul]
    rw [hT]
    dsimp [T]
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
  rw [hrotate z hz, hrotate 1 (Subgroup.one_mem _), hgram]
  exact autocorrelation_coeff_le K z

end

end D5.S3.FiniteGroups.RegularRepresentation.CentralAutocorrelation
