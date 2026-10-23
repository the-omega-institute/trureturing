/- GID: D5/S3/Quantum/ScalarFidelityEndpoint
   generality: G
   mirror-B: D5/B/S3/Quantum/ScalarFidelityEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Sqrt]
   utility: none
   digest: Sharp squared imbalance characterizes scalar fidelity endpoint dominance. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.ScalarFidelityEndpoint

/-- The real scalar quotient occurring in the qubit fidelity formula. -/
def scalarQuotient (a b c : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 + c ^ 2 - 1) / (2 * a * b)

/-
proof_shape: endpoint_certificate: bind-only; consumer: endpoint_nondecrease
proof_shape: endpoint_nondecrease: content
proof_shape: necessary_one_coordinate: content
proof_shape: lower_corner_dominance_iff: content
admission_basis: escape-witness
The characterization uses a constructive violating endpoint and a nonnegative
endpoint estimate. The polynomial identity alone supplies no new content.
utility: none; all variables range over real intervals, with no finite-instance
enumeration, checker, numerical reduction or certified-instance conclusion.
-/

private theorem endpoint_certificate (a b c x y : ℝ) :
    a * b * ((a + x) ^ 2 + (b + y) ^ 2 + c ^ 2 - 1) -
      (a + x) * (b + y) * (a ^ 2 + b ^ 2 + c ^ 2 - 1) =
    b * x * (a ^ 2 - b ^ 2 + (1 - c ^ 2)) +
      a * y * (b ^ 2 - a ^ 2 + (1 - c ^ 2)) +
      a * b * (x - y) ^ 2 + ((1 - c ^ 2) - (a - b) ^ 2) * x * y := by
  ring

private theorem endpoint_nondecrease {a b c A B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hbalance : |a ^ 2 - b ^ 2| ≤ 1 - c ^ 2)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) :
    scalarQuotient a b c ≤ scalarQuotient A B C := by
  have hx : 0 ≤ A - a := sub_nonneg.mpr hA
  have hy : 0 ≤ B - b := sub_nonneg.mpr hB
  have hp : 0 ≤ a ^ 2 - b ^ 2 + (1 - c ^ 2) := by
    have h := (abs_le.mp hbalance).1
    linarith
  have hq : 0 ≤ b ^ 2 - a ^ 2 + (1 - c ^ 2) := by
    have h := (abs_le.mp hbalance).2
    linarith
  have hab : (a - b) ^ 2 ≤ 1 - c ^ 2 := by
    rcases le_total a b with h | h
    · have ht := (abs_le.mp hbalance).1
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h)]
    · have ht := (abs_le.mp hbalance).2
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr h)]
  have h1 := mul_nonneg (mul_nonneg hb.le hx) hp
  have h2 := mul_nonneg (mul_nonneg ha.le hy) hq
  have h3 := mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg ((A - a) - (B - b)))
  have h4 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) hx) hy
  have hid := endpoint_certificate a b c (A - a) (B - b)
  have gap : 0 ≤ a * b * (A ^ 2 + B ^ 2 + c ^ 2 - 1) -
      A * B * (a ^ 2 + b ^ 2 + c ^ 2 - 1) := by
    nlinarith only [hid, h1, h2, h3, h4]
  have hCsq : c ^ 2 ≤ C ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (show 0 ≤ C + c by linarith)]
  have h5 := mul_nonneg (mul_nonneg ha.le hb.le) (sub_nonneg.mpr hCsq)
  have hApos : 0 < A := lt_of_lt_of_le ha hA
  have hBpos : 0 < B := lt_of_lt_of_le hb hB
  unfold scalarQuotient
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * a * b)
    (by positivity : 0 < 2 * A * B)).mpr
  nlinarith only [gap, h5]

private theorem necessary_one_coordinate {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : ∀ A : ℝ, a ≤ A → A ≤ 1 →
      scalarQuotient a b c ≤ scalarQuotient A b c) :
    b ^ 2 - a ^ 2 ≤ 1 - c ^ 2 := by
  by_contra hn
  have hbad : a ^ 2 < b ^ 2 + c ^ 2 - 1 := by linarith
  have hk : 0 ≤ b ^ 2 + c ^ 2 - 1 := by nlinarith [sq_nonneg a]
  let s : ℝ := Real.sqrt (b ^ 2 + c ^ 2 - 1)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = b ^ 2 + c ^ 2 - 1 := Real.sq_sqrt hk
  have has : a < s := by nlinarith
  have hs1 : s ≤ 1 := by
    have hb2 : b ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hb1)]
    have hc2 : c ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]
    nlinarith
  have hcompare := (div_le_div_iff₀
    (by positivity : 0 < 2 * a * b)
    (by have : 0 < s := lt_trans ha has; positivity : 0 < 2 * s * b)).mp
    (h s has.le hs1)
  have strict : 0 < b * s * (s - a) ^ 2 := by
    have hspos : 0 < s := lt_trans ha has
    have hsq : 0 < (s - a) ^ 2 := sq_pos_of_pos (sub_pos.mpr has)
    exact mul_pos (mul_pos hb hspos) hsq
  have hin : a ^ 2 + b ^ 2 + c ^ 2 - 1 = a ^ 2 + s ^ 2 := by
    linarith only [hs2]
  have hout : s ^ 2 + b ^ 2 + c ^ 2 - 1 = 2 * s ^ 2 := by
    linarith only [hs2]
  rw [hin, hout] at hcompare
  nlinarith only [hcompare, strict]

/-- Exact lower-corner dominance for every independent upper endpoint. -/
theorem lower_corner_dominance_iff (a b c : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (∀ A B C : ℝ, a ≤ A → A ≤ 1 → b ≤ B → B ≤ 1 → c ≤ C → C ≤ 1 →
      scalarQuotient a b c ≤ scalarQuotient A B C) ↔
      |a ^ 2 - b ^ 2| ≤ 1 - c ^ 2 := by
  constructor
  · intro h
    have hleft := necessary_one_coordinate ha hb hb1 hc hc1
      (fun A hA hA1 => h A b c hA hA1 le_rfl hb1 le_rfl hc1)
    have hright := necessary_one_coordinate hb ha ha1 hc hc1 (by
      intro B hB hB1
      simpa [scalarQuotient, add_comm, add_left_comm, mul_comm, mul_left_comm]
        using h a B c le_rfl ha1 hB hB1 le_rfl hc1)
    exact abs_le.mpr ⟨by linarith, hright⟩
  · intro hbalance A B C hA _hA1 hB _hB1 hC _hC1
    exact endpoint_nondecrease ha hb hc hbalance hA hB hC

end D5.S3.Quantum.ScalarFidelityEndpoint
