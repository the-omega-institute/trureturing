/- GID: D5/S3/Quantum/Recovery/PetzProjectedHessian
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzProjectedHessian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The weighted representative of a trace test on the full two-flag partial-trace kernel. -/


import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Explicit weighted coordinates on the two-flag partial-trace kernel. -/


noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Recovery.PetzProjectedHessian

open Matrix
open scoped BigOperators
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

abbrev Slot := Fin 2 × Fin 2
abbrev Joint := Matrix Slot Slot ℂ
abbrev Weights := Slot → Slot → ℝ

/-- The real weighted pairing on all complex matrix entries. -/
def pairing (w : Weights) (U Z : Joint) : ℝ :=
  ∑ i, ∑ j, (star (U i j) * Z i j).re / w i j

/-- The squared Hessian length in diagonal coordinates. -/
def energy (w : Weights) (Z : Joint) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (Z i j) / w i j

/-- The effective weight for the constrained pair of same-flag entries. -/
def reducedWeight (w : Weights) (b d : Fin 2) : ℝ :=
  w (b, 0) (d, 0) * w (b, 1) (d, 1) / (w (b, 0) (d, 0) + w (b, 1) (d, 1))

/-- In each retained entry the same-flag coherence is represented by an
opposite pair. Inter-flag entries are free and retain their original weights. -/
def representative (w : Weights) (Y : Joint) : Joint := fun i j =>
  if i.2 = j.2 then
    let δ := (reducedWeight w i.1 j.1 : ℂ) * (Y (i.1, 0) (j.1, 0) - Y (i.1, 1) (j.1, 1))
    if i.2 = 0 then δ else -δ
  else (w i j : ℂ) * Y i j

private theorem sum_entries (f : Slot → Slot → ℝ) :
    ∑ i, ∑ j, f i j =
      ∑ b : Fin 2, ∑ d : Fin 2,
        (f (b, 0) (d, 0) + f (b, 1) (d, 1) +
         f (b, 0) (d, 1) + f (b, 1) (d, 0)) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private theorem pair_scaled (a w : ℝ) (u z : ℂ) :
    (star ((a : ℂ) * u) * z).re / w = (a / w) * (star u * z).re := by
  rw [star_mul, mul_comm (star u), mul_assoc]
  simp [Complex.mul_re]
  ring

private theorem normSq_scaled (a : ℝ) (u : ℂ) :
    Complex.normSq ((a : ℂ) * u) = a ^ 2 * Complex.normSq u := by
  rw [map_mul, Complex.normSq_ofReal]
  ring

private theorem reducedWeight_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a * b / (a + b)) / a + (a * b / (a + b)) / b = 1 := by
  field_simp [ha.ne', hb.ne', (add_pos ha hb).ne']
  exact add_comm _ _

/-- The actual partial-trace kernel representative preserves Hermiticity, represents
the trace pairing on the entire kernel, and has the stated exact weighted energy. -/
theorem representative_spec (w : Weights) (Y : Joint)
    (hw : ∀ i j, 0 < w i j) (hs : ∀ i j, w i j = w j i) (hY : Y.IsHermitian) :
    (representative w Y).IsHermitian ∧ partialTraceRight (representative w Y) = 0 ∧
    (∀ Z : Joint, partialTraceRight Z = 0 → pairing w (representative w Y) Z = (Y * Z).trace.re) ∧
    energy w (representative w Y) =
      ∑ b : Fin 2, ∑ d : Fin 2,
        (reducedWeight w b d * Complex.normSq (Y (b, 0) (d, 0) - Y (b, 1) (d, 1)) +
         w (b, 0) (d, 1) * Complex.normSq (Y (b, 0) (d, 1)) +
         w (b, 1) (d, 0) * Complex.normSq (Y (b, 1) (d, 0))) := by
  have hsym (b d : Fin 2) : reducedWeight w d b = reducedWeight w b d := by
    unfold reducedWeight
    rw [hs (d, 0) (b, 0), hs (d, 1) (b, 1)]
  have hd (b d : Fin 2) :
      reducedWeight w b d / w (b, 0) (d, 0) +
      reducedWeight w b d / w (b, 1) (d, 1) = 1 :=
    reducedWeight_div _ _ (hw _ _) (hw _ _)
  refine ⟨Matrix.IsHermitian.ext ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : i.2 = j.2
    · simp only [representative, ite_eq_left h, ite_eq_left h.symm]
      rw [h]
      split <;> simp only [star_neg, star_mul', star_sub,
        show ∀ a : ℝ, star (a : ℂ) = (a : ℂ) from Complex.conj_ofReal, hY.apply, hsym]
    · simp only [representative, ite_eq_right h, ite_eq_right (Ne.symm h), star_mul',
        show ∀ a : ℝ, star (a : ℂ) = (a : ℂ) from Complex.conj_ofReal, hY.apply, hs j i]
  · ext b d
    simp [partialTraceRight, Fin.sum_univ_two, representative]
  · intro Z hZ
    rw [Matrix.trace_mul_comm]
    unfold pairing Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    have htrace : (∑ i, ∑ j, (Z i j * Y j i).re) =
        ∑ i, ∑ j, (star (Y i j) * Z i j).re := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hY.apply, mul_comm]
    rw [htrace]
    rw [sum_entries, sum_entries]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
    have hz : Z (b, 1) (d, 1) = - Z (b, 0) (d, 0) := by
      have he := congrFun (congrFun hZ b) d
      simp only [partialTraceRight, Fin.sum_univ_two, Matrix.zero_apply] at he
      exact eq_neg_of_add_eq_zero_right he
    simp only [representative, if_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),
      ite_eq_right (show (0 : Fin 2) ≠ 1 by decide), hz, star_neg, neg_mul_neg,
      pair_scaled, div_self (hw _ _).ne', one_mul, mul_neg, Complex.neg_re]
    rw [← add_mul, hd, one_mul, star_sub, sub_mul, Complex.sub_re]
    ring
  · unfold energy
    rw [sum_entries]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [representative, if_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide),
      ite_eq_right (show (0 : Fin 2) ≠ 1 by decide), Complex.normSq_neg, normSq_scaled]
    have hsquare (a w q : ℝ) : a ^ 2 * q / w = (a / w) * (a * q) := by ring
    rw [hsquare, hsquare, ← add_mul, hd, one_mul, hsquare, hsquare,
      div_self (hw (b, 0) (d, 1)).ne', div_self (hw (b, 1) (d, 0)).ne', one_mul, one_mul]

#print axioms representative_spec

end D5.S3.Quantum.Recovery.PetzProjectedHessian
