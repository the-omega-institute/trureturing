import D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
import D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
SOURCE-ONLY, UNELABORATED transient exact-application candidate for original #8330 §9.4.
Project source: 7716a33a25feda45ad185b97597f8a5cdf89a66d.
Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679; Lean: 4.35.0.
This file is runner evidence, not a proposed retained D5 module or admission decision.
No validation, report, emission, registration, coverage, freeze or publication is asserted.
-/

namespace Original8330Literal94SourceOnly

noncomputable section

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality (run_unit_word)
open D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw (HasFiniteHorizonPredictor)

-- This is a derived estimate, not an extra Lipschitz hypothesis on the machine.
private theorem chord_of_real_residual (z : UnitAddCircle) (r : ℝ) :
    ‖(AddCircle.toCircle (T := (1 : ℝ)) (z + (r : UnitAddCircle)) : ℂ) - (AddCircle.toCircle (T := (1 : ℝ)) z : ℂ)‖ ≤
      2 * Real.pi * |r| := by
  have hexp : (AddCircle.toCircle (T := (1 : ℝ)) (r : UnitAddCircle) : ℂ) =
      Complex.exp (Complex.I * ((2 * Real.pi * r : ℝ) : ℂ)) := by
    rw [AddCircle.toCircle_apply_mk (T := (1 : ℝ)) r, Circle.coe_exp]
    simp only [div_one]
    congr 1
    exact mul_comm _ _
  rw [AddCircle.toCircle_add (T := (1 : ℝ)) z (r : UnitAddCircle), Circle.coe_mul]
  rw [show (AddCircle.toCircle (T := (1 : ℝ)) z : ℂ) * (AddCircle.toCircle (T := (1 : ℝ)) (r : UnitAddCircle) : ℂ) -
      (AddCircle.toCircle (T := (1 : ℝ)) z : ℂ) =
      (AddCircle.toCircle (T := (1 : ℝ)) z : ℂ) * ((AddCircle.toCircle (T := (1 : ℝ)) (r : UnitAddCircle) : ℂ) - 1) by ring]
  rw [norm_mul, Circle.norm_coe, one_mul, hexp]
  calc
    ‖Complex.exp (Complex.I * ((2 * Real.pi * r : ℝ) : ℂ)) - 1‖ ≤
        ‖(2 * Real.pi * r : ℝ)‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * r)
    _ = |2 * Real.pi| * |r| := by rw [Real.norm_eq_abs, abs_mul]
    _ = 2 * Real.pi * |r| := by
      rw [abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]

-- The single root contains both the exact q-state witnesses and the actual
-- finite-word receiving predicate. All witnesses precede every x, n and word.
theorem full_exact_application (α : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (H : ℕ) :
    letI : NeZero q := ⟨ne_of_gt hq⟩
    let ε : ℝ := Real.pi / (q : ℝ) +
      2 * Real.pi * (H : ℝ) * |α - (p : ℝ) / (q : ℝ)|
    0 ≤ ε ∧ Nonempty (ZMod q) ∧ Fintype.card (ZMod q) = q ∧
      ∃ (e : UnitAddCircle → ZMod q) (G : ZMod q → ZMod q) (h : ZMod q → ℂ),
        (∀ x, e x = (round ((q : ℝ) *
          (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) : ZMod q)) ∧
        G = (fun j => j + (p : ZMod q)) ∧
        h = (fun j => ZMod.stdAddChar j) ∧
        (∀ x (n : ℕ), n ≤ H →
          ‖h ((G^[n]) (e x)) -
            (AddCircle.toCircle (T := (1 : ℝ)) (x + n • (α : UnitAddCircle)) : ℂ)‖ ≤ ε) ∧
        (∀ x (w : List Unit), w.length ≤ H →
          dist (h (runWord (fun _ : Unit => G) w (e x)))
            (AddCircle.toCircle (T := (1 : ℝ)) (runWord (fun (_ : Unit) (y : UnitAddCircle) =>
              y + (α : UnitAddCircle)) w x) : ℂ) ≤ ε) ∧
        HasFiniteHorizonPredictor
          (fun (_ : Unit) (y : UnitAddCircle) => y + (α : UnitAddCircle))
          (fun y => (AddCircle.toCircle (T := (1 : ℝ)) y : ℂ)) H ε q := by
  classical
  letI : NeZero q := ⟨ne_of_gt hq⟩
  let ε : ℝ := Real.pi / (q : ℝ) +
    2 * Real.pi * (H : ℝ) * |α - (p : ℝ) / (q : ℝ)|
  let t : UnitAddCircle → ℝ := fun x =>
    (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)
  let m : UnitAddCircle → ℤ := fun x => round ((q : ℝ) * t x)
  let e : UnitAddCircle → ZMod q := fun x => (m x : ZMod q)
  let G : ZMod q → ZMod q := fun j => j + (p : ZMod q)
  let h : ZMod q → ℂ := fun j => ZMod.stdAddChar j
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have ht (x : UnitAddCircle) : (t x : UnitAddCircle) = x := by
    simpa only [t] using
      (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x))
  -- The range of equivIco is [0,1). The half-grid estimate below does not
  -- exclude either endpoint tie or the rounded value m(x)=q.
  have hround (x : UnitAddCircle) :
      |t x - (m x : ℝ) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
    have hb : |(q : ℝ) * t x - (m x : ℝ)| ≤ (1 : ℝ) / 2 := by
      simpa only [m] using (abs_sub_round ((q : ℝ) * t x))
    have hrewrite : t x - (m x : ℝ) / (q : ℝ) =
        ((q : ℝ) * t x - (m x : ℝ)) / (q : ℝ) := by
      field_simp [hqne] <;> ring
    rw [hrewrite, abs_div, abs_of_pos hqR]
    calc
      |(q : ℝ) * t x - (m x : ℝ)| / (q : ℝ) ≤
          ((1 : ℝ) / 2) / (q : ℝ) :=
        (div_le_div_iff_of_pos_right hqR).mpr hb
      _ = 1 / (2 * (q : ℝ)) := by rw [div_div]
  have hG (x : UnitAddCircle) (n : ℕ) :
      (G^[n]) (e x) = (m x : ZMod q) + n • (p : ZMod q) := by
    simpa only [G, e] using
      (add_right_iterate_apply (p : ZMod q) (m x : ZMod q) (n := n))
  -- Apply the actual homomorphism to signed integer casts. No assertion
  -- identifying ZMod.val with an arbitrary integer representative is used.
  have hphase (x : UnitAddCircle) (n : ℕ) :
      ZMod.toAddCircle ((G^[n]) (e x)) =
        (((m x : ℝ) / (q : ℝ) +
          (n : ℝ) * ((p : ℝ) / (q : ℝ)) : ℝ) : UnitAddCircle) := by
    calc
      ZMod.toAddCircle ((G^[n]) (e x)) =
          ZMod.toAddCircle (m x : ZMod q) +
            n • ZMod.toAddCircle (p : ZMod q) := by
        rw [hG, map_add, map_nsmul]
      _ = ((m x : ℝ) / (q : ℝ) : UnitAddCircle) +
          n • ((p : ℝ) / (q : ℝ) : UnitAddCircle) := by
        rw [ZMod.toAddCircle_intCast, ZMod.toAddCircle_intCast]
      _ = _ := by
        rw [← AddCircle.coe_nsmul, ← AddCircle.coe_add]
        simp only [nsmul_eq_mul]
  have hscale : 2 * Real.pi * (1 / (2 * (q : ℝ))) =
      Real.pi / (q : ℝ) := by
    field_simp [hqne] <;> ring
  have hacc (x : UnitAddCircle) (n : ℕ) (hn : n ≤ H) :
      ‖h ((G^[n]) (e x)) -
        (AddCircle.toCircle (T := (1 : ℝ)) (x + n • (α : UnitAddCircle)) : ℂ)‖ ≤ ε := by
    let b : ℝ := (m x : ℝ) / (q : ℝ) +
      (n : ℝ) * ((p : ℝ) / (q : ℝ))
    let r : ℝ := t x - (m x : ℝ) / (q : ℝ) +
      (n : ℝ) * (α - (p : ℝ) / (q : ℝ))
    have hclock : h ((G^[n]) (e x)) =
        (AddCircle.toCircle (T := (1 : ℝ)) (b : UnitAddCircle) : ℂ) := by
      dsimp only [h]
      rw [ZMod.stdAddChar_apply]
      change (AddCircle.toCircle (T := (1 : ℝ))
        (ZMod.toAddCircle (N := q) ((G^[n]) (e x))) : ℂ) = _
      rw [hphase]
    have htrue : x + n • (α : UnitAddCircle) =
        (b : UnitAddCircle) + (r : UnitAddCircle) := by
      calc
        x + n • (α : UnitAddCircle) =
            (t x : UnitAddCircle) + n • (α : UnitAddCircle) := by rw [ht]
        _ = ((t x + (n : ℝ) * α : ℝ) : UnitAddCircle) := by
          rw [← AddCircle.coe_nsmul, ← AddCircle.coe_add]
          simp only [nsmul_eq_mul]
        _ = ((b + r : ℝ) : UnitAddCircle) := by
          congr 1
          dsimp only [b, r]
          ring
        _ = (b : UnitAddCircle) + (r : UnitAddCircle) :=
          AddCircle.coe_add (1 : ℝ) b r
    have hres : |r| ≤ 1 / (2 * (q : ℝ)) +
        (H : ℝ) * |α - (p : ℝ) / (q : ℝ)| := by
      calc
        |r| ≤ |t x - (m x : ℝ) / (q : ℝ)| +
            |(n : ℝ) * (α - (p : ℝ) / (q : ℝ))| :=
          abs_add_le _ _
        _ = |t x - (m x : ℝ) / (q : ℝ)| +
            (n : ℝ) * |α - (p : ℝ) / (q : ℝ)| := by
          have hnabs : |(n : ℝ)| = (n : ℝ) :=
            abs_of_nonneg (Nat.cast_nonneg n)
          rw [abs_mul, hnabs]
        _ ≤ 1 / (2 * (q : ℝ)) +
            (H : ℝ) * |α - (p : ℝ) / (q : ℝ)| :=
          add_le_add (hround x)
            (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) (abs_nonneg _))
    calc
      ‖h ((G^[n]) (e x)) -
          (AddCircle.toCircle (T := (1 : ℝ)) (x + n • (α : UnitAddCircle)) : ℂ)‖ =
          ‖(AddCircle.toCircle (T := (1 : ℝ)) (x + n • (α : UnitAddCircle)) : ℂ) -
            h ((G^[n]) (e x))‖ := norm_sub_rev _ _
      _ = ‖(AddCircle.toCircle (T := (1 : ℝ))
          ((b : UnitAddCircle) + (r : UnitAddCircle)) : ℂ) -
          (AddCircle.toCircle (T := (1 : ℝ)) (b : UnitAddCircle) : ℂ)‖ := by rw [hclock, htrue]
      _ ≤ 2 * Real.pi * |r| := chord_of_real_residual (b : UnitAddCircle) r
      _ ≤ 2 * Real.pi * (1 / (2 * (q : ℝ)) +
          (H : ℝ) * |α - (p : ℝ) / (q : ℝ)|) :=
        mul_le_mul_of_nonneg_left hres (by positivity)
      _ = ε := by
        rw [mul_add, hscale]
        dsimp only [ε]
        ring
  have hword (x : UnitAddCircle) (w : List Unit) (hw : w.length ≤ H) :
      dist (h (runWord (fun _ : Unit => G) w (e x)))
        (AddCircle.toCircle (T := (1 : ℝ)) (runWord (fun (_ : Unit) (y : UnitAddCircle) =>
          y + (α : UnitAddCircle)) w x) : ℂ) ≤ ε := by
    simpa only [run_unit_word, add_right_iterate_apply, dist_eq_norm] using
      (hacc x w.length hw)
  have hpred : HasFiniteHorizonPredictor
      (fun (_ : Unit) (y : UnitAddCircle) => y + (α : UnitAddCircle))
      (fun y => (AddCircle.toCircle (T := (1 : ℝ)) y : ℂ)) H ε q := by
    refine ⟨ZMod q, inferInstance, ⟨0⟩, (ZMod.card q).le,
      e, (fun _ : Unit => G), h, ?_⟩
    exact hword
  refine ⟨hε, ⟨0⟩, ZMod.card q, e, G, h, ?_, rfl, rfl, hacc, hword, hpred⟩
  intro x
  rfl

-- For the later single whole-candidate check, this audits the root and its
-- transitive helper dependencies in the same invocation. Nothing is run here.
#check full_exact_application
#print axioms full_exact_application

end

end Original8330Literal94SourceOnly
