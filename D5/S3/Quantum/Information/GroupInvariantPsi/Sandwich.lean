/- GID: D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GroupInvariantPsi/Sandwich
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.MeanInequalitiesPow, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics]
   utility: none
   digest: Uniform finite mixtures have the same exponential overlap rate as their largest component pair. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open Finset Filter
open scoped BigOperators Topology
noncomputable section
namespace D5.S3.Quantum.Information.GroupInvariantPsi.Sandwich
private lemma sum_rpow_bound {I : Type*} [Fintype I] (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∑ i, a i) ^ s ≤ ∑ i, a i ^ s := by
  exact Finset.le_sum_of_subadditive_on_pred (fun x : ℝ => x ^ s)
    (fun x => 0 ≤ x) (by simp [Real.zero_rpow hs.ne'])
    (fun x y hx hy => Real.rpow_add_le_add_rpow hx hy hs.le hs1)
    (fun _ _ => add_nonneg) a (fun i _ => ha i)
/-- Uniform mixtures preserve a largest component overlap up to the number of components. -/
theorem sandwich {I W : Type*} [Fintype I] [Nonempty I] [Fintype W]
    (a b : I → W → ℝ) (ha : ∀ i w, 0 ≤ a i w) (hb : ∀ i w, 0 ≤ b i w)
    {s R : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hR : ∀ i j, (∑ w, a i w ^ s * b j w ^ (1 - s)) ≤ R)
    (hattain : ∃ i j, (∑ w, a i w ^ s * b j w ^ (1 - s)) = R) :
    R / Fintype.card I ≤
      ∑ w, ((Fintype.card I : ℝ)⁻¹ * ∑ i, a i w) ^ s *
        ((Fintype.card I : ℝ)⁻¹ * ∑ i, b i w) ^ (1 - s) ∧
    (∑ w, ((Fintype.card I : ℝ)⁻¹ * ∑ i, a i w) ^ s *
        ((Fintype.card I : ℝ)⁻¹ * ∑ i, b i w) ^ (1 - s)) ≤
      Fintype.card I * R := by
  classical
  have hk : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have ht : 0 < 1 - s := sub_pos.mpr hs1
  have hn (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      ((Fintype.card I : ℝ)⁻¹ * x) ^ s *
        ((Fintype.card I : ℝ)⁻¹ * y) ^ (1 - s) =
      (Fintype.card I : ℝ)⁻¹ * (x ^ s * y ^ (1 - s)) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hk.le) hx,
      Real.mul_rpow (inv_nonneg.mpr hk.le) hy]
    calc
      _ = (((Fintype.card I : ℝ)⁻¹) ^ s *
          ((Fintype.card I : ℝ)⁻¹) ^ (1 - s)) * (x ^ s * y ^ (1 - s)) := by ring
      _ = _ := by rw [← Real.rpow_add (inv_pos.mpr hk), add_sub_cancel,
        Real.rpow_one]
  simp_rw [hn _ _ (sum_nonneg fun i _ => ha i _) (sum_nonneg fun i _ => hb i _),
    ← mul_sum]
  constructor
  · obtain ⟨i, j, hij⟩ := hattain
    rw [div_eq_inv_mul, ← hij]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
    apply sum_le_sum
    intro w _
    exact mul_le_mul
      (Real.rpow_le_rpow (ha i w) (single_le_sum (fun k _ => ha k w) (mem_univ i)) hs.le)
      (Real.rpow_le_rpow (hb j w) (single_le_sum (fun k _ => hb k w) (mem_univ j)) ht.le)
      (Real.rpow_nonneg (hb j w) _) (Real.rpow_nonneg (sum_nonneg fun k _ => ha k w) _)
  · have hu : (∑ w, (∑ i, a i w) ^ s * (∑ i, b i w) ^ (1 - s)) ≤
        (Fintype.card I : ℝ) * (Fintype.card I : ℝ) * R := by
      calc
        _ ≤ ∑ w, (∑ i, a i w ^ s) * (∑ j, b j w ^ (1 - s)) := by
          apply sum_le_sum
          intro w _
          exact mul_le_mul (sum_rpow_bound _ (fun i => ha i w) hs hs1.le)
            (sum_rpow_bound _ (fun i => hb i w) ht (by linarith))
            (Real.rpow_nonneg (sum_nonneg fun i _ => hb i w) _)
            (sum_nonneg fun i _ => Real.rpow_nonneg (ha i w) _)
        _ = ∑ i, ∑ j, ∑ w, a i w ^ s * b j w ^ (1 - s) := by
          simp_rw [sum_mul, mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro i _
          rw [sum_comm]
        _ ≤ ∑ _i : I, ∑ _j : I, R := sum_le_sum fun i _ => sum_le_sum fun j _ => hR i j
        _ = _ := by simp [mul_assoc]
    calc
      _ ≤ (Fintype.card I : ℝ)⁻¹ * ((Fintype.card I : ℝ) * Fintype.card I * R) :=
        mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hk.le)
      _ = _ := by field_simp
end D5.S3.Quantum.Information.GroupInvariantPsi.Sandwich
