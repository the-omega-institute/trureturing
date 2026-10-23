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
set_option maxHeartbeats 800000
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
private theorem uniform_sandwich {I W : Type*} [Fintype I] [Nonempty I] [Fintype W]
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
/-- Single-site overlap for a relative permutation. -/
def componentCoeff {d : ℕ} {G : Type*} [Group G]
    (σ : G →* Equiv.Perm (Fin d)) (p q : Fin d → ℝ) (s : ℝ) (g : G) : ℝ :=
  ∑ i, p i ^ s * q (σ g i) ^ (1 - s)

/-- Largest single-site overlap. -/
def maxCoeff {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (σ : G →* Equiv.Perm (Fin d)) (p q : Fin d → ℝ) (s : ℝ) : ℝ :=
  univ.sup' univ_nonempty (componentCoeff σ p q s)

/-- Tensor overlaps of the uniform orbit mixtures have exponential bounds. -/
theorem sandwich {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (σ : G →* Equiv.Perm (Fin d)) (p q : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (n : ℕ) :
    maxCoeff σ p q s ^ n / Fintype.card G ≤
      ∑ w : Fin n → Fin d,
        ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∏ j, p ((σ g)⁻¹ (w j))) ^ s *
        ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∏ j, q ((σ g)⁻¹ (w j))) ^ (1 - s) ∧
    (∑ w : Fin n → Fin d,
        ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∏ j, p ((σ g)⁻¹ (w j))) ^ s *
        ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∏ j, q ((σ g)⁻¹ (w j))) ^ (1 - s)) ≤
      Fintype.card G * maxCoeff σ p q s ^ n := by
  classical
  have hc (g : G) : 0 ≤ componentCoeff σ p q s g :=
    sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hp i) _)
      (Real.rpow_nonneg (hq _) _)
  have hpair (g h : G) :
      (∑ w : Fin n → Fin d, (∏ j, p ((σ g)⁻¹ (w j))) ^ s *
        (∏ j, q ((σ h)⁻¹ (w j))) ^ (1 - s)) =
      componentCoeff σ p q s (h⁻¹ * g) ^ n := by
    calc
      _ = ∑ w : Fin n → Fin d, ∏ j,
          p ((σ g)⁻¹ (w j)) ^ s * q ((σ h)⁻¹ (w j)) ^ (1 - s) := by
        apply sum_congr rfl
        intro w _
        rw [← Real.finsetProd_rpow _ _ (fun j _ => hp _) s,
          ← Real.finsetProd_rpow _ _ (fun j _ => hq _) (1 - s), prod_mul_distrib]
      _ = (∑ i, p ((σ g)⁻¹ i) ^ s * q ((σ h)⁻¹ i) ^ (1 - s)) ^ n :=
        (Fintype.sum_pow (fun i : Fin d =>
          p ((σ g)⁻¹ i) ^ s * q ((σ h)⁻¹ i) ^ (1 - s)) n).symm
      _ = _ := by
        congr 1
        rw [← Equiv.sum_comp (σ g) (fun i => p ((σ g)⁻¹ i) ^ s * q ((σ h)⁻¹ i) ^ (1 - s))]
        simp [componentCoeff, map_mul, map_inv, Equiv.Perm.mul_apply]
  apply uniform_sandwich _ _
    (fun g w => prod_nonneg fun j _ => hp _)
    (fun g w => prod_nonneg fun j _ => hq _) hs hs1
  · intro g h
    rw [hpair]
    exact pow_le_pow_left₀ (hc _) (Finset.le_sup' _ (mem_univ _)) n
  · obtain ⟨g, _, hg⟩ := univ.exists_mem_eq_sup' univ_nonempty (componentCoeff σ p q s)
    refine ⟨g, 1, ?_⟩
    rw [hpair, inv_one, one_mul]
    exact congrArg (fun x : ℝ => x ^ n) hg.symm

private theorem log_rate (Z : ℕ → ℝ) {M k : ℝ} (hM : 0 < M) (hk : 0 < k)
    (hZ : ∀ n, M ^ n / k ≤ Z n ∧ Z n ≤ k * M ^ n) :
    Tendsto (fun n : ℕ => Real.log (Z n) / n) atTop (𝓝 (Real.log M)) := by
  have hlo : Tendsto (fun n : ℕ => Real.log M - Real.log k / n) atTop (𝓝 (Real.log M)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log k))
  have hhi : Tendsto (fun n : ℕ => Real.log M + Real.log k / n) atTop (𝓝 (Real.log M)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log k))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hlog := Real.log_le_log (div_pos (pow_pos hM n) hk) (hZ n).1
    rw [Real.log_div (pow_ne_zero n hM.ne') hk.ne', Real.log_pow] at hlog
    have hh := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    convert hh using 1 <;> field_simp <;> ring
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hpos : 0 < Z n := (div_pos (pow_pos hM n) hk).trans_le (hZ n).1
    have hlog := Real.log_le_log hpos (hZ n).2
    rw [Real.log_mul hk.ne' (pow_ne_zero n hM.ne'), Real.log_pow] at hlog
    have hh := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    convert hh using 1 <;> field_simp <;> ring

end D5.S3.Quantum.Information.GroupInvariantPsi.Sandwich
