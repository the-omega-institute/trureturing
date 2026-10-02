/- GID: D5/S3/Arith/Robin/ShortCofactorCharacterEnergy
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ShortCofactorCharacterEnergy
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Short positive intervals have a logarithmic multiplicative energy bound. -/

import Mathlib.Combinatorics.Additive.Energy
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

namespace D5.S3.Arith.Robin.ShortCofactorCharacterEnergy

open Finset

/-- The positive natural numbers strictly below a real cutoff. -/
noncomputable def shortInterval (H : ℝ) : Finset ℕ := Ico 1 ⌈H⌉₊

/-- The classical gcd parametrization gives a logarithmic energy bound. -/
theorem short_interval_energy (H : ℝ) (hH : 1 ≤ H) :
    ((shortInterval H).mulEnergy (shortInterval H) : ℝ) ≤
      2 * H ^ 2 * (1 + Real.log H) := by
  classical
  have integer_bound (N : ℕ) :
      ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ) ≤
        2 * (N : ℝ) ^ 2 * (harmonic N : ℝ) := by
    let bucket (m : ℕ) : Finset (Bool × ℕ × ℕ × ℕ) :=
      univ ×ˢ (Icc 1 m) ×ˢ (Icc 1 (N / m)) ×ˢ (Icc 1 (N / m))
    let parameters := (Icc 1 N).sigma bucket
    let decode : (Σ _ : ℕ, Bool × ℕ × ℕ × ℕ) → (ℕ × ℕ) × ℕ × ℕ :=
      fun z => if z.2.1 then
        ((z.2.2.2.1 * z.1, z.2.2.2.1 * z.2.2.1),
          z.2.2.2.2 * z.2.2.1, z.2.2.2.2 * z.1)
      else
        ((z.2.2.2.1 * z.2.2.1, z.2.2.2.1 * z.1),
          z.2.2.2.2 * z.1, z.2.2.2.2 * z.2.2.1)
    have cover : Set.SurjOn decode (↑parameters)
        (↑(((Icc 1 N ×ˢ Icc 1 N) ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
          fun x => x.1.1 * x.2.1 = x.1.2 * x.2.2)) := by
      intro x hx
      simp only [mem_coe, mem_filter, mem_product, mem_Icc] at hx
      obtain ⟨⟨⟨ha, hc⟩, hb, hd⟩, heq⟩ := hx
      let g := Nat.gcd x.1.1 x.1.2
      let u := x.1.1 / g
      let v := x.1.2 / g
      have hg : 0 < g := Nat.gcd_pos_of_pos_left _ ha.1
      have hu : g * u = x.1.1 := Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _)
      have hv : g * v = x.1.2 := Nat.mul_div_cancel_left' (Nat.gcd_dvd_right _ _)
      have hu0 : 0 < u := by nlinarith [ha.1]
      have hv0 : 0 < v := by nlinarith [hc.1]
      have huv : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd hg
      have heq' : u * x.2.1 = v * x.2.2 := by
        apply Nat.eq_of_mul_eq_mul_left hg
        calc g * (u * x.2.1) = x.1.1 * x.2.1 := by rw [← mul_assoc, hu]
             _ = x.1.2 * x.2.2 := heq
             _ = g * (v * x.2.2) := by rw [← mul_assoc, hv]
      have hud : u ∣ x.2.2 := huv.dvd_of_dvd_mul_right
        (by rw [mul_comm x.2.2 v, ← heq']; exact dvd_mul_right u _)
      obtain ⟨j, hj⟩ := hud
      have hj0 : 0 < j := by nlinarith [hd.1]
      have hjv : j * v = x.2.1 := by
        apply Nat.eq_of_mul_eq_mul_left hu0
        calc u * (j * v) = (u * j) * v := by ring
             _ = x.2.2 * v := by rw [← hj]
             _ = v * x.2.2 := mul_comm _ _
             _ = u * x.2.1 := heq'.symm
      have hju : j * u = x.2.2 := by rw [mul_comm, ← hj]
      by_cases huvle : v ≤ u
      · have hum : u ≤ N := (Nat.div_le_self _ _).trans ha.2
        have hgu : g ≤ N / u := (Nat.le_div_iff_mul_le hu0).mpr (hu ▸ ha.2)
        have hjuN : j ≤ N / u := (Nat.le_div_iff_mul_le hu0).mpr (hju ▸ hd.2)
        refine ⟨⟨u, true, v, g, j⟩, ?_, ?_⟩
        · simp only [mem_coe, parameters, mem_sigma, bucket, mem_product, mem_univ,
            mem_Icc, true_and]
          exact ⟨⟨hu0, hum⟩, ⟨hv0, huvle⟩, ⟨hg, hgu⟩, ⟨hj0, hjuN⟩⟩
        · simp only [decode, ↓reduceIte]
          exact Prod.ext (Prod.ext hu hv) (Prod.ext hjv hju)
      · have huvle' : u ≤ v := by omega
        have hvm : v ≤ N := (Nat.div_le_self _ _).trans hc.2
        have hgv : g ≤ N / v := (Nat.le_div_iff_mul_le hv0).mpr (hv ▸ hc.2)
        have hjvN : j ≤ N / v := (Nat.le_div_iff_mul_le hv0).mpr (hjv ▸ hb.2)
        refine ⟨⟨v, false, u, g, j⟩, ?_, ?_⟩
        · simp only [mem_coe, parameters, mem_sigma, bucket, mem_product, mem_univ,
            mem_Icc, true_and]
          exact ⟨⟨hv0, hvm⟩, ⟨hu0, huvle'⟩, ⟨hg, hgv⟩, ⟨hj0, hjvN⟩⟩
        · simp only [decode, Bool.false_eq_true, ↓reduceIte]
          exact Prod.ext (Prod.ext hu hv) (Prod.ext hjv hju)
    have count : (Icc 1 N).mulEnergy (Icc 1 N) ≤
        ∑ m ∈ Icc 1 N, 2 * m * (N / m) ^ 2 := by
      have hc := card_le_card_of_surjOn decode cover
      simp only [parameters, card_sigma, bucket, card_product, card_univ,
        Fintype.card_bool, Nat.card_Icc, Nat.add_sub_cancel] at hc
      simpa only [Finset.mulEnergy, pow_two, mul_assoc] using hc
    have real_count : ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ) ≤
        ∑ m ∈ Icc 1 N, 2 * (m : ℝ) * (N / m : ℕ) ^ 2 := by
      exact_mod_cast count
    calc
      ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ)
          ≤ ∑ m ∈ Icc 1 N, 2 * (m : ℝ) * (N / m : ℕ) ^ 2 := real_count
      _ ≤ ∑ m ∈ Icc 1 N, 2 * (N : ℝ) ^ 2 * (m : ℝ)⁻¹ := by
        apply sum_le_sum
        intro m hm
        have hm0 : 0 < (m : ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
        have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
        calc
          2 * (m : ℝ) * (N / m : ℕ) ^ 2
              ≤ 2 * (m : ℝ) * ((N : ℝ) / m) ^ 2 := by gcongr
          _ = 2 * (N : ℝ) ^ 2 * (m : ℝ)⁻¹ := by field_simp
      _ = 2 * (N : ℝ) ^ 2 * (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, mul_sum]
  let N := ⌈H⌉₊ - 1
  have hceil : 1 ≤ ⌈H⌉₊ := (Nat.ceil_pos.mpr (by linarith : 0 < H))
  have hN : (N : ℝ) < H := by
    have hlt : N < ⌈H⌉₊ := by dsimp [N]; omega
    exact Nat.lt_ceil.mp hlt
  have interval_eq : shortInterval H = Icc 1 N := by
    ext n
    simp only [shortInterval, mem_Ico, mem_Icc]
    dsimp [N]
    omega
  rw [interval_eq]
  by_cases hN0 : N = 0
  · simp only [hN0, Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      mulEnergy_empty_left, Nat.cast_zero]
    exact mul_nonneg (by positivity) (by linarith [Real.log_nonneg hH])
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
  calc
    ((Icc 1 N).mulEnergy (Icc 1 N) : ℝ)
        ≤ 2 * (N : ℝ) ^ 2 * (harmonic N : ℝ) := integer_bound N
    _ ≤ 2 * (N : ℝ) ^ 2 * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N
    _ ≤ 2 * H ^ 2 * (1 + Real.log H) := by
      gcongr

end D5.S3.Arith.Robin.ShortCofactorCharacterEnergy
