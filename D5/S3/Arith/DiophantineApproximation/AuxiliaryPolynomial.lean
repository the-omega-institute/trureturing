/- GID: D5/S3/Arith/DiophantineApproximation/AuxiliaryPolynomial
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/AuxiliaryPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct a nonzero auxiliary polynomial with bounded index and logarithmic height. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

public import D5.S3.Arith.AbsoluteValues.Heights.BombieriVaalerRelative
public import D5.S3.Arith.DiophantineApproximation.BoxMonomial
public import D5.S3.Arith.DiophantineApproximation.CountingVolume
public import D5.S3.Arith.DiophantineApproximation.PolynomialIndex
public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
public import D5.S3.Arith.DiophantineApproximation.MvHasseDeriv
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Nat.Choose.Bounds

public import D5.S3.Arith.DiophantineApproximation.AuxiliaryPolynomialFixedDegree

@[expose] public section

open Finset Height Height.AdmissibleAbsValues MeasureTheory Module MvPolynomial NumberField Real

noncomputable section

namespace MvPolynomial

set_option maxHeartbeats 2000000 in
/-- **Layer 2.6 — the auxiliary polynomial** (Bombieri–Gubler, Lemma 6.3.4). -/
theorem exists_ne_zero_le_index_logHeight_le
    {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F] [Algebra K F]
    {m N : ℕ} (α : Fin N → Fin m → F) {t : Fin N → ℝ} (ht : ∀ k, 0 < t k)
    (hfeas : (finrank K F : ℝ) * ∑ k, cubeSimplexVolume m (t k) < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ D₀ : ℕ, ∀ d : Fin m → ℕ, (∀ j, D₀ ≤ d j) →
      ∃ P : MvPolynomial (Fin m) K, P ≠ 0 ∧ (∀ j, P.degreeOf j ≤ d j) ∧
        (∀ k, ENNReal.ofReal (t k)
            ≤ index (fun j ↦ (d j : ℝ)) (α k) (P.map (algebraMap K F))) ∧
        Real.log P.mulHeight / (finrank ℚ K : ℝ)
          ≤ (finrank K F : ℝ) / (1 - (finrank K F : ℝ) * ∑ k, cubeSimplexVolume m (t k))
            * ∑ k, ∑ j, cubeSimplexVolume m (t k)
                * (absLogHeight₁ (α k j) + Real.log 2 + δ) * (d j : ℝ) := by
  have nativeSource50 := (open Set in (open scoped Pointwise ENNReal Nat in (fun (m : ℕ) {t : ℝ} (ht : (m : ℝ) ≤ t) => (show MeasureTheory.cubeSimplexVolume m t = 1 from by
    classical
    have hset : MeasureTheory.cubeSimplex m t = univ.pi fun _ ↦ Icc (0 : ℝ) 1 := by
      refine Set.Subset.antisymm ((fun m t ↦ (show MeasureTheory.cubeSimplex m t ⊆ Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1) from
        Set.inter_subset_left)) m t) fun x hx ↦ ?_
      refine (show x ∈ MeasureTheory.cubeSimplex m t ↔
          (∀ j, 0 ≤ (x) j ∧ (x) j ≤ 1) ∧ ∑ j, (x) j ≤ t from by
        simp [MeasureTheory.cubeSimplex, Pi.le_def, forall_and]).2 ⟨fun j ↦ hx j (mem_univ j), ?_⟩
      calc ∑ j, x j ≤ ∑ _j : Fin m, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ ↦ (hx j (mem_univ j)).2
        _ = m := by simp
        _ ≤ t := ht
    rw [MeasureTheory.cubeSimplexVolume, hset, (show MeasureTheory.MeasureSpace.volume (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) = 1 from by
        rw [MeasureTheory.volume_pi_pi]
        simp)]
    simp))))
  have nativeSource61 := (open Finset Height Height.AdmissibleAbsValues MeasureTheory Module MvPolynomial NumberField Real in (fun {r S κ ε δ Δ lm G D L : ℝ}
      (hr : 0 < r) (hS : 0 < S) (hrS : r * S < 1)
      (hκ1 : 1 ≤ κ) (hκ : κ ≤ 1 + ε) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
      (hεa : ε * (r * S) ≤ (1 - r * S) / 2)
      (hlm0 : 0 ≤ lm) (hlmD : lm ≤ ε * D) (hΔD : Δ ≤ ε * D)
      (hD0 : 0 ≤ D) (hGD : G ≤ S * D * L) (hL0 : 0 < L)
      (hfin : ε * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))
        ≤ r * δ * S / (1 - r * S)) => (show Δ + r * κ / (1 - r * κ * S) * (G + S / 2 * lm) ≤ r / (1 - r * S) * (G + δ * S * D) from by
    classical
    have ha0 : (0 : ℝ) < 1 - r * S := by linarith
    have hb2 : (1 - r * S) / 2 ≤ 1 - r * κ * S := by nlinarith
    have hb0 : (0 : ℝ) < 1 - r * κ * S := by linarith
    have hba : 1 - r * κ * S ≤ 1 - r * S := by
      nlinarith [mul_nonneg (mul_nonneg hr.le hS.le) (sub_nonneg.mpr hκ1)]
    have hC1 : r * κ / (1 - r * κ * S) ≤ 4 * r / (1 - r * S) := by
      rw [div_le_div_iff₀ hb0 ha0]
      nlinarith [mul_nonneg (mul_pos hr ha0).le (by linarith : (0 : ℝ) ≤ 2 - κ),
        mul_nonneg hr.le (sub_nonneg.mpr hb2)]
    have hkey : r * κ / (1 - r * κ * S) - r / (1 - r * S)
        = r * (κ - 1) / ((1 - r * S) * (1 - r * κ * S)) := by field_simp; ring
    have hdiff : r * κ / (1 - r * κ * S) - r / (1 - r * S) ≤ 2 * r * ε / (1 - r * S) ^ 2 := by
      rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hr.le (sq_nonneg (1 - r * S)))
          (by linarith : (0 : ℝ) ≤ ε - (κ - 1)),
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le) hε0.le)
          (mul_nonneg ha0.le (sub_nonneg.mpr hb2))]
    have hp1 : (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
        ≤ 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L) := by
      have h1 : (0 : ℝ) ≤ r * κ / (1 - r * κ * S) - r / (1 - r * S) := by rw [hkey]; positivity
      calc (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
          ≤ (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * (S * D * L) :=
            mul_le_mul_of_nonneg_left hGD h1
        _ ≤ 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L) :=
            mul_le_mul_of_nonneg_right hdiff (by positivity)
    have hp2 : r * κ / (1 - r * κ * S) * (S / 2 * lm)
        ≤ 4 * r / (1 - r * S) * (S / 2 * (ε * D)) :=
      mul_le_mul hC1 (by nlinarith) (by positivity) (by positivity)
    have hexp : Δ + r * κ / (1 - r * κ * S) * (G + S / 2 * lm)
        = Δ + (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
          + r * κ / (1 - r * κ * S) * (S / 2 * lm) + r / (1 - r * S) * G := by ring
    have hsum : Δ + (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
        + r * κ / (1 - r * κ * S) * (S / 2 * lm)
        ≤ ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S)) := by
      have e1 : 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L)
          = ε * D * (2 * r * S * L / (1 - r * S) ^ 2) := by field_simp
      have e2 : 4 * r / (1 - r * S) * (S / 2 * (ε * D))
          = ε * D * (2 * r * S / (1 - r * S)) := by field_simp; ring
      calc Δ + (r * κ / (1 - r * κ * S) - r / (1 - r * S)) * G
            + r * κ / (1 - r * κ * S) * (S / 2 * lm)
          ≤ ε * D + 2 * r * ε / (1 - r * S) ^ 2 * (S * D * L)
              + 4 * r / (1 - r * S) * (S / 2 * (ε * D)) := by linarith
        _ = ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S)) := by
            rw [e1, e2]; ring
    have hlast : ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))
        ≤ r / (1 - r * S) * (δ * S * D) := by
      have h := mul_le_mul_of_nonneg_left hfin hD0
      calc ε * D * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))
          = D * (ε * (1 + 2 * r * S * L / (1 - r * S) ^ 2 + 2 * r * S / (1 - r * S))) := by ring
        _ ≤ D * (r * δ * S / (1 - r * S)) := h
        _ = r / (1 - r * S) * (δ * S * D) := by field_simp
    rw [hexp, show r / (1 - r * S) * (G + δ * S * D)
      = r / (1 - r * S) * (δ * S * D) + r / (1 - r * S) * G by ring]
    linarith)))
  have nativeSource91 := (open Function IntermediateField Module in (open scoped Classical in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] (x : K) => (show 0 ≤ NumberField.absLogHeight₁ x from by
    classical
    rw [NumberField.absLogHeight₁]
    apply Real.log_nonneg
    by_cases hx : IsIntegral ℚ x
    · haveI : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
      haveI : NumberField ℚ⟮x⟯ := {}
      rw [NumberField.absMulHeight₁, dif_pos hx]
      exact Real.one_le_rpow (Height.one_le_mulHeight₁ _) (by positivity)
    · rw [NumberField.absMulHeight₁, dif_neg hx]))))
  classical
  have hst : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hFin : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hrpos : 0 < finrank K F := Module.finrank_pos
  have hr1 : (1 : ℝ) ≤ (finrank K F : ℝ) := by exact_mod_cast hrpos
  -- No points: the constant polynomial `1` does the job.
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    exact ⟨0, fun d _ ↦ ⟨1, one_ne_zero, fun j ↦ by simp, fun k ↦ k.elim0,
      by
        have hOne : (1 : MvPolynomial (Fin m) K).mulHeight = 1 := by
          rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero']
          haveI : Subsingleton ((AddMonoidAlgebra.coeff (MvPolynomial.monomial 0 (1 : K) : MvPolynomial (Fin m) K)).support) := by
            refine ⟨fun i j ↦ Subtype.ext ?_⟩
            have hi := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (by
              simpa only [MvPolynomial.finsupp_support_eq_support] using i.prop))
            have hj := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (by
              simpa only [MvPolynomial.finsupp_support_eq_support] using j.prop))
            exact hi.trans hj.symm
          rw [MvPolynomial.mulHeight, Finsupp.mulHeight]
          exact Height.mulHeight_eq_one_of_subsingleton _
        simp [hOne]⟩⟩
  -- No variables: the feasibility hypothesis is contradictory.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exfalso
    subst hm0
    have hV : ∀ k : Fin N, cubeSimplexVolume 0 (t k) = 1 := fun k ↦
      nativeSource50 0 (by simpa using (ht k).le)
    have hS : ∑ k, cubeSimplexVolume 0 (t k) = (N : ℝ) := by simp [hV]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    rw [hS] at hfeas
    nlinarith
  have : NeZero N := ⟨hNpos.ne'⟩
  have : NeZero m := ⟨hmpos.ne'⟩
  -- The data of the estimate.
  have hVpos : ∀ k, 0 < cubeSimplexVolume m (t k) := fun k ↦ cubeSimplexVolume_pos m (ht k)
  have hSpos : 0 < ∑ k, cubeSimplexVolume m (t k) :=
    Finset.sum_pos (fun k _ ↦ hVpos k) Finset.univ_nonempty
  set rr : ℝ := (finrank K F : ℝ) with hrrdef
  set S : ℝ := ∑ k, cubeSimplexVolume m (t k) with hSdef
  have ha0 : 0 < 1 - rr * S := by linarith
  -- a uniform bound for the local heights
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log 2 + ∑ k, ∑ j, absLogHeight₁ (α k j) := ⟨_, rfl⟩
  have hL0 : 0 < L := by
    have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : (0 : ℝ) ≤ ∑ k, ∑ j, absLogHeight₁ (α k j) :=
      Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun j _ ↦ nativeSource91 _
    rw [hLdef]; linarith
  have hLle : ∀ k j, Real.log 2 + absLogHeight₁ (α k j) ≤ L := by
    intro k j
    have h1 : absLogHeight₁ (α k j) ≤ ∑ j', absLogHeight₁ (α k j') :=
      Finset.single_le_sum (fun j' _ ↦ nativeSource91 _) (Finset.mem_univ j)
    have h2 : (∑ j', absLogHeight₁ (α k j')) ≤ ∑ k', ∑ j', absLogHeight₁ (α k' j') :=
      Finset.single_le_sum
        (fun k' _ ↦ Finset.sum_nonneg fun j' _ ↦ nativeSource91 _) (Finset.mem_univ k)
    rw [hLdef]; linarith
  -- the small parameter
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = 1 + 2 * rr * S * L / (1 - rr * S) ^ 2 + 2 * rr * S / (1 - rr * S) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by
    rw [hQdef]
    have h1 : (0 : ℝ) < 2 * rr * S * L / (1 - rr * S) ^ 2 := by positivity
    have h2 : (0 : ℝ) < 2 * rr * S / (1 - rr * S) := by positivity
    linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ,
      ε = min 1 (min ((1 - rr * S) / (2 * rr * S)) ((rr * δ * S / (1 - rr * S)) / Q)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεa : ε * (rr * S) ≤ (1 - rr * S) / 2 := by
    have h : ε ≤ (1 - rr * S) / (2 * rr * S) :=
      le_trans (by rw [hεdef]; exact min_le_right _ _) (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hfin : ε * Q ≤ rr * δ * S / (1 - rr * S) := by
    have h : ε ≤ (rr * δ * S / (1 - rr * S)) / Q :=
      le_trans (by rw [hεdef]; exact min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ hQ0] at h
    exact h
  -- the threshold
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 + ∑ k, (t k)⁻¹ := ⟨_, rfl⟩
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]
    have : (0 : ℝ) ≤ ∑ k, (t k)⁻¹ :=
      Finset.sum_nonneg fun k _ ↦ inv_nonneg.mpr (ht k).le
    linarith
  have hTk : ∀ k, max 1 (t k)⁻¹ ≤ T := by
    intro k
    refine max_le hT1 ?_
    have h1 : (t k)⁻¹ ≤ ∑ k', (t k')⁻¹ :=
      Finset.single_le_sum (f := fun k' ↦ (t k')⁻¹)
        (fun k' _ ↦ inv_nonneg.mpr (ht k').le) (Finset.mem_univ k)
    rw [hTdef]; linarith
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ,
      Δ = (2 * (finrank ℚ K : ℝ))⁻¹ * Real.log |(NumberField.discr K : ℝ)| := ⟨_, rfl⟩
  have hdisc1 : (1 : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
    have h : (1 : ℤ) ≤ |NumberField.discr K| :=
      Int.one_le_abs (NumberField.discr_ne_zero K)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |(NumberField.discr K : ℝ)| := by push_cast [abs_abs]; rfl
  have hΔ0 : 0 ≤ Δ := by
    rw [hΔdef]
    have : (0 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)| := Real.log_nonneg hdisc1
    positivity
  refine ⟨⌈max (max (T * m ^ 2 * 2 ^ m / ε) (9 / ε ^ 2)) (Δ / ε)⌉₊ + 1, fun d hd ↦ ?_⟩
  have hdX : ∀ j, max (max (T * m ^ 2 * 2 ^ m / ε) (9 / ε ^ 2)) (Δ / ε) ≤ (d j : ℝ) := by
    intro j
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (Nat.le_succ _) (hd j)
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (Nat.le_add_left 1 _) (hd j)
  have hdpos : ∀ j, 0 < d j := fun j ↦ hd1 j
  have hd1R : ∀ j, (1 : ℝ) ≤ (d j : ℝ) := fun j ↦ by exact_mod_cast hd1 j
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
  -- The lattice-point correction is at most `κ = 1 + ε`.
  have hκ0 : (0 : ℝ) < 1 + ε := by linarith
  have hκ1 : (1 : ℝ) ≤ 1 + ε := by linarith
  have hrκS : rr * (1 + ε) * S < 1 := by linarith only [hεa, hfeas]
  have hXpos : (0 : ℝ) < T * (m : ℝ) ^ 2 * 2 ^ m := by positivity
  have hinv : ∀ j, ((d j : ℝ))⁻¹ ≤ ε / (T * (m : ℝ) ^ 2 * 2 ^ m) := by
    intro j
    have h1 : T * (m : ℝ) ^ 2 * 2 ^ m / ε ≤ (d j : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hdX j)
    rw [div_le_iff₀ hε0] at h1
    rw [← one_div, div_le_div_iff₀ (by linarith [hd1R j]) hXpos]
    nlinarith [hd1R j]
  have hsuminv : ∑ j, ((d j : ℝ))⁻¹ ≤ ε / (T * (m : ℝ) * 2 ^ m) := by
    calc ∑ j, ((d j : ℝ))⁻¹ ≤ ∑ _j : Fin m, ε / (T * (m : ℝ) ^ 2 * 2 ^ m) :=
          Finset.sum_le_sum fun j _ ↦ hinv j
      _ = (m : ℝ) * (ε / (T * (m : ℝ) ^ 2 * 2 ^ m)) := by simp
      _ = ε / (T * (m : ℝ) * 2 ^ m) := by field_simp
  have hmpow : (1 : ℝ) ≤ (m : ℝ) * 2 ^ m := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hpow : ∀ k, (1 + max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹) ^ m ≤ 1 + ε := by
    intro k
    have hs0 : (0 : ℝ) ≤ ∑ j, ((d j : ℝ))⁻¹ := Finset.sum_nonneg fun j _ ↦ by positivity
    have hmax0 : (0 : ℝ) ≤ max 1 (t k)⁻¹ := le_trans zero_le_one (le_max_left _ _)
    have h0 : 0 ≤ max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹ := mul_nonneg hmax0 hs0
    have hrhok : max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹ ≤ ε / ((m : ℝ) * 2 ^ m) := by
      calc max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹ ≤ T * (ε / (T * (m : ℝ) * 2 ^ m)) :=
            mul_le_mul (hTk k) hsuminv hs0 (by linarith)
        _ = ε / ((m : ℝ) * 2 ^ m) := by field_simp
    let ρ : ℝ := max 1 (t k)⁻¹ * ∑ j, ((d j : ℝ))⁻¹
    change 0 ≤ ρ at h0
    change ρ ≤ ε / ((m : ℝ) * 2 ^ m) at hrhok
    change (1 + ρ) ^ m ≤ 1 + ε
    have hρ1 : ρ ≤ 1 := by
      refine hrhok.trans ?_
      exact (div_le_one (by linarith : (0 : ℝ) < (m : ℝ) * 2 ^ m)).2
        (by linarith)
    have hpowBase : (max |1 + ρ| |(1 : ℝ)|) ^ (m - 1) ≤ 2 ^ m := by
      have hbase : max |1 + ρ| |(1 : ℝ)| ≤ 2 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + ρ), abs_one]
        exact max_le (by linarith) (by norm_num)
      exact (pow_le_pow_left₀ (by positivity) hbase _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le m 1))
    have hdiff := abs_pow_sub_pow_le (1 + ρ) (1 : ℝ) m
    have habs : |(1 + ρ) - (1 : ℝ)| = ρ := by
      rw [show (1 + ρ) - (1 : ℝ) = ρ by ring, abs_of_nonneg h0]
    rw [one_pow, habs] at hdiff
    have hbound : |(1 + ρ) ^ m - 1| ≤ ρ * (m : ℝ) * 2 ^ m :=
      hdiff.trans (mul_le_mul_of_nonneg_left hpowBase
        (mul_nonneg h0 (Nat.cast_nonneg m)))
    have hscaled : ρ * (m : ℝ) * 2 ^ m ≤ ε := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < (m : ℝ) * 2 ^ m)] at hrhok
      nlinarith [hrhok]
    linarith [le_abs_self ((1 + ρ) ^ m - 1)]
  -- Apply the index theorem at this multidegree.
  obtain ⟨P, hP0, hPdeg, hPindex, hPheight⟩ :=
    exists_ne_zero_le_index_logHeight_le_of_pow_le α ht hdpos hκ1 hpow
      (by rw [← hrrdef, ← hSdef]; exact hrκS)
  refine ⟨P, hP0, hPdeg, hPindex, le_trans hPheight ?_⟩
  -- The bookkeeping.
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = ∑ k, cubeSimplexVolume m (t k)
      * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ∑ j, (d j : ℝ) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact Finset.sum_nonneg fun j _ ↦ Nat.cast_nonneg _
  have hGD : G ≤ S * D * L := by
    rw [hGdef, hSdef, hDdef]
    have hk : ∀ k : Fin N, ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
        ≤ (∑ j, (d j : ℝ)) * L := by
      intro k
      calc ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
          ≤ ∑ j, L * (d j : ℝ) :=
            Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hLle k j) (Nat.cast_nonneg _)
        _ = (∑ j, (d j : ℝ)) * L := by rw [← Finset.mul_sum]; ring
    calc ∑ k, cubeSimplexVolume m (t k) * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
        ≤ ∑ k, cubeSimplexVolume m (t k) * ((∑ j, (d j : ℝ)) * L) :=
          Finset.sum_le_sum fun k _ ↦
            mul_le_mul_of_nonneg_left (hk k) ((fun m t ↦ (show 0 ≤ MeasureTheory.cubeSimplexVolume m t from ENNReal.toReal_nonneg)) m (t k))
      _ = (∑ k, cubeSimplexVolume m (t k)) * (∑ j, (d j : ℝ)) * L := by
          rw [← Finset.sum_mul]; ring
  -- the number of monomials is negligible
  have hMprod : ((Fintype.card (∀ j : Fin m, Fin (d j + 1))) : ℝ) = ∏ j, ((d j : ℝ) + 1) := by
    rw [Fintype.card_pi]
    push_cast
    simp
  have hlogd : ∀ j, Real.log ((d j : ℝ) + 1) ≤ ε * (d j : ℝ) := by
    intro j
    have hx := hd1R j
    have h9 : 9 / ε ^ 2 ≤ (d j : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hdX j)
    have hsq : 3 / ε ≤ Real.sqrt (d j : ℝ) := by
      rw [show (3 : ℝ) / ε = Real.sqrt ((3 / ε) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      refine Real.sqrt_le_sqrt ?_
      rw [div_pow]
      norm_num
      exact h9
    have hl1 : Real.log ((d j : ℝ) + 1) ≤ 2 * Real.sqrt ((d j : ℝ) + 1) := by
      have h := Real.log_le_rpow_div
        (x := (d j : ℝ) + 1) (ε := (1 / 2 : ℝ)) (by positivity) (by norm_num)
      calc
        Real.log ((d j : ℝ) + 1)
            ≤ (((d j : ℝ) + 1) ^ (1 / 2 : ℝ)) / (1 / 2 : ℝ) := h
        _ = 2 * Real.sqrt ((d j : ℝ) + 1) := by
          rw [← Real.sqrt_eq_rpow]
          ring
    have hl2 : Real.sqrt ((d j : ℝ) + 1) ≤ Real.sqrt (2 * (d j : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hl3 : Real.sqrt (2 * (d j : ℝ)) ≤ 1.5 * Real.sqrt (d j : ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
      have h2 : Real.sqrt 2 ≤ 1.5 := by
        rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from
          (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg (d j : ℝ)]
    have hsqsq : Real.sqrt (d j : ℝ) * Real.sqrt (d j : ℝ) = (d j : ℝ) :=
      Real.mul_self_sqrt (by linarith)
    have h3 : 3 ≤ ε * Real.sqrt (d j : ℝ) := by
      rw [div_le_iff₀ hε0] at hsq
      linarith
    calc
      Real.log ((d j : ℝ) + 1) ≤ 2 * Real.sqrt ((d j : ℝ) + 1) := hl1
      _ ≤ 2 * (1.5 * Real.sqrt (d j : ℝ)) := by linarith
      _ = 3 * Real.sqrt (d j : ℝ) := by ring
      _ ≤ (ε * Real.sqrt (d j : ℝ)) * Real.sqrt (d j : ℝ) := by
        nlinarith [Real.sqrt_nonneg (d j : ℝ)]
      _ = ε * (d j : ℝ) := by rw [mul_assoc, hsqsq]
  have hlmD : Real.log ((Fintype.card (∀ j : Fin m, Fin (d j + 1))) : ℝ) ≤ ε * D := by
    rw [hMprod, Real.log_prod (f := fun j : Fin m ↦ (d j : ℝ) + 1)
      (fun j _ ↦ by have := hd1R j; positivity), hDdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ hlogd j
  have hlm0 : 0 ≤ Real.log ((Fintype.card (∀ j : Fin m, Fin (d j + 1))) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast Fintype.card_pos
  have hΔD : Δ ≤ ε * D := by
    obtain ⟨j0⟩ : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
    have h1 : Δ / ε ≤ (d j0 : ℝ) := le_trans (le_max_right _ _) (hdX j0)
    have h2 : (d j0 : ℝ) ≤ D := by
      rw [hDdef]
      exact Finset.single_le_sum (f := fun j ↦ (d j : ℝ))
        (fun j _ ↦ Nat.cast_nonneg _) (Finset.mem_univ j0)
    rw [div_le_iff₀ hε0] at h1
    nlinarith
  -- the target, rewritten
  have htarget : ∑ k, ∑ j, cubeSimplexVolume m (t k)
      * (absLogHeight₁ (α k j) + Real.log 2 + δ) * (d j : ℝ) = G + δ * S * D := by
    rw [hGdef, hSdef, hDdef]
    have hk : ∀ k : Fin N, ∑ j, cubeSimplexVolume m (t k)
          * (absLogHeight₁ (α k j) + Real.log 2 + δ) * (d j : ℝ)
        = cubeSimplexVolume m (t k) * ∑ j, (Real.log 2 + absLogHeight₁ (α k j)) * (d j : ℝ)
          + δ * (cubeSimplexVolume m (t k) * ∑ j, (d j : ℝ)) := by
      intro k
      rw [Finset.mul_sum, show δ * (cubeSimplexVolume m (t k) * ∑ j, (d j : ℝ))
          = ∑ j, δ * (cubeSimplexVolume m (t k) * (d j : ℝ)) by
            rw [Finset.mul_sum, Finset.mul_sum], ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [Finset.sum_congr rfl fun k _ ↦ hk k, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  rw [← hrrdef, ← hSdef, ← hGdef, ← hΔdef, htarget]
  rw [hQdef] at hfin
  exact nativeSource61 (by linarith) hSpos hfeas hκ1 le_rfl hε0 hε1 hεa
    hlm0 hlmD hΔD hD0 hGD hL0 hfin

end MvPolynomial

end
