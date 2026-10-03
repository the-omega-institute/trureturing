/- GID: D5/S3/Arith/DiophantineApproximation/RothMovingChain
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RothMovingChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A long moving chain of sufficiently strong approximants is impossible. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import D5.S3.Arith.DiophantineApproximation.RothAuxiliary
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Height.NumberField
public import D5.S3.Arith.AbsoluteValues.Heights.AbsoluteScalarHeight
public import D5.S3.Arith.DiophantineApproximation.RothKeyInequality
import D5.S3.Arith.DiophantineApproximation.PlacesOverFinite
import D5.S3.Arith.DiophantineApproximation.PlacesOverInfinite

@[expose] public section

open Height MvPolynomial Module
namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

noncomputable def rothEps (κ : ℝ) : ℝ := (1 / 2 - 1 / κ) / 16

noncomputable def rothClassSize (κ : ℝ) (s : ℕ) : ℕ := ⌈2 * (s : ℝ) / (1 / 2 - 1 / κ)⌉₊ + 1

noncomputable def rothChainLength (κ : ℝ) (s r : ℕ) : ℕ :=
  ⌈Real.log (2 * (r : ℝ) * s + 1) / (6 * rothEps κ ^ 2)⌉₊

noncomputable def rothRatio (κ : ℝ) (s r : ℕ) : ℝ := 2 / rothEps κ ^ 2 ^ rothChainLength κ s r

noncomputable def rothDelta (κ : ℝ) (s r : ℕ) (rF : ℝ) : ℝ :=
  min (rothEps κ ^ 2 ^ rothChainLength κ s r / (12 * ((rothChainLength κ s r : ℝ) + 1)))
    ((κ * (1 - (s : ℝ) / rothClassSize κ s) * (1 / 2 - 4 * rothEps κ) - 1)
      / (2 * (8 * rF * s + 8)))

theorem roth_no_moving_chain_aux (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ0 : 0 < κ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hε4 : 0 < 1 / 2 - 4 * ε) {N : ℕ}
    (hΘ : 1 < κ * (1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * (1 / 2 - 4 * ε)) {mnum : ℕ}
    (hfeasA : (finrank K F : ℝ) * ((Sinf.card + Sfin.card : ℕ) : ℝ)
      * Real.exp (-(6 * ((mnum : ℝ) + 1) * ε ^ 2)) < 1 / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδσ : 12 * ((mnum : ℝ) + 1) * δ ≤ ε ^ 2 ^ mnum)
    (hδΘ : 2 * (8 * (finrank ℚ F : ℝ) * ((Sinf.card + Sfin.card : ℕ) : ℝ) + 8) * δ
      ≤ κ * (1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N) * (1 / 2 - 4 * ε) - 1) :
    ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
      1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / N ≤ ∑ a, lam a →
      ∀ (α : Fin (mnum + 1) → AbsoluteValue K ℝ → F) (β : Fin (mnum + 1) → K),
        (∀ j, 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α j (sPlaceAbsValue a))
          ≤ δ * absLogHeight₁ (β j)) →
        (∀ j : Fin mnum, 2 / ε ^ 2 ^ mnum * logHeight₁ (β j.castSucc) ≤ logHeight₁ (β j.succ)) →
        ¬ ∀ j a, localApprox Sinf Sfin w (α j) a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
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
  have hLogThreshold {B E c D₁ : ℝ} (_hB : 0 ≤ B) (hc : 0 < c) :
      ∃ D : ℝ, D₁ ≤ D ∧ 0 < D ∧ B * Real.log (D + 2) + E < c * D := by
    have hsmall : (fun t : ℝ => B * Real.log t + (E + 2 * c)) =o[Filter.atTop] id :=
      (Real.isLittleO_log_id_atTop.const_mul_left B).add
        (Asymptotics.isLittleO_const_id_atTop (E + 2 * c))
    have hnorm := hsmall.bound (show 0 < c / 2 by positivity)
    obtain ⟨T, hTnorm, hTlow⟩ :=
      (hnorm.and (Filter.eventually_ge_atTop (max (D₁ + 2) 3))).exists
    have hT₁ : D₁ + 2 ≤ T := (le_max_left _ _).trans hTlow
    have hT₃ : (3 : ℝ) ≤ T := (le_max_right _ _).trans hTlow
    have hTpos : 0 < T := by linarith
    have hb : |B * Real.log T + (E + 2 * c)| ≤ (c / 2) * T := by
      simpa [Real.norm_eq_abs, abs_of_pos hTpos] using hTnorm
    have hu := (le_abs_self (B * Real.log T + (E + 2 * c))).trans hb
    refine ⟨T - 2, by linarith, by linarith, ?_⟩
    rw [show T - 2 + 2 = T by ring]
    nlinarith [mul_pos hc hTpos]
  have hImported16 {Sinf : Finset (InfinitePlace K)}
      {Sfin : Finset (FinitePlace K)} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
      (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
      (a : ↥Sinf ⊕ ↥Sfin) (x : F) : max (w (sPlaceAbsValue a) x) 1 ≤ mulHeight₁ x := by
    classical
    have hInfBound (u : InfinitePlace F) : max (u x) 1 ≤ mulHeight₁ x := by
      rw [NumberField.mulHeight₁_eq]
      calc
        max (u x) 1 ≤ max (u x) 1 ^ u.mult :=
          le_self_pow₀ (le_max_right _ _) u.mult_ne_zero
        _ = ∏ z ∈ ({u} : Finset (InfinitePlace F)), max (z x) 1 ^ z.mult := by simp
        _ ≤ ∏ z : InfinitePlace F, max (z x) 1 ^ z.mult :=
          Finset.prod_le_prod_of_subset_of_one_le
            (Finset.singleton_subset_iff.mpr (Finset.mem_univ u))
            (fun z _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
            (fun z _ _ ↦ one_le_pow₀ (le_max_right _ _))
        _ ≤ (∏ z : InfinitePlace F, max (z x) 1 ^ z.mult)
            * ∏ᶠ z : FinitePlace F, max (z x) 1 :=
          le_mul_of_one_le_right
            (Finset.prod_nonneg fun z _ ↦ pow_nonneg
              (le_trans zero_le_one (le_max_right _ _)) _)
            (one_le_finprod fun _ ↦ le_max_right _ _)
    have hFinBound (u : FinitePlace F) : max (u x) 1 ≤ mulHeight₁ x := by
      rw [NumberField.mulHeight₁_eq]
      have hf : (fun z : FinitePlace F ↦ max (z x) 1).HasFiniteMulSupport := by
        rcases eq_or_ne x 0 with rfl | hx
        · simp [Function.HasFiniteMulSupport]
        · have hfx : (fun z : FinitePlace F ↦ z x).HasFiniteMulSupport :=
            FinitePlace.hasFiniteMulSupport hx
          exact Function.HasFiniteMulSupport.max hfx (by simp [Function.HasFiniteMulSupport])
      calc
        max (u x) 1 = ∏ z ∈ ({u} : Finset (FinitePlace F)), max (z x) 1 := by simp
        _ ≤ ∏ z ∈ insert u hf.toFinset, max (z x) 1 :=
          Finset.prod_le_prod_of_subset_of_one_le
            (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self u hf.toFinset))
            (fun z _ ↦ le_trans zero_le_one (le_max_right _ _))
            (fun z _ _ ↦ le_max_right _ _)
        _ = ∏ᶠ z : FinitePlace F, max (z x) 1 :=
          (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm
        _ ≤ (∏ z : InfinitePlace F, max (z x) 1 ^ z.mult)
            * ∏ᶠ z : FinitePlace F, max (z x) 1 :=
          le_mul_of_one_le_left
            (finprod_nonneg fun _ ↦ le_trans zero_le_one (le_max_right _ _))
            (Finset.one_le_prod fun z _ ↦ one_le_pow₀ (le_max_right _ _))
    rcases a with v | v
    · letI : (w v.1.1).LiesOver v.1.1 := hwInf v.1 v.2
      obtain ⟨u, hu⟩ := (isInfinitePlace_iff (w v.1.1)).mp
        (isInfinitePlace_of_liesOver v.1 (w v.1.1))
      change max ((w v.1.1) x) 1 ≤ mulHeight₁ x
      rw [← hu]
      exact hInfBound u
    · letI : (w v.1.1).LiesOver v.1.1 := hwFin v.1 v.2
      obtain ⟨P, _, hw⟩ :=
        exists_finitePlace_rpow_inv_eq_of_liesOver v.1 (w v.1.1)
      let t : ℝ :=
        (((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ))⁻¹
      have hef : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) :=
        Nat.mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K)) (P.asIdeal.inertiaDeg_pos (𝓞 K))
      have hefR : (1 : ℝ) ≤
          ((P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ) := by
        exact_mod_cast hef
      have ht0 : 0 < t := by
        dsimp [t]
        exact inv_pos.mpr (by exact_mod_cast hef)
      have ht1 : t ≤ 1 := by
        dsimp [t]
        exact inv_le_one_of_one_le₀ hefR
      change ∀ y : F, (w v.1.1) y = FinitePlace.mk P y ^ t at hw
      refine le_trans ?_ (hFinBound (FinitePlace.mk P))
      change max ((w v.1.1) x) 1 ≤ max (FinitePlace.mk P x) 1
      rw [hw]
      rcases le_or_gt (FinitePlace.mk P x) 1 with h1 | h1
      · rw [max_eq_right (Real.rpow_le_one (apply_nonneg _ _) h1 ht0.le)]
        exact le_max_right _ _
      · refine max_le_max_right 1 ?_
        calc FinitePlace.mk P x ^ t ≤ FinitePlace.mk P x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1.le ht1
          _ = FinitePlace.mk P x := Real.rpow_one _
  have hwA : ∀ a : ↥Sinf ⊕ ↥Sfin, (w (sPlaceAbsValue a)).LiesOver (sPlaceAbsValue a) := by
    rintro (v | v)
    · exact hwInf v v.2
    · exact hwFin v v.2
  set SA : ℕ := Sinf.card + Sfin.card with hSAdef
  have hSAcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = SA := by
    rw [hSAdef, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  clear_value SA
  set Θ : ℝ := κ * (1 - (SA : ℝ) / N) * (1 / 2 - 4 * ε) with hΘdef
  clear_value Θ
  have hΘ1 : (0 : ℝ) < Θ - 1 := by linarith
  rw [← hSAcard] at hfeasA
  -- the parameters that do not see the chain
  set σ : ℝ := ε ^ 2 ^ mnum with hσdef
  have hσ0 : (0 : ℝ) < σ := pow_pos hε0 _
  have hσ1 : σ ≤ 1 / 2 := by
    rw [hσdef]
    calc ε ^ 2 ^ mnum ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le (by linarith) Nat.one_le_two_pow
      _ = ε := pow_one _
      _ ≤ 1 / 2 := hε1.le
  clear_value σ
  set tw : ℕ := totalWeight K with htwdef
  have htw1 : (1 : ℝ) ≤ (tw : ℝ) := by
    rw [htwdef]
    exact_mod_cast totalWeight_pos K
  clear_value tw
  set Wsum : ℕ := ∑ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a with hWdef
  clear_value Wsum
  set rF : ℝ := (finrank ℚ F : ℝ) with hrFdef
  have hrF1 : (1 : ℝ) ≤ rF := by
    rw [hrFdef]
    exact_mod_cast Module.finrank_pos
  set Mind : ℝ := 2 / σ with hMdef
  have hM1 : (1 : ℝ) ≤ Mind := by
    rw [hMdef, le_div_iff₀ hσ0]
    linarith
  clear_value Mind
  have hm1 : (0 : ℝ) < (mnum : ℝ) + 1 := by positivity
  have hW0 : (0 : ℝ) ≤ (Wsum : ℝ) := Nat.cast_nonneg _
  have hWle : (Wsum : ℝ) ≤ 2 * (SA : ℝ) := by
    rw [hWdef, hSAdef]
    have hweight : ∀ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a ≤ 2 := by
      intro a
      cases a with
      | inl v =>
        change (v : InfinitePlace K).mult ≤ 2
        unfold InfinitePlace.mult
        split_ifs <;> norm_num
      | inr v => exact one_le_two
    have hsum : ∑ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a
        ≤ 2 * (Sinf.card + Sfin.card) := by
      calc ∑ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a ≤ ∑ _a : ↥Sinf ⊕ ↥Sfin, 2 :=
            Finset.sum_le_sum fun a _ ↦ hweight a
        _ = 2 * (Sinf.card + Sfin.card) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_coe,
              Fintype.card_coe, smul_eq_mul, mul_comm]
    exact_mod_cast hsum
  have hδΘ : 2 * (4 * rF * (Wsum : ℝ) + 8) * δ ≤ Θ - 1 := by
    have h1 : 4 * rF * (Wsum : ℝ) ≤ 8 * rF * (SA : ℝ) := by
      calc 4 * rF * (Wsum : ℝ) ≤ (4 * rF) * (2 * (SA : ℝ)) :=
            mul_le_mul_of_nonneg_left hWle
              (mul_nonneg (by norm_num) (le_trans zero_le_one hrF1))
        _ = 8 * rF * (SA : ℝ) := by ring
    have h2 : 2 * (4 * rF * (Wsum : ℝ) + 8) * δ ≤ 2 * (8 * rF * (SA : ℝ) + 8) * δ :=
      mul_le_mul_of_nonneg_right (by linarith only [h1]) hδ0.le
    have hΘbound : 2 * (8 * rF * (SA : ℝ) + 8) * δ ≤ Θ - 1 := by
      simpa only [hΘdef, hrFdef, hSAdef] using hδΘ
    exact h2.trans hΘbound
  have hδ1 : δ ≤ 1 := by
    have hmul := mul_nonneg (Nat.cast_nonneg mnum : (0 : ℝ) ≤ mnum) hδ0.le
    have hbound : 12 * ((mnum : ℝ) + 1) * δ ≤ σ := by simpa only [hσdef] using hδσ
    linarith only [hmul, hbound, hσ1]
  intro lam hlam0 hlamsum α β hαβ hchain hblocal
  -- the heights of the targets, against the heights of the chain
  set Hα : Fin (mnum + 1) → ℝ :=
    fun j ↦ ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α j (sPlaceAbsValue a)) with hHαdef
  have hHα0 : ∀ j, 0 ≤ Hα j := fun j ↦ Finset.sum_nonneg fun a _ ↦ nativeSource91 _
  have hsingle : ∀ j a, absLogHeight₁ (α j (sPlaceAbsValue a)) ≤ Hα j := fun j a ↦
    Finset.single_le_sum (f := fun b : ↥Sinf ⊕ ↥Sfin ↦ absLogHeight₁ (α j (sPlaceAbsValue b)))
      (fun b _ ↦ nativeSource91 _) (Finset.mem_univ a)
  have hαβ' : ∀ j, 1 + Hα j ≤ δ * absLogHeight₁ (β j) := fun j ↦ hαβ j
  have habs : ∀ j, (tw : ℝ) * absLogHeight₁ (β j) = logHeight₁ (β j) := fun j ↦ by
    simpa only [htwdef, totalWeight_eq_finrank, logHeight₁_eq_log_mulHeight₁] using
      (scalar_absolute_log_height (β j)).symm
  have habsF : ∀ x : F, Real.log (mulHeight₁ x) = rF * absLogHeight₁ x := fun x ↦ by
    simpa only [hrFdef] using scalar_absolute_log_height x
  have hsmall : ∀ j, (tw : ℝ) * (1 + Hα j) ≤ δ * logHeight₁ (β j) := fun j ↦ by
    rw [← habs j]
    have h := mul_le_mul_of_nonneg_left (hαβ' j) (by linarith : (0 : ℝ) ≤ (tw : ℝ))
    linarith
  have hβpos : ∀ j, 0 < logHeight₁ (β j) := fun j ↦ by
    have h1 := hsmall j
    have h2 : (0 : ℝ) < (tw : ℝ) * (1 + Hα j) := by
      have := hHα0 j
      positivity
    by_contra hneg
    push Not at hneg
    have h3 := mul_le_mul_of_nonneg_left hneg hδ0.le
    linarith
  have hβ1 : ∀ j, (1 : ℝ) ≤ logHeight₁ (β j) := fun j ↦ by
    have h1 := hsmall j
    have h2 : (1 : ℝ) ≤ (tw : ℝ) * (1 + Hα j) :=
      one_le_mul_of_one_le_of_one_le htw1 (by linarith [hHα0 j])
    have h3 := mul_le_mul_of_nonneg_right hδ1 (hβpos j).le
    linarith
  have hmono : Monotone fun j ↦ logHeight₁ (β j) :=
    Fin.monotone_iff_le_succ.mpr fun j ↦
      le_trans (le_mul_of_one_le_left (hβpos _).le hM1) (hchain j)
  set Hmax : ℝ := logHeight₁ (β (Fin.last mnum)) with hHmaxdef
  have hHmax0 : (0 : ℝ) < Hmax := hβpos _
  have hβle : ∀ j : Fin (mnum + 1), logHeight₁ (β j) ≤ Hmax := fun j ↦ hmono (Fin.le_last j)
  clear_value Hmax
  set Hβ : ℝ := ∑ j : Fin (mnum + 1), logHeight₁ (β j) with hHβdef
  have hHβ0 : (0 : ℝ) ≤ Hβ := Finset.sum_nonneg fun j _ ↦ (hβpos j).le
  clear_value Hβ
  -- the targets as points, and the two constants that measure them
  set tgt : (↥Sinf ⊕ ↥Sfin) → Fin (mnum + 1) → F := fun a j ↦ α j (sPlaceAbsValue a)
    with htgtdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  set C₁ : Fin (mnum + 1) → ℝ := fun j ↦ Real.log 2 + 1 + Hα j with hC₁def
  have hC₁0 : ∀ j, 0 ≤ C₁ j := fun j ↦ by
    simp only [hC₁def]
    linarith [hHα0 j]
  have hC₁ : ∀ a j, absLogHeight₁ (tgt a j) + Real.log 2 + 1 ≤ C₁ j := fun a j ↦ by
    simp only [htgtdef, hC₁def]
    linarith [hsingle j a]
  have hC₁le : ∀ j, (tw : ℝ) * C₁ j ≤ 2 * δ * logHeight₁ (β j) := fun j ↦ by
    have h := hsmall j
    have h2 : C₁ j ≤ 2 * (1 + Hα j) := by
      simp only [hC₁def]
      linarith [hHα0 j]
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ (tw : ℝ))
    linarith
  set Cα : Fin (mnum + 1) → ℝ := fun j ↦ Real.exp (rF * Hα j) with hCαdef
  have hCα1 : ∀ j, 1 ≤ Cα j := fun j ↦ Real.one_le_exp (by
    have := hHα0 j
    positivity)
  have hCα : ∀ (a : ↥Sinf ⊕ ↥Sfin) j, w (sPlaceAbsValue a) (α j (sPlaceAbsValue a)) ≤ Cα j := by
    intro a j
    have h1 := hImported16 hwInf hwFin a (α j (sPlaceAbsValue a))
    have h2 : mulHeight₁ (α j (sPlaceAbsValue a)) ≤ Cα j := by
      rw [← Real.exp_log (mulHeight₁_pos _), habsF]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hsingle j a) (by linarith))
    exact le_trans (le_max_left _ _) (le_trans h1 h2)
  have hlogCα : ∀ j, Real.log 4 + 2 * Real.log (Cα j) ≤ 2 * rF * δ * logHeight₁ (β j) := by
    intro j
    rw [show Real.log (Cα j) = rF * Hα j from Real.log_exp _]
    have h := hsmall j
    have hlog4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      linarith
    have h2 : Real.log 4 + 2 * (rF * Hα j) ≤ 2 * rF * (1 + Hα j) := by linarith
    have h3 : 2 * rF * (1 + Hα j) ≤ 2 * rF * ((tw : ℝ) * (1 + Hα j)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith [hHα0 j]) htw1)
        (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * rF)
    linarith
  -- Steps I and II
  obtain ⟨D₀, hD₀⟩ := exists_auxiliary_deriv tgt hε0 hε1 hfeasA hC₁0 hC₁
  rw [← hσdef, ← htwdef] at hD₀
  -- a large `D`
  obtain ⟨D, hDbig, hD0, hDlog⟩ := hLogThreshold
    (B := (tw : ℝ) + 2 * (Wsum : ℝ)) (E := Hβ) (c := (Θ - 1) / 2)
    (D₁ := max (((max D₀ 1 : ℕ) : ℝ) * Hmax) (2 * Hmax / σ))
    (by positivity) (by linarith only [hΘ1])
  have hDD₀ : ((max D₀ 1 : ℕ) : ℝ) * Hmax ≤ D := le_trans (le_max_left _ _) hDbig
  have hDσ : 2 * Hmax / σ ≤ D := le_trans (le_max_right _ _) hDbig
  have hmax1 : (1 : ℝ) ≤ ((max D₀ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right D₀ 1
  have hDH : ∀ j, logHeight₁ (β j) ≤ D := fun j ↦
    le_trans (hβle j) (le_trans (le_mul_of_one_le_left hHmax0.le hmax1) hDD₀)
  -- the multidegree
  set d : Fin (mnum + 1) → ℕ := fun j ↦ ⌈D / logHeight₁ (β j)⌉₊ with hddef
  have hdlow : ∀ j, D / logHeight₁ (β j) ≤ (d j : ℝ) := fun j ↦ Nat.le_ceil _
  have hdhigh : ∀ j, (d j : ℝ) < D / logHeight₁ (β j) + 1 := fun j ↦
    Nat.ceil_lt_add_one (div_nonneg hD0.le (hβpos j).le)
  have hdD : ∀ j, D ≤ (d j : ℝ) * logHeight₁ (β j) := fun j ↦ by
    rw [← div_le_iff₀ (hβpos j)]
    exact hdlow j
  have hdone : ∀ j, (1 : ℝ) ≤ D / logHeight₁ (β j) := fun j ↦ by
    rw [le_div_iff₀ (hβpos j), one_mul]
    exact hDH j
  have hd2 : ∀ j, (d j : ℝ) * logHeight₁ (β j) ≤ 2 * D := fun j ↦ by
    have h : (d j : ℝ) ≤ 2 * (D / logHeight₁ (β j)) := by linarith only [hdhigh j, hdone j]
    calc (d j : ℝ) * logHeight₁ (β j) ≤ 2 * (D / logHeight₁ (β j)) * logHeight₁ (β j) :=
          mul_le_mul_of_nonneg_right h (hβpos j).le
      _ = 2 * D := by rw [mul_assoc, div_mul_cancel₀ D (hβpos j).ne']
  have hdD₀ : ∀ j, max D₀ 1 ≤ d j := fun j ↦ by
    have h1 : ((max D₀ 1 : ℕ) : ℝ) ≤ (d j : ℝ) := by
      calc ((max D₀ 1 : ℕ) : ℝ) ≤ D / Hmax := by rw [le_div_iff₀ hHmax0]; exact hDD₀
        _ ≤ D / logHeight₁ (β j) := by
            rw [div_le_div_iff₀ hHmax0 (hβpos j)]
            exact mul_le_mul_of_nonneg_left (hβle j) hD0.le
        _ ≤ (d j : ℝ) := hdlow j
    exact_mod_cast h1
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (le_max_right D₀ 1) (hdD₀ j)
  -- the degrees drop fast enough for Roth's lemma
  have hratio : ∀ j : Fin mnum, (d j.succ : ℝ) ≤ σ * (d j.castSucc : ℝ) := by
    intro j
    have hsucc : Mind * logHeight₁ (β j.castSucc) ≤ logHeight₁ (β j.succ) := hchain j
    have hquo0 : (0 : ℝ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) :=
      mul_nonneg (by positivity) (div_nonneg hD0.le (hβpos _).le)
    have heq : σ / 2 * (D / logHeight₁ (β j.castSucc))
        * (Mind * logHeight₁ (β j.castSucc)) = D := by
      rw [hMdef, show σ / 2 * (D / logHeight₁ (β j.castSucc))
          * (2 / σ * logHeight₁ (β j.castSucc))
          = σ / 2 * (2 / σ) * (D / logHeight₁ (β j.castSucc) * logHeight₁ (β j.castSucc)) from
        by ring, div_mul_cancel₀ D (hβpos _).ne', show σ / 2 * (2 / σ) = 1 from by field_simp,
        one_mul]
    have hstep : D / logHeight₁ (β j.succ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) := by
      rw [div_le_iff₀ (hβpos _)]
      calc D = σ / 2 * (D / logHeight₁ (β j.castSucc))
              * (Mind * logHeight₁ (β j.castSucc)) := heq.symm
        _ ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) * logHeight₁ (β j.succ) :=
            mul_le_mul_of_nonneg_left hsucc hquo0
    have hu2 : 2 / σ ≤ D / logHeight₁ (β j.castSucc) := by
      rw [div_le_div_iff₀ hσ0 (hβpos _)]
      rw [div_le_iff₀ hσ0] at hDσ
      linarith only [hDσ, hβle j.castSucc]
    have hone : (1 : ℝ) ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) := by
      have h := mul_le_mul_of_nonneg_left hu2 (by positivity : (0 : ℝ) ≤ σ / 2)
      rwa [show σ / 2 * (2 / σ) = 1 by field_simp] at h
    calc (d j.succ : ℝ) ≤ D / logHeight₁ (β j.succ) + 1 := (hdhigh _).le
      _ ≤ σ / 2 * (D / logHeight₁ (β j.castSucc)) + 1 := by linarith only [hstep]
      _ ≤ σ * (D / logHeight₁ (β j.castSucc)) := by linarith only [hone]
      _ ≤ σ * (d j.castSucc : ℝ) := mul_le_mul_of_nonneg_left (hdlow _) hσ0.le
  -- the heights of the targets cost `O(δ D)` per coordinate
  have hterm : ∀ i, (tw : ℝ) * (C₁ i * (d i : ℝ)) ≤ 4 * δ * D := fun i ↦ by
    have hdi : (0 : ℝ) ≤ d i := Nat.cast_nonneg _
    calc (tw : ℝ) * (C₁ i * (d i : ℝ)) = ((tw : ℝ) * C₁ i) * (d i : ℝ) := by ring
      _ ≤ (2 * δ * logHeight₁ (β i)) * (d i : ℝ) := mul_le_mul_of_nonneg_right (hC₁le i) hdi
      _ = 2 * δ * ((d i : ℝ) * logHeight₁ (β i)) := by ring
      _ ≤ 2 * δ * (2 * D) := mul_le_mul_of_nonneg_left (hd2 i) (by positivity)
      _ = 4 * δ * D := by ring
  have hsumC₁ : (tw : ℝ) * ∑ i, C₁ i * (d i : ℝ) ≤ ((mnum : ℝ) + 1) * (4 * δ * D) := by
    rw [Finset.mul_sum]
    calc ∑ i, (tw : ℝ) * (C₁ i * (d i : ℝ)) ≤ ∑ _i : Fin (mnum + 1), 4 * δ * D :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ((mnum : ℝ) + 1) * (4 * δ * D) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  -- the height condition of Roth's lemma
  have hRothH : ∀ j, (tw : ℝ) * ∑ i, C₁ i * (d i : ℝ)
      + 4 * ((mnum : ℝ) + 1) * (d 0 : ℝ) * (tw : ℝ)
      ≤ σ * ((d j : ℝ) * logHeight₁ (β j)) := by
    intro j
    have hd0term : (d 0 : ℝ) * (tw : ℝ) ≤ 2 * δ * D := by
      have h1 : (tw : ℝ) ≤ δ * logHeight₁ (β 0) := by
        have := mul_nonneg (by linarith only [htw1] : (0 : ℝ) ≤ (tw : ℝ)) (hHα0 0)
        linarith only [hsmall 0, this]
      calc (d 0 : ℝ) * (tw : ℝ) ≤ (d 0 : ℝ) * (δ * logHeight₁ (β 0)) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = δ * ((d 0 : ℝ) * logHeight₁ (β 0)) := by ring
        _ ≤ δ * (2 * D) := mul_le_mul_of_nonneg_left (hd2 0) hδ0.le
        _ = 2 * δ * D := by ring
    have h4 := mul_le_mul_of_nonneg_left hd0term (by positivity : (0 : ℝ) ≤ 4 * ((mnum : ℝ) + 1))
    have h5 := mul_le_mul_of_nonneg_right hδσ hD0.le
    have h3 : σ * D ≤ σ * ((d j : ℝ) * logHeight₁ (β j)) :=
      mul_le_mul_of_nonneg_left (hdD j) hσ0.le
    linarith only [hsumC₁, h4, h5, h3]
  -- Steps I and II produce the polynomial
  obtain ⟨Q, hQβ, hQdeg, hQindex, hQheight⟩ :=
    hD₀ d (fun j ↦ le_trans (le_max_left D₀ 1) (hdD₀ j)) β hratio hRothH
  -- Steps III to V
  simp only [htgtdef] at hQindex
  have hkey := roth_key_inequality hwA α (fun j ↦ hd1 j) hQdeg hQβ hQindex hlam0 hκ0.le hD0.le
    hblocal hdD hCα1 hCα
  have hWcast : ∑ a : ↥Sinf ⊕ ↥Sfin, ((sPlaceWeight a : ℕ) : ℝ) = (Wsum : ℝ) := by
    rw [hWdef]
    push_cast
    ring
  rw [← htwdef, hWcast] at hkey
  -- the four remaining estimates
  have hsumlog : (∑ j, Real.log ((d j : ℝ) + 1)) ≤ ((mnum : ℝ) + 1) * Real.log (D + 2) := by
    calc (∑ j : Fin (mnum + 1), Real.log ((d j : ℝ) + 1))
        ≤ ∑ _j : Fin (mnum + 1), Real.log (D + 2) := by
          refine Finset.sum_le_sum fun j _ ↦ Real.log_le_log ?_ ?_
          · positivity
          · have h1 : D / logHeight₁ (β j) ≤ D := div_le_self hD0.le (hβ1 j)
            linarith only [hdhigh j, h1]
      _ = ((mnum : ℝ) + 1) * Real.log (D + 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  have hsumCα : (∑ j, (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j)))
      ≤ ((mnum : ℝ) + 1) * (4 * rF * δ * D) := by
    calc (∑ j : Fin (mnum + 1), (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j)))
        ≤ ∑ _j : Fin (mnum + 1), 4 * rF * δ * D := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          calc (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j))
              ≤ (d j : ℝ) * (2 * rF * δ * logHeight₁ (β j)) :=
                mul_le_mul_of_nonneg_left (hlogCα j) (Nat.cast_nonneg _)
            _ = 2 * rF * δ * ((d j : ℝ) * logHeight₁ (β j)) := by ring
            _ ≤ 2 * rF * δ * (2 * D) :=
                mul_le_mul_of_nonneg_left (hd2 j) (by positivity)
            _ = 4 * rF * δ * D := by ring
      _ = ((mnum : ℝ) + 1) * (4 * rF * δ * D) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
  have hQh : Real.log Q.mulHeight ≤ ((mnum : ℝ) + 1) * (8 * δ * D) := by
    have hle : (tw : ℝ) * ∑ i, (C₁ i + Real.log 2) * (d i : ℝ)
        ≤ 2 * ((tw : ℝ) * ∑ i, C₁ i * (d i : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hC : Real.log 2 ≤ C₁ i := by
        simp only [hC₁def]
        linarith only [hHα0 i]
      have hdi : (0 : ℝ) ≤ d i := Nat.cast_nonneg _
      have h3 := mul_le_mul_of_nonneg_left hC
        (mul_nonneg (by linarith only [htw1] : (0 : ℝ) ≤ (tw : ℝ)) hdi)
      linarith only [h3]
    linarith only [hsumC₁, hle, hQheight]
  have hsumdh : (∑ j, (d j : ℝ) * logHeight₁ (β j)) ≤ ((mnum : ℝ) + 1) * D + Hβ := by
    have hterm' : ∀ j : Fin (mnum + 1),
        (d j : ℝ) * logHeight₁ (β j) ≤ D + logHeight₁ (β j) := fun j ↦ by
      have h := mul_le_mul_of_nonneg_right (hdhigh j).le (hβpos j).le
      rwa [add_mul, div_mul_cancel₀ D (hβpos j).ne', one_mul] at h
    calc (∑ j : Fin (mnum + 1), (d j : ℝ) * logHeight₁ (β j))
        ≤ ∑ j : Fin (mnum + 1), (D + logHeight₁ (β j)) := Finset.sum_le_sum fun j _ ↦ hterm' j
      _ = ((mnum : ℝ) + 1) * D + Hβ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_fin, hHβdef]
          push_cast
          ring
  -- Step V: the comparison
  have hlhs : Θ * (((mnum : ℝ) + 1) * D)
      ≤ κ * (∑ a, lam a) * ((1 / 2 - 4 * ε) * ((mnum : ℝ) + 1)) * D := by
    have hfac : (0 : ℝ) ≤ κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) :=
      mul_nonneg hκ0.le (mul_nonneg hε4.le (mul_nonneg hm1.le hD0.le))
    have h := mul_le_mul_of_nonneg_left hlamsum hfac
    calc Θ * (((mnum : ℝ) + 1) * D)
        = κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) * (1 - (SA : ℝ) / N) := by
          rw [hΘdef]; ring
      _ ≤ κ * ((1 / 2 - 4 * ε) * (((mnum : ℝ) + 1) * D)) * (∑ a, lam a) := h
      _ = κ * (∑ a, lam a) * ((1 / 2 - 4 * ε) * ((mnum : ℝ) + 1)) * D := by ring
  have hb1 := mul_le_mul_of_nonneg_left hsumlog
    (by positivity : (0 : ℝ) ≤ (tw : ℝ) + 2 * (Wsum : ℝ))
  have hb2 := mul_le_mul_of_nonneg_left hsumCα hW0
  have hδD := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδΘ hD0.le) hm1.le
  have hDlog' := mul_lt_mul_of_pos_left hDlog hm1
  have hmH : (0 : ℝ) ≤ (mnum : ℝ) * Hβ := mul_nonneg (Nat.cast_nonneg _) hHβ0
  linarith only [hlhs, hkey, hb1, hb2, hQh, hsumdh, hδD, hDlog', hmH]


end NumberField
