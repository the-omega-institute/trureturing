/- GID: D5/S3/Arith/DiophantineApproximation/RothKeyInequality
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RothKeyInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The auxiliary-polynomial estimates imply Roth's key local approximation inequality. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

import all Mathlib.Algebra.MvPolynomial.Basic

public import Mathlib.NumberTheory.Height.NumberField
import all Mathlib.NumberTheory.Height.Basic
public import D5.S3.Arith.DiophantineApproximation.BoxMonomial
public import D5.S3.Arith.DiophantineApproximation.CountingVolume
public import D5.S3.Arith.DiophantineApproximation.PolynomialIndex
public import D5.S3.Arith.DiophantineApproximation.MvPolynomialEvalBound
public import Mathlib.Analysis.Normed.Ring.WithAbs

@[expose] public section

open Height MvPolynomial

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]

/-- **The places of `S`, as one finite index type.** Over a number field the index set of
Mahler's reduction is the disjoint union of the two typed finsets, never a set of absolute
values; this is the absolute value attached to such an index. -/
def sPlaceAbsValue {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (a : ↥Sinf ⊕ ↥Sfin) : AbsoluteValue K ℝ :=
  a.elim (fun v : ↥Sinf ↦ (v : InfinitePlace K).1) fun v : ↥Sfin ↦ (v : FinitePlace K).1

/-- **The weight of a place of `S`** in Mathlib's relative normalisation: `mult` at an infinite
place and `1` at a finite one. -/
noncomputable def sPlaceWeight {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (a : ↥Sinf ⊕ ↥Sfin) : ℕ :=
  a.elim (fun v : ↥Sinf ↦ (v : InfinitePlace K).mult) fun _ : ↥Sfin ↦ 1

/-- **The local approximation factor at a place of `S`**, in Mathlib's relative normalisation:
`min 1 |β - α_v|_v` raised to the weight of `v`. Its product over the places of `S` is the
quantity Roth's theorem bounds. -/
noncomputable def localApprox (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)
    (a : ↥Sinf ⊕ ↥Sfin) (β : K) : ℝ :=
  min 1 (w (sPlaceAbsValue a) (algebraMap K F β - α (sPlaceAbsValue a))) ^ sPlaceWeight a

/-- **Steps III to V of Roth's proof, at a fixed multidegree.** The coordinate `β j` has its own
targets `α j`, and `Cα j` bounds their sizes at the places of `S`; Roth's theorem takes both
constant, and Layer 3.8 lets them move. -/
theorem roth_key_inequality
    {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    (hw : ∀ a : ↥Sinf ⊕ ↥Sfin, (w (sPlaceAbsValue a)).LiesOver (sPlaceAbsValue a))
    {ι : Type*} [Fintype ι] (α : ι → AbsoluteValue K ℝ → F)
    {d : ι → ℕ} (hd : ∀ j, 0 < d j)
    {Q : MvPolynomial ι K} (hQdeg : ∀ j, Q.degreeOf j ≤ d j)
    {β : ι → K} (hQβ : eval β Q ≠ 0)
    {T : ℝ}
    (hindex : ∀ a : ↥Sinf ⊕ ↥Sfin, ENNReal.ofReal T
      ≤ index (fun j ↦ (d j : ℝ)) (fun j ↦ α j (sPlaceAbsValue a)) (Q.map (algebraMap K F)))
    {lam : (↥Sinf ⊕ ↥Sfin) → ℝ} (hlam0 : ∀ a, 0 ≤ lam a)
    {κ D : ℝ} (hκ0 : 0 ≤ κ) (hD0 : 0 ≤ D)
    (hlocal : ∀ j a, localApprox Sinf Sfin w (α j) a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a))
    (hDd : ∀ j, D ≤ (d j : ℝ) * logHeight₁ (β j))
    {Cα : ι → ℝ} (hCα1 : ∀ j, 1 ≤ Cα j)
    (hCα : ∀ (a : ↥Sinf ⊕ ↥Sfin) j, w (sPlaceAbsValue a) (α j (sPlaceAbsValue a)) ≤ Cα j) :
    κ * (∑ a, lam a) * T * D
      ≤ ((totalWeight K : ℝ) + 2 * ∑ a : ↥Sinf ⊕ ↥Sfin, (sPlaceWeight a : ℝ))
            * ∑ j, Real.log ((d j : ℝ) + 1)
        + (∑ a : ↥Sinf ⊕ ↥Sfin, (sPlaceWeight a : ℝ))
            * ∑ j, (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j))
        + Real.log Q.mulHeight + ∑ j, (d j : ℝ) * logHeight₁ (β j) := by
  let nativeSource64 := (open Nat Finset in (fun {σ : Type _} [instSource1 : Fintype σ] {K : Type _} [instSource3 : Field K] (v : AbsoluteValue K ℝ) {d : σ → ℕ} {P : MvPolynomial σ K}
      (hP : ∀ j, P.degreeOf j ≤ d j) => (show (⨆ I : (∀ j, Fin (d j + 1)), v (P.coeff (boxMonomial d I))) = ⨆ ν, v (P.coeff ν) from by
    classical
    refine le_antisymm (Real.iSup_le (fun I ↦ le_ciSup ((by have hFiniteRange := ((AddMonoidAlgebra.coeff P)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) _)
      (Real.iSup_nonneg fun _ ↦ v.nonneg _)) ?_
    refine Real.iSup_le (fun ν ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    rcases eq_or_ne (P.coeff ν) 0 with h | h
    · rw [h, AbsoluteValue.map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · obtain ⟨I, rfl⟩ : ∃ I : ∀ j, Fin (d j + 1), boxMonomial d I = ν := by
        refine ⟨fun j ↦ ⟨ν j, Nat.lt_succ_of_le ?_⟩, ?_⟩
        · exact degreeOf_le_iff.mp (hP j) ν (mem_support_iff.mpr h)
        · ext j; rfl
      exact le_ciSup (Set.Finite.bddAbove (Set.finite_range
        fun I : (∀ j, Fin (d j + 1)) ↦ v (P.coeff (boxMonomial d I)))) I)))
  have hLocalApproxNonneg (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
      (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)
      (a : ↥Sinf ⊕ ↥Sfin) (β : K) : 0 ≤ localApprox Sinf Sfin w α a β :=
    pow_nonneg (le_min zero_le_one ((w _).nonneg _)) _
  have hLocalBound {v : AbsoluteValue K ℝ} {W : AbsoluteValue F ℝ}
      (hW : W.LiesOver v) {d : ι → ℕ} {Q : MvPolynomial ι K} (hQ : ∀ j, Q.degreeOf j ≤ d j)
      (α : ι → F) {β : ι → K} (hβ : eval β Q ≠ 0) :
      ∃ ν : ι →₀ ℕ, (∀ j, ν j ≤ d j) ∧
        eval α (hasseDeriv ν (Q.map (algebraMap K F))) ≠ 0 ∧
        v (eval β Q) ≤ (∏ j, ((d j : ℝ) + 1)) * (⨆ μ, v (Q.coeff μ))
            * (∏ j, max (v (β j)) 1 ^ d j)
          * ((∏ j, ((d j : ℝ) + 1)) * 4 ^ (∑ j, d j) * (∏ j, max (W (α j)) 1 ^ d j) ^ 2
            * ∏ j, min 1 (W (algebraMap K F (β j) - α j)) ^ ν j) := by
    have hWv : ∀ z : K, W (algebraMap K F z) = v z := fun z ↦ by
      letI : W.LiesOver v := hW
      exact congrArg (fun a : AbsoluteValue K ℝ => a z) (AbsoluteValue.LiesOver.comp_eq W v)
    have hQFdeg : ∀ j, (Q.map (algebraMap K F)).degreeOf j ≤ d j := fun j ↦
      degreeOf_le_iff.mpr fun ν hν ↦ degreeOf_le_iff.mp (hQ j) ν
        (support_map_subset (algebraMap K F) Q hν)
    have hkey : ∀ P : MvPolynomial ι K,
        eval₂ (algebraMap K F) (fun j ↦ algebraMap K F (β j)) P = algebraMap K F (eval β P) := by
      intro P
      simpa only [Function.comp_def] using
        (MvPolynomial.eval₂_comp (algebraMap K F) β P).symm
    have hevalb : eval (fun j ↦ algebraMap K F (β j)) (Q.map (algebraMap K F))
        = algebraMap K F (eval β Q) := by
      rw [eval_map]
      exact hkey Q
    have hbne : eval (fun j ↦ algebraMap K F (β j)) (Q.map (algebraMap K F)) ≠ 0 := by
      rw [hevalb]
      exact fun h ↦ hβ ((map_eq_zero_iff _ (algebraMap K F).injective).mp h)
    obtain ⟨ν, hν, hνne, hbound⟩ :=
      exists_apply_eval_le_of_sub W hQFdeg α (fun j ↦ algebraMap K F (β j)) hbne
    refine ⟨ν, hν, hνne, ?_⟩
    have hcoeff : (⨆ μ, W ((Q.map (algebraMap K F)).coeff μ)) = ⨆ μ, v (Q.coeff μ) := by
      refine iSup_congr fun μ ↦ ?_
      rw [coeff_map, hWv]
    have hb : ∀ j, max (W (algebraMap K F (β j))) 1 = max (v (β j)) 1 := fun j ↦ by rw [hWv]
    rw [hevalb, hWv] at hbound
    rw [hcoeff] at hbound
    simp only [hb] at hbound
    refine le_trans hbound (le_of_eq ?_)
    ring
  classical
  set n : ℕ := ∑ j, d j with hndef
  set Wsum : ℕ := ∑ a : ↥Sinf ⊕ ↥Sfin, sPlaceWeight a with hWdef
  set Mbox : ℝ := ∏ j, ((d j : ℝ) + 1) with hMboxdef
  set Pα : ℝ := ∏ j, Cα j ^ (2 * d j) with hPαdef
  have hMbox1 : (1 : ℝ) ≤ Mbox := by
    rw [hMboxdef]
    calc (1 : ℝ) = ∏ _j : ι, (1 : ℝ) := by simp
      _ ≤ ∏ j, ((d j : ℝ) + 1) :=
        Finset.prod_le_prod₀ (fun j _ ↦ zero_le_one)
          (fun j _ ↦ le_add_of_nonneg_left (Nat.cast_nonneg (d j)))
  have hMbox0 : (0 : ℝ) < Mbox := lt_of_lt_of_le zero_lt_one hMbox1
  have hCα0 : ∀ j, (0 : ℝ) < Cα j := fun j ↦ lt_of_lt_of_le zero_lt_one (hCα1 j)
  have hPα0 : (0 : ℝ) < Pα := Finset.prod_pos fun j _ ↦ pow_pos (hCα0 j) _
  have hQ0 : Q ≠ 0 := fun h ↦ hQβ (by rw [h, map_zero])
  -- the coefficient vector on the box
  have hxbox0 : (fun I ↦ Q.coeff (boxMonomial d I)) ≠ (0 : (∀ j, Fin (d j + 1)) → K) := by
    obtain ⟨μ, hμ⟩ := support_nonempty.mpr hQ0
    obtain ⟨I, rfl⟩ : ∃ I : ∀ j, Fin (d j + 1), boxMonomial d I = μ := by
      refine ⟨fun j ↦ ⟨μ j, Nat.lt_succ_of_le ?_⟩, ?_⟩
      · exact degreeOf_le_iff.mp (hQdeg j) μ hμ
      · ext j; rfl
    exact fun h ↦ (mem_support_iff.mp hμ) (congrFun h I)
  have hiSup : ∀ v : AbsoluteValue K ℝ,
      (⨆ I : (∀ j, Fin (d j + 1)), v (Q.coeff (boxMonomial d I))) = ⨆ μ, v (Q.coeff μ) :=
    fun v ↦ nativeSource64 v hQdeg
  have hming : ∀ (a : ↥Sinf ⊕ ↥Sfin) (j : ι),
      0 ≤ min 1 (w (sPlaceAbsValue a) (algebraMap K F (β j) - α j (sPlaceAbsValue a))) :=
    fun a j ↦ le_min zero_le_one ((w _).nonneg _)
  -- the surviving Hasse derivative at each place of `S`
  have hex : ∀ a : ↥Sinf ⊕ ↥Sfin, ∃ μ : ι →₀ ℕ,
      (T ≤ μ.sum fun j k ↦ (k : ℝ) / d j) ∧
      sPlaceAbsValue a (eval β Q)
        ≤ Mbox * (⨆ I : (∀ j, Fin (d j + 1)), sPlaceAbsValue a (Q.coeff (boxMonomial d I)))
          * (∏ j, max (sPlaceAbsValue a (β j)) 1 ^ d j)
          * (Mbox * 4 ^ n
              * (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2
            * ∏ j, min 1 (w (sPlaceAbsValue a)
                (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ μ j) := by
    intro a
    obtain ⟨μ, _, hμne, hμb⟩ :=
      hLocalBound (hw a) hQdeg (fun j ↦ α j (sPlaceAbsValue a)) hQβ
    refine ⟨μ, ?_, ?_⟩
    · have h1 : index (fun j ↦ (d j : ℝ)) (fun j ↦ α j (sPlaceAbsValue a))
          (Q.map (algebraMap K F)) ≤ ENNReal.ofReal (μ.sum fun j k ↦ (k : ℝ) / d j) :=
        (fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {μ : _ →₀ ℕ}
      (h : MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) ≠ 0) ↦
      (show MvPolynomial.index d α P ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j) from
        iInf_le_of_le μ (iInf_le _ h))) _ hμne
      have hnn : (0 : ℝ) ≤ μ.sum fun j k ↦ (k : ℝ) / d j :=
        Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact (ENNReal.ofReal_le_ofReal_iff hnn).mp (le_trans (hindex a) h1)
    · rw [hiSup, hndef, hMboxdef]
      exact hμb
  choose ν hνT hνbound using hex
  -- the global inequality
  have hg0 : ∀ a : ↥Sinf ⊕ ↥Sfin,
      0 ≤ Mbox * 4 ^ n * (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ ν a j := fun a ↦
    mul_nonneg (mul_nonneg (mul_nonneg hMbox0.le (by positivity))
        (pow_nonneg (Finset.prod_nonneg fun j _ ↦
          pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) _))
      (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hming a j) _)
  have hProductBound
      {y : K} (hy : y ≠ 0) {x : (∀ j, Fin (d j + 1)) → K} (hx : x ≠ 0)
      (β : ι → K) (e : ι → ℕ)
      {C : ℝ} (hC : 1 ≤ C)
      {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
      {s : InfinitePlace K → ℝ} {t : FinitePlace K → ℝ}
      (hs0 : ∀ v, 0 ≤ s v)
      (hs1 : ∀ v ∉ Sinf, s v = 1) (ht1 : ∀ v ∉ Sfin, t v = 1)
      (hinf : ∀ v : InfinitePlace K,
        v y ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * s v)
      (hfin : ∀ v : FinitePlace K,
        v y ≤ (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * t v) :
      1 ≤ C ^ totalWeight K * mulHeight x * (∏ i, mulHeight₁ (β i) ^ e i)
        * ((∏ v ∈ Sinf, s v ^ v.mult) * ∏ v ∈ Sfin, t v) := by
    have hsup : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i, v (x i) :=
      fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
    have hmax : ∀ (v : AbsoluteValue K ℝ) (i : ι), (0 : ℝ) ≤ max (v (β i)) 1 :=
      fun v i ↦ le_trans zero_le_one (le_max_right _ _)
    have hprodmax : ∀ v : AbsoluteValue K ℝ, (0 : ℝ) ≤ ∏ i, max (v (β i)) 1 ^ e i :=
      fun v ↦ Finset.prod_nonneg fun i _ ↦ pow_nonneg (hmax v i) _
    -- the infinite places
    have hInf : (∏ v : InfinitePlace K, v y ^ v.mult)
        ≤ C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
          * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
          * ∏ v ∈ Sinf, s v ^ v.mult := by
      calc (∏ v : InfinitePlace K, v y ^ v.mult)
          ≤ ∏ v : InfinitePlace K,
              (C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * s v) ^ v.mult :=
            Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (v.1.nonneg _) _)
              fun v _ ↦ pow_le_pow_left₀ (v.1.nonneg _) (hinf v) _
        _ = (∏ _v : InfinitePlace K, C ^ _v.mult)
              * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
              * (∏ v : InfinitePlace K, (∏ i, max (v (β i)) 1 ^ e i) ^ v.mult)
              * ∏ v : InfinitePlace K, s v ^ v.mult := by
            simp only [mul_pow]
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        _ = C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
              * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
              * ∏ v ∈ Sinf, s v ^ v.mult := by
            congr 1
            · congr 1
              · congr 1
                · rw [Finset.prod_pow_eq_pow_sum, ← totalWeight_eq_sum_mult]
              · calc ∏ v : InfinitePlace K, (∏ i, max (v (β i)) 1 ^ e i) ^ v.mult
                    = ∏ v : InfinitePlace K, ∏ i, (max (v (β i)) 1 ^ v.mult) ^ e i := by
                      refine Finset.prod_congr rfl fun v _ ↦ ?_
                      rw [← Finset.prod_pow]
                      exact Finset.prod_congr rfl fun i _ ↦ by
                        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
                  _ = ∏ i, ∏ v : InfinitePlace K, (max (v (β i)) 1 ^ v.mult) ^ e i :=
                      Finset.prod_comm
                  _ = ∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i :=
                      Finset.prod_congr rfl fun i _ ↦ Finset.prod_pow _ _ _
            · exact (Finset.prod_subset (Finset.subset_univ Sinf)
                fun v _ hv ↦ by rw [hs1 v hv, one_pow]).symm
    -- the finite places
    have hfsup : Function.HasFiniteMulSupport fun v : FinitePlace K ↦ ⨆ i, v (x i) :=
      Height.hasFiniteMulSupport_iSup_nonarchAbsVal hx
    have hfmax : ∀ i, Function.HasFiniteMulSupport fun v : FinitePlace K ↦ max (v (β i)) 1 ^ e i := by
      intro i
      have hbase : Function.HasFiniteMulSupport
          (fun v : FinitePlace K ↦ max (v (β i)) 1) :=
        Height.hasFiniteMulSupport_max_nonarchAbsVal (β i)
      exact Set.Finite.subset hbase fun v hv ↦ by
        simp only [Function.mem_mulSupport] at hv ⊢
        exact fun h ↦ hv (by rw [h, one_pow])
    have hfprod : Function.HasFiniteMulSupport
        fun v : FinitePlace K ↦ ∏ i, max (v (β i)) 1 ^ e i :=
      Set.Finite.subset ((Finset.univ : Finset ι).finite_toSet.biUnion fun i _ ↦ hfmax i)
        (Finset.mulSupport_prod Finset.univ _)
    have hmulsupp : ∀ {f g : FinitePlace K → ℝ}, Function.HasFiniteMulSupport f →
        Function.HasFiniteMulSupport g → Function.HasFiniteMulSupport fun v ↦ f v * g v :=
      fun {f g} hf hg ↦ Set.Finite.subset (Set.Finite.union hf hg) (Function.mulSupport_mul f g)
    have hft : Function.HasFiniteMulSupport t :=
      Set.Finite.subset Sfin.finite_toSet fun v hv ↦ by
        by_contra hmem
        exact hv (ht1 v hmem)
    have hFin : (∏ᶠ v : FinitePlace K, v y)
        ≤ (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
          * (∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i)
          * ∏ v ∈ Sfin, t v := by
      calc (∏ᶠ v : FinitePlace K, v y)
          ≤ ∏ᶠ v : FinitePlace K, (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * t v :=
            finprod_le_finprod₀ (FinitePlace.hasFiniteMulSupport hy) (fun v ↦ v.1.nonneg _)
              (hmulsupp (hmulsupp hfsup hfprod) hft) hfin
        _ = (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
              * (∏ᶠ v : FinitePlace K, ∏ i, max (v (β i)) 1 ^ e i)
              * ∏ᶠ v : FinitePlace K, t v := by
            rw [finprod_mul_distrib (hmulsupp hfsup hfprod) hft,
              finprod_mul_distrib hfsup hfprod]
        _ = (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
              * (∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i)
              * ∏ v ∈ Sfin, t v := by
            congr 1
            · congr 1
              rw [finprod_prod_comm _ _ fun i _ ↦ hfmax i]
              exact Finset.prod_congr rfl fun i _ ↦ by
                have hmaxsupport : Function.HasFiniteMulSupport
                    (fun v : FinitePlace K ↦ max (v (β i)) 1) :=
                  Height.hasFiniteMulSupport_max_nonarchAbsVal (β i)
                exact (finprod_pow hmaxsupport (e i)).symm
            · exact finprod_eq_prod_of_mulSupport_subset t fun v hv ↦ by
                by_contra hmem
                exact hv (ht1 v hmem)
    -- putting the two halves together
    have hInf0 : (0 : ℝ) ≤ C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
        * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
        * ∏ v ∈ Sinf, s v ^ v.mult := by
      have h1 : (0 : ℝ) ≤ C ^ totalWeight K := pow_nonneg (le_trans zero_le_one hC) _
      have h2 : (0 : ℝ) ≤ ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult :=
        Finset.prod_nonneg fun v _ ↦ pow_nonneg (hsup v.1) _
      have h3 : (0 : ℝ) ≤ ∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i :=
        Finset.prod_nonneg fun i _ ↦ pow_nonneg
          (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hmax v.1 i) _) _
      have h4 : (0 : ℝ) ≤ ∏ v ∈ Sinf, s v ^ v.mult :=
        Finset.prod_nonneg fun v _ ↦ pow_nonneg (hs0 v) _
      positivity
    calc (1 : ℝ) = (∏ v : InfinitePlace K, v y ^ v.mult) * ∏ᶠ v : FinitePlace K, v y :=
          (prod_abs_eq_one hy).symm
      _ ≤ (C ^ totalWeight K * (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
            * (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
            * ∏ v ∈ Sinf, s v ^ v.mult)
          * ((∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
            * (∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i)
            * ∏ v ∈ Sfin, t v) :=
          mul_le_mul hInf hFin (finprod_nonneg fun v ↦ v.1.nonneg _) hInf0
      _ = C ^ totalWeight K * mulHeight x * (∏ i, mulHeight₁ (β i) ^ e i)
            * ((∏ v ∈ Sinf, s v ^ v.mult) * ∏ v ∈ Sfin, t v) := by
          have hxsplit : (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
              * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = mulHeight x := (mulHeight_eq hx).symm
          have hβsplit : (∏ i, (∏ v : InfinitePlace K, max (v (β i)) 1 ^ v.mult) ^ e i)
              * ∏ i, (∏ᶠ v : FinitePlace K, max (v (β i)) 1) ^ e i
                = ∏ i, mulHeight₁ (β i) ^ e i := by
            rw [← Finset.prod_mul_distrib]
            exact Finset.prod_congr rfl fun i _ ↦ by rw [mulHeight₁_eq, mul_pow]
          rw [← hxsplit, ← hβsplit]
          ring
  
  have hGlobalBound
      {y : K} (hy : y ≠ 0) {x : (∀ j, Fin (d j + 1)) → K} (hx : x ≠ 0)
      (β : ι → K) (e : ι → ℕ) {C : ℝ} (hC : 1 ≤ C)
      {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
      {g : (↥Sinf ⊕ ↥Sfin) → ℝ} (hg0 : ∀ a, 0 ≤ g a)
      (hinf : ∀ v : InfinitePlace K, v y ≤ C * (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i)
      (hfin : ∀ v : FinitePlace K, v y ≤ (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i)
      (hS : ∀ a : ↥Sinf ⊕ ↥Sfin, sPlaceAbsValue a y ≤ C * (⨆ i, sPlaceAbsValue a (x i))
        * (∏ i, max (sPlaceAbsValue a (β i)) 1 ^ e i) * g a) :
      1 ≤ C ^ totalWeight K * mulHeight x * (∏ i, mulHeight₁ (β i) ^ e i)
        * ∏ a, (C * g a) ^ sPlaceWeight a := by
    classical
    have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
    set s : InfinitePlace K → ℝ :=
      fun v ↦ if h : v ∈ Sinf then C * g (Sum.inl ⟨v, h⟩) else 1 with hsdef
    set t : FinitePlace K → ℝ :=
      fun v ↦ if h : v ∈ Sfin then C * g (Sum.inr ⟨v, h⟩) else 1 with htdef
    have hs0 : ∀ v, 0 ≤ s v := fun v ↦ by
      simp only [hsdef]
      by_cases h : v ∈ Sinf <;> simp [h, mul_nonneg hC0 (hg0 _)]
    have hs1 : ∀ v ∉ Sinf, s v = 1 := fun v hv ↦ by simp [hsdef, hv]
    have ht1 : ∀ v ∉ Sfin, t v = 1 := fun v hv ↦ by simp [htdef, hv]
    have key := hProductBound (x := x) hy hx β e hC hs0 hs1 ht1
      (fun v ↦ by
        by_cases h : v ∈ Sinf
        · have hsv : s v = C * g (Sum.inl ⟨v, h⟩) := by simp [hsdef, h]
          have hb := hS (Sum.inl ⟨v, h⟩)
          simp only [NumberField.sPlaceAbsValue] at hb
          have hnn : (0 : ℝ) ≤ (⨆ i, v (x i)) * ∏ i, max (v (β i)) 1 ^ e i :=
            mul_nonneg (Real.iSup_nonneg fun _ ↦ v.1.nonneg _)
              (Finset.prod_nonneg fun i _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
          rw [hsv]
          calc v y ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * g (Sum.inl ⟨v, h⟩) := hb
            _ ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * (C * g (Sum.inl ⟨v, h⟩)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by rw [mul_assoc]; exact mul_nonneg hC0 hnn)
                nlinarith [hg0 (Sum.inl ⟨v, h⟩)]
        · rw [hs1 v h, mul_one]
          exact hinf v)
      (fun v ↦ by
        by_cases h : v ∈ Sfin
        · have htv : t v = C * g (Sum.inr ⟨v, h⟩) := by simp [htdef, h]
          rw [htv]
          have hb := hS (Sum.inr ⟨v, h⟩)
          simp only [NumberField.sPlaceAbsValue] at hb
          calc v y ≤ C * (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * g (Sum.inr ⟨v, h⟩) := hb
            _ = (⨆ i, v (x i)) * (∏ i, max (v (β i)) 1 ^ e i) * (C * g (Sum.inr ⟨v, h⟩)) := by ring
        · rw [ht1 v h, mul_one]
          exact hfin v)
    refine le_trans key (le_of_eq ?_)
    congr 1
    rw [Fintype.prod_sum_type]
    congr 1
    · rw [← Finset.prod_coe_sort Sinf fun v ↦ s v ^ v.mult]
      exact Finset.prod_congr rfl fun v _ ↦ by simp [hsdef, v.2, sPlaceWeight]
    · rw [← Finset.prod_coe_sort Sfin fun v ↦ t v]
      exact Finset.prod_congr rfl fun v _ ↦ by simp [htdef, v.2, sPlaceWeight]
  
  have hglob := hGlobalBound (x := fun I ↦ Q.coeff (boxMonomial d I)) hQβ hxbox0 β d hMbox1 hg0
    (fun v : InfinitePlace K ↦ by
      have h := apply_eval_le v.1 hQdeg β
      rw [← hiSup v.1] at h
      simpa only [InfinitePlace.coe_apply] using h)
    (fun v : FinitePlace K ↦ by
      have h := apply_eval_le_of_isNonarchimedean (v := v.1) (FinitePlace.add_le v) hQdeg β
      rw [← hiSup v.1] at h
      simpa only [FinitePlace.coe_apply] using h)
    hνbound
  have hsupp (x : (ι →₀ ℕ) →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : (ι →₀ ℕ), v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hcoe (x : (ι →₀ ℕ) →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
    rcases eq_or_ne x 0 with rfl | hx
    · have : IsEmpty ((0 : (ι →₀ ℕ) →₀ K).support : Type _) := by
        simp only [Finsupp.support_zero]; infer_instance
      rw [Finsupp.coe_zero, Height.mulHeight_zero, Finsupp.mulHeight]
      exact (Height.mulHeight_eq_one_of_subsingleton _).symm
    have hx' : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
    have hxs : (fun i : x.support ↦ x i.val) ≠ 0 := by
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
      exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
    rw [Height.mulHeight_eq hx', Finsupp.mulHeight, Height.mulHeight_eq hxs]
    congr 1
    · congr 2
      ext1 v
      exact hsupp x v
    · exact finprod_congr fun v ↦ hsupp x v.val
  have hCoeffHeight : Q.mulHeight = Height.mulHeight
      (fun I : (∀ j, Fin (d j + 1)) ↦ Q.coeff (boxMonomial d I)) := by
    have hcoeff0 : (fun a : ι →₀ ℕ ↦ Q.coeff a) ≠ 0 := by
      intro hzero
      apply hQ0
      ext a
      simpa only [MvPolynomial.coeff_zero, Pi.zero_apply] using! congrFun hzero a
    rw [MvPolynomial.mulHeight, ← hcoe (AddMonoidAlgebra.coeff Q)]
    change Height.mulHeight (fun a : ι →₀ ℕ ↦ Q.coeff a) =
      Height.mulHeight (fun I : (∀ j, Fin (d j + 1)) ↦ Q.coeff (boxMonomial d I))
    rw [Height.mulHeight_eq hcoeff0, Height.mulHeight_eq hxbox0]
    congr 1
    · congr 2
      ext v
      exact (hiSup v).symm
    · exact finprod_congr fun v ↦ (hiSup v.val).symm
  rw [← hCoeffHeight] at hglob
  -- collecting the constants place by place
  have hstep : ∀ a : ↥Sinf ⊕ ↥Sfin,
      (Mbox * (Mbox * 4 ^ n
          * (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ ν a j)) ^ sPlaceWeight a
      ≤ (Mbox ^ 2 * 4 ^ n * Pα) ^ sPlaceWeight a
        * ∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j := by
    intro a
    have hmax : (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2 ≤ Pα := by
      rw [← Finset.prod_pow, hPαdef]
      refine Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (pow_nonneg
        (le_trans zero_le_one (le_max_right _ _)) _) _) fun j _ ↦ ?_
      rw [← pow_mul, Nat.mul_comm]
      exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _))
        (max_le (hCα a j) (hCα1 j)) _
    have heq : Mbox * (Mbox * 4 ^ n
          * (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ ν a j)
        = (Mbox ^ 2 * 4 ^ n
            * (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2)
          * ∏ j, min 1 (w (sPlaceAbsValue a)
              (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ ν a j := by ring
    have hlast : (∏ j, min 1 (w (sPlaceAbsValue a)
          (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ ν a j) ^ sPlaceWeight a
        = ∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun j _ ↦ by
        rw [localApprox, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [heq, mul_pow, hlast]
    refine mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hLocalApproxNonneg _ _ _ _ _ _) _)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact mul_le_mul_of_nonneg_left hmax (by positivity)
  -- the approximation class makes the surviving product exponentially small
  have hTD : ∀ a : ↥Sinf ⊕ ↥Sfin, T * D ≤ ∑ j, (ν a j : ℝ) * logHeight₁ (β j) := by
    intro a
    have hsum : ((ν a).sum fun j k ↦ (k : ℝ) / d j) = ∑ j, (ν a j : ℝ) / d j :=
      Finsupp.sum_fintype _ _ fun j ↦ by simp
    have h1 : ∀ j, ((ν a j : ℝ) / d j) * D ≤ (ν a j : ℝ) * logHeight₁ (β j) := by
      intro j
      have hd0 : (0 : ℝ) < d j := by exact_mod_cast hd j
      have hq : (0 : ℝ) ≤ (ν a j : ℝ) / d j := div_nonneg (Nat.cast_nonneg _) hd0.le
      calc ((ν a j : ℝ) / d j) * D ≤ ((ν a j : ℝ) / d j) * ((d j : ℝ) * logHeight₁ (β j)) :=
            mul_le_mul_of_nonneg_left (hDd j) hq
        _ = (ν a j : ℝ) * logHeight₁ (β j) := by field_simp
    calc T * D ≤ (∑ j, (ν a j : ℝ) / d j) * D := by
          refine mul_le_mul_of_nonneg_right ?_ hD0
          rw [← hsum]
          exact hνT a
      _ = ∑ j, ((ν a j : ℝ) / d j) * D := Finset.sum_mul _ _ _
      _ ≤ ∑ j, (ν a j : ℝ) * logHeight₁ (β j) := Finset.sum_le_sum fun j _ ↦ h1 j
  have hsmall : ∀ a : ↥Sinf ⊕ ↥Sfin, (∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j)
      ≤ Real.exp (-(κ * lam a * (T * D))) := by
    intro a
    have hc : (0 : ℝ) ≤ κ * lam a := mul_nonneg hκ0 (hlam0 a)
    have hterm : ∀ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j
        ≤ Real.exp (-(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) := by
      intro j
      have hH : (0 : ℝ) < mulHeight₁ (β j) := mulHeight₁_pos _
      calc localApprox Sinf Sfin w (α j) a (β j) ^ ν a j
          ≤ (mulHeight₁ (β j) ^ (-κ * lam a)) ^ ν a j :=
            pow_le_pow_left₀ (hLocalApproxNonneg _ _ _ _ _ _) (hlocal j a) _
        _ = Real.exp (-(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) := by
            rw [← Real.rpow_natCast (mulHeight₁ (β j) ^ (-κ * lam a)) (ν a j),
              ← Real.rpow_mul hH.le, Real.rpow_def_of_pos hH, logHeight₁_eq_log_mulHeight₁]
            ring_nf
    calc (∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j)
        ≤ ∏ j, Real.exp (-(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) :=
          Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hLocalApproxNonneg _ _ _ _ _ _) _)
            fun j _ ↦ hterm j
      _ = Real.exp (∑ j, -(κ * lam a) * ((ν a j : ℝ) * logHeight₁ (β j))) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (-(κ * lam a * (T * D))) := by
          refine Real.exp_le_exp.mpr ?_
          rw [← Finset.mul_sum, neg_mul]
          exact neg_le_neg (mul_le_mul_of_nonneg_left (hTD a) hc)
  have hsmallprod : (∏ a : ↥Sinf ⊕ ↥Sfin, ∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j)
      ≤ Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by
    calc (∏ a : ↥Sinf ⊕ ↥Sfin, ∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j)
        ≤ ∏ a : ↥Sinf ⊕ ↥Sfin, Real.exp (-(κ * lam a * (T * D))) :=
          Finset.prod_le_prod₀ (fun a _ ↦ Finset.prod_nonneg fun j _ ↦
            pow_nonneg (hLocalApproxNonneg _ _ _ _ _ _) _) fun a _ ↦ hsmall a
      _ = Real.exp (∑ a : ↥Sinf ⊕ ↥Sfin, -(κ * lam a * (T * D))) := (Real.exp_sum _ _).symm
      _ = Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by
          congr 1
          have hrw : ∀ a : ↥Sinf ⊕ ↥Sfin, -(κ * lam a * (T * D)) = lam a * (-(κ * (T * D))) :=
            fun a ↦ by ring
          simp only [hrw, ← Finset.sum_mul]
          ring
  -- the constants, collected
  have hbase0 : (0 : ℝ) < Mbox ^ 2 * 4 ^ n * Pα :=
    mul_pos (mul_pos (pow_pos hMbox0 2) (by positivity)) hPα0
  have hprodS : (∏ a : ↥Sinf ⊕ ↥Sfin,
      (Mbox * (Mbox * 4 ^ n
          * (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2
        * ∏ j, min 1 (w (sPlaceAbsValue a)
            (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ ν a j)) ^ sPlaceWeight a)
      ≤ (Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum
        * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by
    calc (∏ a : ↥Sinf ⊕ ↥Sfin,
        (Mbox * (Mbox * 4 ^ n
            * (∏ j, max (w (sPlaceAbsValue a) (α j (sPlaceAbsValue a))) 1 ^ d j) ^ 2
          * ∏ j, min 1 (w (sPlaceAbsValue a)
              (algebraMap K F (β j) - α j (sPlaceAbsValue a))) ^ ν a j)) ^ sPlaceWeight a)
        ≤ ∏ a : ↥Sinf ⊕ ↥Sfin, ((Mbox ^ 2 * 4 ^ n * Pα) ^ sPlaceWeight a
            * ∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j) :=
          Finset.prod_le_prod₀ (fun a _ ↦ pow_nonneg (mul_nonneg hMbox0.le (hg0 a)) _)
            fun a _ ↦ hstep a
      _ = (Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum
            * ∏ a : ↥Sinf ⊕ ↥Sfin, ∏ j, localApprox Sinf Sfin w (α j) a (β j) ^ ν a j := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hWdef]
      _ ≤ (Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum
            * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) :=
          mul_le_mul_of_nonneg_left hsmallprod (pow_nonneg hbase0.le _)
  -- the multiplicative form of the final inequality
  have hQh0 : (0 : ℝ) < Q.mulHeight := (fun p : MvPolynomial _ K ↦ (show 0 < p.mulHeight from Height.mulHeight_pos (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val))) Q
  have hprodH0 : (0 : ℝ) < ∏ j, mulHeight₁ (β j) ^ d j :=
    Finset.prod_pos fun j _ ↦ pow_pos (mulHeight₁_pos _) _
  have hA0 : (0 : ℝ) < Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j) :=
    mul_pos (mul_pos (pow_pos hMbox0 _) hQh0) hprodH0
  have hB0 : (0 : ℝ) < (Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum := pow_pos hbase0 _
  have hfinal : 1 ≤ (Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j))
      * ((Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum
        * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D))) :=
    le_trans hglob (mul_le_mul_of_nonneg_left hprodS hA0.le)
  have hexp : Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)
      ≤ Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j)
        * (Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum := by
    calc Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)
        = 1 * Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D) := (one_mul _).symm
      _ ≤ ((Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j))
            * ((Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum
              * Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D))))
            * Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D) :=
          mul_le_mul_of_nonneg_right hfinal (Real.exp_pos _).le
      _ = (Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j)
            * (Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum)
            * (Real.exp (-(κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D))
              * Real.exp (κ * (∑ a : ↥Sinf ⊕ ↥Sfin, lam a) * T * D)) := by ring
      _ = Mbox ^ totalWeight K * Q.mulHeight * (∏ j, mulHeight₁ (β j) ^ d j)
            * (Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  -- take logarithms
  have hM0 : Mbox ≠ 0 := hMbox0.ne'
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have e1 : Real.log (Mbox ^ totalWeight K) = (totalWeight K : ℝ) * Real.log Mbox :=
    Real.log_pow _ _
  have e2 : Real.log (∏ j, mulHeight₁ (β j) ^ d j) = ∑ j, (d j : ℝ) * logHeight₁ (β j) := by
    rw [Real.log_prod fun j _ ↦ pow_ne_zero (d j) (mulHeight₁_pos (β j)).ne']
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [Real.log_pow, logHeight₁_eq_log_mulHeight₁]
  have ePα : Real.log Pα = ∑ j, 2 * (d j : ℝ) * Real.log (Cα j) := by
    rw [hPαdef, Real.log_prod fun j _ ↦ pow_ne_zero _ (hCα0 j).ne']
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [Real.log_pow]
      push_cast
      ring
  have e3 : Real.log ((Mbox ^ 2 * 4 ^ n * Pα) ^ Wsum)
      = (Wsum : ℝ) * (2 * Real.log Mbox + (n : ℝ) * Real.log 4 + Real.log Pα) := by
    rw [Real.log_pow, Real.log_mul (mul_pos (pow_pos hMbox0 2) (by positivity)).ne' hPα0.ne',
      Real.log_mul (pow_ne_zero _ hM0) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [Real.log_mul hA0.ne' hB0.ne',
    Real.log_mul (mul_pos (pow_pos hMbox0 _) hQh0).ne' hprodH0.ne',
    Real.log_mul (pow_ne_zero _ hM0) hQh0.ne', e1, e2, e3, ePα] at hlog
  have hlogMbox : Real.log Mbox = ∑ j, Real.log ((d j : ℝ) + 1) := by
    rw [hMboxdef, Real.log_prod fun j _ ↦ by positivity]
  have hncast : (n : ℝ) = ∑ j, (d j : ℝ) := by rw [hndef]; push_cast; ring
  have hWcast : (Wsum : ℝ) = ∑ a : ↥Sinf ⊕ ↥Sfin, (sPlaceWeight a : ℝ) := by
    rw [hWdef]; push_cast; ring
  have hsplit : ∑ j, (d j : ℝ) * (Real.log 4 + 2 * Real.log (Cα j))
      = (∑ j, (d j : ℝ)) * Real.log 4 + ∑ j, 2 * (d j : ℝ) * Real.log (Cα j) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlogMbox, hncast, hWcast] at hlog
  rw [hsplit]
  linarith [hlog]

end NumberField

end
