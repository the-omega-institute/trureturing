/- GID: D5/S3/Arith/DiophantineApproximation/RothTheorem
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RothTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected-place approximants beyond exponent two form a finite set. -/
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
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Height.NumberField
public import D5.S3.Arith.AbsoluteValues.Heights.AbsoluteScalarHeight
public import D5.S3.Arith.DiophantineApproximation.RothKeyInequality
public import D5.S3.Arith.DiophantineApproximation.RothMovingChain

@[expose] public section

open Height MvPolynomial Module

namespace NumberField
variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

noncomputable def rothThreshold (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (α : AbsoluteValue K ℝ → F) (κ : ℝ) : ℝ :=
  (totalWeight K : ℝ) * (1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)))
    / rothDelta κ (Sinf.card + Sfin.card) (finrank K F) (finrank ℚ F)

theorem finite_setOf_prod_min_one_le (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  let hCellIndex (N : ℕ) (y : (↥Sinf ⊕ ↥Sfin) → ℝ) (a : (↥Sinf ⊕ ↥Sfin)) : ℕ :=
    ⌊(N : ℝ) * y a⌋₊
  let hLogProfile (f : (↥Sinf ⊕ ↥Sfin) → ℝ) (a : (↥Sinf ⊕ ↥Sfin)) : ℝ :=
    Real.log (f a) / Real.log (∏ b, f b)
  have hClass1 (N : ℕ) :
      {c : (↥Sinf ⊕ ↥Sfin) → ℕ | ∑ a, c a ≤ N}.Finite := by
    classical
    refine Set.Finite.subset (Finset.finite_toSet
      (Fintype.piFinset fun _ : (↥Sinf ⊕ ↥Sfin) ↦ Finset.range (N + 1))) fun c hc ↦ ?_
    have hc' : ∑ a, c a ≤ N := hc
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    exact fun a ↦ Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := c) (fun i _ ↦ Nat.zero_le (c i)) (Finset.mem_univ a)).trans hc')
  have hClass2 {X : Set K} (hX : X.Infinite) {f : K → ((↥Sinf ⊕ ↥Sfin) → ℕ)}
      {T : Set ((↥Sinf ⊕ ↥Sfin) → ℕ)} (hT : T.Finite) (hf : ∀ x ∈ X, f x ∈ T) :
      ∃ c ∈ T, {x ∈ X | f x = c}.Infinite := by
    by_contra h
    push Not at h
    refine hX (Set.Finite.subset (hT.biUnion fun c hc ↦ h c hc) fun x hx ↦ ?_)
    exact Set.mem_biUnion (hf x hx) ⟨hx, rfl⟩
  have hClass3 (N : ℕ) (y : (↥Sinf ⊕ ↥Sfin) → ℝ) (a : (↥Sinf ⊕ ↥Sfin)) :
      hCellIndex N y a = ⌊(N : ℝ) * y a⌋₊ := rfl
  have hClass4 {N : ℕ} (hN : 0 < N) {y : (↥Sinf ⊕ ↥Sfin) → ℝ} {a : (↥Sinf ⊕ ↥Sfin)} (hy : 0 ≤ y a) :
      (hCellIndex N y a : ℝ) / N ≤ y a := by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    rw [hClass3]
    calc (⌊(N : ℝ) * y a⌋₊ : ℝ) ≤ (N : ℝ) * y a :=
          Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) hy)
    _ = y a * N := mul_comm _ _
  have hClass5 {N : ℕ} (hN : 0 < N) (y : (↥Sinf ⊕ ↥Sfin) → ℝ) (a : (↥Sinf ⊕ ↥Sfin)) :
      y a < ((hCellIndex N y a : ℝ) + 1) / N := by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [lt_div_iff₀ hN', hClass3, mul_comm]
    exact Nat.lt_floor_add_one ((N : ℝ) * y a)
  have hClass6 {N : ℕ} {y : (↥Sinf ⊕ ↥Sfin) → ℝ} (hy : ∀ a, 0 ≤ y a)
      (hsum : ∑ a, y a ≤ 1) : ∑ a, hCellIndex N y a ≤ N := by
    have key : ((∑ a, hCellIndex N y a : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      calc ∑ a, (hCellIndex N y a : ℝ)
          ≤ ∑ a, (N : ℝ) * y a :=
            Finset.sum_le_sum fun a _ ↦ Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hy a))
        _ = (N : ℝ) * ∑ a, y a := by rw [Finset.mul_sum]
        _ ≤ (N : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (N : ℝ) := mul_one _
    exact_mod_cast key
  have hClass7 {N : ℕ} (hN : 0 < N) {y : (↥Sinf ⊕ ↥Sfin) → ℝ}
      (hsum : ∑ a, y a = 1) :
      1 - (Fintype.card (↥Sinf ⊕ ↥Sfin) : ℝ) / N < ∑ a, (hCellIndex N y a : ℝ) / N := by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hlt : ∑ a, y a < ∑ a, ((hCellIndex N y a : ℝ) + 1) / N :=
      Finset.sum_lt_sum_of_nonempty
        (by
          rcases isEmpty_or_nonempty (↥Sinf ⊕ ↥Sfin) with h | h
          · exfalso
            simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
            exact absurd hsum (by norm_num)
          · exact Finset.univ_nonempty)
        fun a _ ↦ hClass5 hN y a
    have hsplit : ∑ a, ((hCellIndex N y a : ℝ) + 1) / N
        = (∑ a, (hCellIndex N y a : ℝ) / N) + (Fintype.card (↥Sinf ⊕ ↥Sfin) : ℝ) / N := by
      simp only [add_div]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one_div]
    rw [hsum, hsplit] at hlt
    linarith
  have hClass8 (f : (↥Sinf ⊕ ↥Sfin) → ℝ) (a : (↥Sinf ⊕ ↥Sfin)) :
      hLogProfile f a = Real.log (f a) / Real.log (∏ b, f b) := rfl
  have hClass9 {f : (↥Sinf ⊕ ↥Sfin) → ℝ} (hpos : ∀ a, 0 < f a) (hprod : ∏ b, f b < 1) :
      Real.log (∏ b, f b) < 0 :=
    Real.log_neg (Finset.prod_pos fun a _ ↦ hpos a) hprod
  have hClass10 {f : (↥Sinf ⊕ ↥Sfin) → ℝ} (hpos : ∀ a, 0 < f a) (hf : ∀ a, f a ≤ 1)
      (hprod : ∏ b, f b < 1) (a : (↥Sinf ⊕ ↥Sfin)) : 0 ≤ hLogProfile f a :=
    div_nonneg_iff.mpr <| Or.inr ⟨Real.log_nonpos (hpos a).le (hf a),
      (hClass9 hpos hprod).le⟩
  have hClass11 {f : (↥Sinf ⊕ ↥Sfin) → ℝ} (hpos : ∀ a, 0 < f a) (hprod : ∏ b, f b < 1) :
      ∑ a, hLogProfile f a = 1 := by
    have hlog : Real.log (∏ b, f b) = ∑ a, Real.log (f a) :=
      Real.log_prod fun a _ ↦ (hpos a).ne'
    simp only [hClass8]
    rw [show (∑ a, Real.log (f a) / Real.log (∏ b, f b)) = (∑ a, Real.log (f a)) / Real.log (∏ b, f b) from
      (Finset.sum_div _ _ _).symm, ← hlog]
    exact div_self (hClass9 hpos hprod).ne
  have hClass12 {N : ℕ} (hN : 0 < N) {f : (↥Sinf ⊕ ↥Sfin) → ℝ} (hpos : ∀ a, 0 < f a)
      (hf : ∀ a, f a ≤ 1) (hprod : ∏ b, f b < 1) (a : (↥Sinf ⊕ ↥Sfin)) :
      f a ≤ (∏ b, f b) ^ ((hCellIndex N (hLogProfile f) a : ℝ) / N) := by
    have hprod0 : 0 < ∏ b, f b := Finset.prod_pos fun b _ ↦ hpos b
    have hL : Real.log (∏ b, f b) < 0 := hClass9 hpos hprod
    rw [← Real.log_le_log_iff (hpos a) (Real.rpow_pos_of_pos hprod0 _), Real.log_rpow hprod0]
    have hcell := hClass4 (y := hLogProfile f) hN (hClass10 hpos hf hprod a)
    rw [hClass8, le_div_iff_of_neg hL] at hcell
    exact hcell
  have hClass13 {X : Set K} (hX : X.Infinite)
      (φ : (↥Sinf ⊕ ↥Sfin) → K → ℝ) (hφ0 : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ1 : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
      ∃ c : (↥Sinf ⊕ ↥Sfin) → ℕ, (∑ a, c a ≤ N) ∧ {x ∈ X | hCellIndex N (fun a ↦ φ a x) = c}.Infinite := by
    obtain ⟨c, hc, hinf⟩ := hClass2 hX (f := fun x ↦ hCellIndex N fun a ↦ φ a x)
      (T := {c : (↥Sinf ⊕ ↥Sfin) → ℕ | ∑ a, c a ≤ N}) (hClass1 N)
      fun x hx ↦ hClass6 (fun a ↦ hφ0 a x hx) (hφ1 x hx)
    exact ⟨c, hc, hinf⟩
  have hLocalApproxLeOne (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
      (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)
      (a : ↥Sinf ⊕ ↥Sfin) (β : K) : localApprox Sinf Sfin w α a β ≤ 1 :=
    pow_le_one₀ (le_min zero_le_one ((w _).nonneg _)) (min_le_left _ _)
  have hProdLocalApprox (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
      (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F) (β : K) :
      ∏ a, localApprox Sinf Sfin w α a β
        = (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult)
          * ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) := by
    rw [Fintype.prod_sum_type]
    congr 1
    · rw [← Finset.prod_coe_sort Sinf fun v ↦ min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult]
      rfl
    · rw [← Finset.prod_coe_sort Sfin fun v ↦ min 1 (w v.1 (algebraMap K F β - α v.1))]
      exact Finset.prod_congr rfl fun v _ ↦ pow_one _
  have hIndependentClass (f : (↥Sinf ⊕ ↥Sfin) → K → ℝ) {X : Set K} (hX : X.Infinite)
      (hpos : ∀ a, ∀ β ∈ X, 0 < f a β) (hle : ∀ a, ∀ β ∈ X, f a β ≤ 1)
      {κ : ℝ} (hκ : 0 < κ)
      (happrox : ∀ β ∈ X, (∏ a, f a β) ≤ mulHeight₁ β ^ (-κ))
      (hheight : ∀ β ∈ X, 1 < mulHeight₁ β)
      {N : ℕ} (hN : 0 < N) (L M : ℝ) :
      ∃ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) ∧ 1 - (Fintype.card (↥Sinf ⊕ ↥Sfin) : ℝ) / N ≤ ∑ a, lam a ∧
        ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧
          (L ≤ logHeight₁ (β 0) ∧ ∀ j, M * logHeight₁ (β j) ≤ logHeight₁ (β (j + 1))) ∧
          ∀ j a, f a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
    -- every member of `X` is a non-trivial approximation
    have hprod : ∀ β ∈ X, (∏ a, f a β) < 1 := fun β hβ ↦
      lt_of_le_of_lt (happrox β hβ) (Real.rpow_lt_one_of_one_lt_of_neg (hheight β hβ) (by linarith))
    set φ : (↥Sinf ⊕ ↥Sfin) → K → ℝ := fun a β ↦ hLogProfile (fun b ↦ f b β) a with hφdef
    have hφ0 : ∀ a, ∀ β ∈ X, 0 ≤ φ a β := fun a β hβ ↦
      hClass10 (fun b ↦ hpos b β hβ) (fun b ↦ hle b β hβ) (hprod β hβ) a
    have hφsum : ∀ β ∈ X, ∑ a, φ a β = 1 := fun β hβ ↦
      hClass11 (fun b ↦ hpos b β hβ) (hprod β hβ)
    obtain ⟨c, _, hinf⟩ := hClass13 hX φ hφ0
      (fun β hβ ↦ le_of_eq (hφsum β hβ)) N
    have hUnbounded : ∀ C : ℝ, ∃ x ∈ {x ∈ X | hCellIndex N (fun a ↦ φ a x) = c},
        C < logHeight₁ x := by
      intro C
      by_contra h
      push Not at h
      exact hinf ((NumberField.finite_setOfPred_logHeight₁_le K C).subset fun x hx ↦ h x hx)
    choose y hyX hy using hUnbounded
    let β : ℕ → K := fun j ↦ Nat.rec (motive := fun _ ↦ K) (y L)
      (fun _ prev ↦ y (M * logHeight₁ prev)) j
    have hβClass : ∀ j, β j ∈ {x ∈ X | hCellIndex N (fun a ↦ φ a x) = c} := by
      intro j
      cases j with
      | zero => exact hyX L
      | succ j => exact hyX _
    have hβX : ∀ j, β j ∈ X := fun j ↦ (hβClass j).1
    have hβc : ∀ j, hCellIndex N (fun a ↦ φ a (β j)) = c :=
      fun j ↦ (hβClass j).2
    have hβind : L ≤ logHeight₁ (β 0) ∧
        ∀ j, M * logHeight₁ (β j) ≤ logHeight₁ (β (j + 1)) :=
      ⟨(hy L).le, fun j ↦ (hy _).le⟩
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨fun a ↦ (c a : ℝ) / N, fun a ↦ by positivity, ?_, β, hβX, hβind, fun j a ↦ ?_⟩
    · have h610 := hClass7 (y := fun a ↦ φ a (β 0)) hN
        (hφsum (β 0) (hβX 0))
      rw [hβc 0] at h610
      exact h610.le
    · have hβj := hβX j
      have hpos' : ∀ b, 0 < f b (β j) := fun b ↦ hpos b (β j) hβj
      have hprod0 : (0 : ℝ) < ∏ b, f b (β j) := Finset.prod_pos fun b _ ↦ hpos' b
      have hcell := hClass12 (f := fun b ↦ f b (β j)) hN hpos'
        (fun b ↦ hle b (β j) hβj) (hprod (β j) hβj) a
      rw [show hLogProfile (fun b ↦ f b (β j)) = fun a ↦ φ a (β j) from rfl, hβc j] at hcell
      refine le_trans hcell ?_
      calc (∏ b, f b (β j)) ^ ((c a : ℝ) / N)
          ≤ (mulHeight₁ (β j) ^ (-κ)) ^ ((c a : ℝ) / N) :=
            Real.rpow_le_rpow hprod0.le (happrox (β j) hβj) (by positivity)
        _ = mulHeight₁ (β j) ^ (-κ * ((c a : ℝ) / N)) := by
            rw [← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one (hheight (β j) hβj)))]
  have hImported10 {κ : ℝ} (hκ : 2 < κ) :
      0 < rothEps κ ∧ rothEps κ < 1 / 2 ∧ 0 < 1 / 2 - 4 * rothEps κ := by
    have hκ0 : (0 : ℝ) < κ := by linarith
    have hη0 : 0 < 1 / 2 - 1 / κ := by
      have h : 1 / κ < 1 / 2 := by
        rw [div_lt_div_iff₀ hκ0 two_pos]
        linarith
      linarith
    have hη1 : 1 / 2 - 1 / κ < 1 / 2 := by
      have : (0 : ℝ) < 1 / κ := by positivity
      linarith
    unfold rothEps
    exact ⟨by positivity, by linarith, by linarith⟩
  have hImported11 {κ : ℝ} (hκ : 2 < κ) (s : ℕ) :
      0 < rothClassSize κ s ∧ (s : ℝ) / rothClassSize κ s ≤ 1 ∧
        1 < κ * (1 - (s : ℝ) / rothClassSize κ s) * (1 / 2 - 4 * rothEps κ) := by
    have hκ0 : (0 : ℝ) < κ := by linarith
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / 2 - 1 / κ := ⟨_, rfl⟩
    have hη0 : 0 < η := by
      rw [hηdef]
      have h : 1 / κ < 1 / 2 := by
        rw [div_lt_div_iff₀ hκ0 two_pos]
        linarith
      linarith
    have hη1 : η < 1 / 2 := by
      rw [hηdef]
      have : (0 : ℝ) < 1 / κ := by positivity
      linarith
    have hε : rothEps κ = η / 16 := by rw [rothEps, hηdef]
    have hNdef : (rothClassSize κ s : ℝ) = (⌈2 * (s : ℝ) / η⌉₊ : ℝ) + 1 := by
      rw [rothClassSize, hηdef]
      push_cast
      ring
    have hNbig : 2 * (s : ℝ) / η < (rothClassSize κ s : ℝ) := by
      rw [hNdef]
      linarith [Nat.le_ceil (2 * (s : ℝ) / η)]
    have hNpos : (0 : ℝ) < (rothClassSize κ s : ℝ) := by
      rw [hNdef]
      positivity
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    rw [div_lt_iff₀ hη0] at hNbig
    refine ⟨Nat.succ_pos _, ?_, ?_⟩
    · rw [div_le_one hNpos]
      nlinarith [mul_lt_mul_of_pos_left hη1 hNpos]
    rw [hε]
    set N : ℝ := (rothClassSize κ s : ℝ) with hN
    have hx : (s : ℝ) / N < η / 2 := by
      rw [div_lt_div_iff₀ hNpos two_pos]
      linarith
    have hx0 : (0 : ℝ) ≤ (s : ℝ) / N := by positivity
    have h1 : (1 / 2 - 4 * (η / 16)) - (s : ℝ) / N
        ≤ (1 - (s : ℝ) / N) * (1 / 2 - 4 * (η / 16)) := by nlinarith
    have hinv : κ * (1 / κ) = 1 := by field_simp
    have hstep1 : κ * ((1 / 2 - 4 * (η / 16)) - (s : ℝ) / N)
        ≤ κ * ((1 - (s : ℝ) / N) * (1 / 2 - 4 * (η / 16))) :=
      mul_le_mul_of_nonneg_left h1 hκ0.le
    have hk : 1 / κ < (1 / 2 - 4 * (η / 16)) - (s : ℝ) / N := by
      have hkk : 1 / κ = 1 / 2 - η := by rw [hηdef]; ring
      rw [hkk]
      linarith
    have hstep2 : 1 < κ * ((1 / 2 - 4 * (η / 16)) - (s : ℝ) / N) := by
      calc (1 : ℝ) = κ * (1 / κ) := hinv.symm
        _ < κ * ((1 / 2 - 4 * (η / 16)) - (s : ℝ) / N) := mul_lt_mul_of_pos_left hk hκ0
    rw [mul_assoc]
    linarith
  have hImported12 {κ : ℝ} (hκ : 2 < κ) (s r : ℕ) :
      (r : ℝ) * s * Real.exp (-(6 * ((rothChainLength κ s r : ℝ) + 1) * rothEps κ ^ 2)) < 1 / 2 := by
    obtain ⟨hε0, -, -⟩ := hImported10 hκ
    set ε := rothEps κ with hεdef
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    have hY : (0 : ℝ) < 2 * (r : ℝ) * s + 1 := by positivity
    have hε2 : (0 : ℝ) < 6 * ε ^ 2 := by positivity
    have hm : (rothChainLength κ s r : ℝ)
        = (⌈Real.log (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2)⌉₊ : ℝ) := by
      rw [rothChainLength]
    rw [hm]
    have hmbig : Real.log (2 * (r : ℝ) * s + 1)
        < 6 * ((⌈Real.log (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2 := by
      have h := Nat.le_ceil (Real.log (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2))
      rw [div_le_iff₀ hε2] at h
      nlinarith
    have h1 : Real.exp (-(6 * ((⌈Real.log (2 * (r : ℝ) * s + 1)
          / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2))
        ≤ 1 / (2 * (r : ℝ) * s + 1) := by
      rw [show (1 : ℝ) / (2 * (r : ℝ) * s + 1)
          = Real.exp (-(Real.log (2 * (r : ℝ) * s + 1))) by
        rw [Real.exp_neg, Real.exp_log hY, one_div]]
      exact Real.exp_le_exp.mpr (by linarith)
    calc (r : ℝ) * s * Real.exp (-(6 * ((⌈Real.log
            (2 * (r : ℝ) * s + 1) / (6 * ε ^ 2)⌉₊ : ℝ) + 1) * ε ^ 2))
        ≤ (r : ℝ) * s * (1 / (2 * (r : ℝ) * s + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((r : ℝ) * s) / (2 * (r : ℝ) * s + 1) := by rw [mul_one_div]
      _ < 1 / 2 := by
          rw [div_lt_div_iff₀ hY two_pos]
          nlinarith
  have hImported13 {κ : ℝ} (hκ : 2 < κ) (s r : ℕ) : 1 ≤ rothRatio κ s r := by
    obtain ⟨hε0, hε1, -⟩ := hImported10 hκ
    have hσ0 : 0 < rothEps κ ^ 2 ^ rothChainLength κ s r := pow_pos hε0 _
    have hσ1 : rothEps κ ^ 2 ^ rothChainLength κ s r ≤ 1 / 2 :=
      le_trans (pow_le_of_le_one hε0.le (by linarith) (by positivity)) hε1.le
    rw [rothRatio, le_div_iff₀ hσ0]
    linarith
  have hImported14 {κ : ℝ} (hκ : 2 < κ) (s r : ℕ) {rF : ℝ} (hrF : 0 ≤ rF) :
      0 < rothDelta κ s r rF ∧
        12 * ((rothChainLength κ s r : ℝ) + 1) * rothDelta κ s r rF
          ≤ rothEps κ ^ 2 ^ rothChainLength κ s r ∧
        2 * (8 * rF * s + 8) * rothDelta κ s r rF
          ≤ κ * (1 - (s : ℝ) / rothClassSize κ s) * (1 / 2 - 4 * rothEps κ) - 1 := by
    obtain ⟨hε0, -, -⟩ := hImported10 hκ
    have hΘ := (hImported11 hκ s).2.2
    have hm : (0 : ℝ) < (rothChainLength κ s r : ℝ) + 1 := by positivity
    have hW : (0 : ℝ) < 2 * (8 * rF * s + 8) := by positivity
    refine ⟨lt_min (by positivity) (div_pos (by linarith) hW), ?_, ?_⟩
    · rw [← le_div_iff₀' (by positivity)]
      exact min_le_left _ _
    · rw [← le_div_iff₀' hW]
      exact min_le_right _ _
  have hImported15 {κ : ℝ} (hκ : 2 < κ) (s r : ℕ) {rF : ℝ} (hrF : 0 ≤ rF) :
      0 < rothDelta κ s r rF :=
    (hImported14 hκ s r hrF).1
  have hImported17 (Sinf : Finset (InfinitePlace K))
      (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
      (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
      {κ : ℝ} (hκ : 2 < κ) :
      ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
        1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / rothClassSize κ (Sinf.card + Sfin.card)
          ≤ ∑ a, lam a →
        ∀ (α : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) →
            AbsoluteValue K ℝ → F)
          (β : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) → K),
          (∀ j, 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α j (sPlaceAbsValue a))
            ≤ rothDelta κ (Sinf.card + Sfin.card) (finrank K F) (finrank ℚ F)
              * absLogHeight₁ (β j)) →
          (∀ j : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F)),
            rothRatio κ (Sinf.card + Sfin.card) (finrank K F) * logHeight₁ (β j.castSucc)
              ≤ logHeight₁ (β j.succ)) →
          ¬ ∀ j a, localApprox Sinf Sfin w (α j) a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
    obtain ⟨hε0, hε1, hε4⟩ := hImported10 hκ
    obtain ⟨hδ0, hδσ, hδΘ⟩ := hImported14 hκ (Sinf.card + Sfin.card) (finrank K F)
      (Nat.cast_nonneg (finrank ℚ F))
    exact roth_no_moving_chain_aux Sinf Sfin w hwInf hwFin (by linarith) hε0 hε1 hε4
      (hImported11 hκ _).2.2 (hImported12 hκ _ _) hδ0 hδσ (by exact_mod_cast hδΘ)
  have hImported18 (Sinf : Finset (InfinitePlace K))
      (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
      (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
      (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
      ∀ lam : (↥Sinf ⊕ ↥Sfin) → ℝ, (∀ a, 0 ≤ lam a) →
        1 - ((Sinf.card + Sfin.card : ℕ) : ℝ) / rothClassSize κ (Sinf.card + Sfin.card)
          ≤ ∑ a, lam a →
        ∀ β : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F) + 1) → K,
          rothThreshold Sinf Sfin α κ ≤ logHeight₁ (β 0) →
          (∀ j : Fin (rothChainLength κ (Sinf.card + Sfin.card) (finrank K F)),
            rothRatio κ (Sinf.card + Sfin.card) (finrank K F) * logHeight₁ (β j.castSucc)
              ≤ logHeight₁ (β j.succ)) →
          ¬ ∀ j a, localApprox Sinf Sfin w α a (β j) ≤ mulHeight₁ (β j) ^ (-κ * lam a) := by
    have hδ0 := hImported15 hκ (Sinf.card + Sfin.card) (finrank K F)
      (Nat.cast_nonneg (finrank ℚ F))
    have hδ := hImported17 Sinf Sfin w hwInf hwFin hκ
    set δ := rothDelta κ (Sinf.card + Sfin.card) (finrank K F) (finrank ℚ F) with hδdef
    intro lam hlam0 hlamsum β hβL hchain
    refine hδ lam hlam0 hlamsum (fun _ ↦ α) β (fun j ↦ ?_) hchain
    rw [rothThreshold, ← hδdef] at hβL
    have hmono : Monotone fun j ↦ logHeight₁ (β j) :=
      Fin.monotone_iff_le_succ.mpr fun j ↦
        le_trans (le_mul_of_one_le_left (zero_le_logHeight₁ _) (hImported13 hκ _ _))
          (hchain j)
    have hLj : (totalWeight K : ℝ) * (1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)))
        / δ ≤ logHeight₁ (β j) := le_trans hβL (hmono (Fin.zero_le j))
    have htw : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
    have habs : (totalWeight K : ℝ) * absLogHeight₁ (β j) = logHeight₁ (β j) := by
      simpa only [totalWeight_eq_finrank, logHeight₁_eq_log_mulHeight₁] using
        (scalar_absolute_log_height (β j)).symm
    rw [div_le_iff₀ hδ0, ← habs] at hLj
    change 1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)) ≤ δ * absLogHeight₁ (β j)
    refine le_of_mul_le_mul_left ?_ htw
    calc (totalWeight K : ℝ) * (1 + ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (sPlaceAbsValue a)))
        ≤ (totalWeight K : ℝ) * absLogHeight₁ (β j) * δ := hLj
      _ = (totalWeight K : ℝ) * (δ * absLogHeight₁ (β j)) := by ring
  by_contra hinf
  rw [Set.not_finite] at hinf
  have hκ0 : (0 : ℝ) < κ := by linarith
  -- discard the finitely many degenerate solutions
  have hbad : ({β : K | mulHeight₁ β ≤ 1}
      ∪ ⋃ a : ↥Sinf ⊕ ↥Sfin, {β : K | algebraMap K F β = α (sPlaceAbsValue a)}).Finite := by
    refine Set.Finite.union (finite_setOfPred_mulHeight₁_le (K := K) 1)
      (Set.finite_iUnion fun a ↦ ?_)
    exact Set.Subsingleton.finite fun x hx y hy ↦
      (algebraMap K F).injective ((Set.mem_ofPred_eq ▸ hx).trans (Set.mem_ofPred_eq ▸ hy).symm)
  have hXinf := hinf.sdiff hbad
  set X : Set K := {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}
      \ ({β : K | mulHeight₁ β ≤ 1}
        ∪ ⋃ a : ↥Sinf ⊕ ↥Sfin, {β : K | algebraMap K F β = α (sPlaceAbsValue a)}) with hXdef
  have hXh : ∀ β ∈ X, 1 < mulHeight₁ β := fun β hβ ↦ by
    by_contra h
    exact hβ.2 (Set.mem_union_left _ (not_lt.mp h))
  have hXne : ∀ (a : ↥Sinf ⊕ ↥Sfin), ∀ β ∈ X, algebraMap K F β ≠ α (sPlaceAbsValue a) :=
    fun a β hβ h ↦ hβ.2 (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hXsub : ∀ β ∈ X, (∏ a, localApprox Sinf Sfin w α a β) ≤ mulHeight₁ β ^ (-κ) := by
    intro β hβ
    rw [hProdLocalApprox]
    exact hβ.1
  have hfpos : ∀ a, ∀ β ∈ X, 0 < localApprox Sinf Sfin w α a β := fun a β hβ ↦
    pow_pos (lt_min one_pos ((w _).pos (sub_ne_zero.mpr (hXne a β hβ)))) _
  have hfle : ∀ a, ∀ β ∈ X, localApprox Sinf Sfin w α a β ≤ 1 :=
    fun a β _ ↦ hLocalApproxLeOne _ _ _ _ _ _
  -- the parameters `ε` and `N`
  -- the core, fed by Step 0
  have hL := hImported18 Sinf Sfin w hwInf hwFin α hκ
  have hcard : Fintype.card (↥Sinf ⊕ ↥Sfin) = Sinf.card + Sfin.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  obtain ⟨lam, hlam0, hlamsum, b, -, hbind, hblocal⟩ :=
    hIndependentClass (localApprox Sinf Sfin w α) hXinf hfpos hfle hκ0
      hXsub hXh (hImported11 hκ (Sinf.card + Sfin.card)).1 (rothThreshold Sinf Sfin α κ)
      (rothRatio κ (Sinf.card + Sfin.card) (finrank K F))
  rw [hcard] at hlamsum
  refine hL lam hlam0 hlamsum (fun j ↦ b j.val) (by simpa using hbind.1) (fun j ↦ ?_)
    fun j a ↦ hblocal j.val a
  simpa [Fin.val_succ, Fin.val_castSucc] using hbind.2 j.val

end NumberField
