/- GID: D5/S3/Arith/AbsoluteValues/Heights/PseudoBasisMetrics
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/PseudoBasisMetrics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The projective Arakelov height descends from the tuple height under nonzero scalar multiplication. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasis

public section

namespace NumberField

open Finset Function Height Real

variable {K : Type*} [Field K] [NumberField K] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The **Arakelov height** of a tuple of elements of a number field: the ℓ² norm at the
archimedean places, weighted by `InfinitePlace.mult`, and the sup norm at the finite places.
For the zero tuple we take the junk value `1`, as `Height.mulHeight` does.

This is the normalization in which the constants of the Siegel-lemma literature are stated;
`Height.mulHeight` uses the sup norm at every place. Both live in the library and every bound
says which one it is in. -/
@[expose] noncomputable def arakelovMulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)

/-- The logarithmic Arakelov height. As everywhere in this development, the logarithmic height
is *defined* as the logarithm of the multiplicative one and never independently. -/
@[expose] noncomputable def arakelovLogHeight (x : ι → K) : ℝ := log (arakelovMulHeight x)

section Smul

variable {κ : Type*}

end Smul

section Comparison

end Comparison

/-- The multiplicative Arakelov height of an element of a number field, i.e. of the point
`(x : 1)` of the projective line. -/
@[expose] noncomputable def arakelovMulHeight₁ (x : K) : ℝ := arakelovMulHeight ![x, 1]

/-- The logarithmic Arakelov height of an element of a number field. -/
@[expose] noncomputable def arakelovLogHeight₁ (x : K) : ℝ := log (arakelovMulHeight₁ x)

end NumberField

namespace Projectivization

open NumberField Real

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- The multiplicative Arakelov height of a point of projective space over a number field. -/
@[expose] noncomputable def projectiveArakelovMulHeight
    (x : Projectivization K (ι → K)) : ℝ := by
  let nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite :
        (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace K) :
        (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
          = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
      have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
      have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
        rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
          ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
        congr 1
        push_cast
        ring
      rw [hsum, Real.mul_rpow (by positivity) (by positivity),
        hPower]
    rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
    simp only [harch, Finset.prod_mul_distrib]
    rw [mul_right_comm, hFinite, mul_comm])))
  exact x.lift (fun r ↦ NumberField.arakelovMulHeight r.val) (fun a b t h ↦ by
      have ht : t ≠ 0 := by
        contrapose! h
        simpa [h] using a.prop
      exact h ▸ nativeSource12 _ ht)
/-- The logarithmic Arakelov height of a point of projective space over a number field. -/
noncomputable def arakelovLogHeight (x : Projectivization K (ι → K)) : ℝ := by
  let nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite :
        (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace K) :
        (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
          = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
      have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
      have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
        rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
          ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
        congr 1
        push_cast
        ring
      rw [hsum, Real.mul_rpow (by positivity) (by positivity),
        hPower]
    rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
    simp only [harch, Finset.prod_mul_distrib]
    rw [mul_right_comm, hFinite, mul_comm])))
  exact x.lift (fun r ↦ NumberField.arakelovLogHeight r.val) (fun a b t h ↦ by
      have ht : t ≠ 0 := by
        contrapose! h
        simpa [h] using a.prop
      simp only [NumberField.arakelovLogHeight]
      exact congrArg Real.log (h ▸ nativeSource12 _ ht))

end Projectivization

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `NumberField.arakelovMulHeight` is always positive. -/
@[positivity NumberField.arakelovMulHeight _]
meta def evalArakelovMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovMulHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q((
      let nativeSource12 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · rw [smul_zero]
        have hcx : c • x ≠ 0 := by simp [hc, hx]
        have hFinite :
            (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
              = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
          have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
            obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
            exact _root_.Finset.prod_pos fun v _ ↦ pow_pos
              ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
          have h := Height.mulHeight_smul_eq_mulHeight x hc
          rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
          have hSupInfinite (v : NumberField.InfinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          have hSupFinite (v : NumberField.FinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          simp only [hSupInfinite, hSupFinite, mul_pow, _root_.Finset.prod_mul_distrib] at h ⊢
          exact mul_left_cancel₀ hA.ne' (by linear_combination h)
        have harch (v : NumberField.InfinitePlace K) :
            (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
              = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
          have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
            rw [_root_.Finset.mul_sum]
            exact _root_.Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
          have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
            rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
              ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
            congr 1
            push_cast
            ring
          rw [hsum, Real.mul_rpow (by positivity) (by positivity),
            hPower]
        rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
        simp only [harch, _root_.Finset.prod_mul_distrib]
        rw [mul_right_comm, hFinite, mul_comm])));
      let nativeSource13 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · simp [NumberField.arakelovMulHeight]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
        have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
        rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
        refine one_le_mul_of_one_le_of_one_le (_root_.Finset.one_le_prod₀ fun v _ ↦ ?_)
          (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
        have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
          le_trans (le_of_eq (by simp [hi']))
            (_root_.Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (_root_.Finset.mem_univ i))
        exact Real.one_le_rpow h1 (by positivity))));
      let nativeSource16 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 0 < NumberField.arakelovMulHeight x from by
        classical
        exact (
          zero_lt_one.trans_le <| nativeSource13 x
        ))));
      nativeSource16 $a)))
  | _, _, _ => throwError "not NumberField.arakelovMulHeight"

/-- Extension for the `positivity` tactic: `NumberField.arakelovLogHeight` is always
nonnegative. -/
@[positivity NumberField.arakelovLogHeight _]
meta def evalArakelovLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovLogHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q((
      let nativeSource12 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · rw [smul_zero]
        have hcx : c • x ≠ 0 := by simp [hc, hx]
        have hFinite :
            (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
              = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
          have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
            obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
            exact _root_.Finset.prod_pos fun v _ ↦ pow_pos
              ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
          have h := Height.mulHeight_smul_eq_mulHeight x hc
          rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
          have hSupInfinite (v : NumberField.InfinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          have hSupFinite (v : NumberField.FinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          simp only [hSupInfinite, hSupFinite, mul_pow, _root_.Finset.prod_mul_distrib] at h ⊢
          exact mul_left_cancel₀ hA.ne' (by linear_combination h)
        have harch (v : NumberField.InfinitePlace K) :
            (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
              = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
          have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
            rw [_root_.Finset.mul_sum]
            exact _root_.Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
          have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
            rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
              ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
            congr 1
            push_cast
            ring
          rw [hsum, Real.mul_rpow (by positivity) (by positivity),
            hPower]
        rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
        simp only [harch, _root_.Finset.prod_mul_distrib]
        rw [mul_right_comm, hFinite, mul_comm])));
      let nativeSource13 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · simp [NumberField.arakelovMulHeight]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
        have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
        rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
        refine one_le_mul_of_one_le_of_one_le (_root_.Finset.one_le_prod₀ fun v _ ↦ ?_)
          (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
        have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
          le_trans (le_of_eq (by simp [hi']))
            (_root_.Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (_root_.Finset.mem_univ i))
        exact Real.one_le_rpow h1 (by positivity))));
      let nativeSource14 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 0 ≤ NumberField.arakelovLogHeight x from by
        classical
        exact (
          log_nonneg <| nativeSource13 x
        ))));
      nativeSource14 $a)))
  | _, _, _ => throwError "not NumberField.arakelovLogHeight"

/-- Extension for the `positivity` tactic: `NumberField.arakelovMulHeight₁` is always
positive. -/
@[positivity NumberField.arakelovMulHeight₁ _]
meta def evalArakelovMulHeight₁ : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovMulHeight₁ $K $KF $KNF $a) =>
    assertInstancesCommute
    pure (.positive q((
      let nativeSource12 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · rw [smul_zero]
        have hcx : c • x ≠ 0 := by simp [hc, hx]
        have hFinite :
            (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
              = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
          have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
            obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
            exact _root_.Finset.prod_pos fun v _ ↦ pow_pos
              ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
          have h := Height.mulHeight_smul_eq_mulHeight x hc
          rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
          have hSupInfinite (v : NumberField.InfinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          have hSupFinite (v : NumberField.FinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          simp only [hSupInfinite, hSupFinite, mul_pow, _root_.Finset.prod_mul_distrib] at h ⊢
          exact mul_left_cancel₀ hA.ne' (by linear_combination h)
        have harch (v : NumberField.InfinitePlace K) :
            (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
              = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
          have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
            rw [_root_.Finset.mul_sum]
            exact _root_.Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
          have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
            rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
              ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
            congr 1
            push_cast
            ring
          rw [hsum, Real.mul_rpow (by positivity) (by positivity),
            hPower]
        rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
        simp only [harch, _root_.Finset.prod_mul_distrib]
        rw [mul_right_comm, hFinite, mul_comm])));
      let nativeSource13 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · simp [NumberField.arakelovMulHeight]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
        have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
        rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
        refine one_le_mul_of_one_le_of_one_le (_root_.Finset.one_le_prod₀ fun v _ ↦ ?_)
          (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
        have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
          le_trans (le_of_eq (by simp [hi']))
            (_root_.Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (_root_.Finset.mem_univ i))
        exact Real.one_le_rpow h1 (by positivity))));
      let nativeSource16 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 0 < NumberField.arakelovMulHeight x from by
        classical
        exact (
          zero_lt_one.trans_le <| nativeSource13 x
        ))));
      let nativeSource111 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] (x : K) => (show 0 < NumberField.arakelovMulHeight₁ x from by
        classical
        exact (
          nativeSource16 _
        ))));
      nativeSource111 $a)))
  | _, _, _ => throwError "not NumberField.arakelovMulHeight₁"

/-- Extension for the `positivity` tactic: `NumberField.arakelovLogHeight₁` is always
nonnegative. -/
@[positivity NumberField.arakelovLogHeight₁ _]
meta def evalArakelovLogHeight₁ : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@NumberField.arakelovLogHeight₁ $K $KF $KNF $a) =>
    assertInstancesCommute
    pure (.nonnegative q((
      let nativeSource12 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · rw [smul_zero]
        have hcx : c • x ≠ 0 := by simp [hc, hx]
        have hFinite :
            (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
              = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
          have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
            obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
            exact _root_.Finset.prod_pos fun v _ ↦ pow_pos
              ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
          have h := Height.mulHeight_smul_eq_mulHeight x hc
          rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
          have hSupInfinite (v : NumberField.InfinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          have hSupFinite (v : NumberField.FinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          simp only [hSupInfinite, hSupFinite, mul_pow, _root_.Finset.prod_mul_distrib] at h ⊢
          exact mul_left_cancel₀ hA.ne' (by linear_combination h)
        have harch (v : NumberField.InfinitePlace K) :
            (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
              = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
          have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
            rw [_root_.Finset.mul_sum]
            exact _root_.Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
          have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
            rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
              ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
            congr 1
            push_cast
            ring
          rw [hsum, Real.mul_rpow (by positivity) (by positivity),
            hPower]
        rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
        simp only [harch, _root_.Finset.prod_mul_distrib]
        rw [mul_right_comm, hFinite, mul_comm])));
      let nativeSource13 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · simp [NumberField.arakelovMulHeight]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
        have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
        rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
        refine one_le_mul_of_one_le_of_one_le (_root_.Finset.one_le_prod₀ fun v _ ↦ ?_)
          (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
        have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
          le_trans (le_of_eq (by simp [hi']))
            (_root_.Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (_root_.Finset.mem_univ i))
        exact Real.one_le_rpow h1 (by positivity))));
      let nativeSource14 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 0 ≤ NumberField.arakelovLogHeight x from by
        classical
        exact (
          log_nonneg <| nativeSource13 x
        ))));
      let nativeSource99 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] (x : K) => (show 0 ≤ NumberField.arakelovLogHeight₁ x from by
        classical
        exact (
          nativeSource14 _
        ))));
      nativeSource99 $a)))
  | _, _, _ => throwError "not NumberField.arakelovLogHeight₁"

/-- Extension for the `positivity` tactic: `Projectivization.projectiveArakelovMulHeight` is always
positive. -/
@[positivity Projectivization.projectiveArakelovMulHeight _]
meta def evalProjArakelovMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Projectivization.projectiveArakelovMulHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q((
      let nativeSource12 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · rw [smul_zero]
        have hcx : c • x ≠ 0 := by simp [hc, hx]
        have hFinite :
            (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
              = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
          have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
            obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
            exact _root_.Finset.prod_pos fun v _ ↦ pow_pos
              ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
          have h := Height.mulHeight_smul_eq_mulHeight x hc
          rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
          have hSupInfinite (v : NumberField.InfinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          have hSupFinite (v : NumberField.FinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          simp only [hSupInfinite, hSupFinite, mul_pow, _root_.Finset.prod_mul_distrib] at h ⊢
          exact mul_left_cancel₀ hA.ne' (by linear_combination h)
        have harch (v : NumberField.InfinitePlace K) :
            (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
              = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
          have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
            rw [_root_.Finset.mul_sum]
            exact _root_.Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
          have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
            rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
              ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
            congr 1
            push_cast
            ring
          rw [hsum, Real.mul_rpow (by positivity) (by positivity),
            hPower]
        rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
        simp only [harch, _root_.Finset.prod_mul_distrib]
        rw [mul_right_comm, hFinite, mul_comm])));
      let nativeSource13 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · simp [NumberField.arakelovMulHeight]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
        have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
        rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
        refine one_le_mul_of_one_le_of_one_le (_root_.Finset.one_le_prod₀ fun v _ ↦ ?_)
          (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
        have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
          le_trans (le_of_eq (by simp [hi']))
            (_root_.Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (_root_.Finset.mem_univ i))
        exact Real.one_le_rpow h1 (by positivity))));
      let nativeSource125 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : Projectivization K (ι → K)) => (show 1 ≤ Projectivization.projectiveArakelovMulHeight x from by
        classical
        rw [← x.mk_rep, (fun {x : _ → _} hx ↦ (show Projectivization.projectiveArakelovMulHeight (Projectivization.mk _ x hx) =
            NumberField.arakelovMulHeight x from rfl))]
        exact nativeSource13 _)));
      let nativeSource128 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : Projectivization K (ι → K)) => (show 0 < Projectivization.projectiveArakelovMulHeight x from by
        classical
        exact (
          zero_lt_one.trans_le <| nativeSource125 x
        ))));
      nativeSource128 $a)))
  | _, _, _ => throwError "not Projectivization.projectiveArakelovMulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.arakelovLogHeight` is always
nonnegative. -/
@[positivity Projectivization.arakelovLogHeight _]
meta def evalProjArakelovLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Projectivization.arakelovLogHeight $K $KF $KNF $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q((
      let nativeSource12 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · rw [smul_zero]
        have hcx : c • x ≠ 0 := by simp [hc, hx]
        have hFinite :
            (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
              = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
          have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
            obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
            exact _root_.Finset.prod_pos fun v _ ↦ pow_pos
              ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
          have h := Height.mulHeight_smul_eq_mulHeight x hc
          rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
          have hSupInfinite (v : NumberField.InfinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          have hSupFinite (v : NumberField.FinitePlace K) :
              (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
          simp only [hSupInfinite, hSupFinite, mul_pow, _root_.Finset.prod_mul_distrib] at h ⊢
          exact mul_left_cancel₀ hA.ne' (by linear_combination h)
        have harch (v : NumberField.InfinitePlace K) :
            (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
              = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
          have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
            rw [_root_.Finset.mul_sum]
            exact _root_.Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
          have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
            rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
              ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
            congr 1
            push_cast
            ring
          rw [hsum, Real.mul_rpow (by positivity) (by positivity),
            hPower]
        rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
        simp only [harch, _root_.Finset.prod_mul_distrib]
        rw [mul_right_comm, hFinite, mul_comm])));
      let nativeSource13 := (open _root_.Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
        classical
        rcases eq_or_ne x 0 with rfl | hx
        · simp [NumberField.arakelovMulHeight]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
        have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
        rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
        refine one_le_mul_of_one_le_of_one_le (_root_.Finset.one_le_prod₀ fun v _ ↦ ?_)
          (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
        have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
          le_trans (le_of_eq (by simp [hi']))
            (_root_.Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (_root_.Finset.mem_univ i))
        exact Real.one_le_rpow h1 (by positivity))));
      let nativeSource122 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : Projectivization K (ι → K)) => (show Projectivization.arakelovLogHeight x = log (Projectivization.projectiveArakelovMulHeight x) from by
        classical
        rw [← x.mk_rep]
        change NumberField.arakelovLogHeight x.rep = Real.log (NumberField.arakelovMulHeight x.rep)
        rfl)));
      let nativeSource125 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : Projectivization K (ι → K)) => (show 1 ≤ Projectivization.projectiveArakelovMulHeight x from by
        classical
        rw [← x.mk_rep, (fun {x : _ → _} hx ↦ (show Projectivization.projectiveArakelovMulHeight (Projectivization.mk _ x hx) =
            NumberField.arakelovMulHeight x from rfl))]
        exact nativeSource13 _)));
      let nativeSource126 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : Projectivization K (ι → K)) => (show 0 ≤ Projectivization.arakelovLogHeight x from by
        classical
        rw [nativeSource122]
        exact log_nonneg (nativeSource125 x))));
      nativeSource126 $a)))
  | _, _, _ => throwError "not Projectivization.arakelovLogHeight"

end Mathlib.Meta.Positivity

section Examples

open Height NumberField

end Examples

end

public section

open FractionalIdeal Module
open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] {ι : Type*}

end
