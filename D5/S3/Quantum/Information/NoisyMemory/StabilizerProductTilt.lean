/- GID: D5/S3/Quantum/Information/NoisyMemory/StabilizerProductTilt
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/NoisyMemory/StabilizerProductTilt
   mirror-E: none(waiver:analytic-collision-comparison)
   anchors: []
   utility: none
   digest: Sharp reciprocal moments for paired product laws with bounded coordinate increments. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The two product-law expectations needed in the stabilizer erasure bound for
arXiv:2611.34474v1. At each coordinate the positive observable increases by
a factor between one and two. Conditioning recursively proves the sharp
inhomogeneous inequality directly.
-/

open scoped BigOperators

namespace StabilizerProductTilt

set_option autoImplicit false

/-- Expectation on independent Boolean coordinates with success probabilities `p`. -/
def productAverage : {n : ℕ} → (Fin n → ℝ) → ((Fin n → Bool) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | n + 1, p, f =>
      (1 - p 0) * productAverage (fun i : Fin n => p i.succ) (fun x => f (Fin.cons false x)) +
      p 0 * productAverage (fun i : Fin n => p i.succ) (fun x => f (Fin.cons true x))

private theorem average_mono {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) {f g : (Fin n → Bool) → ℝ}
    (hfg : ∀ x, f x ≤ g x) :
    productAverage p f ≤ productAverage p g := by
  induction n with
  | zero => exact hfg _
  | succ n ih =>
      change
        (1 - p 0) * productAverage (fun i => p i.succ) (fun x => f (Fin.cons false x)) +
          p 0 * productAverage (fun i => p i.succ) (fun x => f (Fin.cons true x)) ≤
        (1 - p 0) * productAverage (fun i => p i.succ) (fun x => g (Fin.cons false x)) +
          p 0 * productAverage (fun i => p i.succ) (fun x => g (Fin.cons true x))
      exact add_le_add
        (mul_le_mul_of_nonneg_left (ih _ (fun i => hp i.succ) (fun x => hfg _)) (sub_nonneg.mpr (hp 0).2))
        (mul_le_mul_of_nonneg_left (ih _ (fun i => hp i.succ) (fun x => hfg _)) (hp 0).1)

private theorem average_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, 0 < f x) : 0 < productAverage p f := by
  induction n with
  | zero => exact hf _
  | succ n ih =>
      rw [productAverage]
      have hfalse := ih (fun i => p i.succ) (fun i => hp i.succ)
        (fun x => f (Fin.cons false x)) (fun x => hf _)
      have htrue := ih (fun i => p i.succ) (fun i => hp i.succ)
        (fun x => f (Fin.cons true x)) (fun x => hf _)
      rcases (hp 0).1.eq_or_lt with hp0 | hp0
      · simpa [← hp0] using hfalse
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr (hp 0).2) hfalse.le) (mul_pos hp0 htrue)

private theorem average_const_mul {n : ℕ} (p : Fin n → ℝ) (c : ℝ)
    (f : (Fin n → Bool) → ℝ) :
    productAverage p (fun x => c * f x) = c * productAverage p f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [productAverage, ih]
      ring

private theorem two_point (p w t : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    ((1 - p) + p * t) * ((1 - w) + w / t) ≤ max 1 ((1 + p) * (1 - w / 2)) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hsecant : 1 / t ≤ (3 - t) / 2 := by
    apply (div_le_iff₀ htpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ht.1)]
  have hweighted := mul_le_mul_of_nonneg_left hsecant
    (mul_nonneg (sub_nonneg.mpr hp.2) hw.1)
  let M := max 1 ((1 + p) * (1 - w / 2))
  calc
    _ = (1 - p) * (1 - w) + p * w + p * (1 - w) * t +
        ((1 - p) * w) * (1 / t) := by field_simp; ring
    _ ≤ (1 - p) * (1 - w) + p * w + p * (1 - w) * t +
        ((1 - p) * w) * ((3 - t) / 2) := add_le_add_right hweighted _
    _ = (2 - t) * 1 + (t - 1) * ((1 + p) * (1 - w / 2)) := by ring
    _ ≤ (2 - t) * M + (t - 1) * M :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr ht.1))
    _ = M := by ring

/-- Sharp reciprocal-product bound for two independent Boolean laws. -/
theorem product_average_mul_reciprocal_le {n : ℕ} (p w : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (f : (Fin n → Bool) → ℝ) (hf : ∀ x, 0 < f x)
    (hstep : ∀ i x, f (Function.update x i false) ≤ f (Function.update x i true) ∧
      f (Function.update x i true) ≤ 2 * f (Function.update x i false)) :
    productAverage p f * productAverage w (fun x => (f x)⁻¹) ≤
      ∏ i, max 1 ((1 + p i) * (1 - w i / 2)) := by
  induction n with
  | zero =>
      simp only [productAverage, Finset.univ_eq_empty, Finset.prod_empty]
      exact (mul_inv_cancel₀ (hf _).ne').le
  | succ n ih =>
      let p' : Fin n → ℝ := fun i => p i.succ
      let w' : Fin n → ℝ := fun i => w i.succ
      let f₀ : (Fin n → Bool) → ℝ := fun x => f (Fin.cons false x)
      let f₁ : (Fin n → Bool) → ℝ := fun x => f (Fin.cons true x)
      have hp' (i : Fin n) := hp i.succ
      have hw' (i : Fin n) := hw i.succ
      have hcons_update (b c : Bool) (x : Fin n → Bool) (i : Fin n) :
          Fin.cons b (Function.update x i c) = Function.update (Fin.cons b x : Fin (n + 1) → Bool) i.succ c := by
        ext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
        · by_cases h : j = i
          · subst j
            simp
          · have hs : j.succ ≠ i.succ := (Fin.succ_injective n).ne h
            simp [Function.update_of_ne h, Function.update_of_ne hs]
      have hsub (b : Bool) (i : Fin n) (x : Fin n → Bool) :
          f (Fin.cons b (Function.update x i false)) ≤ f (Fin.cons b (Function.update x i true)) ∧
            f (Fin.cons b (Function.update x i true)) ≤
              2 * f (Fin.cons b (Function.update x i false)) := by
        simpa only [hcons_update] using hstep i.succ (Fin.cons b x)
      let A := productAverage p' f₀
      let B := productAverage p' f₁
      let P := ∏ i, max 1 ((1 + p' i) * (1 - w' i / 2))
      have hA : 0 < A := average_pos p' hp' f₀ (fun x => hf _)
      have hB : 0 < B := average_pos p' hp' f₁ (fun x => hf _)
      have hc := ih p' w' hp' hw' f₀ (fun x => hf _) (hsub false)
      have hd := ih p' w' hp' hw' f₁ (fun x => hf _) (hsub true)
      have hpoint (x : Fin n → Bool) : f₀ x ≤ f₁ x ∧ f₁ x ≤ 2 * f₀ x := by
        have hhead (b : Bool) : Function.update (Fin.cons false x : Fin (n + 1) → Bool) 0 b = Fin.cons b x := by
          ext j
          refine Fin.cases ?_ (fun j => ?_) j <;> simp
        simpa only [hhead] using hstep 0 (Fin.cons false x)
      have hAB : A ≤ B := average_mono p' hp' (fun x => (hpoint x).1)
      have hBA : B ≤ 2 * A := by
        rw [← average_const_mul p' 2 f₀]
        exact average_mono p' hp' (fun x => (hpoint x).2)
      have hratio : B / A ∈ Set.Icc (1 : ℝ) 2 :=
        ⟨(le_div_iff₀ hA).mpr (by simpa using hAB), (div_le_iff₀ hA).mpr hBA⟩
      have hP : 0 ≤ P := Finset.prod_nonneg fun i _ =>
        zero_le_one.trans (le_max_left _ _)
      have hrec₀ : productAverage w' (fun x => (f₀ x)⁻¹) ≤ P / A :=
        (le_div_iff₀ hA).mpr (by simpa [mul_comm] using hc)
      have hrec₁ : productAverage w' (fun x => (f₁ x)⁻¹) ≤ P / B :=
        (le_div_iff₀ hB).mpr (by simpa [mul_comm] using hd)
      rw [Fin.prod_univ_succ]
      change ((1 - p 0) * A + p 0 * B) *
          ((1 - w 0) * productAverage w' (fun x => (f₀ x)⁻¹) +
            w 0 * productAverage w' (fun x => (f₁ x)⁻¹)) ≤
        max 1 ((1 + p 0) * (1 - w 0 / 2)) * P
      calc
        _ ≤ ((1 - p 0) * A + p 0 * B) * ((1 - w 0) * (P / A) + w 0 * (P / B)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left hrec₀ (sub_nonneg.mpr (hw 0).2))
              (mul_le_mul_of_nonneg_left hrec₁ (hw 0).1))
            (add_nonneg (mul_nonneg (sub_nonneg.mpr (hp 0).2) hA.le)
              (mul_nonneg (hp 0).1 hB.le))
        _ = (((1 - p 0) + p 0 * (B / A)) * ((1 - w 0) + w 0 / (B / A))) * P := by
          field_simp
          <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (two_point _ _ _ (hp 0) (hw 0) hratio) hP

#print axioms product_average_mul_reciprocal_le

end StabilizerProductTilt
