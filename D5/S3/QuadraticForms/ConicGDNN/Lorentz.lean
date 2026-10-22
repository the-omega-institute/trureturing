/- GID: D5/S3/QuadraticForms/ConicGDNN/Lorentz
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ConicGDNN/Lorentz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset, mathlib/module/Mathlib.Algebra.BigOperators.Field]
   utility: none
   digest: Self-duality and homogeneous linear square certificates for product Lorentz cones. -/

import D5.S3.QuadraticForms.ConicGDNN.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
noncomputable section
open Matrix MvPolynomial Finset
open scoped BigOperators
namespace D5.S3.QuadraticForms.ConicGDNN.Lorentz
open Defs
private def blockVector {p r : ℕ} {k : Fin r → ℕ} (j : Fin r)
    (a : ℝ) (w : Fin (k j) → ℝ) : Idx p r k → ℝ :=
  Sum.elim (fun _ => 0) (fun s => Pi.single (M := fun l => Option (Fin (k l)) → ℝ) j (fun o => o.elim a w) s.1 s.2)
private lemma blockVector_mem {p r : ℕ} {k : Fin r → ℕ} (j : Fin r)
    (a : ℝ) (w : Fin (k j) → ℝ) (h : Real.sqrt (∑ i, w i ^ 2) ≤ a) :
    blockVector (p := p) j a w ∈ cone p r k := by
  classical
  constructor
  · intro i; simp [blockVector]
  · intro l
    by_cases hl : l = j
    · subst l; simpa [blockVector] using h
    · simp [blockVector, Pi.single_eq_of_ne hl]
private lemma dot_blockVector {p r : ℕ} {k : Fin r → ℕ} (u : Idx p r k → ℝ)
    (j : Fin r) (a : ℝ) (w : Fin (k j) → ℝ) :
    u ⬝ᵥ blockVector j a w = u (Sum.inr ⟨j, none⟩) * a +
      ∑ i, u (Sum.inr ⟨j, some i⟩) * w i := by
  classical
  simp only [dotProduct, Fintype.sum_sum_type, blockVector, Sum.elim_inl,
    mul_zero, sum_const_zero, Sum.elim_inr, Fintype.sum_sigma, zero_add]
  rw [Fintype.sum_eq_single j]
  · simp [Fintype.sum_option]
  · intro l hl
    simp [Pi.single_eq_of_ne hl]
private lemma lorentz_pair_nonneg {ι : Type*} [Fintype ι]
    (a b : ℝ) (w z : ι → ℝ)
    (hw : Real.sqrt (∑ i, w i ^ 2) ≤ a)
    (hz : Real.sqrt (∑ i, z i ^ 2) ≤ b) :
    0 ≤ a * b + ∑ i, w i * z i := by
  have hw0 : 0 ≤ ∑ i, w i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hz0 : 0 ≤ ∑ i, z i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hs := sum_mul_sq_le_sq_mul_sq (univ : Finset ι) w z
  have hww := Real.sq_sqrt hw0
  have hzz := Real.sq_sqrt hz0
  have ha : 0 ≤ a := (Real.sqrt_nonneg _).trans hw
  have hb : 0 ≤ b := (Real.sqrt_nonneg _).trans hz
  have hm := mul_le_mul hw hz (Real.sqrt_nonneg _) ha
  have hpos := mul_nonneg (Real.sqrt_nonneg (∑ i, w i ^ 2))
    (Real.sqrt_nonneg (∑ i, z i ^ 2))
  nlinarith [sq_nonneg (Real.sqrt (∑ i, w i ^ 2) * Real.sqrt (∑ i, z i ^ 2) + ∑ i, w i * z i)]
/-- The product of orthant and Lorentz cones is self-dual for the standard pairing. -/
theorem dualCone_cone (p r : ℕ) (k : Fin r → ℕ) :
    dualCone (cone p r k) = cone p r k := by
  classical
  ext u
  constructor
  · intro hu
    constructor
    · intro i
      have he : Pi.single (Sum.inl i) (1 : ℝ) ∈ cone p r k := by
        constructor
        · intro l; simp [Pi.single_apply]; positivity
        · intro j; simp
      simpa only [dotProduct_single, mul_one] using hu _ he
    · intro j
      have ha := hu _ (blockVector_mem (p := p) j 1 (fun _ => 0) (by simp))
      rw [dot_blockVector] at ha
      simp only [mul_one, mul_zero, sum_const_zero, add_zero] at ha
      let w : Fin (k j) → ℝ := fun i => u (Sum.inr ⟨j, some i⟩)
      have hw0 : 0 ≤ ∑ i, w i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      have hs := Real.sq_sqrt hw0
      have hn := Real.sqrt_nonneg (∑ i, w i ^ 2)
      have hb : Real.sqrt (∑ i, (-w i) ^ 2) ≤ Real.sqrt (∑ i, w i ^ 2) := by simp
      have ht := hu _ (blockVector_mem (p := p) j _ (fun i => -w i) hb)
      rw [dot_blockVector] at ht
      change 0 ≤ u (Sum.inr ⟨j, none⟩) * Real.sqrt (∑ i, w i ^ 2) +
        ∑ i, w i * -w i at ht
      have he : (∑ i, w i * -w i) = -(∑ i, w i ^ 2) := by
        simp [← sum_neg_distrib, pow_two]
      rw [he] at ht
      change Real.sqrt (∑ i, w i ^ 2) ≤ _
      nlinarith
  · intro hu y hy
    change 0 ≤ ∑ a, u a * y a
    rw [Fintype.sum_sum_type]
    apply add_nonneg
    · exact sum_nonneg fun i _ => mul_nonneg (hu.1 i) (hy.1 i)
    · rw [Fintype.sum_sigma]
      apply sum_nonneg
      intro j _
      rw [Fintype.sum_option]
      exact lorentz_pair_nonneg _ _ _ _ (hu.2 j) (hy.2 j)

private def LinearSOS {σ : Type*} (f : MvPolynomial σ ℝ) : Prop :=
  ∃ L : List (MvPolynomial σ ℝ), (∀ ℓ ∈ L, ℓ.IsHomogeneous 1) ∧
    f = (L.map (· ^ 2)).sum
private lemma linearSOS_zero {σ : Type*} : LinearSOS (0 : MvPolynomial σ ℝ) := by
  exact ⟨[], by simp, by simp⟩
private lemma linearSOS_add {σ : Type*} {f g : MvPolynomial σ ℝ}
    (hf : LinearSOS f) (hg : LinearSOS g) : LinearSOS (f + g) := by
  obtain ⟨L, hL, eL⟩ := hf
  obtain ⟨M, hM, eM⟩ := hg
  exact ⟨L ++ M, by
    intro f hf
    rcases List.mem_append.mp hf with h | h
    · exact hL f h
    · exact hM f h, by simp [eL, eM]⟩
private lemma linearSOS_term {σ : Type*} (c : ℝ) (hc : 0 ≤ c)
    (f : MvPolynomial σ ℝ) (hf : f.IsHomogeneous 1) : LinearSOS (C c * f ^ 2) := by
  refine ⟨[C (Real.sqrt c) * f], ?_, ?_⟩
  · simpa using hf.C_mul (Real.sqrt c)
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [mul_pow, ← map_pow, Real.sq_sqrt hc]
private lemma linearSOS_sum {σ ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ ℝ) (hf : ∀ i ∈ s, LinearSOS (f i)) :
    LinearSOS (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using linearSOS_zero
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact linearSOS_add (hf i (mem_insert_self _ _))
      (ih fun j hj => hf j (mem_insert_of_mem hj))
private lemma lorentz_linearSOS {σ ι : Type*} [Fintype ι]
    (a : ℝ) (w : ι → ℝ) (ha : Real.sqrt (∑ i, w i ^ 2) ≤ a)
    (t : MvPolynomial σ ℝ) (z : ι → MvPolynomial σ ℝ)
    (ht : t.IsHomogeneous 1) (hz : ∀ i, (z i).IsHomogeneous 1) :
    LinearSOS (C a * (t ^ 2 + ∑ i, z i ^ 2) +
      ∑ i, 2 * C (w i) * t * z i) := by
  classical
  have hw0 : 0 ≤ ∑ i, w i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have ha0 : 0 ≤ a := (Real.sqrt_nonneg _).trans ha
  have hwa : (∑ i, w i ^ 2) ≤ a ^ 2 := by
    nlinarith [Real.sq_sqrt hw0, Real.sqrt_nonneg (∑ i, w i ^ 2)]
  by_cases hzero : a = 0
  · have hw (i : ι) : w i = 0 := by
      have hi : w i ^ 2 ≤ ∑ j, w j ^ 2 := single_le_sum (fun j _ => sq_nonneg (w j)) (mem_univ i)
      rw [hzero] at hwa
      nlinarith [sq_nonneg (w i)]
    simpa [hzero, hw] using (linearSOS_zero (σ := σ))
  · have ha' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
    have hc : 0 ≤ (a ^ 2 - ∑ i, w i ^ 2) / a := div_nonneg (sub_nonneg.mpr hwa) ha0
    have hfirst : LinearSOS (∑ i, C (1 / a) * (C a * z i + C (w i) * t) ^ 2) :=
      linearSOS_sum univ _ (fun i _ => linearSOS_term _ (by positivity) _
        ((hz i).C_mul a |>.add (ht.C_mul (w i))))
    have hlast := linearSOS_term ((a ^ 2 - ∑ i, w i ^ 2) / a) hc t ht
    have hid (i : ι) :
        C (1 / a) * (C a * z i + C (w i) * t) ^ 2 =
          C a * z i ^ 2 + 2 * C (w i) * t * z i + C (w i ^ 2 / a) * t ^ 2 := by
      have he : C (1 / a) * C a = (1 : MvPolynomial σ ℝ) := by
        rw [← map_mul, one_div_mul_cancel hzero, map_one]
      simp only [div_eq_mul_inv, map_mul, map_pow, map_one] at *
      linear_combination (z i ^ 2 * C a + 2 * C (w i) * t * z i) * he
    have heq : (∑ i, C (1 / a) * (C a * z i + C (w i) * t) ^ 2) +
        C ((a ^ 2 - ∑ i, w i ^ 2) / a) * t ^ 2 =
        C a * (t ^ 2 + ∑ i, z i ^ 2) + ∑ i, 2 * C (w i) * t * z i := by
      simp_rw [hid, sum_add_distrib]
      rw [← mul_sum, ← sum_mul, ← map_sum]
      have he : (∑ i, w i ^ 2 / a) + (a ^ 2 - ∑ i, w i ^ 2) / a = a := by
        rw [← sum_div]
        field_simp
        ring
      have hep := congrArg (fun c : ℝ => (C c : MvPolynomial σ ℝ) * t ^ 2) he
      simp only [map_add, add_mul] at hep
      linear_combination hep
    rw [← heq]
    exact linearSOS_add hfirst hlast

/-- Pairing a cone vector with the Jordan square is a sum of squares of homogeneous linear polynomials. -/
theorem pullback_eq_sum_sq {p r : ℕ} {k : Fin r → ℕ}
    (u : Idx p r k → ℝ) (hu : u ∈ cone p r k) :
    ∃ L : List (MvPolynomial (Idx p r k) ℝ),
      (∀ ℓ ∈ L, ℓ.IsHomogeneous 1) ∧
      ∑ a, C (u a) * jsq a = (L.map (· ^ 2)).sum := by
  classical
  change LinearSOS _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  apply linearSOS_add
  · apply linearSOS_sum
    intro i _
    exact linearSOS_term _ (hu.1 i) _ (isHomogeneous_X _ _)
  · apply linearSOS_sum
    intro j _
    rw [Fintype.sum_option]
    have H := lorentz_linearSOS (σ := Idx p r k) (u (Sum.inr ⟨j, none⟩))
      (fun i => u (Sum.inr ⟨j, some i⟩)) (hu.2 j)
      (X (Sum.inr ⟨j, none⟩)) (fun i => X (Sum.inr ⟨j, some i⟩))
      (isHomogeneous_X _ _) (fun i => isHomogeneous_X _ _)
    convert H using 1
    simp only [jsq, Fintype.sum_option]
    congr 1
    apply sum_congr rfl
    intro i _
    ring

end D5.S3.QuadraticForms.ConicGDNN.Lorentz
