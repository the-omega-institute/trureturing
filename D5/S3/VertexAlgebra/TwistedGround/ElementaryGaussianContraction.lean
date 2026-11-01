/- GID: D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite factorial contraction of Gaussian kernels with zero shared diagonal. -/

import D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment
import Mathlib.Algebra.BigOperators.Finprod

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction

open NativeGaussianMoment (nativeMoment nativeMoment_step sub_single_degree occupation_nonzero)
open FactorialFockQuadraticEstimate (gaussianCoefficient gaussianCoefficient_zero)
open FactorialFockMetric (weight weight_pos weight_add_single)

universe u v w
variable {I : Type u} {J : Type v} {E : Type w}
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [Fintype E] [DecidableEq E]

private theorem join_add_left (d : I →₀ ℕ) (n : J →₀ ℕ) (i : I) :
    (d + Finsupp.single i 1).sumElim n =
      d.sumElim n + Finsupp.single (.inl i) 1 := by
  ext (a | a) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]

private theorem join_add_right (d : I →₀ ℕ) (n : J →₀ ℕ) (a : J) :
    d.sumElim (n + Finsupp.single a 1) =
      d.sumElim n + Finsupp.single (.inr a) 1 := by
  ext (b | b) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]

private theorem join_sub_left (d : I →₀ ℕ) (n : J →₀ ℕ) (i : I) :
    d.sumElim n - Finsupp.single (.inl i) 1 =
      (d - Finsupp.single i 1).sumElim n := by
  ext (a | a) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]

private theorem join_sub_right (d : I →₀ ℕ) (n : J →₀ ℕ) (a : J) :
    d.sumElim n - Finsupp.single (.inr a) 1 =
      d.sumElim (n - Finsupp.single a 1) := by
  ext (b | b) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]

private theorem step_left (A : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (n : J →₀ ℕ) (i : I) :
    nativeMoment A ((d + Finsupp.single i 1).sumElim n) =
      (∑ k, (d k : ℂ) * A (.inl i) (.inl k) *
        nativeMoment A ((d - Finsupp.single k 1).sumElim n)) +
      ∑ a, (n a : ℂ) * A (.inl i) (.inr a) *
        nativeMoment A (d.sumElim (n - Finsupp.single a 1)) := by
  rw [join_add_left, nativeMoment_step A hs, Fintype.sum_sum_type]
  simp only [Finsupp.sumElim_inl, Finsupp.sumElim_inr, join_sub_left, join_sub_right]

private theorem step_right (A : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (n : J →₀ ℕ) (a : J) :
    nativeMoment A (d.sumElim (n + Finsupp.single a 1)) =
      (∑ i, (d i : ℂ) * A (.inr a) (.inl i) *
        nativeMoment A ((d - Finsupp.single i 1).sumElim n)) +
      ∑ b, (n b : ℂ) * A (.inr a) (.inr b) *
        nativeMoment A (d.sumElim (n - Finsupp.single b 1)) := by
  rw [join_add_right, nativeMoment_step A hs, Fintype.sum_sum_type]
  simp only [Finsupp.sumElim_inl, Finsupp.sumElim_inr, join_sub_left, join_sub_right]

/-- Each shared occurrence must pair with an external occurrence. The proof
uses the shared insertion equation, including zero external dimension. -/
private theorem shared_support (M : (I →₀ ℕ) → (J →₀ ℕ) → ℂ)
    (T : Matrix I J ℂ)
    (hstep : ∀ d n a, M d (n + Finsupp.single a 1) =
      ∑ i, (d i : ℂ) * T i a * M (d - Finsupp.single i 1) n)
    (d : I →₀ ℕ) (n : J →₀ ℕ) (h : d.degree < n.degree) : M d n = 0 := by
  have go : ∀ k (d : I →₀ ℕ), d.degree = k →
      ∀ n : J →₀ ℕ, k < n.degree → M d n = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hd n hn
      have hn0 : n ≠ 0 := by intro hz; subst n; simp at hn
      obtain ⟨a, ha⟩ := occupation_nonzero n hn0
      let r := n - Finsupp.single a 1
      have hr : r + Finsupp.single a 1 = n := Finsupp.sub_add_single_one_cancel ha
      have hrd : r.degree + 1 = n.degree := sub_single_degree n a ha
      rw [← hr, hstep]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hz : d i = 0
      · simp [hz]
      · have hdd := sub_single_degree d i hz
        rw [ih _ (by omega) _ rfl r (by omega), mul_zero]
  exact go d.degree d rfl n h

private theorem support_finite (f : (J →₀ ℕ) → ℂ) (N : ℕ)
    (h : ∀ n, N < n.degree → f n = 0) : Function.HasFiniteSupport f := by
  apply (Finsupp.finite_of_degree_le N).subset
  intro n hn
  by_contra hh
  exact hn (h n (Nat.lt_of_not_ge hh))

private theorem weight_join (d : I →₀ ℕ) (n : J →₀ ℕ) :
    weight (d.sumElim n) = weight d * weight n := by
  exact Finsupp.prod_sumElim d n (fun _ k => k.factorial)

private theorem moment_zero (A : Matrix I I ℂ) : nativeMoment A 0 = 1 := by
  simp [nativeMoment, gaussianCoefficient_zero, weight]

/-- The first elementary kernel has no shared/shared quadratic term. -/
def leftKernel (P : Matrix I I ℂ) (R : Matrix I J ℂ) :
    Matrix (I ⊕ J) (I ⊕ J) ℂ := Matrix.fromBlocks P R R.transpose 0

/-- The second elementary kernel has no shared/shared quadratic term. -/
def rightKernel (Q : Matrix E E ℂ) (S : Matrix J E ℂ) :
    Matrix (J ⊕ E) (J ⊕ E) ℂ := Matrix.fromBlocks 0 S S.transpose Q

/-- Bilinear composition: transpose, never conjugate transpose. -/
def effectiveKernel (P : Matrix I I ℂ) (Q : Matrix E E ℂ)
    (R : Matrix I J ℂ) (S : Matrix J E ℂ) :
    Matrix (I ⊕ E) (I ⊕ E) ℂ := Matrix.fromBlocks P (R * S) (R * S).transpose Q

private theorem left_symm (P : Matrix I I ℂ) (R : Matrix I J ℂ)
    (hP : ∀ i k, P i k = P k i) :
    ∀ i k, leftKernel P R i k = leftKernel P R k i := by
  intro i k
  cases i <;> cases k <;> simp [leftKernel, Matrix.transpose_apply, hP]

private theorem right_symm (Q : Matrix E E ℂ) (S : Matrix J E ℂ)
    (hQ : ∀ j k, Q j k = Q k j) :
    ∀ i k, rightKernel Q S i k = rightKernel Q S k i := by
  intro i k
  cases i <;> cases k <;> simp [rightKernel, Matrix.transpose_apply, hQ]

private theorem effective_symm (P : Matrix I I ℂ) (Q : Matrix E E ℂ)
    (R : Matrix I J ℂ) (S : Matrix J E ℂ)
    (hP : ∀ i k, P i k = P k i) (hQ : ∀ j k, Q j k = Q k j) :
    ∀ i k, effectiveKernel P Q R S i k = effectiveKernel P Q R S k i := by
  intro i k
  cases i <;> cases k
  · exact hP _ _
  · rfl
  · rfl
  · exact hQ _ _

private theorem left_shared_step (P : Matrix I I ℂ) (R : Matrix I J ℂ)
    (hP : ∀ i k, P i k = P k i) (d : I →₀ ℕ) (n : J →₀ ℕ) (a : J) :
    nativeMoment (leftKernel P R) (d.sumElim (n + Finsupp.single a 1)) =
      ∑ i, (d i : ℂ) * R i a *
        nativeMoment (leftKernel P R) ((d - Finsupp.single i 1).sumElim n) := by
  simpa [leftKernel, Matrix.transpose_apply] using
    step_right (leftKernel P R) (left_symm P R hP) d n a

private theorem right_shared_step (Q : Matrix E E ℂ) (S : Matrix J E ℂ)
    (hQ : ∀ j k, Q j k = Q k j) (e : E →₀ ℕ) (n : J →₀ ℕ) (a : J) :
    nativeMoment (rightKernel Q S) ((n + Finsupp.single a 1).sumElim e) =
      ∑ j, (e j : ℂ) * S a j *
        nativeMoment (rightKernel Q S) (n.sumElim (e - Finsupp.single j 1)) := by
  simpa [rightKernel] using
    step_left (rightKernel Q S) (right_symm Q S hQ) n e a

private theorem left_vanish (P : Matrix I I ℂ) (R : Matrix I J ℂ)
    (hP : ∀ i k, P i k = P k i) (d : I →₀ ℕ) (n : J →₀ ℕ)
    (h : d.degree < n.degree) :
    nativeMoment (leftKernel P R) (d.sumElim n) = 0 :=
  shared_support (fun d n => nativeMoment (leftKernel P R) (d.sumElim n))
    R (left_shared_step P R hP) d n h

private theorem right_vanish (Q : Matrix E E ℂ) (S : Matrix J E ℂ)
    (hQ : ∀ j k, Q j k = Q k j) (n : J →₀ ℕ) (e : E →₀ ℕ)
    (h : e.degree < n.degree) :
    nativeMoment (rightKernel Q S) (n.sumElim e) = 0 :=
  shared_support (fun e n => nativeMoment (rightKernel Q S) (n.sumElim e))
    S.transpose (right_shared_step Q S hQ) e n h

private theorem weighted_shift (f g : (J →₀ ℕ) → ℂ) (a : J) :
    (∑ᶠ n, (n a : ℂ) * f (n - Finsupp.single a 1) * g n / (weight n : ℂ)) =
      ∑ᶠ m, f m * g (m + Finsupp.single a 1) / (weight m : ℂ) := by
  classical
  let h := fun n : J →₀ ℕ =>
    (n a : ℂ) * f (n - Finsupp.single a 1) * g n / (weight n : ℂ)
  have hinj : Function.Injective (fun m : J →₀ ℕ => m + Finsupp.single a 1) :=
    fun _ _ he => add_right_cancel he
  have hr : ∀ n ∈ Function.support h,
      n ∈ Set.range (fun m : J →₀ ℕ => m + Finsupp.single a 1) := by
    intro n hn
    have hn0 : n a ≠ 0 := by
      intro hz
      exact hn (by simp [h, hz])
    exact ⟨n - Finsupp.single a 1, Finsupp.sub_add_single_one_cancel hn0⟩
  calc
    _ = ∑ᶠ n ∈ Set.range (fun m : J →₀ ℕ => m + Finsupp.single a 1), h n := by
      rw [← finsum_mem_univ h]
      exact finsum_mem_inter_support_eq' h _ _ (fun n hn => by simp [hr n hn])
    _ = ∑ᶠ m, h (m + Finsupp.single a 1) := finsum_mem_range hinj
    _ = _ := by
      apply finsum_congr
      intro m
      have hw : (weight m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (weight_pos m))
      have ha : (m a : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (m a))
      simp only [h, Finsupp.add_apply, Finsupp.single_eq_same,
        add_tsub_cancel_right, weight_add_single, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp

private def pairing (F : (I →₀ ℕ) → (J →₀ ℕ) → ℂ)
    (G : (J →₀ ℕ) → (E →₀ ℕ) → ℂ) (d : I →₀ ℕ) (e : E →₀ ℕ) : ℂ :=
  ∑ᶠ n, F d n * G n e / (weight n : ℂ)

private theorem pairing_step
    (F : (I →₀ ℕ) → (J →₀ ℕ) → ℂ)
    (G : (J →₀ ℕ) → (E →₀ ℕ) → ℂ)
    (P : Matrix I I ℂ) (R : Matrix I J ℂ) (S : Matrix J E ℂ)
    (hf : ∀ d n, d.degree < n.degree → F d n = 0)
    (hF : ∀ d n i, F (d + Finsupp.single i 1) n =
      (∑ k, (d k : ℂ) * P i k * F (d - Finsupp.single k 1) n) +
      ∑ a, (n a : ℂ) * R i a * F d (n - Finsupp.single a 1))
    (hG : ∀ n e a, G (n + Finsupp.single a 1) e =
      ∑ j, (e j : ℂ) * S a j * G n (e - Finsupp.single j 1))
    (d : I →₀ ℕ) (e : E →₀ ℕ) (i : I) :
    pairing F G (d + Finsupp.single i 1) e =
      (∑ k, (d k : ℂ) * P i k * pairing F G (d - Finsupp.single k 1) e) +
      ∑ j, (e j : ℂ) * (R * S) i j * pairing F G d (e - Finsupp.single j 1) := by
  classical
  have hsub (k : I) : (d - Finsupp.single k 1).degree ≤ d.degree :=
    Finsupp.degree_mono (tsub_le_self)
  have hfin₁ (k : I) : Function.HasFiniteSupport (fun n : J →₀ ℕ =>
      (d k : ℂ) * P i k * F (d - Finsupp.single k 1) n * G n e / (weight n : ℂ)) :=
    support_finite _ d.degree (fun n hn => by rw [hf _ _ (lt_of_le_of_lt (hsub k) hn)]; simp)
  have hfin₂ (a : J) : Function.HasFiniteSupport (fun n : J →₀ ℕ =>
      (n a : ℂ) * R i a * F d (n - Finsupp.single a 1) * G n e / (weight n : ℂ)) := by
    apply support_finite _ (d.degree + 1)
    intro n hn
    by_cases hz : n a = 0
    · simp [hz]
    · have hd := sub_single_degree n a hz
      rw [hf _ _ (by omega)]
      simp
  have hsum₁ : Function.HasFiniteSupport (fun n : J →₀ ℕ =>
      ∑ k, (d k : ℂ) * P i k * F (d - Finsupp.single k 1) n * G n e / (weight n : ℂ)) := by
    apply support_finite _ d.degree
    intro n hn
    apply Finset.sum_eq_zero
    intro k hk
    rw [hf _ _ (lt_of_le_of_lt (hsub k) hn)]
    simp
  have hsum₂ : Function.HasFiniteSupport (fun n : J →₀ ℕ =>
      ∑ a, (n a : ℂ) * R i a * F d (n - Finsupp.single a 1) * G n e / (weight n : ℂ)) := by
    apply support_finite _ (d.degree + 1)
    intro n hn
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hz : n a = 0
    · simp [hz]
    · have hd := sub_single_degree n a hz
      rw [hf _ _ (by omega)]
      simp
  have hsep : pairing F G (d + Finsupp.single i 1) e =
      (∑ k, (d k : ℂ) * P i k * pairing F G (d - Finsupp.single k 1) e) +
      ∑ a, R i a * ∑ᶠ n, (n a : ℂ) * F d (n - Finsupp.single a 1) *
        G n e / (weight n : ℂ) := by
    unfold pairing
    simp_rw [hF, add_mul, add_div, Finset.sum_mul, Finset.sum_div]
    rw [finsum_add_distrib hsum₁ hsum₂,
      finsum_sum_comm _ _ (fun k _ => hfin₁ k),
      finsum_sum_comm _ _ (fun a _ => hfin₂ a)]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [mul_finsum]
      apply finsum_congr
      intro n
      ring
    · apply Finset.sum_congr rfl
      intro a ha
      rw [mul_finsum]
      apply finsum_congr
      intro n
      ring
  rw [hsep]
  congr 1
  simp_rw [weighted_shift, hG, Finset.mul_sum, Finset.sum_div]
  have hfin₃ (a : J) (j : E) : Function.HasFiniteSupport (fun n : J →₀ ℕ =>
      F d n * ((e j : ℂ) * S a j * G n (e - Finsupp.single j 1)) / (weight n : ℂ)) :=
    support_finite _ d.degree (fun n hn => by rw [hf _ _ hn]; simp)
  simp_rw [finsum_sum_comm _ _ (fun j _ => hfin₃ _ j), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  unfold pairing
  simp_rw [mul_finsum]
  apply finsum_congr
  intro n
  ring

private theorem right_boundary
    (A : Matrix (I ⊕ E) (I ⊕ E) ℂ) (B : Matrix (J ⊕ E) (J ⊕ E) ℂ)
    (hA : ∀ i k, A i k = A k i) (hB : ∀ i k, B i k = B k i)
    (hAB : ∀ j k, A (.inr j) (.inr k) = B (.inr j) (.inr k)) (e : E →₀ ℕ) :
    nativeMoment A ((0 : I →₀ ℕ).sumElim e) =
      nativeMoment B ((0 : J →₀ ℕ).sumElim e) := by
  have go : ∀ k (e : E →₀ ℕ), e.degree = k →
      nativeMoment A ((0 : I →₀ ℕ).sumElim e) =
        nativeMoment B ((0 : J →₀ ℕ).sumElim e) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he
      by_cases hz : e = 0
      · subst e
        simp [moment_zero]
      obtain ⟨j, hj⟩ := occupation_nonzero e hz
      let r := e - Finsupp.single j 1
      have hr : r + Finsupp.single j 1 = e := Finsupp.sub_add_single_one_cancel hj
      have hd : r.degree + 1 = k := (sub_single_degree e j hj).trans he
      rw [← hr, step_right A hA, step_right B hB]
      simp only [Finsupp.zero_apply, Nat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
      apply Finset.sum_congr rfl
      intro l hl
      rw [hAB, ih _ (by
        have hh : (r - Finsupp.single l 1).degree ≤ r.degree :=
          Finsupp.degree_mono tsub_le_self
        omega) _ rfl]
  exact go e.degree e rfl

private theorem moment_contraction (P : Matrix I I ℂ) (Q : Matrix E E ℂ)
    (R : Matrix I J ℂ) (S : Matrix J E ℂ)
    (hP : ∀ i k, P i k = P k i) (hQ : ∀ j k, Q j k = Q k j)
    (d : I →₀ ℕ) (e : E →₀ ℕ) :
    pairing (fun d n => nativeMoment (leftKernel P R) (d.sumElim n))
      (fun n e => nativeMoment (rightKernel Q S) (n.sumElim e)) d e =
      nativeMoment (effectiveKernel P Q R S) (d.sumElim e) := by
  let F := fun (d : I →₀ ℕ) (n : J →₀ ℕ) => nativeMoment (leftKernel P R) (d.sumElim n)
  let G := fun (n : J →₀ ℕ) (e : E →₀ ℕ) => nativeMoment (rightKernel Q S) (n.sumElim e)
  have hF : ∀ d n i, F (d + Finsupp.single i 1) n =
      (∑ k, (d k : ℂ) * P i k * F (d - Finsupp.single k 1) n) +
      ∑ a, (n a : ℂ) * R i a * F d (n - Finsupp.single a 1) := by
    intro d n i
    exact step_left (leftKernel P R) (left_symm P R hP) d n i
  have hG : ∀ n e a, G (n + Finsupp.single a 1) e =
      ∑ j, (e j : ℂ) * S a j * G n (e - Finsupp.single j 1) := by
    intro n e a
    exact right_shared_step Q S hQ e n a
  have hf : ∀ d n, d.degree < n.degree → F d n = 0 := left_vanish P R hP
  have go : ∀ k (d : I →₀ ℕ), d.degree = k → ∀ e : E →₀ ℕ,
      pairing F G d e = nativeMoment (effectiveKernel P Q R S) (d.sumElim e) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hd e
      by_cases hz : d = 0
      · subst d
        unfold pairing
        rw [finsum_eq_single _ (0 : J →₀ ℕ) (by
          intro n hn
          have hn0 : 0 < n.degree := Nat.pos_of_ne_zero (by
            intro he
            exact hn ((Finsupp.degree_eq_zero_iff n).mp he))
          rw [hf 0 n (by simpa using hn0)]
          simp)]
        have hb := right_boundary (effectiveKernel P Q R S) (rightKernel Q S)
          (effective_symm P Q R S hP hQ) (right_symm Q S hQ) (by intros; rfl) e
        simpa [F, G, moment_zero, weight] using hb.symm
      obtain ⟨i, hi⟩ := occupation_nonzero d hz
      let r := d - Finsupp.single i 1
      have hr : r + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
      have hrd : r.degree + 1 = k := (sub_single_degree d i hi).trans hd
      rw [← hr, pairing_step F G P R S hf hF hG,
        step_left _ (effective_symm P Q R S hP hQ)]
      change (∑ l, (r l : ℂ) * P i l * pairing F G (r - Finsupp.single l 1) e) +
        (∑ j, (e j : ℂ) * (R * S) i j * pairing F G r (e - Finsupp.single j 1)) = _
      congr 1
      · apply Finset.sum_congr rfl
        intro l hl
        rw [ih _ (by
          have hh : (r - Finsupp.single l 1).degree ≤ r.degree :=
            Finsupp.degree_mono tsub_le_self
          omega) _ rfl]
        rfl
      · apply Finset.sum_congr rfl
        intro j hj
        rw [ih _ (by omega) _ rfl]
        rfl
  exact go d.degree d rfl e

/-- Exact support for the summand in elementary Gaussian sewing. Shared
occupation degree is bounded by both external occupation degrees. -/
private theorem coefficient_support (P : Matrix I I ℂ) (Q : Matrix E E ℂ)
    (R : Matrix I J ℂ) (S : Matrix J E ℂ)
    (hP : ∀ i k, P i k = P k i) (hQ : ∀ j k, Q j k = Q k j)
    (d : I →₀ ℕ) (e : E →₀ ℕ) (n : J →₀ ℕ)
    (hn : min d.degree e.degree < n.degree) :
    (weight n : ℂ) * gaussianCoefficient (leftKernel P R) (d.sumElim n) *
      gaussianCoefficient (rightKernel Q S) (n.sumElim e) = 0 := by
  have hw (r : I ⊕ J →₀ ℕ) : (weight r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (weight_pos r))
  have hw' (r : J ⊕ E →₀ ℕ) : (weight r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (weight_pos r))
  by_cases hd : d.degree < n.degree
  · have hz := left_vanish P R hP d n hd
    have hc := (mul_eq_zero.mp hz).resolve_left (hw (d.sumElim n))
    simp [hc]
  · have he : e.degree < n.degree := by omega
    have hz := right_vanish Q S hQ n e he
    have hc := (mul_eq_zero.mp hz).resolve_left (hw' (n.sumElim e))
    simp [hc]

/-- Finite, native factorial Gaussian contraction. P and Q are arbitrary
complex symmetric matrices; R and S are arbitrary compatible matrices.
All finite mode types, including empty types, are admitted. -/
theorem coefficient_contraction (P : Matrix I I ℂ) (Q : Matrix E E ℂ)
    (R : Matrix I J ℂ) (S : Matrix J E ℂ)
    (hP : ∀ i k, P i k = P k i) (hQ : ∀ j k, Q j k = Q k j)
    (d : I →₀ ℕ) (e : E →₀ ℕ) :
    (∑ n ∈ (Finsupp.finite_of_degree_le (σ := J) (min d.degree e.degree)).toFinset,
      (weight n : ℂ) * gaussianCoefficient (leftKernel P R) (d.sumElim n) *
        gaussianCoefficient (rightKernel Q S) (n.sumElim e)) =
      gaussianCoefficient (effectiveKernel P Q R S) (d.sumElim e) := by
  classical
  let c := fun n : J →₀ ℕ =>
    (weight n : ℂ) * gaussianCoefficient (leftKernel P R) (d.sumElim n) *
      gaussianCoefficient (rightKernel Q S) (n.sumElim e)
  have heq : (∑ᶠ n, c n) =
      ∑ n ∈ (Finsupp.finite_of_degree_le (σ := J) (min d.degree e.degree)).toFinset,
        c n := by
    apply finsum_eq_sum_of_support_subset_of_finite c _
      (Finsupp.finite_of_degree_le (σ := J) (min d.degree e.degree))
    intro n hn
    by_contra hh
    exact hn (coefficient_support P Q R S hP hQ d e n (Nat.lt_of_not_ge hh))
  rw [← heq]
  have hw (r : I →₀ ℕ) : (weight r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (weight_pos r))
  have hw' (r : E →₀ ℕ) : (weight r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (weight_pos r))
  apply mul_left_cancel₀ (mul_ne_zero (hw d) (hw' e))
  have h := moment_contraction P Q R S hP hQ d e
  rw [nativeMoment, weight_join, Nat.cast_mul] at h
  rw [← h, mul_finsum]
  unfold pairing
  apply finsum_congr
  intro n
  have hwn : (weight n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (weight_pos n))
  simp only [c, nativeMoment, weight_join, Nat.cast_mul]
  field_simp

end D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
