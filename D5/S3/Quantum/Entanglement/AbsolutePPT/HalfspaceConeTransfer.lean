/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Nonnegative halfspace combinations reduce to signed two-generator cancellations. -/

/-
proof_shape: halfspace_transfer: content
escape_witness: halfspace_transfer; the explicit positive-negative mass decomposition
  reconstructs the given combination using two-generator cancellation terms.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
open Finset

theorem halfspace_transfer {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]
    (Good : E → Prop) (hzero : Good 0)
    (hadd : ∀ u v, Good u → Good v → Good (u+v))
    (hsmul : ∀ (t : ℝ) u, 0 ≤ t → Good u → Good (t • u))
    (v : I → E) (a x : I → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ha : 0 ≤ ∑ i, x i * a i)
    (hpos : ∀ i, 0 ≤ a i → Good (v i))
    (hpair : ∀ i j, 0 < a i → a j < 0 → Good ((-a j) • v i + a i • v j)) :
    Good (∑ i, x i • v i) := by
  have sum_mem_of_closed
      (Good : E → Prop) (hzero : Good 0) (hadd : ∀ u v, Good u → Good v → Good (u+v))
      (s : Finset I) (f : I → E) (hf : ∀ i ∈ s, Good (f i)) : Good (∑ i ∈ s, f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert i s hi ih =>
      rw [sum_insert hi]
      exact hadd _ _ (hf i (mem_insert_self _ _)) (ih (fun j hj => hf j (mem_insert_of_mem hj)))

  classical
  let p := univ.filter (fun i => 0 < a i)
  let n := univ.filter (fun i => a i < 0)
  let z := univ.filter (fun i => a i = 0)
  let A := ∑ i ∈ p, x i * a i
  let B := ∑ i ∈ n, x i * (-a i)
  have hp (i) (hi : i ∈ p) : 0 < a i := (mem_filter.mp hi).2
  have hn (i) (hi : i ∈ n) : a i < 0 := (mem_filter.mp hi).2
  have hz (i) (hi : i ∈ z) : a i = 0 := (mem_filter.mp hi).2
  have splitR (f : I → ℝ) :
      ∑ i, f i = (∑ i ∈ p, f i) + (∑ i ∈ n, f i) + ∑ i ∈ z, f i := by
    simp only [p,n,z,sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rcases lt_trichotomy (a i) 0 with h|h|h
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
    · simp [h]
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_gt h]
  have splitE (f : I → E) :
      ∑ i, f i = (∑ i ∈ p, f i) + (∑ i ∈ n, f i) + ∑ i ∈ z, f i := by
    simp only [p,n,z,sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rcases lt_trichotomy (a i) 0 with h|h|h
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
    · simp [h]
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_gt h]
  have hAB : B ≤ A := by
    rw [splitR (fun i => x i * a i)] at ha
    have hz0 : (∑ i ∈ z, x i * a i) = 0 := sum_eq_zero (fun i hi => by rw [hz i hi,mul_zero])
    have hB : (∑ i ∈ n, x i * a i) = -B := by simp [B, mul_neg, sum_neg_distrib]
    rw [hz0,hB] at ha
    dsimp only [A]
    linarith
  have hA : 0 ≤ A := sum_nonneg (fun i hi => mul_nonneg (hx i) (le_of_lt (hp i hi)))
  have hB : 0 ≤ B := sum_nonneg (fun i hi => mul_nonneg (hx i) (neg_nonneg.mpr (le_of_lt (hn i hi))))
  have gz : Good (∑ i ∈ z, x i • v i) :=
    sum_mem_of_closed Good hzero hadd z _ (fun i hi => hsmul _ _ (hx i) (hpos i (le_of_eq (hz i hi).symm)))
  by_cases hAz : A = 0
  · have hBz : B = 0 := le_antisymm (by simpa [hAz] using hAB) hB
    have hnx : ∀ i ∈ n, x i = 0 := by
      intro i hi
      have ht : x i * (-a i) = 0 := (sum_eq_zero_iff_of_nonneg (fun j hj => mul_nonneg (hx j) (neg_nonneg.mpr (le_of_lt (hn j hj))))).mp hBz i hi
      exact (mul_eq_zero.mp ht).resolve_right (ne_of_gt (neg_pos.mpr (hn i hi)))
    rw [splitE (fun i => x i • v i)]
    have he : (∑ i ∈ n, x i • v i) = 0 := sum_eq_zero (fun i hi => by rw [hnx i hi,zero_smul])
    rw [he,add_zero]
    apply hadd _ _ _ gz
    exact sum_mem_of_closed Good hzero hadd p _ (fun i hi => hsmul _ _ (hx i) (hpos i (le_of_lt (hp i hi))))
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hres : 0 ≤ 1-B/A := by apply sub_nonneg.mpr; exact (div_le_one hAp).mpr hAB
    have gp : Good ((1-B/A) • (∑ i ∈ p, x i • v i)) := by
      apply hsmul _ _ hres
      exact sum_mem_of_closed Good hzero hadd p _ (fun i hi => hsmul _ _ (hx i) (hpos i (le_of_lt (hp i hi))))
    have gpair : Good (∑ i ∈ p, ∑ j ∈ n, (x i*x j/A) • ((-a j) • v i+a i • v j)) := by
      apply sum_mem_of_closed Good hzero hadd p
      intro i hi
      apply sum_mem_of_closed Good hzero hadd n
      intro j hj
      exact hsmul _ _ (div_nonneg (mul_nonneg (hx i) (hx j)) hA) (hpair i j (hp i hi) (hn j hj))
    have he : (∑ i ∈ p, ∑ j ∈ n, (x i*x j/A) • ((-a j) • v i+a i • v j)) =
        (B/A) • (∑ i ∈ p, x i • v i) + ∑ j ∈ n, x j • v j := by
      simp only [smul_add,smul_smul,sum_add_distrib]
      congr 1
      · simp_rw [show ∀ i j, (x i*x j/A)*(-a j) = (x i/A)*(x j*(-a j)) from fun i j => by ring]
        simp_rw [← sum_smul,← mul_sum]
        rw [smul_sum]
        apply sum_congr rfl
        intro i _
        rw [smul_smul]
        congr 1
        dsimp only [B]
        ring
      · rw [sum_comm]
        apply sum_congr rfl
        intro j _
        simp_rw [show ∀ i, (x i*x j/A)*a i = (x j/A)*(x i*a i) from fun i => by ring]
        rw [← sum_smul,← mul_sum]
        change ((x j/A)*A) • v j = x j • v j
        rw [div_mul_cancel₀ _ hAz]
    rw [he] at gpair
    have gf := hadd _ _ (hadd _ _ gp gpair) gz
    have eq : (1-B/A) • (∑ i ∈ p, x i • v i) +
        ((B/A) • (∑ i ∈ p, x i • v i) + ∑ j ∈ n, x j • v j) + ∑ i ∈ z, x i • v i = ∑ i, x i • v i := by
      rw [← add_assoc,← add_smul]
      simp only [sub_add_cancel,one_smul]
      exact (splitE _).symm
    rwa [eq] at gf

#print axioms halfspace_transfer
end D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
