/- GID: D5/S3/Quantum/Algebra/Knot/WeightedPathReverseTemperleyLieb
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Endpoint reversal of actual weighted path kernels yields the reverse adjacent Temperley-Lieb law. -/

import D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Reverse every coordinate of a legal path and exchange its two endpoints. -/
def reversePath (R : L → L → Prop) (hR : Std.Symm R)
    (n : ℕ) (s t : L) (x : LegalPath R n s t) : LegalPath R n t s := by
  refine ⟨fun k => x.1 k.rev, ?_, ?_, ?_⟩
  · simpa only [Fin.rev_zero] using x.2.2.1
  · simpa only [Fin.rev_last] using x.2.1
  · intro k
    simpa only [Fin.rev_castSucc, Fin.rev_succ] using
      hR.symm _ _ (x.2.2.2 k.rev)

/-- Literal coordinate reversal is an equivalence between opposite-endpoint fibers. -/
def reverseEquiv (R : L → L → Prop) (hR : Std.Symm R)
    (n : ℕ) (s t : L) : LegalPath R n s t ≃ LegalPath R n t s where
  toFun := reversePath R hR n s t
  invFun := reversePath R hR n t s
  left_inv x := by
    apply Subtype.ext
    funext k
    simp only [reversePath, Fin.rev_rev]
  right_inv x := by
    apply Subtype.ext
    funext k
    simp only [reversePath, Fin.rev_rev]

/-- Reversal transports the literal local kernel from index n-i to i.
The common-flank support, not any extra symmetry of weights, transports its denominator. -/
private theorem reverse_kernel
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (δ : ℝ) (n : ℕ) (s t : L)
    (i : ℕ) (hi : 0 < i ∧ i < n) :
    (pathProjection R d δ n t s (n-i) ⟨by omega, by omega⟩).submatrix
      (reverseEquiv R hR n s t) (reverseEquiv R hR n s t) =
      pathProjection R d δ n s t i hi := by
  classical
  ext x y
  have hc : (⟨n-i, by omega⟩ : Fin (n+1)).rev = ⟨i, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_mk]
    omega
  have hp : (⟨n-i-1, by omega⟩ : Fin (n+1)).rev = ⟨i+1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_mk]
    omega
  have hn : (⟨n-i+1, by omega⟩ : Fin (n+1)).rev = ⟨i-1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_mk]
    omega
  have haway : (∀ k : Fin (n+1), k.val ≠ n-i → x.1 k.rev = y.1 k.rev) ↔
      (∀ k : Fin (n+1), k.val ≠ i → x.1 k = y.1 k) := by
    constructor
    · intro h k hk
      have hr : k.rev.val ≠ n-i := by
        simp only [Fin.val_rev]
        have := k.is_lt
        omega
      simpa only [Fin.rev_rev] using h k.rev hr
    · intro h k hk
      apply h k.rev
      simp only [Fin.val_rev]
      have := k.is_lt
      omega
  change pathProjection R d δ n t s (n-i) ⟨by omega, by omega⟩
      (reversePath R hR n s t x) (reversePath R hR n s t y) = _
  unfold pathProjection
  simp only [reversePath, hc, hp, hn, haway]
  by_cases ha : ∀ k : Fin (n+1), k.val ≠ i → x.1 k = y.1 k
  · by_cases hf : x.1 ⟨i-1, by omega⟩ = x.1 ⟨i+1, by omega⟩
    · have hguard : (∀ k : Fin (n+1), k.val ≠ i → x.1 k = y.1 k) ∧
          x.1 ⟨i-1, by omega⟩ = x.1 ⟨i+1, by omega⟩ := ⟨ha, hf⟩
      rw [if_pos hguard]
      rw [if_pos ⟨ha, hf.symm⟩]
      rw [hf]
    · have hfn : x.1 ⟨i+1, by omega⟩ ≠ x.1 ⟨i-1, by omega⟩ := Ne.symm hf
      simp only [ha, hf, hfn, and_false, if_false]
  · simp only [ha, false_and, if_false]

/-- The missing reverse adjacent relation for the actual fixed-endpoint weighted legal paths. -/
theorem weighted_path_reverse_temperley_lieb
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a)
    (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (n : ℕ) (s t : L) (i : ℕ) (hi : 0 < i ∧ i+1 < n) :
    pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩ *
        pathProjection R d δ n s t i ⟨hi.1, by omega⟩ *
        pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩ =
      ((δ⁻¹ : ℂ)^2) • pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩ := by
  classical
  let j := n-(i+1)
  have hj : 0 < j ∧ j+1 < n := by dsimp [j]; omega
  have h := (weighted_legal_path_temperley_lieb R hR d hd δ hδ hPF n t s).2.1 j hj
  let e := reverseEquiv R hR n s t
  have transported := congrArg (fun M => M.submatrix e e) h
  rw [show (pathProjection R d δ n t s j ⟨hj.1, by omega⟩ *
      pathProjection R d δ n t s (j+1) ⟨by omega, hj.2⟩ *
      pathProjection R d δ n t s j ⟨hj.1, by omega⟩).submatrix e e =
      (pathProjection R d δ n t s j ⟨hj.1, by omega⟩).submatrix e e *
      (pathProjection R d δ n t s (j+1) ⟨by omega, hj.2⟩).submatrix e e *
      (pathProjection R d δ n t s j ⟨hj.1, by omega⟩).submatrix e e from by
        rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv],
    Matrix.submatrix_smul] at transported
  have hjindex : j = n-(i+1) := rfl
  have hjpindex : j+1 = n-i := by dsimp [j]; omega
  have hfirst : (pathProjection R d δ n t s j ⟨hj.1, by omega⟩).submatrix e e =
      pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩ := by
    simpa only [hjindex] using
      reverse_kernel R hR d δ n s t (i+1) ⟨by omega, hi.2⟩
  have hsecond : (pathProjection R d δ n t s (j+1) ⟨by omega, hj.2⟩).submatrix e e =
      pathProjection R d δ n s t i ⟨hi.1, by omega⟩ := by
    have hh := reverse_kernel R hR d δ n s t i ⟨hi.1, by omega⟩
    have hidxP :
        pathProjection R d δ n t s (j+1) ⟨by omega, hj.2⟩ =
          pathProjection R d δ n t s (n-i) ⟨by omega, by omega⟩ := by
      congr 1
    rw [hidxP]
    simpa only [e] using hh
  have hscalar :
      (((δ⁻¹ : ℂ)^2) • (pathProjection R d δ n t s j ⟨hj.1, by omega⟩).submatrix) e e =
        ((δ⁻¹ : ℂ)^2) • pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩ := by
    ext x y
    change ((δ⁻¹ : ℂ)^2) *
        pathProjection R d δ n t s j ⟨hj.1, by omega⟩ (e x) (e y) =
      ((δ⁻¹ : ℂ)^2) *
        pathProjection R d δ n s t (i+1) ⟨by omega, hi.2⟩ x y
    exact congrArg (fun z : ℂ => ((δ⁻¹ : ℂ)^2) * z)
      (congrFun (congrFun hfirst x) y)
  rw [hfirst, hsecond, hscalar] at transported
  exact transported

#print axioms weighted_path_reverse_temperley_lieb
end D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb
