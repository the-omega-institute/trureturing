/- GID: D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.claim; result=D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.result; claim=D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.claim
   digest: A unique coherence-minimizing dual of the frame (3, 2, 1) is not canonical. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#12319; Refuted)
Direct frozen dependencies: none; pinned Mathlib only.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumBounds.Designs.CrossFrameExclusiveDualRefutation

open scoped BigOperators

/-- The finite real frame inequalities of Definition 1. -/
def IsFrame {n k : ℕ} (F : Fin k → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ x : EuclideanSpace ℝ (Fin n),
    A * ‖x‖ ^ 2 ≤ ∑ i, |inner ℝ x (F i)| ^ 2 ∧
      (∑ i, |inner ℝ x (F i)| ^ 2) ≤ B * ‖x‖ ^ 2

/-- The reconstruction identity `θ_F* θ_G = I`; over the reals its adjoint gives
the other identity in Definition 3. -/
def IsDualFrame {n k : ℕ} (F G : Fin k → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), ∑ i, inner ℝ x (G i) • F i = x

/-- The maximal off-diagonal magnitude of the cross-Gramian. The empty maximum
is zero; nonnegative real norms allow the finite supremum to use this convention. -/
noncomputable def mu {n k : ℕ} (F G : Fin k → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ p.2)).sup
    (fun p => ‖inner ℝ (F p.1) (G p.2)‖₊) : NNReal) : ℝ)

/-- The frame operator `S x = Σ_i ⟪x, F_i⟫ F_i`. -/
noncomputable def frameOperator {n k : ℕ} (F : Fin k → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ i, inner ℝ x (F i) • F i

/-- `S⁻¹ F_i`, using Mathlib's inverse function. For a frame, `S` is invertible. -/
noncomputable def canonicalDual {n k : ℕ} (F : Fin k → EuclideanSpace ℝ (Fin n))
    (i : Fin k) : EuclideanSpace ℝ (Fin n) :=
  Function.invFun (frameOperator F) (F i)

/-- Conjecture 42: a unique minimizing dual must be canonical. -/
def claim : Prop :=
  ∀ n k (F G : Fin k → EuclideanSpace ℝ (Fin n)), n ≤ k →
    IsFrame F → IsDualFrame F G →
    (∀ H, IsDualFrame F H → mu F G ≤ mu F H) →
    (∀ H, IsDualFrame F H → mu F H ≤ mu F G → H = G) →
    G = canonicalDual F

/-- The frame `(3, 2, 1)` has unique minimizing dual `(1/5, 2/15, 2/15)`,
which differs from its canonical dual. -/
theorem result : ¬ claim := by
  classical
  let F : Fin 3 → EuclideanSpace ℝ (Fin 1) :=
    fun i => WithLp.toLp 2 (fun _ => (![3, 2, 1] : Fin 3 → ℝ) i)
  let G : Fin 3 → EuclideanSpace ℝ (Fin 1) :=
    fun i => WithLp.toLp 2 (fun _ => (![1 / 5, 2 / 15, 2 / 15] : Fin 3 → ℝ) i)
  have hframe : IsFrame F := by
    refine ⟨14, 14, by norm_num, le_rfl, ?_⟩
    intro x
    have hn := (real_inner_self_eq_norm_sq x).symm
    rw [PiLp.inner_apply] at hn
    norm_num [Fin.sum_univ_succ] at hn
    rw [hn]
    norm_num [F, PiLp.inner_apply, Fin.sum_univ_succ,
      sq_abs, mul_pow]
    constructor <;> nlinarith
  have hdual : IsDualFrame F G := by
    intro x
    ext j
    fin_cases j
    norm_num [F, G, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  have hmu : mu F G = 2 / 5 := by
    let s := (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 ≠ p.2)
    let f := fun p : Fin 3 × Fin 3 => ‖inner ℝ (F p.1) (G p.2)‖₊
    have hn : s.sup f = (2 / 5 : NNReal) := by
      apply le_antisymm
      · apply Finset.sup_le
        rintro ⟨i, j⟩ hij
        fin_cases i <;> fin_cases j
        all_goals norm_num [s] at hij
        all_goals norm_num [f, F, G, PiLp.inner_apply, Fin.sum_univ_succ]
        all_goals apply NNReal.coe_le_coe.mp
        all_goals norm_num
      · calc
          (2 / 5 : NNReal) = f (1, 0) := by
            norm_num [f, F, G, PiLp.inner_apply, Fin.sum_univ_succ]
          _ ≤ s.sup f := Finset.le_sup (f := f)
            (show ((1, 0) : Fin 3 × Fin 3) ∈ s by norm_num [s])
    change (↑(s.sup f) : ℝ) = 2 / 5
    rw [hn]
    norm_num
  have hbounds : ∀ H : Fin 3 → EuclideanSpace ℝ (Fin 1),
      2 * |H 0 0| ≤ mu F H ∧ 3 * |H 1 0| ≤ mu F H ∧
        3 * |H 2 0| ≤ mu F H := by
    intro H
    have hb : ∀ i j : Fin 3, i ≠ j →
        |inner ℝ (F i) (H j)| ≤ mu F H := by
      intro i j hij
      have h := Finset.le_sup (f := fun p : Fin 3 × Fin 3 =>
        ‖inner ℝ (F p.1) (H p.2)‖₊)
        (show (i, j) ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).filter
          (fun p => p.1 ≠ p.2) by simp [hij])
      have hr := NNReal.coe_le_coe.mpr h
      simpa only [coe_nnnorm, Real.norm_eq_abs, mu] using hr
    have h0 := hb 1 0 (by decide)
    have h1 := hb 0 1 (by decide)
    have h2 := hb 0 2 (by decide)
    norm_num [F, PiLp.inner_apply, Fin.sum_univ_succ,
      abs_mul] at h0 h1 h2
    exact ⟨by simpa only [mul_comm] using h0,
      by simpa only [mul_comm] using h1, by simpa only [mul_comm] using h2⟩
  have hidentity : ∀ H : Fin 3 → EuclideanSpace ℝ (Fin 1), IsDualFrame F H →
      3 * H 0 0 + 2 * H 1 0 + H 2 0 = 1 := by
    intro H hd
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin 1) => x 0)
      (hd (WithLp.toLp 2 (fun _ => (1 : ℝ))))
    norm_num [F, PiLp.inner_apply, Fin.sum_univ_succ] at h
    linarith
  have hmin : ∀ H, IsDualFrame F H → mu F G ≤ mu F H := by
    intro H hd
    rw [hmu]
    obtain ⟨h0, h1, h2⟩ := hbounds H
    have heq := hidentity H hd
    have a0 := le_abs_self (H 0 0)
    have a1 := le_abs_self (H 1 0)
    have a2 := le_abs_self (H 2 0)
    linarith
  have hunique : ∀ H, IsDualFrame F H → mu F H ≤ mu F G → H = G := by
    intro H hd hm
    rw [hmu] at hm
    obtain ⟨h0, h1, h2⟩ := hbounds H
    have heq := hidentity H hd
    have a0 := le_abs_self (H 0 0)
    have a1 := le_abs_self (H 1 0)
    have a2 := le_abs_self (H 2 0)
    have e0 : H 0 0 = 1 / 5 := by linarith
    have e1 : H 1 0 = 2 / 15 := by linarith
    have e2 : H 2 0 = 2 / 15 := by linarith
    funext i
    ext j
    fin_cases j
    fin_cases i
    · simpa [G] using e0
    · simpa [G] using e1
    · simpa [G] using e2
  have hS : ∀ x : EuclideanSpace ℝ (Fin 1), frameOperator F x = (14 : ℝ) • x := by
    intro x
    ext j
    fin_cases j
    norm_num [frameOperator, F, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  have hinj : Function.Injective (frameOperator F) := by
    intro x y hxy
    rw [hS, hS] at hxy
    ext j
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v j) hxy
    change (14 : ℝ) * x j = 14 * y j at h
    linarith
  have hcanon : canonicalDual F 0 = (1 / 14 : ℝ) • F 0 := by
    have hs : frameOperator F ((1 / 14 : ℝ) • F 0) = F 0 := by
      rw [hS, smul_smul]
      norm_num
    change Function.invFun (frameOperator F) (F 0) = _
    calc
      Function.invFun (frameOperator F) (F 0) =
          Function.invFun (frameOperator F) (frameOperator F ((1 / 14 : ℝ) • F 0)) :=
        congrArg (Function.invFun (frameOperator F)) hs.symm
      _ = _ := Function.leftInverse_invFun hinj _
  intro hc
  have heq := hc 1 3 F G (by decide) hframe hdual hmin hunique
  have hv := congrArg (fun K : Fin 3 → EuclideanSpace ℝ (Fin 1) => K 0 0) heq
  rw [hcanon] at hv
  norm_num [G, F] at hv

#print axioms result

end D5.S3.QuantumBounds.Designs.CrossFrameExclusiveDualRefutation
