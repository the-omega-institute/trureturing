/- GID: D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/PathTwinSharpSedentariness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.claim; result=D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.result; claim=D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.claim
   digest: The twin end vertex of P'_9 is not sharply 1/9-sedentary: |U(t)_{1,1}| ≥ 5/18. -/

/-
proof_shape: result: bind-only
escape_witness: null
admission_basis: open-problem-resolution (issue #11607; Refuted)
Direct frozen dependencies: D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow
  (`hamiltonianPropagator`, `hamiltonianGenerator`),
  D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity (`exp_mulVec_of_eigenvector`)
-/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.PathTwinSharpSedentariness

open Complex Matrix Real
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-- The adjacency matrix of `P'_n`: vertex `j + 1` of the source is `j : Fin (n + 1)`; the edges
are those of the path `1, …, n` and the edge between vertex `2` and the added vertex `n + 1`. -/
def pathTwin (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
  if (i.val + 1 = j.val ∧ j.val < n) ∨ (j.val + 1 = i.val ∧ i.val < n) ∨
      (i.val = 1 ∧ j.val = n) ∨ (i.val = n ∧ j.val = 1) then 1 else 0

/-- Vertex `u` is sharply `C`-sedentary: `0 < C ≤ 1` and `inf_{t > 0} |(e^{itA})_{u,u}| = C`, where
`e^{itA} = hamiltonianPropagator A (-t)`. -/
def SharplySedentary {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (u : ι)
    (C : ℝ) : Prop :=
  0 < C ∧ C ≤ 1 ∧ sInf ((fun t : ℝ => ‖hamiltonianPropagator A (-t) u u‖) '' Set.Ioi 0) = C

/-- The conjecture: for every odd `n ≥ 5`, the end vertex `1` of `P'_n` is sharply
`(1/n)`-sedentary. -/
def claim : Prop :=
  ∀ n : ℕ, Odd n → 5 ≤ n → SharplySedentary (pathTwin n) 0 (1 / n)

/-- The eigenvector of `A(P'_9)` for the eigenvalue `2 cos z` when `cos 9z = 0`. -/
private def xv (z : ℂ) : Fin 10 → ℂ :=
  ![1 / 2, Complex.cos z, Complex.cos (2 * z), Complex.cos (3 * z), Complex.cos (4 * z),
    Complex.cos (5 * z), Complex.cos (6 * z), Complex.cos (7 * z), Complex.cos (8 * z), 1 / 2]

/-- The antisymmetric twin vector `e₁ - e₁₀`, in the kernel of `A(P'_9)`. -/
private def yv : Fin 10 → ℂ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, -1]

/-- The angles `θ_k = (2k + 1)π/18`. -/
private def θ (k : ℕ) : ℝ := (2 * k + 1) * π / 18

theorem result : ¬ claim := by
  intro h
  obtain ⟨-, -, hinf⟩ := h 9 (by decide) (by norm_num)
  set A := pathTwin 9 with hA
  have hrow : ∀ x : Fin 10 → ℂ, A *ᵥ x =
      ![x 1, x 0 + x 2 + x 9, x 1 + x 3, x 2 + x 4, x 3 + x 5, x 4 + x 6, x 5 + x 7, x 6 + x 8,
        x 7, x 1] := by
    intro x
    ext i
    fin_cases i <;> simp [A, pathTwin, mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hx : ∀ z : ℂ, Complex.cos (9 * z) = 0 → A *ᵥ xv z = (2 * Complex.cos z) • xv z := by
    intro z hz
    rw [hrow]
    ext i
    fin_cases i
    · simp [xv]; ring
    · simp [xv]; linear_combination Complex.cos_two_mul z
    · have e1 := Complex.cos_add (2 * z) z
      have e2 := Complex.cos_sub (2 * z) z
      simp [xv]; ring_nf at e1 e2 ⊢; linear_combination e1 + e2
    · have e1 := Complex.cos_add (3 * z) z
      have e2 := Complex.cos_sub (3 * z) z
      simp [xv]; ring_nf at e1 e2 ⊢; linear_combination e1 + e2
    · have e1 := Complex.cos_add (4 * z) z
      have e2 := Complex.cos_sub (4 * z) z
      simp [xv]; ring_nf at e1 e2 ⊢; linear_combination e1 + e2
    · have e1 := Complex.cos_add (5 * z) z
      have e2 := Complex.cos_sub (5 * z) z
      simp [xv]; ring_nf at e1 e2 ⊢; linear_combination e1 + e2
    · have e1 := Complex.cos_add (6 * z) z
      have e2 := Complex.cos_sub (6 * z) z
      simp [xv]; ring_nf at e1 e2 ⊢; linear_combination e1 + e2
    · have e1 := Complex.cos_add (7 * z) z
      have e2 := Complex.cos_sub (7 * z) z
      simp [xv]; ring_nf at e1 e2 ⊢; linear_combination e1 + e2
    · have e1 := Complex.cos_add (8 * z) z
      have e2 := Complex.cos_sub (8 * z) z
      simp [xv]; ring_nf at e1 e2 hz ⊢; linear_combination e1 + e2 - hz
    · simp [xv]; ring
  have hy : A *ᵥ yv = (0 : ℂ) • yv := by
    rw [hrow]
    ext i
    fin_cases i <;> simp [yv]
  have hcos9 : ∀ k : ℕ, Complex.cos (9 * (θ k : ℂ)) = 0 := by
    intro k
    rw [Complex.cos_eq_zero_iff]
    exact ⟨k, by simp only [θ]; push_cast; ring⟩
  have hsum : ∀ m : ℕ, 1 ≤ m → m ≤ 8 →
      ∑ k ∈ Finset.range 9, Complex.cos (m * (θ k : ℂ)) = 0 := by
    intro m h1 h8
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hm8 : (m : ℝ) ≤ 8 := by exact_mod_cast h8
    have hs : Real.sin (m * π / 9 / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
    have ht := Real.sin_mul_sum_cos 9 (m * π / 9) (m * π / 18)
    rw [show ((9 : ℕ) : ℝ) * (m * π / 9) / 2 = m * π / 2 by push_cast; ring,
      show (((9 : ℕ) : ℝ) - 1) * (m * π / 9) / 2 + m * π / 18 = m * π / 2 by push_cast; ring] at ht
    have h2 := Real.sin_two_mul (m * π / 2)
    rw [show 2 * (m * π / 2) = (m : ℕ) * π by ring, Real.sin_nat_mul_pi] at h2
    have hz : Real.sin (m * π / 2) * Real.cos (m * π / 2) = 0 := by
      linear_combination (-1 / 2 : ℝ) * h2
    have hr : ∑ k ∈ Finset.range 9, Real.cos (m * θ k) = 0 := by
      have hrw : ∀ k ∈ Finset.range 9,
          Real.cos (m * θ k) = Real.cos (m * π / 9 * k + m * π / 18) :=
        fun k _ => by congr 1; simp only [θ]; ring
      rw [Finset.sum_congr rfl hrw]
      rw [hz] at ht
      exact (mul_eq_zero.mp ht).resolve_left hs
    have := congrArg (fun r : ℝ => (r : ℂ)) hr
    push_cast at this
    exact this
  have hdec : (Pi.single 0 1 : Fin 10 → ℂ) =
      (1 / 2 : ℂ) • yv + (1 / 9 : ℂ) • ∑ k ∈ Finset.range 9, xv (θ k) := by
    have s1 := hsum 1 (by norm_num) (by norm_num)
    have s2 := hsum 2 (by norm_num) (by norm_num)
    have s3 := hsum 3 (by norm_num) (by norm_num)
    have s4 := hsum 4 (by norm_num) (by norm_num)
    have s5 := hsum 5 (by norm_num) (by norm_num)
    have s6 := hsum 6 (by norm_num) (by norm_num)
    have s7 := hsum 7 (by norm_num) (by norm_num)
    have s8 := hsum 8 (by norm_num) (by norm_num)
    push_cast at s1 s2 s3 s4 s5 s6 s7 s8
    simp only [one_mul] at s1
    ext i
    fin_cases i <;> simp [xv, yv, Finset.sum_apply, s1, s2, s3, s4, s5, s6, s7, s8]
    norm_num
  have hact : ∀ (v : Fin 10 → ℂ) (μ : ℂ), A *ᵥ v = μ • v → ∀ t : ℝ,
      hamiltonianPropagator A (-t) *ᵥ v = Complex.exp (I * t * μ) • v := by
    intro v μ hv t
    unfold hamiltonianPropagator hamiltonianGenerator
    apply D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
    rw [smul_mulVec, smul_mulVec, hv, ← Complex.coe_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hU : ∀ t : ℝ, (hamiltonianPropagator A (-t) 0 0).re =
      1 / 2 + 1 / 18 * ∑ k ∈ Finset.range 9, Real.cos (t * (2 * Real.cos (θ k))) := by
    intro t
    have h0 : hamiltonianPropagator A (-t) 0 0 =
        (hamiltonianPropagator A (-t) *ᵥ Pi.single 0 1) 0 := by
      simp [mulVec, dotProduct, Pi.single_apply]
    rw [h0, hdec, mulVec_add, mulVec_smul, mulVec_smul, Matrix.mulVec_sum,
      hact yv 0 hy t]
    rw [Finset.sum_congr rfl fun k _ => hact _ _ (hx _ (hcos9 k)) t]
    have hre : ∀ k : ℕ, (Complex.exp (I * t * (2 * Complex.cos (θ k : ℂ)))).re =
        Real.cos (t * (2 * Real.cos (θ k))) := by
      intro k
      rw [show I * t * (2 * Complex.cos (θ k : ℂ)) =
          ((t * (2 * Real.cos (θ k)) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_ofReal_mul_I_re]
    simp only [Nat.reduceAdd, one_div, mul_zero, Complex.exp_zero, yv, one_smul, smul_cons,
      smul_eq_mul, mul_one, mul_neg, smul_empty, xv, Fin.isValue, Pi.add_apply, cons_val_zero,
      Pi.smul_apply, Finset.sum_apply, add_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
      mul_re, re_sum, hre, inv_im, im_ofNat, neg_zero, zero_div, sub_zero, im_sum, mul_im, zero_add,
      zero_mul, add_right_inj]
    rw [← Finset.sum_mul]
    ring
  have hpair : ∀ k : ℕ, k ≤ 8 → Real.cos (θ (8 - k)) = -Real.cos (θ k) := by
    intro k hk
    have hθ : θ (8 - k) = π - θ k := by
      simp only [θ]
      rw [Nat.cast_sub hk]
      push_cast
      ring
    rw [hθ, Real.cos_pi_sub]
  have h4 : Real.cos (θ 4) = 0 := by
    rw [show θ 4 = π / 2 by simp only [θ]; push_cast; ring, Real.cos_pi_div_two]
  have h0sum : Real.cos (θ 0) = Real.cos (θ 2) + Real.cos (θ 3) := by
    rw [Real.cos_add_cos,
      show (θ 2 + θ 3) / 2 = π / 3 by simp only [θ]; push_cast; ring,
      show (θ 2 - θ 3) / 2 = -θ 0 by simp only [θ]; push_cast; ring,
      Real.cos_pi_div_three, Real.cos_neg]
    ring
  have hbound : ∀ t : ℝ, 5 / 18 ≤ ‖hamiltonianPropagator A (-t) 0 0‖ := by
    intro t
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [hU t]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have p8 : Real.cos (θ 8) = -Real.cos (θ 0) := hpair 0 (by norm_num)
    have p7 : Real.cos (θ 7) = -Real.cos (θ 1) := hpair 1 (by norm_num)
    have p6 : Real.cos (θ 6) = -Real.cos (θ 2) := hpair 2 (by norm_num)
    have p5 : Real.cos (θ 5) = -Real.cos (θ 3) := hpair 3 (by norm_num)
    rw [p8, p7, p6, p5, h4]
    have ev : ∀ x : ℝ, Real.cos (t * (2 * -x)) = Real.cos (t * (2 * x)) := fun x => by
      rw [show t * (2 * -x) = -(t * (2 * x)) by ring, Real.cos_neg]
    simp only [ev, mul_zero, Real.cos_zero]
    set a := t * (2 * Real.cos (θ 2))
    set b := t * (2 * Real.cos (θ 3))
    have hab : t * (2 * Real.cos (θ 0)) = a + b := by rw [h0sum]; ring
    rw [hab]
    have key : -(3 / 2 : ℝ) ≤ Real.cos a + Real.cos b + Real.cos (a + b) := by
      nlinarith [sq_nonneg (1 + Real.cos a + Real.cos b), sq_nonneg (Real.sin a - Real.sin b),
        Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b, Real.cos_add a b]
    have hc1 := Real.neg_one_le_cos (t * (2 * Real.cos (θ 1)))
    norm_num
    linarith
  have hne : ((fun t : ℝ => ‖hamiltonianPropagator A (-t) 0 0‖) '' Set.Ioi 0).Nonempty :=
    ⟨_, 1, by norm_num, rfl⟩
  have hle := le_csInf hne (by rintro _ ⟨t, -, rfl⟩; exact hbound t)
  rw [hinf] at hle
  norm_num at hle

end D5.S3.Quantum.Dynamics.PathTwinSharpSedentariness
