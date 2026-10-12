/- GID: D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.claim; result=D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.result; claim=D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.claim
   digest: A real SUNTF exists for parameters (2,5,3). -/

/-
escape_witness: the explicit three-layer construction
Direct frozen dependencies: none (pinned Mathlib only)
proof_shape: IsUNTF: definition (consumed by IsSUNTF and result)
proof_shape: IsStratified: definition (consumed by IsSUNTF and result)
proof_shape: IsSUNTF: definition (consumed by claim and result)
proof_shape: claim: definition (consumed by result)
proof_shape: result: the proof verifies an explicit finite construction by exact computation
admission_basis: open-problem-resolution (#15883; existence, encoded as refutation of the nonexistence claim)
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace D5.S3.QuantumBounds.Designs.StratifiedTightFrameTwoFiveThree

/- A unit norm tight frame for `ℝ^D` (Definition 3.2 layer condition). -/
def IsUNTF {D N : ℕ} (φ : Fin N → EuclideanSpace ℝ (Fin D)) : Prop :=
  (∀ n, ‖φ n‖ = 1) ∧ ∃ A : ℝ, 0 < A ∧ ∀ x : EuclideanSpace ℝ (Fin D), ∑ n, ⟪φ n, x⟫_ℝ ^ 2 = A * ‖x‖ ^ 2

/- Definition 3.2: stratified. -/
def IsStratified {D N R : ℕ} (φ : Fin R → Fin N → EuclideanSpace ℝ (Fin D)) : Prop :=
  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ n₁ n₂ : Fin N, n₁ ≠ n₂ → (1 / (R : ℝ)) * ∑ r, ⟪φ r n₁, φ r n₂⟫_ℝ ^ 2 = Λ

/- Definition 3.2: a SUNTF_ℝ(D, N, R). -/
def IsSUNTF {D N R : ℕ} (φ : Fin R → Fin N → EuclideanSpace ℝ (Fin D)) : Prop :=
  (∀ r, IsUNTF (φ r)) ∧ IsStratified φ

/- The negative answer to the question of Example 4.4: no SUNTF_ℝ(2,5,3) exists. -/
def claim : Prop := ¬ ∃ φ : Fin 3 → Fin 5 → EuclideanSpace ℝ (Fin 2), IsSUNTF φ

private def vec (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, b]

private noncomputable def u : ℝ := Real.sqrt (3 / 8)
private noncomputable def v : ℝ := Real.sqrt (5 / 8)

private noncomputable def φ : Fin 3 → Fin 5 → EuclideanSpace ℝ (Fin 2) :=
  ![
    ![vec 1 0, vec u v, vec u (-v), vec u (-v), vec u v],
    ![vec 1 0, vec u v, vec u (-v), vec u v, vec u (-v)],
    ![vec 1 0, vec u v, vec u v, vec u (-v), vec u (-v)]
  ]

theorem result : ¬ claim := by
  classical
  have hu : u ^ 2 = (3 / 8 : ℝ) := by
    dsimp [u]
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 8)
    nlinarith
  have hv : v ^ 2 = (5 / 8 : ℝ) := by
    dsimp [v]
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 8)
    nlinarith
  have hnorm (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : ‖vec a b‖ = 1 := by
    have hs : ‖vec a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
      simp [vec, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [hs, h]
    norm_num
  have hunit : ∀ r n, ‖φ r n‖ = 1 := by
    intro r n
    fin_cases r <;> fin_cases n
    all_goals (apply hnorm; nlinarith [hu, hv])
  have htight (r : Fin 3) : ∃ A : ℝ, 0 < A ∧ ∀ x : EuclideanSpace ℝ (Fin 2),
      ∑ n, ⟪φ r n, x⟫_ℝ ^ 2 = A * ‖x‖ ^ 2 := by
    refine ⟨5 / 2, by norm_num, ?_⟩
    intro x
    fin_cases r
    all_goals
      simp [φ, vec, PiLp.inner_apply, Fin.sum_univ_succ,
        EuclideanSpace.real_norm_sq_eq]
      nlinarith [hu, hv]
  have hstrat : IsStratified φ := by
    refine ⟨3 / 8, by norm_num, ?_⟩
    intro n₁ n₂ hne
    fin_cases n₁ <;> fin_cases n₂
    all_goals try {exact (hne rfl).elim}
    all_goals
      simp [φ, vec, PiLp.inner_apply, Fin.sum_univ_succ]
      nlinarith [hu, hv]
  intro h
  apply h
  refine ⟨φ, ?_⟩
  exact ⟨(fun r => ⟨hunit r, htight r⟩), hstrat⟩

end D5.S3.QuantumBounds.Designs.StratifiedTightFrameTwoFiveThree
