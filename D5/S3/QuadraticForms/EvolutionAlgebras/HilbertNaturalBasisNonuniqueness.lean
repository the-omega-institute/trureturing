/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness
   generality: E
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.claim; result=D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.result; claim=D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.claim
   digest: Dense-square Hilbert basis uniqueness fails over the complex scalars. -/

import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
The multiplication table is from arXiv:2505.14584v1, Example 3.7.
The Hilbert realization is covered by arXiv:2012.05124v2, Corollary 2.4;
the equal-square orthonormal change of basis is the method of
arXiv:2311.08387v2, Examples 3.6–3.7.  The assertion is the complete first
interrogative of arXiv:2610.22248v1, Question 46.
-/

open scoped lp
open Complex Submodule TopologicalSpace

namespace D5.S3.QuadraticForms.EvolutionAlgebras.HilbertNaturalBasisNonuniqueness

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable def e : HilbertBasis ℕ+ ℂ (lp (fun _ : ℕ+ => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℕ+ => ℂ) 2))

/- proof_shape: bind-only; consumers: mu_on_e. -/
private theorem e_eq_single (i : ℕ+) : e i = (lp.single 2 i 1 : (lp (fun _ : ℕ+ => ℂ) 2)) := by
  apply e.repr.injective
  rw [e.repr_self]
  rfl

private noncomputable def coefficient (i : ℕ+) : ℂ →L[ℂ] ℂ →L[ℂ] (lp (fun _ : ℕ+ => ℂ) 2) :=
  (LinearMap.mk₂ ℂ (fun a b : ℂ => (a * b) • e (if i = 1 then 1 else i - 1))
    (by intros; simp [add_mul, add_smul])
    (by intros; simp [mul_smul, smul_eq_mul, mul_assoc])
    (by intros; simp [mul_add, add_smul])
    (by intros; simp [mul_smul, smul_eq_mul, mul_left_comm])
  ).mkContinuous₂ 1 (by
    intro a b
    change ‖(a * b) • e (if i = 1 then 1 else i - 1)‖ ≤ 1 * ‖a‖ * ‖b‖
    rw [norm_smul, norm_mul, e.orthonormal.norm_eq_one]
    simp)

noncomputable def mu : (lp (fun _ : ℕ+ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ+ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ+ => ℂ) 2) :=
  lp.dualPairing 2 2 coefficient (K := 1) (by
    intro i
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro b
    change ‖(a * b) • e (if i = 1 then 1 else i - 1)‖ ≤ _
    rw [norm_smul, norm_mul, e.orthonormal.norm_eq_one]
    simp)

/- proof_shape: bind-only; consumers: f_natural, dense_square, complex_refutation. -/
private theorem mu_on_e (i j : ℕ+) :
    mu (e i) (e j) = if i = j then e (if i = 1 then 1 else i - 1) else 0 := by
  classical
  change (∑' k : ℕ+, coefficient k ((e i) k) ((e j) k)) = _
  simp_rw [e_eq_single]
  rw [tsum_eq_single i]
  · simp [coefficient, lp.single_apply, Pi.single_apply, e_eq_single]
  · intro k hk
    simp [lp.single_apply, Pi.single_apply, hk.symm]

private noncomputable def rotated (i : ℕ+) : (lp (fun _ : ℕ+ => ℂ) 2) :=
  if i = 1 then (3 / 5 : ℂ) • e 1 + (4 / 5 : ℂ) • e 2
  else if i = 2 then (-4 / 5 : ℂ) • e 1 + (3 / 5 : ℂ) • e 2
  else e i

/- proof_shape: bind-only; consumers: f. -/
private theorem rotated_orthonormal : Orthonormal ℂ rotated := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [rotated]
  split_ifs <;> subst_vars
  all_goals try simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp e.orthonormal]
  all_goals norm_num [starRingEnd_apply] at *
  all_goals simp_all [eq_comm]

/- proof_shape: bind-only; consumers: f. -/
private theorem e_mem_rotated_span (i : ℕ+) :
    e i ∈ span ℂ (Set.range rotated) := by
  let S := span ℂ (Set.range rotated)
  have h1 : rotated 1 ∈ S := subset_span ⟨1, rfl⟩
  have h2 : rotated 2 ∈ S := subset_span ⟨2, rfl⟩
  have hf1 : rotated 1 = (3 / 5 : ℂ) • e 1 + (4 / 5 : ℂ) • e 2 := by simp [rotated]
  have hf2 : rotated 2 = (-4 / 5 : ℂ) • e 1 + (3 / 5 : ℂ) • e 2 := by norm_num [rotated]
  by_cases hi : i = 1
  · subst i
    have hid : e 1 = (3 / 5 : ℂ) • rotated 1 - (4 / 5 : ℂ) • rotated 2 := by
      rw [hf1, hf2]
      module
    rw [hid]
    exact S.sub_mem (S.smul_mem _ h1) (S.smul_mem _ h2)
  · by_cases hi' : i = 2
    · subst i
      have hid : e 2 = (4 / 5 : ℂ) • rotated 1 + (3 / 5 : ℂ) • rotated 2 := by
        rw [hf1, hf2]
        module
      rw [hid]
      exact S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)
    · have hh : rotated i = e i := by simp [rotated, hi, hi']
      rw [← hh]
      exact subset_span ⟨i, rfl⟩

noncomputable def f : HilbertBasis ℕ+ ℂ (lp (fun _ : ℕ+ => ℂ) 2) :=
  HilbertBasis.mk rotated_orthonormal (by
    rw [← e.dense_span]
    apply Submodule.topologicalClosure_mono
    exact span_le.mpr (by rintro x ⟨i, rfl⟩; exact e_mem_rotated_span i))

/- proof_shape: bind-only; consumers: f_natural, f_not_scalar_e. -/
private theorem f_eq_rotated (i : ℕ+) : f i = rotated i := by
  exact congrFun (HilbertBasis.coe_mk _ _) i

/- proof_shape: bind-only; consumers: complex_refutation. -/
private theorem h_separable : SeparableSpace (lp (fun _ : ℕ+ => ℂ) 2) := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hs := (Set.countable_range e).isSeparable.span (R := ℂ)
  have hc := hs.closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span] at hc
  simpa using hc

/- proof_shape: bind-only; consumers: complex_refutation. -/
private theorem f_natural (i j : ℕ+) (hij : i ≠ j) : mu (f i) (f j) = 0 := by
  classical
  simp only [f_eq_rotated]
  simp only [rotated]
  split_ifs <;> subst_vars
  all_goals try simp only [ContinuousLinearMap.map_add₂, ContinuousLinearMap.map_smul₂]
  all_goals try simp only [map_add, map_smul, mu_on_e]
  all_goals norm_num [show (2 : ℕ+) - 1 = 1 by decide] at *
  all_goals simp_all [eq_comm]
  all_goals module

/- proof_shape: bind-only; consumers: complex_refutation. -/
private theorem dense_square :
    (span ℂ {z : (lp (fun _ : ℕ+ => ℂ) 2) |
      ∃ x y : (lp (fun _ : ℕ+ => ℂ) 2), mu x y = z}).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← e.dense_span]
  apply Submodule.topologicalClosure_mono
  apply span_le.mpr
  rintro x ⟨i, rfl⟩
  apply subset_span
  refine ⟨e (i + 1), e (i + 1), ?_⟩
  rw [mu_on_e, ite_eq_left rfl, ite_eq_right (ne_of_gt (PNat.lt_add_left 1 i))]
  simp

/- proof_shape: bind-only; consumers: complex_refutation. -/
private theorem f_not_scalar_e (j : ℕ+) (c : ℂ) : f 1 ≠ c • e j := by
  classical
  intro heq
  rw [f_eq_rotated] at heq
  have h1 := congrArg (fun x : (lp (fun _ : ℕ+ => ℂ) 2) => inner ℂ (e 1) x) heq
  have h2 := congrArg (fun x : (lp (fun _ : ℕ+ => ℂ) 2) => inner ℂ (e 2) x) heq
  simp only [rotated, ite_true, inner_add_right, inner_smul_right,
    orthonormal_iff_ite.mp e.orthonormal] at h1 h2
  by_cases hj : j = 1
  · norm_num [hj] at h2
  · norm_num [hj, eq_comm] at h1

/-- Natural orthonormal basis uniqueness over the chosen scalar field. -/
def uniqueness (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (A : Type) [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
    [CompleteSpace A] [SeparableSpace A]
    (m : A →ₗ[𝕜] A →ₗ[𝕜] A)
    (a b : HilbertBasis ℕ+ 𝕜 A),
    (∀ v, ∃ M : ℝ, 0 < M ∧ ∀ w, ‖m v w‖ ≤ M * ‖w‖) →
    (∀ i j, i ≠ j → m (a i) (a j) = 0) →
    (∀ i j, i ≠ j → m (b i) (b j) = 0) →
    (span 𝕜 {z : A | ∃ x y : A, m x y = z}).topologicalClosure = ⊤ →
    ∃ (σ : Equiv.Perm ℕ+) (c : ℕ+ → 𝕜),
      (∀ i, ‖c i‖ = 1) ∧ ∀ i, b i = c i • a (σ i)

/- proof_shape: bind-only; consumers: result. -/
private theorem complex_refutation : ¬ uniqueness ℂ := by
  intro h
  have : SeparableSpace (lp (fun _ : ℕ+ => ℂ) 2) := h_separable
  have hm (v : (lp (fun _ : ℕ+ => ℂ) 2)) : ∃ M : ℝ, 0 < M ∧ ∀ w, ‖mu v w‖ ≤ M * ‖w‖ := by
    refine ⟨‖mu v‖ + 1, by positivity, fun w => ?_⟩
    exact (mu v).le_opNorm w |>.trans (by gcongr; linarith)
  obtain ⟨σ, c, _, hid⟩ := h (lp (fun _ : ℕ+ => ℂ) 2) mu.toLinearMap₁₂ e f hm
    (by intro i j hij; simp [mu_on_e, hij]) f_natural dense_square
  exact f_not_scalar_e (σ 1) (c 1) (hid 1)

/-- The entire real-or-complex universal assertion in Question 46's first sentence. -/
def claim : Prop := uniqueness ℝ ∧ uniqueness ℂ

/-- Dense algebraic square does not force uniqueness of a natural orthonormal basis. -/
/- proof_shape: bind-only; admission_basis: open-problem-resolution; refutes: claim. -/
theorem result : ¬ claim := by
  intro h
  exact complex_refutation h.2

end
end D5.S3.QuadraticForms.EvolutionAlgebras.HilbertNaturalBasisNonuniqueness
