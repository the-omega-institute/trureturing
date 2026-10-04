/- GID: D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/StaggeredM1EndpointDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero-energy M1 states satisfy the endpoint-density relation. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none; the settling result applies the endpoint operator identity and positivity of the Hilbert norm.
  Direct frozen dependencies: none.
admission_basis: open-problem-resolution (#12308; Proved)
Direct frozen dependency keys (GID; statement_id):
Direct frozen dependencies: none.
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.EndpointIdentity; freeze in topological import order.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.EndpointIdentity

set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Classical

namespace D5.S3.Quantum.SpinChains.StaggeredM1EndpointDensity
noncomputable section
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.EndpointIdentity

def claim : Prop := ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ, y ≠ 0 →
  ∀ ψ : HardCoreSpace (3 * n), ψ ≠ 0 →
  H (3 * n) (stagII y) ψ = 0 →
  density (3 * n) ψ = (y⁻¹ ^ 2 : ℝ) • density 1 ψ

theorem result : claim := by
  have zero_energy_annihilated
      {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E] (q : E →ₗ[ℂ] E) (ψ : E)
      (h : (q * q.adjoint + q.adjoint * q) ψ = 0) :
      q ψ = 0 ∧ q.adjoint ψ = 0 := by
    have he := congrArg (fun v => (inner ℂ ψ v).re) h
    have h1 : inner ℂ ψ (q (q.adjoint ψ)) =
        inner ℂ (q.adjoint ψ) (q.adjoint ψ) := by
      simpa only [LinearMap.adjoint_adjoint] using
        (LinearMap.adjoint_inner_right q.adjoint ψ (q.adjoint ψ))
    have hn1 : (inner ℂ (q.adjoint ψ) (q.adjoint ψ)).re = ‖q.adjoint ψ‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (q.adjoint ψ)).symm
    have hn2 : (inner ℂ (q ψ) (q ψ)).re = ‖q ψ‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (q ψ)).symm
    have hs : ‖q.adjoint ψ‖ ^ 2 + ‖q ψ‖ ^ 2 = 0 := by
      simp only [LinearMap.add_apply, Module.End.mul_apply, inner_add_right,
        inner_zero_right, Complex.zero_re] at he
      rw [h1, LinearMap.adjoint_inner_right q ψ (q ψ), Complex.add_re,
        hn1, hn2] at he
      exact he
    have hq : ‖q ψ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖q.adjoint ψ‖]
    have hqa : ‖q.adjoint ψ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖q ψ‖]
    exact ⟨norm_eq_zero.mp (by nlinarith [norm_nonneg (q ψ)]),
      norm_eq_zero.mp (by nlinarith [norm_nonneg (q.adjoint ψ)])⟩
  have zero_anticommutator_expectation
      {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E] (q r : E →ₗ[ℂ] E) (ψ : E)
      (hq : q ψ = 0) (hqa : q.adjoint ψ = 0) :
      inner ℂ ψ ((q * r + r * q) ψ) = 0 ∧
      inner ℂ ψ ((q * r + r * q).adjoint ψ) = 0 := by
    constructor
    · simp only [LinearMap.add_apply, Module.End.mul_apply, inner_add_right,
        ← LinearMap.adjoint_inner_left q, hq, hqa, inner_zero_left,
        map_zero, inner_zero_right, add_zero]
    · rw [LinearMap.adjoint_inner_right]
      simp only [LinearMap.add_apply, Module.End.mul_apply, inner_add_left,
        ← LinearMap.adjoint_inner_right q, hq, hqa, inner_zero_right,
        map_zero, inner_zero_left, add_zero]
  have zero_energy_weighted_sum_rule
      {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E] (q r A B : E →ₗ[ℂ] E)
      (k α β : ℝ) (hk : k ≠ 0) (ψ : E)
      (hH : (q * q.adjoint + q.adjoint * q) ψ = 0)
      (hid : q * r + r * q + (q * r + r * q).adjoint =
        k • (α • A - β • B)) :
      α • inner ℂ ψ (A ψ) = β • inner ℂ ψ (B ψ) := by
    obtain ⟨hq,hqa⟩ := zero_energy_annihilated q ψ hH
    obtain ⟨hz,hza⟩ := zero_anticommutator_expectation q r ψ hq hqa
    have he := congrArg (fun t : E →ₗ[ℂ] E => inner ℂ ψ (t ψ)) hid
    rw [LinearMap.add_apply, inner_add_right] at he
    rw [hz, hza, add_zero] at he
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, inner_sub_right,
      inner_smul_right_eq_smul] at he
    have hc : α • inner ℂ ψ (A ψ) - β • inner ℂ ψ (B ψ) = 0 :=
      (smul_eq_zero.mp he.symm).resolve_left hk
    exact sub_eq_zero.mp hc
  have endpoint_identity_implies_claim (hid : EndpointIdentity) : claim := by
    intro n hn y hy ψ _hψ hH
    let q := Q (3 * n) (stagII y)
    let r := Matrix.toEuclideanLin (Rmat (3 * n) y y 1)
    let A := Matrix.toEuclideanLin (number (N := 3 * n) 1)
    let B := Matrix.toEuclideanLin (number (N := 3 * n) (3 * n))
    have hi := hid n hn y y 1
    have hsmul (α : ℝ) (t : Operator (3 * n)) :
        Matrix.toEuclideanLin (α • t) = α • Matrix.toEuclideanLin t :=
      (Matrix.toEuclideanLin : Operator (3 * n) ≃ₗ[ℂ] _).map_smul_of_tower α t
    have hmul (s t : Operator (3 * n)) :
        Matrix.toEuclideanLin (s * t) = Matrix.toEuclideanLin s * Matrix.toEuclideanLin t :=
      Matrix.toLpLin_mul_same 2 s t
    have hiL := congrArg (fun t : Operator (3 * n) => Matrix.toEuclideanLin t) hi
    simp only [map_add, map_sub, hsmul, hmul,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at hiL
    have hqq : (q * q.adjoint + q.adjoint * q) ψ = 0 := hH
    have hrr : q * r + r * q + (q * r + r * q).adjoint =
        (2 * y ^ 2 : ℝ) • ((1 : ℝ) • A - (y ^ 2 : ℝ) • B) := by
      simpa only [q, r, A, B, Q, stagII, one_pow, map_add] using hiL
    have he := zero_energy_weighted_sum_rule q r A B (2 * y ^ 2) 1 (y ^ 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)) ψ hqq hrr
    simp only [one_smul, Complex.real_smul] at he
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    dsimp [density]
    change inner ℂ ψ (B ψ) / inner ℂ ψ ψ =
      (y⁻¹ ^ 2 : ℝ) • (inner ℂ ψ (A ψ) / inner ℂ ψ ψ)
    rw [Complex.real_smul]
    push_cast at he ⊢
    rw [he]
    field_simp
  exact endpoint_identity_implies_claim endpoint_identity

end
end D5.S3.Quantum.SpinChains.StaggeredM1EndpointDensity
