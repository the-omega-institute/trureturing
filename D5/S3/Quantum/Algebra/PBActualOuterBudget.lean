/- GID: D5/S3/Quantum/Algebra/PBActualOuterBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBActualOuterBudget
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Symmetric]
   utility: none
   digest: Supporting vectors read the two actual PB outer calls without descending the original nonlinear response. -/

import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.PBActualOuterBudget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Construct a supporting vector, including the case where the first candidate vanishes. -/
private theorem supporting_vector [Nontrivial H] (n m : H →ₗ[ℝ] H)
    (hn : ∀ v, n (n v) = v) (hm : ∀ v, m (m v) = v)
    (hnm : ∀ v, n (m v) = -m (n v)) :
    ∃ v : H, ‖v‖ = 1 ∧ n v = v := by
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have exists_nonzero : ∃ v : H, v ≠ 0 ∧ n v = v := by
    by_cases h : w + n w = 0
    · have hnw : n w = -w := eq_neg_of_add_eq_zero_left h
      refine ⟨m w + n (m w), ?_, ?_⟩
      · have hmw : m w ≠ 0 := by
          intro hz
          have := hm w
          rw [hz, map_zero] at this
          exact hw this.symm
        rw [hnm, hnw, map_neg, neg_neg]
        intro hz
        exact hmw ((add_self_eq_zero.mp hz))
      · simp only [map_add, hn]
        abel
    · exact ⟨w + n w, h, by simp only [map_add, hn]; abel⟩
  obtain ⟨v, hv, hnv⟩ := exists_nonzero
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), hv]
  · simp [hnv]

/-- A symmetric operator anticommuting with a supported symmetry has zero expectation. -/
private theorem supported_orthogonal (n k : H →ₗ[ℝ] H)
    (hs : n.IsSymmetric) (v : H) (hv : n v = v)
    (hk : ∀ w, n (k w) = -k (n w)) : ⟪v, k v⟫ = 0 := by
  have he := hs v (k v)
  rw [hv, hk, hv, inner_neg_right] at he
  linarith

/-- The complete separate-owner B interface is derived debt, rather than a new raw axiom. -/
structure BDerivedInterface {E : Type*} [AddCommGroup E] [Module ℝ E]
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) (D : E → E → E) : Prop where
  unit_row : ∀ s a, D (s • u) a = 0
  rotation : ∀ a b θ, D (Real.cos θ • a + Real.sin θ • b)
    (-Real.sin θ • a + Real.cos θ • b) = D a b
  odd_left : ∀ a b, D (-a) b = -D a b
  odd_right : ∀ a b, D a (-b) = -D a b
  affine_zero : ∀ a s t x y, D (s • u + x • a) (t • u + y • a) = 0
  square_row : ∀ a s, D a (s • J a a) = 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Original PB, with both actual outer second labels preserved. -/
def PB (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E) : Prop :=
  ∀ a b c, let ν := D a b - J a c
           let ω := J a b + D a c
           D (b + ν) (c + ω) - D (b - ν) (c - ω) =
             (-2 : ℝ) • (J b ν + J c ω)

/-- A readout is linear on every original label. Multiplication is required only on
its known Jordan subspace L, not on unknown outer D outputs. No response on a quotient
is part of this structure. All vector masses, including zero, occur in P2. -/
structure Readout (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) (D : E → E → E)
    (L : Submodule ℝ E) where
  op : E →ₗ[ℝ] (H →ₗ[ℝ] H)
  symmetric : ∀ a, (op a).IsSymmetric
  unit : op u = LinearMap.id
  jordan : ∀ a ∈ L, ∀ b ∈ L, op (J a b) =
    (1 / 2 : ℝ) • ((op a).comp (op b) + (op b).comp (op a))
  p2 : ∀ (v : H) a b,
    ⟪v, op (D a b) v⟫ ^ 2 ≤
      ⟪v, op (J a a) v⟫ * ⟪v, op (J b b) v⟫ - ⟪v, op (J a b) v⟫ ^ 2

/-- An expectation of an original label, not a newly available preparation. -/
def reading {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E}
    {L : Submodule ℝ E} (R : Readout (H := H) J u D L) (v : H) : E →ₗ[ℝ] ℝ where
  toFun a := ⟪v, R.op a v⟫
  map_add' a b := by simp
  map_smul' r a := by simp

private theorem reading_jordan {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E}
    {L : Submodule ℝ E} (R : Readout (H := H) J u D L)
    {a b : E} (ha : a ∈ L) (hb : b ∈ L) (v : H) :
    reading R v (J a b) = ⟪R.op a v, R.op b v⟫ := by
  simp only [reading, LinearMap.coe_mk, AddHom.coe_mk, R.jordan a ha b hb,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    inner_smul_right, inner_add_right]
  rw [← R.symmetric a v (R.op b v), ← R.symmetric b v (R.op a v), real_inner_comm]
  ring

end D5.S3.Quantum.Algebra.PBActualOuterBudget
