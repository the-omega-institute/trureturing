import D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Defs

noncomputable section
open Matrix Set Module
open scoped BigOperators
open D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings
set_option autoImplicit false

-- Exact coefficient-rank/radical-span bridge, using only pinned linear algebra.
theorem fib_radical_span_check {d : ℕ} {R : Type*} [AddCommGroup R] [Module ℝ R]
    (r : Basis (Fin d) ℝ R) (A : Coeff d) :
    A.rank = d ↔
      Submodule.span ℝ (Set.range fun y => ∑ j, A y j • r j) = ⊤ := by
  letI : FiniteDimensional ℝ R := Module.Finite.of_basis r
  let e := r.equivFun.symm
  let P := Submodule.span ℝ (Set.range A.row)
  have hm : P.map e.toLinearMap =
      Submodule.span ℝ (Set.range fun y => ∑ j, A y j • r j) := by
    have he : e ∘ A.row = (fun y => ∑ j, A y j • r j) := by
      funext y
      exact r.equivFun_symm_apply (A y)
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span ℝ (Set.range (e ∘ A.row)) = _
    rw [he]
  have hd : finrank ℝ (Fin d → ℝ) = d := by simp
  have hr : A.rank = finrank ℝ P := A.rank_eq_finrank_span_row
  have hf := LinearEquiv.finrank_map_eq e P
  constructor
  · intro h
    rw [← hm]
    apply Submodule.eq_top_of_finrank_eq
    rw [hf, ← hr, h, ← hd]
    exact LinearEquiv.finrank_eq e
  · intro h
    rw [← hm] at h
    rw [hr, ← hf, h, finrank_top, ← LinearEquiv.finrank_eq e]
    exact hd

-- Full pointwise quotient/section and residual bridge for arbitrary representatives.
theorem fib_quotient_section_check {X W Q : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Q] [Module ℝ Q]
    (ev : W →ₗ[ℝ] (X → ℝ)) (T : W →ₗ[ℝ] Q) (S : Q →ₗ[ℝ] W)
    (hTS : ∀ q, T (S q) = q)
    (oneW : W) (oneQ : Q) (hunit : ev oneW = 1) (hS : S oneQ = oneW)
    (f : Label → Q) (hf : ∑ y, f y = oneQ)
    {d : ℕ} (r : Basis (Fin d) ℝ (LinearMap.ker T))
    (F : W →ₗ[ℝ] W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (Fq : Q →ₗ[ℝ] Q →ₗ[ℝ] Q →ₗ[ℝ] ℝ)
    (hF : ∀ x y z, F x y z = Fq (T x) (T y) (T z))
    (A : Coeff d)
    (hA : A ∈ body (fun y => ev (S (f y))) (fun j => ev (r j).val)) :
    let rho : Label → W := fun y => ∑ j, A y j • (r j).val
    let u : Label → W := fun y => S (f y) + rho y
    (∀ y x, 0 ≤ ev (u y) x) ∧ (∑ y, u y = oneW) ∧
    (∀ x, ∑ y, ev (u y) x = 1) ∧
    (∀ y, T (u y) = f y) ∧
    (∀ y z k, F (u y) (u z) (u k) = Fq (f y) (f z) (f k)) := by
  dsimp only
  have hTr (j) : T (r j).val = 0 := (r j).property
  have hTu (y) : T (S (f y) + ∑ j, A y j • (r j).val) = f y := by
    simp [map_add, map_sum, hTr, hTS]
  have hsum : (∑ y, (S (f y) + ∑ j, A y j • (r j).val)) = oneW := by
    rw [Finset.sum_add_distrib, ← map_sum, hf, hS, Finset.sum_comm]
    have hz : (∑ j, ∑ y, A y j • (r j).val) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [← Finset.sum_smul, hA.1 j, zero_smul]
    rw [hz, add_zero]
  refine ⟨?_, hsum, ?_, hTu, ?_⟩
  · intro y x
    simpa only [map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hA.2 y x
  · intro x
    have he := congrArg ev hsum
    rw [map_sum, hunit] at he
    simpa only [Finset.sum_apply, Pi.one_apply] using congrFun he x
  · intro y z k
    rw [hF, hTu, hTu, hTu]

-- Exact original four-label application; the original whole result remains polymorphic in X.
def fib_exact_application {X : Type*} (b : Label → X → ℝ)
    (r₁ : Fin 1 → X → ℝ) (r₂ : Fin 2 → X → ℝ) := result b r₁ r₂

-- A whole convex zero-sum family with rank two and no rank-one endpoint.
-- This checks the boundary of the conditional exclusion, not an unrestricted converse.
theorem fib_singleton_boundary : ∃ C : Set (Coeff 2),
    Convex ℝ C ∧ (∀ A ∈ C, ZeroSum A) ∧
    (∃ A ∈ C, A.rank = 2) ∧
    ¬ ∃ A ∈ C, ∃ B ∈ C, TransversePair A B := by
  let D : Coeff 2 := fun y j => match y with
    | .zero => if j = 0 then 1 else 0
    | .one => if j = 0 then -1 else 0
    | .three => if j = 1 then 1 else 0
    | .B => if j = 1 then -1 else 0
  rcases result (X := Empty) 0 0 0 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hrank⟩
  have hD : D.rank = 2 := by
    apply (hrank D).mpr
    refine ⟨Label.zero, Label.three, 0, 1, ?_⟩
    unfold minor
    rw [Matrix.det_fin_two]
    change (1 : ℝ) * 1 - 0 * 0 ≠ 0
    norm_num
  refine ⟨{D}, convex_singleton D, ?_, ⟨D, rfl, hD⟩, ?_⟩
  · intro A hA
    have hAD : A = D := hA
    subst A
    intro j
    have he : (Finset.univ : Finset Label) =
        {Label.zero, Label.one, Label.three, Label.B} := by decide
    rw [he]
    fin_cases j <;> norm_num [D]
  · rintro ⟨A, hA, B, _, hp⟩
    have hAD : A = D := hA
    have h1 := hp.2.2.1
    rw [hAD, hD] at h1
    norm_num at h1

#print axioms fib_radical_span_check
#print axioms fib_quotient_section_check
#print axioms fib_exact_application
#print axioms fib_singleton_boundary
