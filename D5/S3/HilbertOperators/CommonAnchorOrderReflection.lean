/- GID: D5/S3/HilbertOperators/CommonAnchorOrderReflection
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/CommonAnchorOrderReflection
   mirror-E: none(waiver:finite-dimensional-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Positive, mathlib/module/Mathlib.LinearAlgebra.Isomorphisms]
   utility: none
   digest: Common-anchor positive sandwich sums reflect order exactly when their linear relations admit a simultaneous decoder. -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HilbertOperators.CommonAnchorOrderReflection

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap

variable {E F S : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [Fintype S]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance : CompleteSpace F := FiniteDimensional.complete ℂ F

/-- The original weighted sandwich map, with all active components retained. -/
def sandwich (V : S → E →L[ℂ] F) (p : S → ℝ) (X : E →L[ℂ] E) : F →L[ℂ] F :=
  ∑ l, (p l : ℂ) • ((V l).comp (X.comp (V l).adjoint))

/-- Reflection is quantified over every Hermitian operator on the original carrier. -/
def ReflectsPSD (V : S → E →L[ℂ] F) (p : S → ℝ) : Prop :=
  ∀ X : E →L[ℂ] E, IsSelfAdjoint X → (sandwich V p X).IsPositive → X.IsPositive

/-- Every unit direction and every strictly positive rank-one excess is tested. -/
def RankOneTests (V : S → E →L[ℂ] F) (p : S → ℝ) : Prop :=
  ∀ x : E, ‖x‖ = 1 → ∀ η : ℝ, 0 < η →
    ¬ (sandwich V p (1 - ((1 + η : ℝ) : ℂ) • rankOne ℂ x x)).IsPositive

/-- A single complex-linear decoder works for every component simultaneously. -/
def HasDecoder (V : S → E →L[ℂ] F) : Prop :=
  ∃ C : F →L[ℂ] E, ∀ l, C.comp (V l) = 1

/-- The unweighted synthesis and sum maps use the same whole finite family. -/
def synthesis (V : S → E →L[ℂ] F) : (S → E) →ₗ[ℂ] F :=
  ∑ l, (V l).toLinearMap.comp (LinearMap.proj l)

def coordinateSum : (S → E) →ₗ[ℂ] E := ∑ l, LinearMap.proj l

/-- All complex linear relations of the local actions must preserve their sum. -/
def Compatible (V : S → E →L[ℂ] F) : Prop :=
  (synthesis V).ker ≤ (coordinateSum (E := E) (S := S)).ker

private def stack {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [AddCommGroup H] [Module ℂ H] (A : S → G →ₗ[ℂ] H) :
    G →ₗ[ℂ] PiLp 2 (fun _ : S => H) :=
  (WithLp.linearEquiv 2 ℂ (S → H)).symm.toLinearMap.comp (LinearMap.pi A)

private theorem stack_apply {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [AddCommGroup H] [Module ℂ H] (A : S → G →ₗ[ℂ] H) (z : G) (l : S) :
    stack A z l = A l z := rfl

private theorem norm_stack_sq {G : Type*} [AddCommGroup G] [Module ℂ G]
    (A : S → G →ₗ[ℂ] E) (z : G) :
    ‖stack A z‖ ^ 2 = ∑ l, ‖A l z‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

private theorem factor_of_kernel {G H K : Type*}
    [AddCommGroup G] [Module ℂ G] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup K] [Module ℂ K]
    (A : G →ₗ[ℂ] K) (B : G →ₗ[ℂ] H) (h : B.ker ≤ A.ker) :
    ∃ D : H →ₗ[ℂ] K, D.comp B = A := by
  let D₀ := (B.ker.liftQ A h).comp B.quotKerEquivRange.symm.toLinearMap
  obtain ⟨D, hD⟩ := D₀.exists_extend
  refine ⟨D, ?_⟩
  ext z
  have hd := congrArg (fun L => L ⟨B z, LinearMap.mem_range_self B z⟩) hD
  simpa [D₀] using hd

private theorem finite_kernel_bound {G H K : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : G →ₗ[ℂ] K) (B : G →ₗ[ℂ] H) (h : B.ker ≤ A.ker) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, ‖A z‖ ^ 2 ≤ c * ‖B z‖ ^ 2 := by
  obtain ⟨D, hD⟩ := factor_of_kernel A B h
  let c := ‖D.toContinuousLinearMap‖ ^ 2 + 1
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro z
  have hd : D (B z) = A z := congrArg (fun L => L z) hD
  have hn := D.toContinuousLinearMap.le_opNorm (B z)
  rw [hd] at hn
  have hs := sq_le_sq₀ (norm_nonneg (A z)) (by positivity) |>.mpr hn
  dsimp [c]
  nlinarith [sq_nonneg ‖B z‖]

private theorem sandwich_selfAdjoint (V : S → E →L[ℂ] F) (p : S → ℝ)
    {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) : IsSelfAdjoint (sandwich V p X) := by
  classical
  apply IsSelfAdjoint.sum
  intro l _
  apply IsSelfAdjoint.smul
  · exact Complex.isSelfAdjoint_ofReal _
  · simpa only [mul_def, comp_assoc] using hX.conjugate (V l).adjoint

private theorem sandwich_positive (V : S → E →L[ℂ] F) (p : S → ℝ)
    (hp : ∀ l, 0 ≤ p l) {X : E →L[ℂ] E} (hX : X.IsPositive) :
    (sandwich V p X).IsPositive := by
  apply isPositive_sum
  intro l _
  exact (hX.conj_adjoint (V l)).smul_of_nonneg (by simpa using hp l)

private theorem decoder_compression (V : S → E →L[ℂ] F) (p : S → ℝ)
    (hsum : ∑ l, p l = 1) (C : F →L[ℂ] E) (hC : ∀ l, C.comp (V l) = 1)
    (X : E →L[ℂ] E) : C.comp ((sandwich V p X).comp C.adjoint) = X := by
  classical
  have hadj (l : S) : (V l).adjoint.comp C.adjoint = 1 := by
    rw [← adjoint_comp, hC l, adjoint_one]
  calc
    _ = ∑ l, (p l : ℂ) • X := by
      simp only [sandwich, sum_comp, comp_sum, smul_comp, comp_smul, comp_assoc]
      apply Finset.sum_congr rfl
      intro l _
      rw [← comp_assoc (C) (V l), hC l, one_comp, comp_assoc, hadj l, comp_one]
    _ = X := by rw [← Finset.sum_smul, ← Complex.ofReal_sum, hsum]; simp

end D5.S3.HilbertOperators.CommonAnchorOrderReflection
