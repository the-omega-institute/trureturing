/- GID: D5/S3/Quantum/Matrix/RadialConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/RadialConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order, mathlib/module/Mathlib.Analysis.InnerProductSpace.Calculus, mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue]
   utility: none
   digest: Endpoint derivative positivity controls both distances on ordered segments. -/

/-
admission_basis: escape-witness
proof_shape: radial_inequalities_of_endpoint_derivative: content
escape_witness: radial_inequalities_of_endpoint_derivative
-/

import D5.S3.Quantum.Matrix.CartesianVariance
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

open Set
open scoped MatrixOrder ComplexOrder RealInnerProductSpace

namespace D5.S3.Quantum.Matrix.RadialConvexity

/-- Continuous functional calculus on Hermitian matrices. Its values outside the
Hermitian domain are irrelevant to the positive-definite predicates below. -/
noncomputable def matFun {n : ℕ} (f : ℝ → ℝ)
    (A : _root_.Matrix (Fin n) (Fin n) ℂ) : _root_.Matrix (Fin n) (Fin n) ℂ :=
  cfc f A

/-- The Frobenius norm, using the Euclidean norm of all matrix entries. -/
def frobeniusNorm {n : ℕ} (A : _root_.Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖CartesianVariance.vectorize n A‖

/-- Both endpoint distances grow along an ordered positive-definite interval. -/
def RadiallyConvexOrder (n : ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ A C B : _root_.Matrix (Fin n) (Fin n) ℂ,
    A.PosDef → C.PosDef → B.PosDef → A ≤ C → C ≤ B →
    frobeniusNorm (matFun f C - matFun f A) ≤
        frobeniusNorm (matFun f B - matFun f A) ∧
      frobeniusNorm (matFun f B - matFun f C) ≤
        frobeniusNorm (matFun f B - matFun f A)

/-- The paper permits either the increasing or the decreasing Loewner direction. -/
def MatrixMonotoneDegree (n : ℕ) (f : ℝ → ℝ) : Prop :=
  (∀ A B : _root_.Matrix (Fin n) (Fin n) ℂ,
    A.PosDef → B.PosDef → A ≤ B → matFun f A ≤ matFun f B) ∨
  (∀ A B : _root_.Matrix (Fin n) (Fin n) ℂ,
    A.PosDef → B.PosDef → A ≤ B → matFun f B ≤ matFun f A)

section EndpointCriterion

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Both endpoint derivative pairings are nonnegative in every positive direction. -/
def EndpointDerivativePositive (s : Set E) (g : E → F) (D : E → E →L[ℝ] F) : Prop :=
  ∀ U ∈ s, ∀ V ∈ s, U ≤ V → ∀ K : E, 0 ≤ K →
    0 ≤ ⟪g V - g U, D U K⟫ ∧ 0 ≤ ⟪g V - g U, D V K⟫

private theorem norm_sub_le_of_segment_derivative
    {g : ℝ → F} {v : ℝ → F} {a : F}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (v t) t)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ⟪g t - a, v t⟫) :
    ‖g 0 - a‖ ≤ ‖g 1 - a‖ := by
  have hd' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := ((hd t ht).sub_const a).norm_sq
  have hc : ContinuousOn (fun t => ‖g t - a‖ ^ 2) (Icc (0 : ℝ) 1) :=
    fun t ht => (hd' t ht).continuousAt.continuousWithinAt
  have hm : MonotoneOn (fun t => ‖g t - a‖ ^ 2) (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc
    · intro t ht
      exact (hd' t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd' t (interior_subset ht)).deriv]
      exact mul_nonneg (by norm_num) (hp t (interior_subset ht))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (hm (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num))

/-- On an ordered convex domain, nonnegative endpoint pairings of the derivative
with every positive direction imply both radial inequalities. The segment
hypothesis exposes the exact order and domain facts needed by the argument. -/
theorem radial_inequalities_of_endpoint_derivative
    (s : Set E) (g : E → F) (D : E → E →L[ℝ] F)
    (hsegment : ∀ U ∈ s, ∀ V ∈ s, U ≤ V → ∀ t ∈ Icc (0 : ℝ) 1,
      U + t • (V - U) ∈ s ∧ U ≤ U + t • (V - U) ∧ U + t • (V - U) ≤ V)
    (hderiv : ∀ C ∈ s, HasFDerivAt g (D C) C)
    (hpositive : EndpointDerivativePositive s g D)
    {A C B : E} (hA : A ∈ s) (hC : C ∈ s) (hB : B ∈ s)
    (hAC : A ≤ C) (hCB : C ≤ B) :
    ‖g C - g A‖ ≤ ‖g B - g A‖ ∧ ‖g B - g C‖ ≤ ‖g B - g A‖ := by
  constructor
  · have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := hsegment C hC B hB hCB t ht
    have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun t : ℝ => g (C + t • (B - C)))
        (D (C + t • (B - C)) (B - C)) t := by
      simpa only [id_eq, one_smul, Function.comp_def] using (hderiv _ (hs t ht).1).comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const (B - C)).const_add C)
    have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ ⟪g (C + t • (B - C)) - g A,
        D (C + t • (B - C)) (B - C)⟫ :=
      (hpositive A hA _ (hs t ht).1 (hAC.trans (hs t ht).2.1)
        (B - C) (sub_nonneg.mpr hCB)).2
    simpa using norm_sub_le_of_segment_derivative hd hp
  · have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := hsegment A hA C hC hAC t ht
    have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun t : ℝ => g (A + t • (C - A)))
        (D (A + t • (C - A)) (C - A)) t := by
      simpa only [id_eq, one_smul, Function.comp_def] using (hderiv _ (hs t ht).1).comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const (C - A)).const_add A)
    have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ ⟪g B - g (A + t • (C - A)),
        D (A + t • (C - A)) (C - A)⟫ :=
      (hpositive _ (hs t ht).1 B hB ((hs t ht).2.2.trans hCB)
        (C - A) (sub_nonneg.mpr hAC)).1
    have hd' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := ((hd t ht).const_sub (g B)).norm_sq
    have hc : ContinuousOn (fun t => ‖g B - g (A + t • (C - A))‖ ^ 2)
        (Icc (0 : ℝ) 1) :=
      fun t ht => (hd' t ht).continuousAt.continuousWithinAt
    have hm : AntitoneOn (fun t => ‖g B - g (A + t • (C - A))‖ ^ 2)
        (Icc (0 : ℝ) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc
      · intro t ht
        exact (hd' t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hd' t (interior_subset ht)).deriv]
        simp only [inner_neg_right]
        nlinarith [hp t (interior_subset ht)]
    have he := hm (by constructor <;> norm_num) (by constructor <;> norm_num)
      (by norm_num : (0 : ℝ) ≤ 1)
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at he
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

end EndpointCriterion

end D5.S3.Quantum.Matrix.RadialConvexity
