/- GID: D5/S3/Quantum/Dynamics/WordHistoryOperators
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/WordHistoryOperators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Word append isometries and the unbounded finite-support length operator. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance] Classical.propDecidable
namespace D5.S3.Quantum.Dynamics.WordHistoryOperators

variable {Alphabet : Type*}
/-- The Hilbert space of square-summable amplitudes on all finite words. -/
abbrev WordHilbert (Alphabet : Type*) := lp (fun _ : List Alphabet => ℂ) 2

private def basisLine (w : List Alphabet) : ℂ →ₗᵢ[ℂ] WordHilbert Alphabet := by
  classical
  exact { lp.lsingle (𝕜 := ℂ) (E := fun _ : List Alphabet => ℂ) 2 w with norm_map' := fun x => lp.norm_single (E := fun _ : List Alphabet => ℂ) (by norm_num : (0 : ℝ≥0∞) < 2) w x }

private theorem append_orthogonal (g : Alphabet) :
    OrthogonalFamily ℂ (fun _ : List Alphabet => ℂ) (fun w => basisLine (w ++ [g])) := by
  classical
  intro v w h a b
  change inner ℂ ((lp.single (E := fun _ : List Alphabet => ℂ)) 2 (v ++ [g]) a) ((lp.single (E := fun _ : List Alphabet => ℂ)) 2 (w ++ [g]) b) = 0
  rw [lp.inner_single_left, lp.single_apply_ne]
  · simp
  · exact (List.append_left_injective [g]).ne h

/-- Right creation on the complete Hilbert space, not a finite truncation. -/
def appendShift (g : Alphabet) : WordHilbert Alphabet →ₗᵢ[ℂ] WordHilbert Alphabet :=
  (append_orthogonal g).linearIsometry

/-- Finite support is a common algebraic domain; no bounded length operator is assumed. -/
def FiniteSupport (f : WordHilbert Alphabet) : Prop := (Function.support f).Finite

/-- Length multiplication on the finite-support domain. -/
def number (f : WordHilbert Alphabet) (hf : FiniteSupport f) : WordHilbert Alphabet :=
  ⟨fun w => (w.length : ℂ) * f w,
    (memℓp_zero (hf.subset (by intro w hw; simp only [Function.mem_support] at *; contrapose! hw; simp [hw]))).of_exponent_ge (by norm_num)⟩

/-- No continuous linear operator agrees with length multiplication even on finite support. -/
theorem number_unbounded (g : Alphabet) :
    ¬ ∃ A : WordHilbert Alphabet →L[ℂ] WordHilbert Alphabet,
      ∀ (f : WordHilbert Alphabet) (hf : FiniteSupport f), A f = number f hf := by
  classical
  rintro ⟨A, hA⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖A‖
  let w := List.replicate n g
  let f : WordHilbert Alphabet := (lp.single (E := fun _ : List Alphabet => ℂ)) 2 w 1
  have hf : FiniteSupport f := by
    apply (Set.finite_singleton w).subset
    intro v hv
    by_contra h
    have hvw : v ≠ w := by simpa using h
    exact hv (lp.single_apply_ne _ _ _ hvw)
  have hN : number f hf = (n : ℂ) • f := by
    ext v
    change (v.length : ℂ) * (lp.single (E := fun _ : List Alphabet => ℂ)) 2 w 1 v = (n : ℂ) * (lp.single (E := fun _ : List Alphabet => ℂ)) 2 w 1 v
    by_cases h : v = w
    · subst v; simp [w]
    · rw [lp.single_apply_ne (E := fun _ : List Alphabet => ℂ) 2 w (1 : ℂ) h]
      simp
  have hnorm : ‖f‖ = 1 := by simp [f, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  have hb := A.le_opNorm f
  rw [hA f hf, hN, norm_smul, hnorm, mul_one, mul_one] at hb
  norm_cast at hb
  exact (not_le_of_gt hn) hb

#print axioms number_unbounded
end D5.S3.Quantum.Dynamics.WordHistoryOperators
