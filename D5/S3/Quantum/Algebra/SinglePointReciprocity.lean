/- GID: D5/S3/Quantum/Algebra/SinglePointReciprocity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/SinglePointReciprocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full single-point compensation forces a scalar commutant and an axial centralizer. -/

import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic

/-! Complete quotient compensation and its conditional invariant-metric consequences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.SinglePointReciprocity

attribute [local instance 100] LieRing.ofAssociativeRing

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable (g : LieSubalgebra ℝ (Module.End ℝ W))

/-- The image of every solution of the original linearized equation in the two full quotients. -/
def tangentRelation (A : g) (x : W) :
    Set ((g ⧸ ℝ ∙ A) × (W ⧸ ℝ ∙ x)) :=
  {p | ∃ K : g, ∃ y : W,
    (Submodule.Quotient.mk K : g ⧸ ℝ ∙ A) = p.1 ∧
    (Submodule.Quotient.mk y : W ⧸ ℝ ∙ x) = p.2 ∧
    (K : Module.End ℝ W) x + (A : Module.End ℝ W) y = 0}

/-- A single nonzero stopped pair and both canonical bijections on the entire relation. -/
structure SinglePoint (A : g) (x : W) : Prop where
  operator_ne_zero : A ≠ 0
  vector_ne_zero : x ≠ 0
  stopped : (A : Module.End ℝ W) x = 0
  control_bijective : Function.Bijective
    (fun p : tangentRelation g A x => p.val.1)
  content_bijective : Function.Bijective
    (fun p : tangentRelation g A x => p.val.2)

variable {g} {A : g} {x : W}

private def solution (K : g) (y : W)
    (h : (K : Module.End ℝ W) x + (A : Module.End ℝ W) y = 0) :
    tangentRelation g A x :=
  ⟨(Submodule.Quotient.mk K, Submodule.Quotient.mk y), K, y, rfl, rfl, h⟩

private theorem kernel_axis (h : SinglePoint g A x) {y : W}
    (hy : (A : Module.End ℝ W) y = 0) : y ∈ ℝ ∙ x := by
  have e := h.control_bijective.1
    (a₁ := solution (0 : g) y (by simpa using hy))
    (a₂ := solution (0 : g) 0 (by simp)) rfl
  have q := congrArg (fun p : tangentRelation g A x => p.val.2) e
  exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa [solution] using q)

private theorem stabilizer_axis (h : SinglePoint g A x) {K : g}
    (hK : (K : Module.End ℝ W) x = 0) : K ∈ ℝ ∙ A := by
  have e := h.content_bijective.1
    (a₁ := solution K 0 (by simpa using hK))
    (a₂ := solution (0 : g) 0 (by simp)) rfl
  have q := congrArg (fun p : tangentRelation g A x => p.val.1) e
  exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa [solution] using q)

/-- A commuting original generator lies on the witness axis, assuming the invariant metric. -/
theorem centralizer_eq_axis (h : SinglePoint g A x)
    (skew : ∀ K : g, ∀ u v : W,
      inner ℝ ((K : Module.End ℝ W) u) v = -inner ℝ u ((K : Module.End ℝ W) v))
    (K : g) :
    Commute (A : Module.End ℝ W) (K : Module.End ℝ W) ↔ K ∈ ℝ ∙ A := by
  constructor
  · intro hc
    have hz : (A : Module.End ℝ W) ((K : Module.End ℝ W) x) = 0 := by
      calc
        _ = (K : Module.End ℝ W) ((A : Module.End ℝ W) x) :=
          LinearMap.congr_fun hc.eq x
        _ = 0 := by rw [h.stopped, map_zero]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (kernel_axis h hz)
    have hip := skew K x x
    rw [← hc, real_inner_smul_left, real_inner_smul_right] at hip
    have hxx : inner ℝ x x ≠ 0 := by exact fun he => h.vector_ne_zero ((inner_self_eq_zero).mp he)
    have hcx : c * inner ℝ x x = 0 := by linarith
    have hc0 : c = 0 := (mul_eq_zero.mp hcx).resolve_right hxx
    apply stabilizer_axis h
    simpa [hc0] using hc.symm
  · intro hK
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hK
    change (A : Module.End ℝ W) * (c • (A : Module.End ℝ W)) =
      (c • (A : Module.End ℝ W)) * (A : Module.End ℝ W)
    simp only [mul_smul_comm, smul_mul_assoc]

end D5.S3.Quantum.Algebra.SinglePointReciprocity
