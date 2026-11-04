/- GID: D5/S3/Quantum/Algebra/OriginalCompactReciprocity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OriginalCompactReciprocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original matrix-group velocities and the complete first-order relation. -/

module

public import D5.S3.Quantum.Algebra.OriginalCompactActionMetric
public import D5.S3.Quantum.Algebra.RankOneInvariantMetric
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section

namespace D5.S3.Quantum.Algebra.OriginalCompactReciprocity

open OriginalCompactActionMetric Module
open scoped Topology InnerProductSpace
noncomputable section
universe u
variable {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]
variable (G : MatrixGroup W)

/-- Velocities in the actual ambient matrix space of actual G-valued curves at 1. -/
def velocitySpace : Submodule ℝ (W →L[ℝ] W) where
  carrier := {K | ∃ c : ℝ → G, c 0 = 1 ∧ HasDerivAt (fun t => (c t).val.val) K 0}
  zero_mem' := ⟨fun _ => 1,rfl,hasDerivAt_const 0 1⟩
  add_mem' := by
    rintro K L ⟨c,hc,hK⟩ ⟨d,hd,hL⟩
    refine ⟨fun t => c t * d t,by simp [hc,hd],?_⟩
    simpa [hc,hd] using hK.mul hL
  smul_mem' := by
    rintro r K ⟨c,hc,hK⟩
    refine ⟨fun t => c (r*t),by simpa using hc,?_⟩
    simpa using hK.scomp 0 ((hasDerivAt_id 0).const_mul r)

private theorem conjugate_velocity (g : G) (K : W →L[ℝ] W)
    (hK : K ∈ velocitySpace G) :
    (g.val.val * K * g⁻¹.val.val) ∈ velocitySpace G := by
  obtain ⟨c,hc,hcK⟩ := hK
  refine ⟨fun t => g * c t * g⁻¹,by simp [hc],?_⟩
  simpa [hc] using ((hasDerivAt_const (0 : ℝ) g.val.val).mul hcK).mul_const g⁻¹.val.val

private theorem bracket_velocity (K L : W →L[ℝ] W)
    (hK : K ∈ velocitySpace G) (hL : L ∈ velocitySpace G) :
    ⁅K,L⁆ ∈ velocitySpace G := by
  obtain ⟨c,hc,hcK⟩ := hK
  have hinv : HasDerivAt (fun t => (c t)⁻¹.val.val) (-K) 0 := by
    have hh := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (W →L[ℝ] W)ˣ)).comp_hasDerivAt
      0 (by simpa [hc] using hcK)
    simpa [Ring.inverse_unit,ContinuousLinearMap.mulLeftRight_apply] using hh
  have hd := (hcK.mul_const L).mul hinv
  have hh : HasDerivAt (fun t => (c t).val.val * L * (c t)⁻¹.val.val)
      (K*L-L*K) 0 := by
    simpa [hc,sub_eq_add_neg] using hd
  have hm : ∀ t : ℝ, (c t).val.val * L * (c t)⁻¹.val.val ∈ velocitySpace G :=
    fun t => conjugate_velocity G (c t) L hL
  have hz := mem_closure_of_tendsto hh.tendsto_slope
    (Filter.Eventually.of_forall fun t =>
      (velocitySpace G).smul_mem _ ((velocitySpace G).sub_mem (hm t) (hm 0)))
  rw [(velocitySpace G).closed_of_finiteDimensional.closure_eq] at hz
  exact hz

/-- The actual curve velocities form a Lie algebra under the actual matrix commutator. -/
def curveLieAlgebra : LieSubalgebra ℝ (W →L[ℝ] W) :=
  { velocitySpace G with
    lie_mem' := fun hK hL => bracket_velocity G _ _ hK hL }

end
end D5.S3.Quantum.Algebra.OriginalCompactReciprocity
