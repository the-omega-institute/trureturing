/- GID: D5/S3/Quantum/Divergence/UmegakiConditionalBKM
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiConditionalBKM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arithmetic inverse residual identity for arbitrary quantum marginals. -/

import D5.S3.Quantum.Divergence.UmegakiReferenceTransport
import D5.S3.Quantum.Divergence.UmegakiBKMPath

/-! Subtracting the marginal quadratic form is exactly the quadratic form
of a zero-partial-trace residual. The reference is an arbitrary quantum
matrix factor, with no block-diagonal restriction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport

namespace D5.S3.Quantum.Divergence.UmegakiConditionalBKM
universe u
variable {R a : Type u} [Fintype R] [DecidableEq R] [Fintype a] [DecidableEq a]

private lemma partialTraceRight_arithmetic_embed
    (Z : Matrix (R × a) (R × a) ℂ) (X : Matrix R R ℂ) (u : ℝ) :
    partialTraceRight (arithmetic Z (X ⊗ₖ (1 : Matrix a a ℂ)) u) =
      arithmetic (partialTraceRight Z) X u := by
  ext r s
  simp only [arithmetic, partialTraceRight_add,
    D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul,
    partialTraceRight_mul_embed, partialTraceRight_embed_mul]

/-- The same marginal inverse determines the residual for every correlated
joint matrix and arbitrary complex tangent. -/
def residual (Z H : Matrix (R × a) (R × a) ℂ) (u : ℝ) : Matrix (R × a) (R × a) ℂ :=
  H - arithmetic Z ((inverseMatrix (partialTraceRight Z) (partialTraceRight H) u) ⊗ₖ
    (1 : Matrix a a ℂ)) u

lemma residual_partialTrace [Nonempty a]
    (Z H : Matrix (R × a) (R × a) ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    partialTraceRight (residual Z H u) = 0 := by
  have hs := partialTraceRight_posDef Z hZ
  have h := arithmetic_inverseMatrix (partialTraceRight Z) (partialTraceRight H) u hs hu
  have hsub (V W : Matrix (R × a) (R × a) ℂ) :
      partialTraceRight (V-W) = partialTraceRight V - partialTraceRight W := by
    ext r s
    simp [partialTraceRight, Finset.sum_sub_distrib]
  rw [residual, hsub, partialTraceRight_arithmetic_embed, h, sub_self]

/-- The joint-minus-marginal form is a single native inverse quadratic form
on the actual zero-partial-trace residual. -/
theorem quadratic_difference_eq_residual [Nonempty a]
    (Z H : Matrix (R × a) (R × a) ℂ) (u : ℝ)
    (hZ : Z.PosDef) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    q Z H u - q (partialTraceRight Z) (partialTraceRight H) u =
      q Z (residual Z H u) u := by
  let S := partialTraceRight Z
  let J := partialTraceRight H
  let X := inverseMatrix S J u
  let W := X ⊗ₖ (1 : Matrix a a ℂ)
  have hs : S.PosDef := partialTraceRight_posDef Z hZ
  have hreal (A B : Matrix R R ℂ) :
      (Aᴴ * B).trace.re = (Bᴴ * A).trace.re := by
    have h := congrArg Complex.re (Matrix.trace_conjTranspose (Aᴴ * B))
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      map_star, Complex.star_def, Complex.conj_re] using h.symm
  have hpair : (Wᴴ * H).trace.re = q S J u := by
    rw [show W = X ⊗ₖ (1 : Matrix a a ℂ) from rfl, trace_embed_pair, hreal]
    exact (q_eq_trace S J u).symm
  have he : energy Z W u = q S J u := by
    rw [energy, show W = X ⊗ₖ (1 : Matrix a a ℂ) from rfl, trace_embed_pair,
      partialTraceRight_arithmetic_embed]
    exact (q_eq_energy_inverse S J u hs hu).symm
  have h := q_sub_arithmetic Z H W u hZ hu
  change q Z (residual Z H u) u = _ at h
  rw [hpair, he] at h
  linarith

end D5.S3.Quantum.Divergence.UmegakiConditionalBKM
