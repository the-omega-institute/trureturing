/- GID: D5/S3/Quantum/Measurement/FullSupportRayCalibration
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FullSupportRayCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Basis.Defs]
   utility: none
   digest: An extra calibration vector identifies precisely its supported basis scalars. -/

module
public import Mathlib.LinearAlgebra.Basis.Defs

/-! A basis and one full-support vector identify a scalar multiple of an injective reference map. -/

@[expose] public section
namespace D5.S3.Quantum.Measurement.FullSupportRayCalibration

variable {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype ι]

/-- For basis-diagonal responses relative to an injective reference, an extra input
tests exactly its supported coefficients. A full-support input determines the entire map. -/
theorem support_calibration (b : Module.Basis ι K V) (J T : V →ₗ[K] W)
    (hJ : Function.Injective J) (a : ι → K) (hb : ∀ i, T (b i) = a i • J (b i))
    (u : V) (c : K) :
    (T u = c • J u ↔ ∀ i, b.repr u i ≠ 0 → a i = c) ∧
    ((∀ i, b.repr u i ≠ 0) → (T u = c • J u ↔ T = c • J)) := by
  classical
  have expand : T u = J (∑ i, (b.repr u i * a i) • b i) := by
    calc
      _ = T (∑ i, b.repr u i • b i) := congrArg T (b.sum_repr u).symm
      _ = _ := by simp only [map_sum, map_smul, hb, mul_smul]
  have eq_iff : T u = c • J u ↔
      (∑ i, (b.repr u i * a i) • b i) = c • u := by
    rw [expand, ← J.map_smul, hJ.eq_iff]
  have local_iff : T u = c • J u ↔ ∀ i, b.repr u i ≠ 0 → a i = c := by
    rw [eq_iff]
    constructor
    · intro h i hi
      have hcoord := congrArg (fun v => b.repr v i) h
      have hc : b.repr u i * a i = c * b.repr u i := by
        simpa only [b.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] using hcoord
      exact mul_left_cancel₀ hi (hc.trans (mul_comm _ _))
    · intro h
      rw [← b.sum_repr (c • u)]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : b.repr u i = 0
      · simp [hi]
      · simp [h i hi, mul_comm]
  refine ⟨local_iff, fun hu => ⟨?_, ?_⟩⟩
  · intro h
    apply b.ext
    intro i
    rw [hb, local_iff.mp h i (hu i), LinearMap.smul_apply]
  · intro h
    exact DFunLike.congr_fun h u

end D5.S3.Quantum.Measurement.FullSupportRayCalibration
