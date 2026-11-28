/- GID: D5/S3/LinearAlgebra/Matrix/RealRayleigh
   generality: G
   mirror-B: none(waiver:covered-by-mixed-power-graft-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate Rayleigh maxima for finite real matrices. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-! Omega original. Coordinate Rayleigh maxima for finite real matrices. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset WithLp Metric

noncomputable section

namespace OmegaMath.RealRayleigh

variable {V : Type*} [Fintype V] [DecidableEq V]

def energy (A : Matrix V V ℝ) (x : V → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

def UnitVector (x : V → ℝ) : Prop := ∑ i, x i ^ 2 = 1

private def operator (A : Matrix V V ℝ) : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  A.toEuclideanLin.toContinuousLinearMap

private theorem energy_operator (A : Matrix V V ℝ) (x : EuclideanSpace ℝ V) :
    (operator A).reApplyInnerSelf x = energy A x.ofLp := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, EuclideanSpace.inner_eq_star_dotProduct]
  change x.ofLp ⬝ᵥ star ((operator A) x).ofLp = _
  simp [operator, energy, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

omit [DecidableEq V] in
private theorem unitVector_iff (x : EuclideanSpace ℝ V) :
    UnitVector x.ofLp ↔ ‖x‖ = 1 := by
  rw [UnitVector, ← EuclideanSpace.real_norm_sq_eq]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    rw [h]
    norm_num

def topEigenvalue (A : Matrix V V ℝ) : ℝ :=
  ⨆ x : sphere (0 : EuclideanSpace ℝ V) 1, (operator A).reApplyInnerSelf x

theorem top_attained [Nonempty V] (A : Matrix V V ℝ) :
    ∃ x : V → ℝ, UnitVector x ∧ energy A x = topEigenvalue A ∧
      ∀ y : V → ℝ, UnitVector y → energy A y ≤ topEigenvalue A := by
  have hn : (sphere (0 : EuclideanSpace ℝ V) 1).Nonempty := by
    let i : V := Classical.choice ‹Nonempty V›
    let x : EuclideanSpace ℝ V := toLp 2 (Pi.single i 1)
    refine ⟨x, ?_⟩
    have hu : UnitVector x.ofLp := by
      simp [UnitVector, x, Pi.single_apply, ite_pow]
    simpa using (unitVector_iff x).mp hu
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ V) 1).exists_isMaxOn hn
      (operator A).reApplyInnerSelf_continuous.continuousOn
  have htop : topEigenvalue A = (operator A).reApplyInnerSelf x :=
    IsMaxOn.iSup_eq hx hmax
  refine ⟨x.ofLp, (unitVector_iff x).mpr (by simpa using hx), ?_, ?_⟩
  · rw [htop, energy_operator]
  · intro y hy
    let z : EuclideanSpace ℝ V := toLp 2 y
    have hz : z ∈ sphere (0 : EuclideanSpace ℝ V) 1 := by
      simpa using (unitVector_iff z).mp hy
    have hle := hmax hz
    change (operator A).reApplyInnerSelf z ≤ (operator A).reApplyInnerSelf x at hle
    rw [energy_operator A z, ← htop] at hle
    exact hle

theorem energy_le_top [Nonempty V] (A : Matrix V V ℝ) {x : V → ℝ}
    (hx : UnitVector x) : energy A x ≤ topEigenvalue A := by
  obtain ⟨_, _, _, h⟩ := top_attained A
  exact h x hx

theorem mulVec_eq_top_of_max [Nonempty V] (A : Matrix V V ℝ) (hA : A.IsHermitian)
    {x : V → ℝ} (hx : UnitVector x) (hmax : energy A x = topEigenvalue A) :
    A *ᵥ x = topEigenvalue A • x := by
  let z : EuclideanSpace ℝ V := toLp 2 x
  have hz : ‖z‖ = 1 := (unitVector_iff z).mp hx
  have hs : IsSelfAdjoint (operator A) :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).toSelfAdjoint.prop
  have hm : IsMaxOn (operator A).reApplyInnerSelf (sphere 0 ‖z‖) z := by
    intro y hy
    rw [hz] at hy
    change (operator A).reApplyInnerSelf y ≤ (operator A).reApplyInnerSelf z
    rw [energy_operator, energy_operator]
    change energy A y.ofLp ≤ energy A x
    rw [hmax]
    exact energy_le_top A ((unitVector_iff y).mpr (by simpa using hy))
  have heq := hs.eq_smul_self_of_isLocalExtrOn_real (Or.inr hm.isLocalMaxOn)
  have hq : (operator A).rayleighQuotient z = topEigenvalue A := by
    simp [ContinuousLinearMap.rayleighQuotient, hz, energy_operator, z, hmax]
  rw [hq] at heq
  have heq' := congrArg (fun y : EuclideanSpace ℝ V => y.ofLp) heq
  simpa [operator, Matrix.toEuclideanLin, Matrix.toLpLin_apply, z] using heq'

theorem top_isGreatest [Nonempty V] (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    IsGreatest (spectrum ℝ A) (topEigenvalue A) := by
  obtain ⟨x, hx, hmax, _⟩ := top_attained A
  have he := mulVec_eq_top_of_max A hA hx hmax
  refine ⟨?_, ?_⟩
  · have hev : Module.End.HasEigenvector A.toEuclideanLin (topEigenvalue A) (toLp 2 x) := by
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, he]
      · intro h
        have hzero : x = 0 := congrArg (fun z : EuclideanSpace ℝ V => z.ofLp) h
        simp [UnitVector, hzero] at hx
    rw [← Matrix.spectrum_toLpLin (A := A) 2]
    exact (Module.End.hasEigenvalue_of_hasEigenvector hev).mem_spectrum
  · intro a ha
    rw [hA.spectrum_real_eq_range_eigenvalues] at ha
    obtain ⟨i, rfl⟩ := ha
    rw [hA.eigenvalues_eq i]
    change energy A (hA.eigenvectorBasis i).ofLp ≤ _
    exact energy_le_top A ((unitVector_iff _).mpr (hA.eigenvectorBasis.orthonormal.1 i))

omit [DecidableEq V] in
theorem energy_expand (A : Matrix V V ℝ) (x : V → ℝ) :
    energy A x = ∑ i, ∑ j, A i j * (x i * x j) := by
  simp only [energy, dotProduct, mulVec, Finset.mul_sum]
  congr 1
  ext i
  congr 1
  ext j
  ring

omit [DecidableEq V] in
private theorem energy_abs_le (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (x : V → ℝ) : energy A x ≤ energy A (fun i => |x i|) := by
  rw [energy_expand, energy_expand]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hA i j)
  rw [← abs_mul]
  exact le_abs_self _

theorem nonnegative_maximizer [Nonempty V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) :
    ∃ x : V → ℝ, UnitVector x ∧ energy A x = topEigenvalue A ∧
      A *ᵥ x = topEigenvalue A • x ∧ ∀ i, 0 ≤ x i := by
  obtain ⟨x, hx, he, _⟩ := top_attained A
  let y : V → ℝ := fun i => |x i|
  have hy : UnitVector y := by simpa [UnitVector, y, sq_abs] using hx
  have hymax : energy A y = topEigenvalue A :=
    le_antisymm (energy_le_top A hy) (he ▸ energy_abs_le A hnonneg x)
  exact ⟨y, hy, hymax, mulVec_eq_top_of_max A hA hy hymax, fun i => abs_nonneg _⟩

end OmegaMath.RealRayleigh
