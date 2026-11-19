/- GID: D5/S3/Quantum/Algebra/Comparison/RoundTripRankOne
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/RoundTripRankOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful radial comparison excludes a two-dimensional commuting subspace. -/


import D5.S3.Quantum.Algebra.Comparison.RoundTripComparison
import D5.S3.Geometry.SphericalAdditiveKernel
import Mathlib.LinearAlgebra.FiniteDimensional.Basic


/-! The exponential kernel excludes a two-dimensional commuting subspace. -/

namespace D5.S3.Quantum.Algebra.Comparison.RoundTripRankOne

open Module
open scoped InnerProductSpace
open RoundTripComparison
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {L : LieSubalgebra ℝ A} {G : Subgroup Aˣ}

/-- The positive inner product supplied by the comparison's quadratic coefficient. -/
def metricCore (D : Data L G) : InnerProductSpace.Core ℝ L where
  inner x y := D.h x y
  conj_inner_symm x y := by simpa using D.symmetric.eq y x
  re_inner_nonneg x := (metric_consequences D).1 x
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := (metric_consequences D).2.1 x hx

/-- A nonzero infinitesimal direction has only its own line as centralizer. -/
theorem centralizer_line (D : Data L G) (X : L) (hX : X ≠ 0)
    (Y : L) (hXY : ⁅X, Y⁆ = 0) : ∃ c : ℝ, Y = c • X := by
  classical
  let B := metricCore D
  letI : NormedAddCommGroup L := B.toNormedAddCommGroup
  letI : InnerProductSpace ℝ L := InnerProductSpace.ofCore B.toCore
  let S : Submodule ℝ L := Submodule.span ℝ {X,Y}
  have hxS : X ∈ S := Submodule.subset_span (by simp)
  have hyS : Y ∈ S := Submodule.subset_span (by simp)
  have hcomm (u v : S) : Commute ((u : L) : A) ((v : L) : A) := by
    obtain ⟨a,b,hu⟩ := Submodule.mem_span_pair.mp u.property
    obtain ⟨c,d,hv⟩ := Submodule.mem_span_pair.mp v.property
    have hyx : ⁅Y,X⁆ = 0 := by rw [← lie_skew, hXY, neg_zero]
    have hh : ⁅(u : L),(v : L)⁆ = 0 := by
      rw [← hu, ← hv]
      simp [add_lie, lie_add, smul_lie, lie_smul, hXY, hyx]
    change ((u : L) : A) * ((v : L) : A) = ((v : L) : A) * ((u : L) : A)
    exact sub_eq_zero.mp (congrArg (fun z : L => (z : A)) hh)
  have hmul (u v : S) : D.exp ((u : L)+(v : L)) = D.exp u * D.exp v := by
    apply Subtype.ext
    apply Units.ext
    letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
    exact NormedSpace.exp_add_of_commute (hcomm u v)
  have hzero : D.exp (0 : L) = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact NormedSpace.exp_zero
  let K : AddSubgroup S :=
    { carrier := {u | D.exp (u : L) = 1}
      zero_mem' := hzero
      add_mem' := by
        intro u v hu hv
        change D.exp ((u : L)+(v : L)) = 1
        rw [hmul, hu, hv, one_mul]
      neg_mem' := by
        intro u hu
        change D.exp (-(u : L)) = 1
        change D.exp (u : L) = 1 at hu
        have hh := hmul (-u) u
        simpa only [Submodule.coe_neg, neg_add_cancel, hzero, hu, mul_one] using hh.symm }
  have hnorm (u : S) : D.h (u : L) (u : L) = ‖u‖^2 := by
    change ⟪(u : L),(u : L)⟫_ℝ = ‖(u : L)‖^2
    exact real_inner_self_eq_norm_sq _
  let r : ℝ := Real.sqrt 2 * Real.pi
  have hr : 0 < r := mul_pos (Real.sqrt_pos.mpr (by norm_num)) Real.pi_pos
  have hfull (u : S) (hu : ‖u‖ = r) : u ∈ K := by
    have hq : D.h (u : L) (u : L)/2 = Real.pi^2 := by
      rw [hnorm, hu]
      dsimp [r]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hs : Real.sqrt (D.h (u : L) (u : L)/2) = Real.pi := by
      rw [hq, Real.sqrt_sq Real.pi_pos.le]
    change D.exp (u : L) = 1
    apply (D.faithful _).mp
    simpa [hs] using (metric_consequences D).2.2.1 1 (u : L)
  have hhalf (u : S) (hu : ‖u‖ = r/2) : u ∉ K := by
    have hq : D.h (u : L) (u : L)/2 = (Real.pi/2)^2 := by
      rw [hnorm, hu]
      dsimp [r]
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hs : Real.sqrt (D.h (u : L) (u : L)/2) = Real.pi/2 := by
      rw [hq, Real.sqrt_sq (by positivity)]
    intro hk
    have hone : D.phi (D.exp (u : L)) = 1 := (D.faithful _).mpr hk
    have hzero : D.phi (D.exp (u : L)) = 0 := by
      simpa [hs] using (metric_consequences D).2.2.1 1 (u : L)
    linarith
  have hdim : finrank ℝ S ≤ 1 :=
    D5.S3.Geometry.SphericalAdditiveKernel.finrank_le_one_of_sphere_mem K hr hfull hhalf
  have hxnon : (⟨X,hxS⟩ : S) ≠ 0 := by
    intro hh
    exact hX (congrArg Subtype.val hh)
  letI : Nontrivial S := ⟨⟨⟨X,hxS⟩,0,hxnon⟩⟩
  have hd : finrank ℝ S = 1 := by have hp := finrank_pos (R := ℝ) (M := S); omega
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hd hxnon (⟨Y,hyS⟩ : S)
  exact ⟨c,(congrArg Subtype.val hc).symm⟩

end
end D5.S3.Quantum.Algebra.Comparison.RoundTripRankOne
