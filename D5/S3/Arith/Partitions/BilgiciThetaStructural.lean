/- GID: D5/S3/Arith/Partitions/BilgiciThetaStructural
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaStructural
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal weight-eleven component has a surviving homogeneous quartic cofactor. -/

import D5.S3.Arith.Partitions.BilgiciThetaJointKernel
import D5.S3.Arith.Partitions.BilgiciThetaLiteralTests

/-! The literal weight-eleven component has a surviving homogeneous quartic cofactor. -/

open D5.S3.Arith.Partitions.BilgiciThetaQuartic MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

private theorem literalF11_joint_tests : tests (q F11) = 0 :=
  Prod.ext ((ell_q 11 (by decide) F11).trans (literalF11_trace_low 11 (by decide)))
    literalF11_epsilon_zero

private theorem literalF11_in_range :
    (⟨q F11, literalF11_eigengrade⟩ : eigengrade 7 11) ∈
      LinearMap.range mulSZComponent := by
  rw [← joint_kernel]
  exact literalF11_joint_tests

private theorem range_trace_coordinates (y : eigengrade 4 9) :
    (mulSZComponent y).val =
      ((9 : K) * ell 30 (by decide) (mulSZComponent y).val) • mulS (q h₁) +
      (ell 49 (by decide) (mulSZComponent y).val -
        (9 : K) * ((9 : K) * ell 30 (by decide) (mulSZComponent y).val)) • mulS (q h₂) := by
  let z := (mulSZComponent y).val
  obtain ⟨a, b, hab⟩ := kernel_coordinates (mulSZComponent y).property (tests_mul_S_Z y)
  obtain ⟨ha, hb⟩ := cubic_trace_coordinates z a b hab.symm
  change z = _
  rw [← ha, ← hb, hab]

noncomputable def structuralQuartic : R :=
  (9 : K) • h₁ + (ell 49 (by decide) (q F11) - (9 : K) * 9) • h₂

private theorem structuralQuartic_quotient :
    q F11 = q S_Z * q structuralQuartic := by
  obtain ⟨y, hy⟩ := literalF11_in_range
  have h : (mulSZComponent y).val = q F11 := congrArg Subtype.val hy
  have hcoord := range_trace_coordinates y
  rw [h, ell_q, literalF11_trace_thirty, mul_one] at hcoord
  rw [structuralQuartic, map_add, map_smul, map_smul, mul_add, mul_smul_comm, mul_smul_comm]
  exact hcoord

/-- The quartic recovered from the joint kernel survives in the full theta quotient. -/
theorem structural_factorization :
    ∃ Q : MvPolynomial (Fin 9) (ZMod 19),
      Q = structuralQuartic ∧ Q ≠ 0 ∧
      Q.IsHomogeneous 4 ∧ Q.IsWeightedHomogeneous w (9 : ZMod 19) ∧
      (weightedHomogeneousComponent w (11 : ZMod 19) (paperB * paperC ^ 3) - S_Z * Q
        ∈ Ideal.span (Set.range theta)) ∧ Ideal.Quotient.mk ITheta Q ≠ 0 := by
  have h₁grade : h₁ ∈ grade 4 9 := by
    rw [h₁, ← spProject_denote]
    exact grade_mem.mpr (denote_grades _ _ _ (by decide))
  have h₂grade : h₂ ∈ grade 4 9 := by
    rw [h₂, ← spProject_denote]
    exact grade_mem.mpr (denote_grades _ _ _ (by decide))
  have hgrade : structuralQuartic ∈ grade 4 9 :=
    (grade 4 9).add_mem ((grade 4 9).smul_mem _ h₁grade) ((grade 4 9).smul_mem _ h₂grade)
  have hclass : q structuralQuartic ≠ 0 := by
    intro h
    exact literalF11_class_nonzero (by rw [structuralQuartic_quotient, h, mul_zero])
  have hpoly : structuralQuartic ≠ 0 := by
    intro h
    exact hclass (by rw [h, map_zero])
  obtain ⟨hd, hw⟩ := grade_mem.mp hgrade
  refine ⟨structuralQuartic, rfl, hpoly, hd, hw, ?_, hclass⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (F11 - S_Z * structuralQuartic) = 0
  rw [map_sub, map_mul, structuralQuartic_quotient, sub_self]

end D5.S3.Arith.Partitions.BilgiciThetaStructural
