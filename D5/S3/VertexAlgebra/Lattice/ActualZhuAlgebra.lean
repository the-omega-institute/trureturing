/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual nonzero unital complex Zhu algebra on the full original quotient. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native adaptation of VOA/Modules/ZhuRing.lean,
Fedor-Popov/Lean_VOA at 013a799ca834a8a6b3afa8129e3e522025b3f45c.
Mathlib supplies bilinear quotient descent. All algebra laws use the proved
native stabilities and associator, with no assumed ZhuRingData.
proof_shape: vacuum_not_mem_zhuO: content; quotientProduct_mk: bind-only.
admission_basis: escape-witness.
escape_witness: grade-zero projection annihilates each literal circle through
the actual mode-energy law, and retains the nonzero vacuum. No grading of O
is asserted. Quotient-product computations are consumed by the ring laws.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuLeftIdeal
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.Algebra.Basic
/-! Bilinear descent, actual ring laws, and the surviving vacuum class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticePositiveEnergy ActualZhuProduct
open scoped BigOperators VertexOperator
noncomputable section

/-- The original additive and complex-linear quotient, without a carrier change. -/
abbrev Q (D : LatticeData) := Carrier D ⧸ ActualZhuFinite.zhuO D

private theorem vacuum_grade (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : vacuum D ∈ grade D 0 := by
  rw [grade_zero D hD]
  exact Submodule.subset_span (Set.mem_singleton _)

private theorem star_vacuum_left (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (v : Carrier D) :
    star D (vacuum D) v = v := by
  rw [star_homogeneous D 0 (vacuum D) v (vacuum_grade D hD)]
  simp [mu, stateField_vacuum, identity_modes]

private theorem star_vacuum_right_homogeneous (D : LatticeData) {K : ℕ} {u : Carrier D}
    (hu : u ∈ grade D (K : ℤ)) : star D u (vacuum D) = u := by
  classical
  rw [star_homogeneous D K u (vacuum D) hu, Finset.sum_range_succ']
  have hz : ∑ j ∈ Finset.range K,
      (K.choose (j+1) : ℂ) • mu D u (((j+1 : ℕ) : ℤ)-1) (vacuum D) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hc := stateField_creativity D u (((j+1 : ℕ) : ℤ)-1) (by omega)
    simp only [mu, hc, smul_zero]
  rw [hz]
  simp [mu, stateField_creation]

private theorem star_vacuum_right (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (u : Carrier D) :
    star D u (vacuum D) = u := by
  classical
  conv_lhs => rw [← sum_gradeProjections D u]
  simp only [map_sum, LinearMap.sum_apply]
  conv_rhs => rw [← sum_gradeProjections D u]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hu : gradeProjection D k u ∈ grade D (k.toNat : ℤ) := by
    simpa only [Int.toNat_of_nonneg (stateEnergies_nonneg hD u k hk)] using
      gradeProjection_mem D k u
  exact star_vacuum_right_homogeneous D hu

private def seed (D : LatticeData) := (star D).compr₂ (ActualZhuFinite.zhuO D).mkQ

private theorem seed_left_kernel (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ActualZhuFinite.zhuO D ≤ (seed D).ker := by
  intro o ho
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro v
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (ActualZhuLeftIdeal.star_left_mem_zhuO D hD o v ho)

private theorem seed_right_kernel (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ActualZhuFinite.zhuO D ≤ (seed D).flip.ker := by
  intro o ho
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro v
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (ActualZhuRightIdeal.star_right_mem_zhuO D hD v o ho)

/-- Actual star descended using both proved stabilities of the literal circle span. -/
def quotientProduct (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : Q D →ₗ[ℂ] Q D →ₗ[ℂ] Q D :=
  (seed D).liftQ₂ (ActualZhuFinite.zhuO D) (ActualZhuFinite.zhuO D)
    (seed_left_kernel D hD) (seed_right_kernel D hD)

/-- Representative computation, consumed by the quotient ring laws. -/
theorem quotientProduct_mk (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (u v : Carrier D) :
    quotientProduct D hD ((ActualZhuFinite.zhuO D).mkQ u) ((ActualZhuFinite.zhuO D).mkQ v)
      = (ActualZhuFinite.zhuO D).mkQ (star D u v) := rfl

/-- The associative unital ring on the existing quotient AddCommGroup. -/
@[instance_reducible]
def quotientRing (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : Ring (Q D) where
  __ := (inferInstance : AddCommGroup (Q D))
  mul := fun x y => quotientProduct D hD x y
  one := (ActualZhuFinite.zhuO D).mkQ (vacuum D)
  mul_assoc x y z := by
    obtain ⟨u,rfl⟩ := (ActualZhuFinite.zhuO D).mkQ_surjective x
    obtain ⟨v,rfl⟩ := (ActualZhuFinite.zhuO D).mkQ_surjective y
    obtain ⟨w,rfl⟩ := (ActualZhuFinite.zhuO D).mkQ_surjective z
    change quotientProduct D hD (quotientProduct D hD _ _) _ =
      quotientProduct D hD _ (quotientProduct D hD _ _)
    simp only [quotientProduct_mk]
    exact (Submodule.Quotient.eq _).mpr (ActualZhuAssociator.associator_mem_zhuO D hD u v w)
  one_mul x := by
    obtain ⟨u,rfl⟩ := (ActualZhuFinite.zhuO D).mkQ_surjective x
    change quotientProduct D hD ((ActualZhuFinite.zhuO D).mkQ (vacuum D))
      ((ActualZhuFinite.zhuO D).mkQ u) = _
    rw [quotientProduct_mk, star_vacuum_left D hD]
  mul_one x := by
    obtain ⟨u,rfl⟩ := (ActualZhuFinite.zhuO D).mkQ_surjective x
    change quotientProduct D hD ((ActualZhuFinite.zhuO D).mkQ u)
      ((ActualZhuFinite.zhuO D).mkQ (vacuum D)) = _
    rw [quotientProduct_mk, star_vacuum_right D hD]
  left_distrib x y z := (quotientProduct D hD x).map_add y z
  right_distrib x y z := congrArg (fun f : Q D →ₗ[ℂ] Q D => f z)
    ((quotientProduct D hD).map_add x y)
  zero_mul x := congrArg (fun f : Q D →ₗ[ℂ] Q D => f x) (map_zero (quotientProduct D hD))
  mul_zero x := map_zero (quotientProduct D hD x)

/-- The original complex module action makes the actual quotient ring an algebra. -/
@[instance_reducible]
def quotientAlgebra (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    letI := quotientRing D hD
    Algebra ℂ (Q D) := by
  letI := quotientRing D hD
  apply Algebra.ofModule
  · intro c x y
    exact congrArg (fun f : Q D →ₗ[ℂ] Q D => f y) ((quotientProduct D hD).map_smul c x)
  · intro c x y
    exact (quotientProduct D hD x).map_smul c y

private theorem projection_circle_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K : ℕ} {a : Carrier D}
    (ha : a ∈ grade D (K : ℤ)) (b : Carrier D) :
    gradeProjection D 0 (NormFourZhuFinite.circle D K a b) = 0 := by
  classical
  conv_lhs => rw [← sum_gradeProjections D b]
  unfold NormFourZhuFinite.circle
  simp only [mu, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro q hq
  have hq0 := stateEnergies_nonneg hD b q hq
  have hm := positive_actual_mode_grade D hD (K : ℤ) q ((i : ℤ)-2)
    a (gradeProjection D q b) ha (gradeProjection_mem D q b)
  have hp : (K : ℤ)+q-((i : ℤ)-2)-1 ≠ 0 := by
    have hi' := Finset.mem_range.mp hi
    omega
  rw [gradeProjection_zero_of_mem_grade_ne D 0 _ hp _ hm, smul_zero]

private theorem projection_O_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (o : Carrier D)
    (ho : o ∈ ActualZhuFinite.zhuO D) : gradeProjection D 0 o = 0 := by
  induction ho using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨K,a,b,ha,rfl⟩ := hz
    exact projection_circle_zero D hD ha b
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- The vacuum survives the literal O quotient; no homogeneity of O is assumed. -/
theorem vacuum_not_mem_zhuO (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    vacuum D ∉ ActualZhuFinite.zhuO D := by
  intro hv
  have hz := projection_O_zero D hD (vacuum D) hv
  rw [gradeProjection_eq_self_of_mem_grade D 0 _ (vacuum_grade D hD)] at hz
  exact vacuum_nonzero D hz

set_option linter.defProp false in
/-- Distinct vacuum and zero classes make the actual algebra nontrivial. -/
@[instance_reducible]
def quotientNontrivial (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : Nontrivial (Q D) :=
  ⟨⟨(ActualZhuFinite.zhuO D).mkQ (vacuum D), 0, fun h =>
    vacuum_not_mem_zhuO D hD ((Submodule.Quotient.mk_eq_zero _).mp h)⟩⟩

#print axioms quotientRing
#print axioms quotientAlgebra
#print axioms vacuum_not_mem_zhuO
#print axioms quotientNontrivial
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuAlgebra
