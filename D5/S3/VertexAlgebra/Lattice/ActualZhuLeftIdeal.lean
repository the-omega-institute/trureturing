/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuLeftIdeal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuLeftIdeal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Translation residue identity and left stability of the original full Zhu O. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native port of VOA/Modules/ZhuModule.lean (cbz_coeff_identity,
zhuMul_L_base) and ZhuRingResidue.lean (left_ideal_gen_of_assoc),
Fedor-Popov/Lean_VOA at 013a799ca834a8a6b3afa8129e3e522025b3f45c.
The literal circle span and all original states are retained.
proof_shape: translation_star_circle: content; star_left_mem_zhuO: content.
admission_basis: escape-witness.
escape_witness: the derivative shifts the star row, whose complete binomial
coefficient cancellation identifies the literal circle; the actual associator
then proves stability on its span. Private helpers are consumed below.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuAssociator
/-! The original circle is a translated star residue, hence is left stable. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuLeftIdeal
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticePositiveEnergy LatticeSugawaraConformal LatticeActualStateDerivative ActualZhuProduct
open scoped BigOperators VertexOperator
open private cbz cbz_nat cbz_apply_neg cbz_lt cbz_pascal cbz_upper_absorption
  from D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
open private translation_grade derivative_mu
  from D5.S3.VertexAlgebra.Lattice.ActualZhuProduct
open private star_homogeneous_cbz
  from D5.S3.VertexAlgebra.Lattice.ActualZhuAssociatorExpansion
noncomputable section

private theorem coeff_identity (K : ℕ) (i : ℤ) :
    cbz ((K : ℤ)+1) i * (-((i : ℂ)-1)) + (K : ℂ) * cbz (K : ℤ) (i-1)
      = cbz (K : ℤ) i := by
  have hp := cbz_pascal ((K : ℤ)+1) i
  rw [show (K : ℤ)+1-1 = K by ring] at hp
  have ha := cbz_upper_absorption (K+1) i
  rw [show (((K+1 : ℕ) : ℤ)-1) = K by omega] at ha
  push_cast at ha
  linear_combination hp - ha

/-- The derivative and weight term have exactly the original circle residue. -/
theorem translation_star_circle (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K : ℕ} {a : Carrier D}
    (ha : a ∈ grade D (K : ℤ)) (b : Carrier D) :
    star D (translation D a + (K : ℂ) • a) b = NormFourZhuFinite.circle D K a b := by
  classical
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  have hT : star D (translation D a) b =
      ∑ i ∈ Finset.range (K+2),
        (cbz ((K : ℤ)+1) (i : ℤ) * (-((i : ℂ)-1))) • mu D a ((i : ℤ)-2) b := by
    rw [star_homogeneous_cbz D (by omega) (translation_grade D hD K a ha) b,
      show ((K : ℤ)+1).toNat+1 = K+2 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [derivative_mu, show (i : ℤ)-1-1 = (i : ℤ)-2 by ring, smul_smul]
    congr 2
    push_cast
    ring
  have hK : (K : ℂ) • star D a b =
      ∑ i ∈ Finset.range (K+2),
        ((K : ℂ) * cbz (K : ℤ) ((i : ℤ)-1)) • mu D a ((i : ℤ)-2) b := by
    rw [star_homogeneous_cbz D (by positivity) ha b, Int.toNat_natCast, Finset.smul_sum]
    rw [Finset.sum_range_succ' (fun i =>
      ((K : ℂ) * cbz (K : ℤ) ((i : ℤ)-1)) • mu D a ((i : ℤ)-2) b) (K+1)]
    rw [show cbz (K : ℤ) ((0 : ℕ)-1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
      mul_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 2
    · congr 1 <;> push_cast <;> ring
    · push_cast; ring
  rw [hT, hK, ← Finset.sum_add_distrib]
  simp only [← add_smul]
  rw [show (∑ i ∈ Finset.range (K+2),
      (cbz ((K : ℤ)+1) (i : ℤ) * (-((i : ℂ)-1)) +
        (K : ℂ) * cbz (K : ℤ) ((i : ℤ)-1)) • mu D a ((i : ℤ)-2) b) =
      ∑ i ∈ Finset.range (K+2), cbz (K : ℤ) (i : ℤ) • mu D a ((i : ℤ)-2) b from by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hc := coeff_identity K (i : ℤ)
    push_cast at hc
    exact hc]
  rw [Finset.sum_range_succ,
    cbz_lt (by positivity) (by omega : (K : ℤ) < ((K+1 : ℕ) : ℤ)), zero_smul, add_zero]
  unfold NormFourZhuFinite.circle
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cbz_nat]
  simp [StateFieldResidueReconstruction.integerBinomial, Ring.choose_natCast]

/-- Star preserves the same literal O in its left argument, for every original state. -/
theorem star_left_mem_zhuO (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (o v : Carrier D)
    (ho : o ∈ ActualZhuFinite.zhuO D) : star D o v ∈ ActualZhuFinite.zhuO D := by
  classical
  induction ho using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨K,a,b,ha,rfl⟩ := hz
    have h1 : star D (translation D a + (K : ℂ) • a) (star D b v)
        ∈ ActualZhuFinite.zhuO D := by
      rw [translation_star_circle D hD ha]
      exact Submodule.subset_span ⟨K,a,star D b v,ha,rfl⟩
    have h2 := ActualZhuAssociator.associator_mem_zhuO D hD
      (translation D a + (K : ℂ) • a) b v
    rw [translation_star_circle D hD ha] at h2
    have h := (ActualZhuFinite.zhuO D).add_mem h1 h2
    convert h using 1; abel
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add, LinearMap.add_apply] using (ActualZhuFinite.zhuO D).add_mem hx hy
  | smul c x _ hx =>
    simpa only [map_smul, LinearMap.smul_apply] using (ActualZhuFinite.zhuO D).smul_mem c hx

#print axioms translation_star_circle
#print axioms star_left_mem_zhuO
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuLeftIdeal
