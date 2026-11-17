/- GID: D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full Zhu quotient action on the entire dual-coset bottom. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native adaptation of VOA/Modules/ZhuModule.lean and
VOA/Modules/ZeroModeMult.lean, Fedor-Popov/Lean_VOA at
013a799ca834a8a6b3afa8129e3e522025b3f45c.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetZhuZeroMode
import D5.S3.VertexAlgebra.Lattice.ActualZhuAlgebra

/-!
The Zhu/Frenkel--Zhu residue construction uses the original full circle span.
The source lineage is Fedor K. Popov's Apache-2.0 Lean_VOA, immutable revision
013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean
and ZeroModeMult.lean. All fields, products, energy decompositions, and the
literal quotient are native suppliers; no module product law is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeDualCosetZhu

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeDualCosetConformal LatticeDualCosetModule LatticeDualCosetEnergy
open Lattice.ActualZhuProduct
open scoped BigOperators VertexOperator

noncomputable section
variable (D : LatticeData) (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

private theorem circle_homogeneous (p q : ℕ) (a b : Carrier D)
    (ha : a ∈ grade D (p : ℤ)) (hb : b ∈ grade D (q : ℤ)) :
    zeroMode D β μ hDual hD (Lattice.NormFourZhuFinite.circle D p a b) = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have he (j : ℕ) :
      (zeroMode D β μ hDual hD (mu D a ((j : ℤ) - 2) b) v).val =
        ((action D β (mu D a ((j : ℤ) - 2) b))[[((p : ℤ) + q - j)]]) v.val := by
    have hg := positive_actual_mode_grade D hD (p : ℤ) (q : ℤ) ((j : ℤ) - 2)
      a b ha hb
    have hi : ((p : ℤ) + q - ((j : ℤ) - 2) - 1) - 1 = (p : ℤ) + q - j := by omega
    simpa only [hi, mu] using zeroMode_homogeneous D β μ hDual hD _ _ hg v
  change (zeroMode D β μ hDual hD
    (∑ j ∈ Finset.range (p + 1), (p.choose j : ℂ) • mu D a ((j : ℤ) - 2) b) v).val = 0
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul]
  simp_rw [he]
  have h := Lattice.NormFourZhuAlgebra.Core.circle_residue_top
    (action D β a) (action D β b) (fun r => action D β (mu D a r b))
    (module_fullLaw D β a b) p q v.val
    (fun j => high_mode_kills_bottom D β μ hDual hD _ _ a v.val ha v.property (by omega))
    (fun j => high_mode_kills_bottom D β μ hDual hD _ _ b v.val hb v.property (by omega))
  simpa only [show ∀ j : ℕ, -2 + (j : ℤ) = (j : ℤ) - 2 from fun j => by omega] using h

private theorem star_homogeneous_zeroMode (p q : ℕ) (a b : Carrier D)
    (ha : a ∈ grade D (p : ℤ)) (hb : b ∈ grade D (q : ℤ)) :
    zeroMode D β μ hDual hD (star D a b) =
      zeroMode D β μ hDual hD a * zeroMode D β μ hDual hD b := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have he (j : ℕ) :
      (zeroMode D β μ hDual hD (mu D a ((j : ℤ) - 1) b) v).val =
        ((action D β (mu D a ((j : ℤ) - 1) b))[[((p : ℤ) + q - 1 - j)]]) v.val := by
    have hg := positive_actual_mode_grade D hD (p : ℤ) (q : ℤ) ((j : ℤ) - 1)
      a b ha hb
    have hi : ((p : ℤ) + q - ((j : ℤ) - 1) - 1) - 1 = (p : ℤ) + q - 1 - j := by omega
    simpa only [hi, mu] using zeroMode_homogeneous D β μ hDual hD _ _ hg v
  rw [star_homogeneous D p a b ha]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, Module.End.mul_apply]
  simp_rw [he, zeroMode_homogeneous D β μ hDual hD _ a ha,
    zeroMode_homogeneous D β μ hDual hD _ b hb]
  have h := Lattice.NormFourZhuAlgebra.Core.star_residue_top
    (action D β a) (action D β b) (fun r => action D β (mu D a r b))
    (module_fullLaw D β a b) p q v.val
    (fun j => high_mode_kills_bottom D β μ hDual hD _ _ a v.val ha v.property (by omega))
    (fun j => high_mode_kills_bottom D β μ hDual hD _ _ b v.val hb v.property (by omega))
  simpa only [show ∀ j : ℕ, -1 + (j : ℤ) = (j : ℤ) - 1 from fun j => by omega,
    show ∀ j : ℕ, (p : ℤ) + ((q : ℤ) - 1) - j = (p : ℤ) + q - 1 - j
      from fun j => by omega] using h

/-- Every literal circle generator, with unrestricted second state, acts by zero. -/
theorem zeroMode_circle (p : ℕ) (a b : Carrier D) (ha : a ∈ grade D (p : ℤ)) :
    zeroMode D β μ hDual hD (Lattice.NormFourZhuFinite.circle D p a b) = 0 := by
  have hb := sum_gradeProjections D b
  have he : Lattice.NormFourZhuFinite.circle D p a b =
      ∑ q ∈ stateEnergies D b,
        Lattice.NormFourZhuFinite.circle D p a (gradeProjection D q b) := by
    conv_lhs => rw [← hb]
    simp only [Lattice.NormFourZhuFinite.circle, mu, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (stateEnergies_nonneg hD b q hq)
  exact circle_homogeneous D β μ hDual hD p q.toNat a (gradeProjection D q b) ha
    (by simpa only [hqn] using gradeProjection_mem D q b)

/-- The original full circle span is contained in the zero-mode kernel. -/
theorem zhuO_le_kernel : Lattice.ActualZhuFinite.zhuO D ≤
    LinearMap.ker (zeroMode D β μ hDual hD) := by
  apply Submodule.span_le.mpr
  rintro z ⟨p, a, b, ha, rfl⟩
  exact zeroMode_circle D β μ hDual hD p a b ha

/-- Multiplicativity on both unrestricted original input states. -/
theorem zeroMode_star (a b : Carrier D) :
    zeroMode D β μ hDual hD (star D a b) =
      zeroMode D β μ hDual hD a * zeroMode D β μ hDual hD b := by
  have he : star D a b = ∑ p ∈ stateEnergies D a, ∑ q ∈ stateEnergies D b,
      star D (gradeProjection D p a) (gradeProjection D q b) := by
    conv_lhs => rw [← sum_gradeProjections D a, ← sum_gradeProjections D b]
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_comm
  rw [he, map_sum]
  have hm (p : ℤ) (hp : p ∈ stateEnergies D a) (q : ℤ) (hq : q ∈ stateEnergies D b) :
      zeroMode D β μ hDual hD (star D (gradeProjection D p a) (gradeProjection D q b)) =
        zeroMode D β μ hDual hD (gradeProjection D p a) *
          zeroMode D β μ hDual hD (gradeProjection D q b) := by
    have hpn : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (stateEnergies_nonneg hD a p hp)
    have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (stateEnergies_nonneg hD b q hq)
    exact star_homogeneous_zeroMode D β μ hDual hD p.toNat q.toNat _ _
      (by simpa only [hpn] using gradeProjection_mem D p a)
      (by simpa only [hqn] using gradeProjection_mem D q b)
  simp_rw [map_sum]
  calc
    _ = ∑ p ∈ stateEnergies D a, ∑ q ∈ stateEnergies D b,
        zeroMode D β μ hDual hD (gradeProjection D p a) *
          zeroMode D β μ hDual hD (gradeProjection D q b) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_congr rfl (fun q hq => hm p hp q hq)
    _ = _ := by
      rw [← Finset.sum_mul_sum, ← map_sum, ← map_sum,
        sum_gradeProjections, sum_gradeProjections]

/-- The original vacuum has the identity zero mode on the full bottom. -/
theorem zeroMode_vacuum : zeroMode D β μ hDual hD (vacuum D) = 1 := by
  have hv : vacuum D ∈ grade D 0 := by
    rw [grade_zero D hD]
    exact Submodule.subset_span (Set.mem_singleton _)
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [zeroMode_homogeneous D β μ hDual hD 0 _ hv, module_vacuum]
  simp [LatticeAllStateField.identity_modes]

/-- Descent through the existing full Zhu quotient, with its existing algebra structure. -/
def representation :
    letI := Lattice.ActualZhuAlgebra.quotientRing D hD
    letI := Lattice.ActualZhuAlgebra.quotientAlgebra D hD
    Lattice.ActualZhuAlgebra.Q D →ₐ[ℂ] Module.End ℂ (Bottom D μ hD) := by
  letI := Lattice.ActualZhuAlgebra.quotientRing D hD
  letI := Lattice.ActualZhuAlgebra.quotientAlgebra D hD
  let f := (Lattice.ActualZhuFinite.zhuO D).liftQ (zeroMode D β μ hDual hD)
    (zhuO_le_kernel D β μ hDual hD)
  apply AlgHom.ofLinearMap f
  · exact zeroMode_vacuum D β μ hDual hD
  · intro x y
    obtain ⟨a, rfl⟩ := (Lattice.ActualZhuFinite.zhuO D).mkQ_surjective x
    obtain ⟨b, rfl⟩ := (Lattice.ActualZhuFinite.zhuO D).mkQ_surjective y
    change f (Lattice.ActualZhuAlgebra.quotientProduct D hD _ _) = _
    rw [Lattice.ActualZhuAlgebra.quotientProduct_mk]
    exact zeroMode_star D β μ hDual hD a b

/-- Representative evaluation is the actual module zero mode in each homogeneous degree. -/
theorem representation_mk (k : ℤ) (a : Carrier D) (ha : a ∈ grade D k)
    (v : Bottom D μ hD) :
    (representation D β μ hDual hD ((Lattice.ActualZhuFinite.zhuO D).mkQ a) v).val =
      ((action D β a)[[k - 1]]) v.val :=
  zeroMode_homogeneous D β μ hDual hD k a ha v

#print axioms module_fullLaw
#print axioms high_mode_kills_bottom
#print axioms zeroMode_circle
#print axioms zhuO_le_kernel
#print axioms zeroMode_star
#print axioms representation

end
end D5.S3.VertexAlgebra.LatticeDualCosetZhu
