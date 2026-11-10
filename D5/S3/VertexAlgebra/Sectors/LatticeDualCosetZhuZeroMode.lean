/- GID: D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original all-state zero modes on the entire dual-coset bottom and their residue law. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native adaptation of VOA/Modules/ZhuModule.lean and
VOA/Modules/ZeroModeMult.lean, Fedor-Popov/Lean_VOA at
013a799ca834a8a6b3afa8129e3e522025b3f45c.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetEnergyEndpoints
import D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra.Core

/-!
The original carrier, fields and dual-coset module are unchanged. The bottom is
an entire rational energy fiber, including every minimizing charge. The residue
argument follows Zhu's module construction, as formalized by Fedor K. Popov,
Lean_VOA commit 013a799ca834a8a6b3afa8129e3e522025b3f45c,
VOA/Modules/ZhuModule.lean and ZeroModeMult.lean, under Apache-2.0.
The native module Borcherds theorem supplies all three separate finite supports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeDualCosetZhu

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeDualCosetConformal LatticeDualCosetModule LatticeDualCosetEnergy
open LatticeHalfFockGroundRightCurrentTransport.Calculus
open scoped BigOperators VertexOperator DirectSum

noncomputable section

variable (D : LatticeData)

/-- The full bottom fiber; no minimizing charge is selected inside the fiber. -/
abbrev Bottom (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :=
  rationalGrade D μ (chargeWeight D μ (minimizingCharge D μ hD))

/-- Original module Borcherds, with its separate supports, in the generic residue calculus. -/
theorem module_fullLaw (β : Charge D) (a b : Carrier D) :
    fullLaw (action D β a) (action D β b)
      (fun r => action D β (mu D a r b)) 0 := by
  have binom (p : ℤ) (i : ℕ) :
      StateFieldResidueReconstruction.integerBinomial p i = Ring.choose (p : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) p i
  intro p q r v
  obtain ⟨hl, hf, hs, h⟩ := module_borcherds D β a b v p q r
  have el : moduleLeft D β p q r a b v =
      leftTerm (fun t => action D β (mu D a t b)) 0 p q r v := by
    funext i
    simp [moduleLeft, leftTerm, binom, mu]
  have ef : moduleFirst D β p q r a b v =
      firstTerm (action D β a) (action D β b) p q r v := by
    funext i
    simp [moduleFirst, firstTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight,
      binom]
  have es : moduleSecond D β p q r a b v =
      secondTerm (action D β a) (action D β b) p q r v := by
    funext i
    simp [moduleSecond, secondTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight,
      StateFieldResidueReconstruction.epsilon, binom]
  refine ⟨el ▸ hl, ef ▸ hf, es ▸ hs, ?_⟩
  simp_rw [smul_sub] at h
  change (∑ᶠ i : ℕ, moduleLeft D β p q r a b v i) =
    ∑ᶠ i : ℕ, (moduleFirst D β p q r a b v i - moduleSecond D β p q r a b v i) at h
  rw [finsum_sub_distrib hf hs, el, ef, es] at h
  exact h

/-- Minimal energy kills every homogeneous mode whose index is at least its weight. -/
theorem high_mode_kills_bottom (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (k n : ℤ) (a v : Carrier D) (ha : a ∈ grade D k)
    (hv : v ∈ Bottom D μ hD) (hkn : k ≤ n) :
    ((action D β a)[[n]]) v = 0 := by
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists D hD
  by_contra hne
  have he := LatticeDualCosetEnergy.actual_mode_grade D β H hHG hGH μ hDual
    k n _ a v ha hv
  have heig := (moduleL_eigen_iff D β H hHG hGH μ hDual _ _).mpr he
  obtain ⟨m, hm⟩ := point_spectrum_subset D β H hHG hGH μ hDual hD _
    ⟨((action D β a)[[n]]) v, hne, heig⟩
  have hq :
      chargeWeight D μ (minimizingCharge D μ hD) + (k : ℚ) - (n : ℚ) - 1 =
      chargeWeight D μ (minimizingCharge D μ hD) + (m : ℚ) := by
    apply (Rat.cast_injective : Function.Injective (fun x : ℚ => (x : ℂ)))
    simpa only [Rat.cast_add] using hm
  have hknQ : (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast hkn
  have hmQ : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  linarith

private def homogeneousZero (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (k : ℤ) :
    grade D k →ₗ[ℂ] Module.End ℂ (Bottom D μ hD) := by
  let H := Classical.choose (complex_inverse_exists D hD)
  have hHG := (Classical.choose_spec (complex_inverse_exists D hD)).1
  have hGH := (Classical.choose_spec (complex_inverse_exists D hD)).2
  have stable (a : grade D k) (v : Bottom D μ hD) :
      ((action D β a.val)[[k - 1]]) v.val ∈ Bottom D μ hD := by
    have he := LatticeDualCosetEnergy.actual_mode_grade D β H hHG hGH μ hDual
      k (k - 1) (chargeWeight D μ (minimizingCharge D μ hD))
      a.val v.val a.property v.property
    have hshift : chargeWeight D μ (minimizingCharge D μ hD) + (k : ℚ) -
        ((k - 1 : ℤ) : ℚ) - 1 = chargeWeight D μ (minimizingCharge D μ hD) := by
      push_cast
      ring
    simpa only [hshift] using he
  let z (a : grade D k) : Module.End ℂ (Bottom D μ hD) := {
    toFun v := ⟨((action D β a.val)[[k - 1]]) v.val, stable a v⟩
    map_add' v w := Subtype.ext (((action D β a.val)[[k - 1]]).map_add v.val w.val)
    map_smul' c v := Subtype.ext (((action D β a.val)[[k - 1]]).map_smul c v.val) }
  refine { toFun := z, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((action D β (a.val + b.val))[[k - 1]]) v.val = _
    simp [z]
  · intro c a
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((action D β (c • a.val))[[k - 1]]) v.val = _
    simp [z]

/-- A complex-linear zero mode on every original state, via the existing internal direct sum. -/
def zeroMode (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Carrier D →ₗ[ℂ] Module.End ℂ (Bottom D μ hD) :=
  (DirectSum.toModule ℂ ℤ (Module.End ℂ (Bottom D μ hD))
    (homogeneousZero D β μ hDual hD)).comp (carrierEnergyDecomposition D).toLinearMap

/-- Evaluation at any integer homogeneous degree, including zero or negative fused degrees. -/
theorem zeroMode_homogeneous (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (k : ℤ) (a : Carrier D) (ha : a ∈ grade D k) (v : Bottom D μ hD) :
    (zeroMode D β μ hDual hD a v).val = ((action D β a)[[k - 1]]) v.val := by
  have he : carrierEnergyDecomposition D a =
      DirectSum.lof ℂ ℤ (fun n => grade D n) k ⟨a, ha⟩ := by
    apply (carrierEnergyDecomposition D).symm.injective
    simp [carrierEnergyDecomposition]
  change (DirectSum.toModule ℂ ℤ (Module.End ℂ (Bottom D μ hD)) _
    (carrierEnergyDecomposition D a) v).val = _
  rw [he, DirectSum.toModule_lof]
  rfl

end
end D5.S3.VertexAlgebra.LatticeDualCosetZhu
