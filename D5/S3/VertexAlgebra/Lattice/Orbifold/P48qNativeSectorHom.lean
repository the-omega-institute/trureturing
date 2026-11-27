/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeSectorHom
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeSectorHom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-field module morphisms out of the ground-containing native cubic sector. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan
import Mathlib.LinearAlgebra.Span.Basic
import OmegaBuild.Commands

/-! The native ground weight distinguishes rotation sector zero and determines
every fixed-field intertwiner out of it. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSectorHom

open P48qNativeConformalSector
  (fixedStates sector fixedField fixedOmega fixedField_conformal_zero vacuum_mem_sector_zero)
open P48qNativeGradingRotation (gradingRotation)
open P48qNativeModeProductSpan (fixedModeSpan fixedModeSpan_eq_top)
open P48qTwistedStateEnergy (totalLZero totalLZero_ground_eigenspace
  vacuum vacuum_ne_zero totalLZero_vacuum)

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- The linear maps commuting with every integral coefficient of every actual fixed field. -/
def sectorHomSpace (r s : Fin 3) : Submodule ℂ (sector r →ₗ[ℂ] sector s) where
  carrier := {f | ∀ (a : fixedStates) (n : ℤ) (v : sector r),
    f (C (fixedField r a) n v) = C (fixedField s a) n (f v)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a n v
    simp only [LinearMap.add_apply, map_add]
    exact congrArg₂ (· + ·) (hf a n v) (hg a n v)
  smul_mem' := by
    intro c f hf a n v
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (c • ·) (hf a n v)

private def groundVector : sector 0 := ⟨vacuum, vacuum_mem_sector_zero⟩

private theorem groundVector_ne_zero : groundVector ≠ 0 :=
  fun h => vacuum_ne_zero (congrArg (fun v : sector 0 => v.val) h)

private theorem fixedConformal_groundVector :
    C (fixedField 0 fixedOmega) (-2) groundVector = (16 / 9 : ℂ) • groundVector := by
  apply Subtype.ext
  exact (fixedField_conformal_zero 0 groundVector).trans totalLZero_vacuum

private theorem ground_weight_scalar {s : Fin 3} {v : sector s}
    (h : C (fixedField s fixedOmega) (-2) v = (16 / 9 : ℂ) • v) :
    ∃ c : ℂ, c • vacuum = v.val := by
  have he : totalLZero v.val = (16 / 9 : ℂ) • v.val := by
    simpa only [fixedField_conformal_zero, Submodule.coe_smul] using
      congrArg (fun w : sector s => w.val) h
  have hm : v.val ∈ totalLZero.eigenspace (16 / 9 : ℂ) :=
    Module.End.mem_eigenspace_iff.mpr he
  rw [totalLZero_ground_eigenspace] at hm
  exact Submodule.mem_span_singleton.mp hm

/-- Sector zero is precisely the rotation sector containing the native ground weight. -/
theorem ground_weight_occurs_iff (s : Fin 3) :
    (∃ v : sector s, v ≠ 0 ∧ C (fixedField s fixedOmega) (-2) v = (16 / 9 : ℂ) • v) ↔
      s = 0 := by
  constructor
  · rintro ⟨v, hv, hweight⟩
    obtain ⟨c, hc⟩ := ground_weight_scalar hweight
    have hgroundRotation : gradingRotation vacuum = vacuum := by
      have h := vacuum_mem_sector_zero
      rw [sector, Module.End.mem_eigenspace_iff, Fin.val_zero, pow_zero, one_smul] at h
      exact h
    have hfixed : gradingRotation v.val = v.val := by
      rw [← hc, map_smul, hgroundRotation]
    have hrot : gradingRotation v.val = ζ ^ s.val • v.val :=
      Module.End.mem_eigenspace_iff.mp v.property
    have hv' : v.val ≠ 0 := fun hz => hv (Subtype.ext hz)
    have hphase : ζ ^ s.val = 1 := smul_left_injective ℂ hv'
      (hrot.symm.trans (hfixed.trans (one_smul ℂ v.val).symm))
    have hζ : IsPrimitiveRoot ζ 3 :=
      IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
    apply Fin.ext
    exact hζ.pow_inj s.isLt (by decide : (0 : ℕ) < 3)
      (by simpa only [Fin.val_zero, pow_zero] using hphase)
  · rintro rfl
    exact ⟨groundVector, groundVector_ne_zero, fixedConformal_groundVector⟩

private theorem vacuum_image_weight {s : Fin 3} (f : sectorHomSpace 0 s) :
    C (fixedField s fixedOmega) (-2) (f.val groundVector) =
      (16 / 9 : ℂ) • f.val groundVector := by
  rw [← f.property fixedOmega (-2) groundVector, fixedConformal_groundVector, map_smul]

private theorem hom_eq_zero_of_vacuum {s : Fin 3} (f : sectorHomSpace 0 s)
    (hf : f.val groundVector = 0) : f = 0 := by
  have hker : fixedModeSpan 0 groundVector ≤ LinearMap.ker f.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, n⟩, rfl⟩
    exact LinearMap.mem_ker.mpr (by rw [f.property a n groundVector, hf, map_zero])
  rw [fixedModeSpan_eq_top 0 groundVector groundVector_ne_zero] at hker
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  exact LinearMap.mem_ker.mp (hker (Submodule.mem_top : v ∈ ⊤))

/-- An actual fixed-field intertwiner from rotation sector zero into a different sector vanishes. -/
theorem hom_wrong_sector (s : Fin 3) (hs : s ≠ 0) (f : sectorHomSpace 0 s) : f = 0 := by
  apply hom_eq_zero_of_vacuum
  by_contra hf
  exact hs ((ground_weight_occurs_iff s).mp ⟨f.val groundVector, hf, vacuum_image_weight f⟩)

/-- The scalar identity maps on the ground-containing sector. -/
def scalarHom : ℂ →ₗ[ℂ] sectorHomSpace 0 0 :=
  LinearMap.toSpanSingleton ℂ (sectorHomSpace 0 0)
    ⟨LinearMap.id, by intro a n v; rfl⟩

/-- Every actual fixed-field endomorphism of rotation sector zero is a unique scalar identity. -/
theorem hom_scalar (f : sectorHomSpace 0 0) : ∃! c : ℂ, scalarHom c = f := by
  obtain ⟨c, hc⟩ := ground_weight_scalar (vacuum_image_weight f)
  have hvalue : (scalarHom c).val groundVector = f.val groundVector := by
    apply Subtype.ext
    exact hc
  have hdiff : scalarHom c - f = 0 := by
    apply hom_eq_zero_of_vacuum
    change (scalarHom c).val groundVector - f.val groundVector = 0
    exact sub_eq_zero.mpr hvalue
  refine ⟨c, sub_eq_zero.mp hdiff, ?_⟩
  intro d hd
  apply smul_left_injective ℂ groundVector_ne_zero
  change (scalarHom d).val groundVector = (scalarHom c).val groundVector
  rw [hd]
  exact hvalue.symm

/-- Scalar normalization for the ground-containing module, with `1` giving the identity. -/
def scalarHomEquiv : ℂ ≃ₗ[ℂ] sectorHomSpace 0 0 :=
  LinearEquiv.ofBijective scalarHom ((Function.bijective_iff_existsUnique _).mpr hom_scalar)

#print axioms ground_weight_occurs_iff
#print axioms hom_wrong_sector
#print axioms hom_scalar
#print axioms scalarHomEquiv

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSectorHom
